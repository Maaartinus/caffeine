/*
 * Copyright 2015 Ben Manes. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.github.benmanes.caffeine.cache;

import java.util.concurrent.ThreadLocalRandom;

import javax.annotation.Nonnegative;
import javax.annotation.Nonnull;
import javax.annotation.concurrent.NotThreadSafe;

/**
 * A probabilistic multiset for estimating the popularity of an element within a time window. The
 * maximum frequency of an element is limited to 15 (4-bits) and an aging process periodically
 * halves the popularity of all elements.
 *
 * @author ben.manes@gmail.com (Ben Manes)
 */
@NotThreadSafe
final class MgFrequencySketch1<E> {

  /*
   * This class maintains a 4-bit CountMinSketch [1] with periodic aging to provide the popularity
   * history for the TinyLfu admission policy [2]. The time and space efficiency of the sketch
   * allows it to cheaply estimate the frequency of an entry in a stream of cache access events.
   *
   * The counter matrix is represented as a single dimensional array holding 16 counters per slot. A
   * fixed depth of four balances the accuracy and cost, resulting in a width of four times the
   * length of the array. To retain an accurate estimation the array's length equals the maximum
   * number of entries in the cache, increased to the closest power-of-two to exploit more efficient
   * bit masking. This configuration results in a confidence of 93.75% and error bound of e / width.
   *
   * The frequency of all entries is aged periodically using a sampling window based on the maximum
   * number of entries in the cache. This is referred to as the reset operation by TinyLfu and keeps
   * the sketch fresh by dividing all counters by two and subtracting based on the number of odd
   * counters found. The O(n) cost of aging is amortized, ideal for hardware prefetching, and uses
   * inexpensive bit manipulations per array location.
   *
   * A per instance smear is used to help protect against hash flooding [3], which would result
   * in the admission policy always rejecting new candidates. The use of a pseudo random hashing
   * function resolves the concern of a denial of service attack by exploiting the hash codes.
   *
   * [1] An Improved Data Stream Summary: The Count-Min Sketch and its Applications
   * http://dimacs.rutgers.edu/~graham/pubs/papers/cm-full.pdf
   * [2] TinyLFU: A Highly Efficient Cache Admission Policy
   * http://arxiv.org/pdf/1512.00727.pdf
   * [3] Denial of Service via Algorithmic Complexity Attack
   * https://www.usenix.org/legacy/events/sec03/tech/full_papers/crosby/crosby.pdf
   */

  // Taken from Murmur3.
  private static final long C1 = 0x87c37b91114253d5L;
  private static final long C2 = 0x4cf5ad432745937fL;

  static final long RESET_MASK = 0x7777777777777777L;
  static final long ONE_MASK = 0x1111111111111111L;

  final int randomSeed;
  boolean conservative;

  int sampleSize;
  int tableShift;
  long[] table;
  int size;

  /**
   * Creates a lazily initialized frequency sketch, requiring {@link #ensureCapacity} be called
   * when the maximum size of the cache has been determined.
   */
  public MgFrequencySketch1() {
    int seed = ThreadLocalRandom.current().nextInt();
    this.randomSeed = ((seed & 1) == 0) ? seed + 1 : seed;
  }

  /**
   * Initializes and increases the capacity of this <tt>FrequencySketch</tt> instance, if necessary,
   * to ensure that it can accurately estimate the popularity of elements given the maximum size of
   * the cache. This operation forgets all previous counts when resizing.
   *
   * @param maximumSize the maximum size of the cache
   */
  public void ensureCapacity(@Nonnegative long maximumSize) {
    Caffeine.requireArgument(maximumSize >= 0);
    int maximum = (int) Math.min(maximumSize, Integer.MAX_VALUE >>> 1);
    if ((table != null) && (table.length >= maximum)) {
      return;
    }

    table = new long[(maximum <= 2) ? 2 : ceilingNextPowerOfTwo(maximum)];
    tableShift = table.length - 1;
    sampleSize = (maximumSize == 0) ? 10 : (10 * maximum);
    if (sampleSize <= 0) {
      sampleSize = Integer.MAX_VALUE;
    }
    size = 0;
  }

  /**
   * Returns if the sketch has not yet been initialized, requiring that {@link #ensureCapacity} is
   * called before it begins to track frequencies.
   */
  public boolean isNotInitialized() {
    return (table == null);
  }

  /**
   * Returns the estimated number of occurrences of an element, up to the maximum (15).
   *
   * @param e the element to count occurrences of
   * @return the estimated number of occurrences of the element; possibly zero but never negative
   */
  @Nonnegative
  public int frequency(@Nonnull E e) {
    if (isNotInitialized()) {
      return 0;
    }

    return frequency(spread(e.hashCode()));
  }

  @Nonnegative
  private int frequency(long hash) {
    if (isNotInitialized()) {
      return 0;
    }

    int result = extract(hash);
    hash = respread1(hash);
    result = Math.min(result, extract(hash));
    hash = respread2(hash);
    result = Math.min(result, extract(hash));
    hash = respread3(hash);
    result = Math.min(result, extract(hash));
    return result;
  }

  /**
   * Increments the popularity of the element if it does not exceed the maximum (15). The popularity
   * of all elements will be periodically down sampled when the observed events exceeds a threshold.
   * This process provides a frequency aging to allow expired long term entries to fade away.
   *
   * @param e the element to add
   */
  public void increment(@Nonnull E e) {
    if (isNotInitialized()) {
      return;
    }

    increment(spread(e.hashCode()), 1);
  }

  private void increment(long hash, @Nonnegative int count) {
    boolean added;
    if (conservative) {
      added = conservativeIncrement(hash, count);
    } else {
      added = regularIncrement(hash, count);
    }

    if (added && (++size == sampleSize)) {
      reset();
    }
  }

  private boolean conservativeIncrement(long hash, @Nonnegative int count) {
    count = Math.min(count, 15);

    final int oldFrequency = frequency(hash);
    if (oldFrequency == 15) {
      return false;
    }

    final int newFrequency = Math.min(oldFrequency + count, 15);
    if (newFrequency == oldFrequency) {
      return false;
    }

    int change = 0;
    change += maximizeAt(hash, newFrequency);
    hash = respread1(hash);
    change += maximizeAt(hash, newFrequency);
    hash = respread2(hash);
    change += maximizeAt(hash, newFrequency);
    hash = respread3(hash);
    change += maximizeAt(hash, newFrequency);

    return change > 0;
  }

  private long maximizeAt(long hash, int value) {
    final int index = index(hash);
    final int shift = shift(hash);

    final long old = (table[index] >>> shift) & 15;
    final long neu = Math.max(old, value);
    final long delta = neu - old;
    table[index] += delta << shift;

    return delta;
  }

  private boolean regularIncrement(long hash, @Nonnegative int count) {
    if (count > 15) count = 15;

    int change = 0;
    change += incrementAt(hash, count);
    hash = respread1(hash);
    change += incrementAt(hash, count);
    hash = respread2(hash);
    change += incrementAt(hash, count);
    hash = respread3(hash);
    change += incrementAt(hash, count);

    return change > 0;
  }

  private long incrementAt(long e, int count) {
    final int index = index(e);
    final int shift = shift(e);

    final long old = (table[index] >>> shift) & 15;
    final long neu = Math.min(old + count, 15);
    final long delta = neu - old;
    table[index] += delta << shift;

    return delta;
  }

  /**
   * Increments the specified counter by 1 if it is not already at the maximum value (15).
   *
   * @param i the table index (16 counters)
   * @param j the counter to increment
   * @return if incremented
   */
  boolean incrementAt(int i, int j) {
    int offset = j << 2;
    long mask = (0xfL << offset);
    if ((table[i] & mask) != mask) {
      table[i] += (1L << offset);
      return true;
    }
    return false;
  }

  /** Reduces every counter by half of its original value. */
  void reset() {
    int count = 0;
    for (int i = 0; i < table.length; i++) {
      count += Long.bitCount(table[i] & ONE_MASK);
      table[i] = (table[i] >>> 1) & RESET_MASK;
    }
    size = (size >>> 1) - (count >>> 2);
  }

  private int extract(long hash) {
    final int index = index(hash);
    final int shift = shift(hash);
    return (int) (table[index] >>> shift) & 15;
  }

  /**
   * Applies a supplemental hash function to a given hashCode, which defends against poor quality
   * hash functions.
   */
  long spread(int x) {
    x *= C1;
    x ^= (x >> 23) ^ (x >> 43);
    return x * randomSeed;
  }

  private long respread1(long hash) {
    // This is enough as each operation uses less than a half of the input.
    // After the rotation, other bits get used.
    return Long.rotateLeft(hash, 32);
  }

  private long respread2(long hash) {
    return hash * C2;
  }

  private long respread3(long hash) {
    // See respread1.
    return Long.rotateLeft(hash, 32);
  }

  /** Return a valid index into the table. */
  private int index(long hash) {
    return (int) (hash >>> tableShift);
  }

  /** Return a number from the set {0, 4, ..., 60}, i.e., a suitable shift distance for nibble extraction. */
  private int shift(long hash) {
    return (int) hash & (15 << 2);
  }


  static int ceilingNextPowerOfTwo(int x) {
    // From Hacker's Delight, Chapter 3, Harry S. Warren Jr.
    return 1 << (Integer.SIZE - Integer.numberOfLeadingZeros(x - 1));
  }
}
