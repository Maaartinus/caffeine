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

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Fork;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;

import com.yahoo.ycsb.generator.NumberGenerator;
import com.yahoo.ycsb.generator.ScrambledZipfianGenerator;

/**
 * <pre>{@code
 *   ./gradlew jmh -PincludePattern=FrequencySketchBenchmark
 * }</pre>
 *
 * @author ben.manes@gmail.com (Ben Manes)
 */
@State(Scope.Benchmark)
@Fork(5)
public class FrequencySketchBenchmark {
  private static final int SIZE = (2 << 14);
  private static final int MASK = SIZE - 1;
  private static final int ITEMS = SIZE / 3;

  int index = 0;
  Integer[] ints;
  FrequencySketch<Integer> sketch;
  MgFrequencySketch1<Integer> mgSketch1Regular;
  MgFrequencySketch1<Integer> mgSketch1Conservative;

  @Setup
  public void setup() {
    ints = new Integer[SIZE];

    sketch = new FrequencySketch<>();
    sketch.ensureCapacity(ITEMS);

    mgSketch1Regular = new MgFrequencySketch1<>();
    mgSketch1Regular.ensureCapacity(ITEMS);
    mgSketch1Regular.conservative = false;

    mgSketch1Conservative = new MgFrequencySketch1<>();
    mgSketch1Conservative.ensureCapacity(ITEMS);
    mgSketch1Conservative.conservative = true;

    NumberGenerator generator = new ScrambledZipfianGenerator(ITEMS);
    for (int i = 0; i < SIZE; i++) {
      ints[i] = generator.nextValue().intValue();
      sketch.increment(i);
      mgSketch1Regular.increment(i);
      mgSketch1Conservative.increment(i);
    }
  }

  @Benchmark
  public void increment() {
    sketch.increment(ints[index++ & MASK]);
  }

  @Benchmark
  public int frequency() {
    return sketch.frequency(ints[index++ & MASK]);
  }

  @Benchmark
  public void increment1Regular() {
    mgSketch1Regular.increment(ints[index++ & MASK]);
  }

  @Benchmark
  public int frequency1Regular() {
    return mgSketch1Regular.frequency(ints[index++ & MASK]);
  }

  @Benchmark
  public void increment1Conservative() {
    mgSketch1Conservative.increment(ints[index++ & MASK]);
  }

  @Benchmark
  public int frequency1Conservative() {
    return mgSketch1Conservative.frequency(ints[index++ & MASK]);
  }
}
