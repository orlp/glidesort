# Glidesort

Glidesort is a novel stable sorting algorithm that combines the best-case behavior
of Timsort-style merge sorts for pre-sorted data with the best-case behavior of
[pattern-defeating quicksort](https://github.com/orlp/pdqsort) for data with many duplicates.
It is a comparison-based sort supporting arbitrary comparison operators,
and while exceptional on data with patterns it is also very fast for random data.

For sorting $n$ elements with $k$ distinct values glidesort has the following
characteristics by default:

Best | Average           | Worst             | Memory        | Stable | Deterministic
---- | ----------------- | ----------------- | ------------- | ------ | -------------
$n$  | $n \times log(k)$ | $n \times log(n)$ | $\frac{n}{8}$ | Yes    | Yes

Glidesort can use as much (up to $n$) or as little extra memory as you want. If
given only $O(1)$ memory the average and worst case become $O(n \times log(n)^2)$, however
in practice its performance is great for all but the most skewed data size /
auxiliary space ratios. The default is to allocate up to $n$ elements worth of
data, unless this exceeds 1MiB, in which case we scale this down to $\frac{n}{2}$
elements worth of data up until 1GiB after which glidesort uses $\frac{n}{8}$ memory.

# Benchmark

Performance varies a lot from machine to machine and dataset to dataset, so your
mileage will vary. Nevertheless, an example benchmark from a 2021 Apple M1
machine comparing against `[T]::sort` and `[T]::sort_unstable` for various input
distributions of `u64`:

![Performance graph](https://i.imgur.com/8fIACqY.png)

Compiled with `rustc 1.69.0-nightly (11d96b593)` using `--release --features unstable` and `lto = "thin"`.


# Usage

Use `cargo add glidesort` and replace `a.sort()` with `glidesort::sort(&mut a)`.
A similar process works for `sort_by` and `sort_by_key`.

Glidesort exposes two more families of sorting functions.
`glidesort::sort_with_buffer(&mut a, buf)` asks you to pass a `&mut
[MaybeUninit<T>]` buffer which it will then (exclusively) use as auxiliary space
to sort the elements. `glidesort::sort_in_vec(&mut v)` behaves like normal
glidesort but will allocate its auxiliary space at the end of the passed `Vec<T>`.
This allows future sorting calls to re-use the same space and reduce allocations.
Both these families also support the `_by` and `_by_key` interface.

# Visualization

This visualization focuses on demonstrating the advanced merging techniques in glidesort:

https://user-images.githubusercontent.com/202547/216675278-e4c8f15c-e42d-4224-b8c7-fdc67fdc2bde.mp4

This visualization shows how glidesort is adaptive to both pre-existing runs as well
as many duplicates together:

https://user-images.githubusercontent.com/202547/216675274-6e61689f-a120-4b7c-b1a7-9b5aa5fd013e.mp4

Note that both visualizations have different small sorting thresholds and
auxiliary memory parameters to show the techniques in action on a smaller scale.


# Technique overview

Glidesort uses a novel main loop based on powersort. Powersort is similar to
Timsort, using heuristics to find a good order of stably merging sorted runs.
Like powersort it does a linear scan over the input, recognizing any ascending
or strictly descending sequences. However, unlike powersort it does not eagerly
sort sequences that are considered unordered into small sorted blocks. Instead
it processes them as-is, unsorted. This process produces *logical runs*, which
may be sorted or unsorted.

Glidesort repeatedly uses a *logical* merge operation on these logical runs, as
powersort would. In a logical merge unsorted runs are simply concatenated into
larger unsorted runs. Sorted runs are also concatenated into *double sorted*
runs. Only when merging a sorted and unsorted run finally the unsorted run is
sorted using stable quicksort, and when merging double sorted runs glidesort
uses interleaved ping-pong merges.

Using this novel hybrid approach glidesort can take advantage of arbitrary
sorted runs in the data as well as process data with many duplicate items faster
similar to pattern-defeating quicksort.


# Stable merging

Glidesort merges multiple sorted runs at the same time, and interleaves their
merging loops for better memory-level parallelism and hiding data dependencies.
This also allows it to use ping-pong merging avoiding unnecessary `memcpy` calls
by using the implicit copy you get from an out-of-place merge. The merging loops
are completely branchless, making it fast for random data as well.

Glidesort uses binary searches to split up large merge operations into smaller
merge operations that it performs at the same time using instruction-level
parallelism. This splitting procedure also allows glidesort to use arbitrarily
small amounts of memory, as it can choose to split a merge repeatedly until it
fits in our scratch space to process.


# Stable quicksort

Yes, stable quicksort. Wikipedia will outright tell you that quicksort is
unstable, or at least all efficient implementations are. That simply isn't true,
all it needs is auxiliary memory. Credit to Igor van den Hoven's
[fluxsort](https://github.com/scandum/fluxsort) for demonstrating that stable
quicksort can be efficient in practice.

Glidesort uses a novel bidirectional stable partitioning method that interleaves
a left-to-right partition scan with a right-to-left partition scan for greater
memory-level parallelism and hiding data dependencies. Partitioning is done
entirely branchlessly (if the comparison operator is), giving consistent
performance on all data.


# License

Glidesort is dual-licensed under the Apache License, Version 2.0 and the MIT license.
