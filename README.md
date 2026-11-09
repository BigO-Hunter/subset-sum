# Subset Sum — Lean 4-verified meet-in-the-middle (Horowitz–Sahni 1974)

A machine-checked proof that the deterministic meet-in-the-middle Subset Sum
decision algorithm is **exactly correct**, plus its `O(2^(n/2) · poly(n))`
word-RAM cost bound. Prepared for submission to
[bigospeedrun/verifier](https://bigospeedrun.com/subset-sum) as the first
Lean-verified Subset Sum result.

## Problem

Given positive integers a₁,…,aₙ and a nonnegative target t, decide whether a
subset of the positions sums to t. The empty subset is allowed; input values
may repeat (each *position* is used at most once — the sub-multiset reading,
matching the `Finset (Fin n)`-mask formulation kept as `subsetSumsTo_mask`).
Deterministic programs satisfy the board's "correct with probability ≥ 2/3"
trivially: this one is correct with probability 1.

## The algorithm

1. Split the n items into halves of ⌊n/2⌋ and ⌈n/2⌉ items (`splitHalves`).
2. Enumerate all subset sums of each half (`subsetSums`; exactly 2^j sums for
   a j-item half — `subsetSums_length`).
3. Merge-sort the left-half sums.
4. For each right-half sum r with r ≤ t, binary-search t − r in the sorted
   left sums (`binSearch`, proved correct on sorted lists).
5. Answer true iff some search succeeds.

Note the `r ≤ t` guard: without it, `t − r` collapses to 0 in ℕ for r > t,
and since 0 is always a left sum the procedure would wrongly answer true
(e.g. `nums = [5]`, `t = 3`). The skeleton's unguarded form was a bug; fixed
and documented in `SubsetSum/Definitions.lean`.

## Main theorems (SubsetSum/Main.lean)

```lean
theorem mitm_correct (x : Instance) :
    mitmDecide x = true ↔ subsetSumsTo x.nums x.target

theorem mitm_time_bound (x : Instance) :
    mitmOpCount x.nums.length ≤ timeBound x.nums.length (maxBitLength x)
    -- = 2^(n/2 + 1) · (n + b + 1) · 100
```

`subsetSumsTo` is the inductive "∃ subset summing to t" specification.
Supporting theorems: `mem_subsetSums_iff` (enumerator = spec),
`mem_subsetSums_append` (sums distribute over `l ++ r` — the MITM key lemma),
`binSearch_correct`, `bruteForce_correct`, `subsetSums_length`.

## Status

* Lean 4.33.1 + Mathlib 0df444a; `lake build` passes.
* **Zero `sorry`, zero `axiom`** (only standard Mathlib axioms).
* Cost model: `mitmOpCount` is an analytic upper bound (enumerate/sort/search
  terms), not a verified operational cost semantics. The correctness theorem
  is the verified part.

## Build

```
lake exe cache get   # Mathlib oleans
lake build
```

---

## Why this repo is up

Reproducible verified results: the first Lean-verified subset-sum result (exact decision correctness + word-RAM cost) — the decision-correctness reference the later bound packages build on.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Complete as the decision-correctness + cost reference. Open work: maintenance and reruns; newer bounds live in subset-sum-half / subset-sum-mitm.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE) ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 
