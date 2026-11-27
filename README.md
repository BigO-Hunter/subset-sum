# subset-sum

Lean 4 formalization of Subset Sum at α = 1/2: deterministic meet-in-the-middle, flat O(2^(n/2)).
Construction: ours (Horowitz–Sahni style MITM as a single finite word-RAM program). AI-assisted (darkhipo swarm), disclosed.
Board: BigO Speedrun, subset-sum.
Status: kernel-verified `Race.bound : SolvedInTime (1/2)` — Lean 4.34.1, zero sorry.

---

## What work can be done here

`Race.bound : SolvedInTime (1/2)` is kernel-verified. Open work: independent reruns; pushing below α = 1/2 (see subset-sum-l25 and the campaign lanes).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work).

## Umbrella layout

- Repository root: the deterministic α = 1/2 submission described above.
- `mitm/`: the `subset-sum-mitm` package (source commit `1b502826f167b25aa20211b89a9b22387b8bad2f`) — a separate 301-instruction finite program and verification material.
- `subset-sum-mitm` v2 branches: archive refs `archive/subset-sum-mitm/v2-alpha-half` and `archive/subset-sum-mitm/v2-budget` (source tips `dcfe97466bbd` / `daf5374ed3b0`) — experimental discharge/budget work.
- `hs74-historical/`: the first Lean-verified subset-sum result (Horowitz–Sahni 1974 MITM: exact decision correctness `mitm_correct` + analytic `O(2^(n/2)·poly(n))` cost `mitm_time_bound`), source commit `e2bd7c3772b48dd5da2ee529a708d9d28dd03412`. Standalone decision-correctness reference on an older pin (Lean 4.33.1 / Mathlib 0df444a).

## Reproduction

Each package builds from its own directory with its own pins:

```sh
# root: the deterministic alpha=1/2 filing (Lean 4.34.1, verifier Mathlib pin)
lake exe cache get && lake build Submission

# mitm/: the 301-instruction MITM package (no Mathlib dependency)
cd mitm && lake build Submission

# hs74-historical/: HS74 decision-correctness reference (Lean 4.33.1 / Mathlib 0df444a)
cd hs74-historical && lake exe cache get && lake build
```

`scratch/` — campaign scratch material (probes, dumps, output logs), outside the filed proofs.

Build and audit each package from its own directory (each keeps its own toolchain pins).

---

[BigO-Hunter](https://github.com/BigO-Hunter) — tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io)
