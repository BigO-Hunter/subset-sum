# subset-sum

Lean 4 formalization of Subset Sum at α = 1/2: deterministic meet-in-the-middle, flat O(2^(n/2)).
Construction: ours (Horowitz–Sahni style MITM as a single finite word-RAM program). AI-assisted (darkhipo swarm), disclosed.
Board: BigO Speedrun, subset-sum.
Status: kernel-verified `Race.bound : SolvedInTime (1/2)` — Lean 4.34.1, zero sorry.

---

## Why this repo is up

Reproducible verified bounds: a kernel-checked Race.bound : SolvedInTime (1/2) — the board's best Lean-verified subset-sum bound, rebuildable by anyone.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
## What work can be done here

`Race.bound : SolvedInTime (1/2)` is kernel-verified. Open work: independent reruns; pushing below α = 1/2 (see subset-sum-l25 and the campaign lanes).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.

## Umbrella layout

- Repository root: the deterministic α = 1/2 submission described above.
- `mitm/`: the complete original `subset-sum-mitm` package at source commit `1b502826f167b25aa20211b89a9b22387b8bad2f`, merged with full history, including its separate 301-instruction finite program and verification material.
- `subset-sum-mitm` v2 branches: preserved as archive refs `archive/subset-sum-mitm/v2-alpha-half` and `archive/subset-sum-mitm/v2-budget` (verbatim source tips `dcfe97466bbd` / `daf5374ed3b0` plus annotation-tidied tips) — experimental discharge/budget work, not a separate filing.
- `hs74-historical/`: the former `subsetsum-lean` repo at source commit `e2bd7c3772b48dd5da2ee529a708d9d28dd03412`, merged with full history — the first Lean-verified subset-sum result (Horowitz–Sahni 1974 MITM: exact decision correctness `mitm_correct` + analytic `O(2^(n/2)·poly(n))` cost `mitm_time_bound`). Historical decision-correctness reference on an older pin (Lean 4.33.1 / Mathlib 0df444a); nothing imports it and it is not a current submission.

These are related but distinct artifacts, not duplicate submissions. Build and audit each package from its own directory (each keeps its own toolchain pins). The umbrella filing name is `subset-sum`.
