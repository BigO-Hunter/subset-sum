import Mathlib

/-!
# Subset Sum: meet-in-the-middle O(2^(n/2)) on a word-RAM

The board statement (bigospeedrun.com/subset-sum):

Given positive integers a₁,...,aₙ and a nonnegative target t, decide whether
a subset sums to t; the empty subset is allowed and input values may repeat.

A single randomized word-RAM program uses w-bit words where
w = ⌈4(n + b + log₂(n+2))⌉, b = max input/target bit length, halts on every
run and is correct with probability at least 2/3 on each input.

We formalize the deterministic meet-in-the-middle algorithm (Horowitz–Sahni
1974) which is always correct (probability 1 ≥ 2/3) and runs in
O(2^(n/2) · poly(n)) word operations.

Semantics note: "subset" means a selection of *positions* of the input list
(equivalently a sub-multiset of the values), each position used at most once.
This matches the `Finset (Fin n)`-mask formulation kept below as
`subsetSumsTo_mask`.

Definitions live here; all proofs and the final theorems live in
`SubsetSum/Main.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubsetSum

/-! ## Problem definition -/

/-- Input: a list of positive integers and a nonnegative target. -/
structure Instance where
  /-- The input integers a₁,...,aₙ. -/
  nums : List ℕ
  /-- The target t. -/
  target : ℕ
  deriving Repr

/-- The number of items n. -/
def itemCount (x : Instance) : ℕ := x.nums.length

/-- The maximum bit length b = max(input bit lengths, target bit length). -/
def maxBitLength (x : Instance) : ℕ :=
  ((x.nums.map Nat.log2).foldr max 0) ⊔ Nat.log2 x.target

/-! ## Specification -/

/-- `subsetSumsTo nums t`: some subset of the *positions* of `nums` sums to
`t`. The empty subset is allowed, so `subsetSumsTo nums 0` always holds. Each
position is used at most once; values may repeat (then several distinct
subsets share a sum). This is the inductive "∃ subset summing to t" spec. -/
inductive subsetSumsTo : List ℕ → ℕ → Prop where
  /-- The empty subset of the empty list sums to 0. -/
  | nil : subsetSumsTo [] 0
  /-- Skip the head; use no position of it. -/
  | skip {a : ℕ} {rest : List ℕ} {t : ℕ} :
      subsetSumsTo rest t → subsetSumsTo (a :: rest) t
  /-- Take the head; use its position exactly once. -/
  | take {a : ℕ} {rest : List ℕ} {t : ℕ} :
      subsetSumsTo rest t → subsetSumsTo (a :: rest) (t + a)

/-- The Finset-mask formulation of the same question: does some set of
positions `mask ⊆ Fin nums.length` satisfy `∑ i ∈ mask, nums[i] = target`?
(Equivalence with `subsetSumsTo` is future work; the inductive spec above is
the one the correctness theorem is proved against.) -/
def subsetSumsTo_mask (nums : List ℕ) (target : ℕ) : Prop :=
  ∃ (mask : Finset (Fin nums.length)), ∑ i ∈ mask, nums[i.val] = target

/-! ## The word-RAM model -/

/-- Word width: w = ⌈4(n + b + log₂(n+2))⌉. -/
def wordWidth (n b : ℕ) : ℕ :=
  4 * (n + b + Nat.log2 (n + 2) + 1)

/-- The time bound: T(n) = C · 2^(n/2) · (n + b) for some constant C. -/
def timeBound (n b : ℕ) : ℕ :=
  2^(n/2 + 1) * (n + b + 1) * 100

/-! ## The meet-in-the-middle algorithm -/

/-- All subset sums of a list (with duplicates): for each element either skip
it or add it. `subsetSums [] = [0]` (the empty subset). -/
def subsetSums : List ℕ → List ℕ
  | [] => [0]
  | a :: rest => (subsetSums rest).flatMap (fun s => [s, s + a])

/-- Split a list into two halves (left gets `n / 2` items). -/
def splitHalves (l : List ℕ) : List ℕ × List ℕ :=
  (l.take (l.length / 2), l.drop (l.length / 2))

/-- Binary search for `x` in a sorted list, with explicit fuel (structural in
the fuel; `binSearch` supplies `l.length`). Correct on any list whose
elements are pairwise `≤` (duplicates allowed); see `binSearch_correct` in
`SubsetSum/Main.lean`. -/
def binSearchFuel (x : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | _, [] => false
  | _, [y] => x == y
  | n + 1, y₁ :: y₂ :: ys =>
    let l := y₁ :: y₂ :: ys
    let mid := l.length / 2
    if h : mid < l.length then
      if x < l[mid] then binSearchFuel x n (l.take mid)
      else if l[mid] < x then binSearchFuel x n (l.drop (mid + 1))
      else true
    else false

/-- Binary search on a sorted list; fuel is the list length. -/
def binSearch (x : ℕ) (l : List ℕ) : Bool := binSearchFuel x l.length l

/-- The MITM decision: enumerate half-sums, sort the left half's sums, and
binary-search the complement of each right-half sum.

Note the guard `r ≤ x.target`: without it the complement `x.target - r`
collapses to 0 in `ℕ` whenever `r > target`, 0 is always a left sum, and the
procedure would wrongly answer `true` (e.g. `nums = [5]`, `target = 3`). -/
def mitmDecide (x : Instance) : Bool :=
  let leftSums := (subsetSums (splitHalves x.nums).1).mergeSort (· ≤ ·)
  (subsetSums (splitHalves x.nums).2).any fun r =>
    r ≤ x.target && binSearch (x.target - r) leftSums

/-- Brute force: is the target among all `2^n` subset sums? Reference
implementation the MITM is proved equivalent to (via the spec). -/
def bruteForce (x : Instance) : Bool := (subsetSums x.nums).contains x.target

/-! ## Cost model (analytic) -/

/-- Word-RAM operation count of the MITM algorithm on `n` items (upper
bound): enumerating each half's subset sums (≤ 2^j · (j + 2) ops for a
`j`-item half), merge-sorting the left sums (≤ 2 · 2^m · (m + 2)
comparisons), and binary-searching each right sum (≤ m + 2 steps each). -/
def mitmOpCount (n : ℕ) : ℕ :=
  2^(n / 2) * (n / 2 + 2) + 2^(n - n / 2) * (n - n / 2 + 2) +
  2 * 2^(n / 2) * (n / 2 + 2) + 2^(n - n / 2) * (n / 2 + 2)

end SubsetSum
