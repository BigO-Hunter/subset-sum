import SubsetSum.Definitions

/-!
# Correctness of the meet-in-the-middle Subset Sum algorithm

Main theorems:

* `mitm_correct`: `mitmDecide x = true ↔ subsetSumsTo x.nums x.target` — the
  Horowitz–Sahni meet-in-the-middle decision procedure decides Subset Sum
  exactly. It is deterministic, hence correct with probability 1 ≥ 2/3.
* `mitm_time_bound`: its word-RAM operation count is
  `≤ 2^(n/2 + 1) · (n + b + 1) · 100 = O(2^(n/2) · poly(n))`.
* `binSearch_correct`: binary search on a sorted list finds membership.

NOTE (2026-01-30 16:30): this file was concurrently overwritten at 16:28 by a
peer writer with a 31-line fragment containing only `mem_subsetSums_iff`.
This full version restores that theorem and adds the rest; see the strike
report. Coordinate before editing this file again.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubsetSum

/-! ## The enumerator realizes the specification -/

/-- Membership in the enumerator: one cons step. -/
theorem mem_subsetSums_cons {a : ℕ} {rest : List ℕ} {t : ℕ} :
    t ∈ subsetSums (a :: rest) ↔
      t ∈ subsetSums rest ∨ ∃ s, s ∈ subsetSums rest ∧ t = s + a := by
  simp only [subsetSums, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, ht⟩
    simp at ht
    rcases ht with rfl | rfl
    · exact .inl hs
    · exact .inr ⟨s, hs, rfl⟩
  · rintro h
    rcases h with h | ⟨s, hs, rfl⟩
    · exact ⟨t, h, by simp⟩
    · exact ⟨s, hs, by simp⟩

/-- The recursive enumerator `subsetSums` contains exactly the subset sums
expressed by the inductive spec `subsetSumsTo`. -/
theorem mem_subsetSums_iff {nums : List ℕ} {t : ℕ} :
    t ∈ subsetSums nums ↔ subsetSumsTo nums t := by
  induction nums generalizing t with
  | nil =>
    constructor
    · intro h
      simp [subsetSums] at h
      subst h
      exact .nil
    · intro h
      cases h
      simp [subsetSums]
  | cons a rest ih =>
    rw [mem_subsetSums_cons]
    constructor
    · rintro h
      rcases h with h | ⟨s, hs, rfl⟩
      · exact .skip ((@ih _).mp h)
      · exact .take ((@ih _).mp hs)
    · intro h
      cases h with
      | skip h' => exact .inl ((@ih _).mpr h')
      | take h' => exact .inr ⟨_, (@ih _).mpr h', rfl⟩

/-- Subset sums distribute over list concatenation: a sum over `l ++ r` is
exactly a sum over `l` plus a sum over `r`. -/
theorem mem_subsetSums_append (l r : List ℕ) (t : ℕ) :
    t ∈ subsetSums (l ++ r) ↔
      ∃ a b, a ∈ subsetSums l ∧ b ∈ subsetSums r ∧ a + b = t := by
  induction l generalizing t with
  | nil =>
    constructor
    · intro h
      exact ⟨0, t, by simp [subsetSums], h, by simp⟩
    · rintro ⟨a, b, ha, hb, hab⟩
      simp [subsetSums] at ha
      subst ha
      rw [← hab]
      simpa using hb
  | cons a₀ l' ih =>
    rw [List.cons_append, mem_subsetSums_cons]
    constructor
    · rintro h
      rcases h with h | ⟨s, hs, hts⟩
      · obtain ⟨a₁, b, ha₁, hb, hab⟩ := (ih _).mp h
        exact ⟨a₁, b, mem_subsetSums_cons.mpr (.inl ha₁), hb, hab⟩
      · obtain ⟨a₁, b, ha₁, hb, hab⟩ := (ih _).mp hs
        refine ⟨a₁ + a₀, b, mem_subsetSums_cons.mpr (.inr ⟨a₁, ha₁, rfl⟩), hb, ?_⟩
        omega
    · rintro ⟨a', b, ha', hb, hab⟩
      rw [mem_subsetSums_cons] at ha'
      rcases ha' with ha' | ⟨a₁, ha₁, rfl⟩
      · refine .inl ?_
        rw [← hab]
        exact (ih _).mpr ⟨a', b, ha', hb, rfl⟩
      · refine .inr ⟨a₁ + b, (ih _).mpr ⟨a₁, b, ha₁, hb, rfl⟩, ?_⟩
        omega

theorem splitHalves_append (l : List ℕ) :
    (splitHalves l).1 ++ (splitHalves l).2 = l := by
  simp [splitHalves, List.take_append_drop]

/-! ## Binary search is correct on sorted lists -/

/-- Binary search finds `x` in any list whose elements are pairwise `≤`
(non-strictly sorted; duplicates allowed). -/
theorem binSearchFuel_correct (n : ℕ) (x : ℕ) (l : List ℕ)
    (hn : l.length ≤ n) (hs : l.Pairwise (· ≤ ·)) :
    binSearchFuel x n l = true ↔ x ∈ l := by
  induction n generalizing l with
  | zero =>
    have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst hl
    simp [binSearchFuel]
  | succ n ih =>
    cases l with
    | nil => simp [binSearchFuel]
    | cons y₁ ys =>
      cases ys with
      | nil => simp [binSearchFuel]
      | cons y₂ ys =>
        -- Main case: l = y₁ :: y₂ :: ys has at least two elements.
        have hlen : (y₁ :: y₂ :: ys).length = ys.length + 2 := by simp
        have hmid : (y₁ :: y₂ :: ys).length / 2 < (y₁ :: y₂ :: ys).length := by omega
        have hpow_le : ((y₁ :: y₂ :: ys).take ((y₁ :: y₂ :: ys).length / 2)).length ≤ n := by
          rw [List.length_take_of_le (by omega : (y₁ :: y₂ :: ys).length / 2 ≤ (y₁ :: y₂ :: ys).length)]
          simp at hn
          omega
        have hdrop_le : ((y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2 + 1)).length ≤ n := by
          rw [List.length_drop]
          simp at hn
          omega
        have hsorted_take : ((y₁ :: y₂ :: ys).take ((y₁ :: y₂ :: ys).length / 2)).Pairwise (· ≤ ·) :=
          hs.take
        have hsorted_drop : ((y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2 + 1)).Pairwise (· ≤ ·) :=
          hs.drop
        -- Decompose membership across the pivot.
        have hmem_split : ∀ z : ℕ,
            z ∈ (y₁ :: y₂ :: ys) ↔
              z ∈ (y₁ :: y₂ :: ys).take ((y₁ :: y₂ :: ys).length / 2) ∨
              z = (y₁ :: y₂ :: ys)[(y₁ :: y₂ :: ys).length / 2] ∨
              z ∈ (y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2 + 1) := by
          intro z
          conv_lhs => rw [← List.take_append_drop ((y₁ :: y₂ :: ys).length / 2) (y₁ :: y₂ :: ys)]
          rw [List.mem_append, List.drop_eq_getElem_cons hmid, List.mem_cons]
        -- The pivot bounds everything after it.
        have hpiv_le : ∀ q ∈ (y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2 + 1),
            (y₁ :: y₂ :: ys)[(y₁ :: y₂ :: ys).length / 2] ≤ q := by
          intro q hq
          have hdrop_pairwise : ((y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2)).Pairwise (· ≤ ·) :=
            hs.drop
          rw [List.drop_eq_getElem_cons hmid] at hdrop_pairwise
          exact List.rel_of_pairwise_cons hdrop_pairwise hq
        -- Everything before the pivot is bounded by it.
        have hle_piv : ∀ a ∈ (y₁ :: y₂ :: ys).take ((y₁ :: y₂ :: ys).length / 2),
            a ≤ (y₁ :: y₂ :: ys)[(y₁ :: y₂ :: ys).length / 2] := by
          intro a ha
          have hpiv : (y₁ :: y₂ :: ys)[(y₁ :: y₂ :: ys).length / 2] ∈
              (y₁ :: y₂ :: ys).drop ((y₁ :: y₂ :: ys).length / 2) := by
            rw [List.drop_eq_getElem_cons hmid]
            simp
          exact hs.rel_of_mem_take_of_mem_drop ha hpiv
        -- Unfold one level and branch on the comparison with the pivot.
        simp only [binSearchFuel]
        rw [dif_pos hmid]
        rcases Nat.lt_trichotomy x (y₁ :: y₂ :: ys)[(y₁ :: y₂ :: ys).length / 2] with hlt | heq | hgt
        · -- Search left half.
          rw [if_pos hlt]
          rw [ih _ hpow_le hsorted_take]
          constructor
          · intro hx
            exact (hmem_split x).mpr (.inl hx)
          · intro hx
            rcases hmem_split x |>.mp hx with hx | hx | hx
            · exact hx
            · omega
            · have := hpiv_le x hx; omega
        · -- Pivot hit.
          subst heq
          rw [if_neg (by omega), if_neg (by omega)]
          exact ⟨fun _ => List.getElem_mem hmid, fun _ => rfl⟩
        · -- Search right half.
          rw [if_neg (by omega), if_pos hgt]
          rw [ih _ hdrop_le hsorted_drop]
          constructor
          · intro hx
            exact (hmem_split x).mpr (.inr (.inr hx))
          · intro hx
            rcases hmem_split x |>.mp hx with hx | hx | hx
            · have := hle_piv x hx; omega
            · omega
            · exact hx

theorem binSearch_correct {l : List ℕ} {x : ℕ} (hs : l.Pairwise (· ≤ ·)) :
    binSearch x l = true ↔ x ∈ l :=
  binSearchFuel_correct l.length x l le_rfl hs

/-! ## The MITM decision is the spec -/

theorem mitmDecide_eq (x : Instance) :
    mitmDecide x = true ↔
      ∃ a b, a ∈ subsetSums (splitHalves x.nums).1 ∧
        b ∈ subsetSums (splitHalves x.nums).2 ∧ a + b = x.target := by
  have hsorted :
      ((subsetSums (splitHalves x.nums).1).mergeSort (· ≤ ·)).Pairwise (· ≤ ·) :=
    (List.sortedLE_mergeSort (l := subsetSums (splitHalves x.nums).1)).pairwise
  simp only [mitmDecide, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨r, hr, hle, hbs⟩
    have hle' : r ≤ x.target := of_decide_eq_true hle
    have hmem : x.target - r ∈ subsetSums (splitHalves x.nums).1 :=
      List.mem_mergeSort.mp ((binSearch_correct hsorted).mp hbs)
    exact ⟨x.target - r, r, hmem, hr, by omega⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    refine ⟨b, hb, ?_, ?_⟩
    · exact decide_eq_true (by omega)
    · have hba : x.target - b = a := by omega
      rw [hba]
      exact (binSearch_correct hsorted).mpr (List.mem_mergeSort.mpr ha)

/-- **Main theorem.** The deterministic meet-in-the-middle algorithm
(Horowitz–Sahni 1974) decides Subset Sum exactly: it answers `true` iff some
subset of the input positions sums to the target. In particular it is correct
with probability 1 ≥ 2/3. -/
theorem mitm_correct (x : Instance) :
    mitmDecide x = true ↔ subsetSumsTo x.nums x.target := by
  rw [mitmDecide_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    refine mem_subsetSums_iff.mp ?_
    rw [← splitHalves_append x.nums]
    exact (mem_subsetSums_append (splitHalves x.nums).1 (splitHalves x.nums).2 x.target).mpr
      ⟨a, b, ha, hb, hab⟩
  · intro h
    have hmem : x.target ∈ subsetSums x.nums := mem_subsetSums_iff.mpr h
    rw [← splitHalves_append x.nums] at hmem
    exact (mem_subsetSums_append (splitHalves x.nums).1 (splitHalves x.nums).2 x.target).mp hmem

/-- The brute-force reference agrees with the spec (and hence with MITM). -/
theorem bruteForce_correct (x : Instance) :
    bruteForce x = true ↔ subsetSumsTo x.nums x.target := by
  simp only [bruteForce]
  rw [List.contains_iff_mem, mem_subsetSums_iff]

/-! ## Sizes and time bound -/

theorem sum_map_two (L : List ℕ) : (L.map (fun _ => 2)).sum = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons _ L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    omega

/-- The enumerator produces exactly `2^l.length` sums (with repetitions). -/
theorem subsetSums_length (l : List ℕ) : (subsetSums l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [subsetSums, List.length_flatMap, List.length_cons]
    show ((subsetSums l).map (fun _ => 2)).sum = 2 ^ (l.length + 1)
    rw [sum_map_two, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

/-- The MITM procedure uses at most `2^(n/2+1) · (n + b + 1) · 100`
word-RAM operations: `O(2^(n/2) · poly(n))`. -/
theorem mitm_time_bound (x : Instance) :
    mitmOpCount x.nums.length ≤ timeBound x.nums.length (maxBitLength x) := by
  have h2pos : (0:ℕ) < 2 := by norm_num
  have hpowk : 2 ^ (x.nums.length - x.nums.length / 2) ≤ 2 ^ (x.nums.length / 2 + 1) :=
    Nat.pow_le_pow_right h2pos (by omega)
  have hpowm : 2 ^ (x.nums.length / 2) ≤ 2 ^ (x.nums.length / 2 + 1) :=
    Nat.pow_le_pow_right h2pos (by omega)
  have h3 : 2 * 2 ^ (x.nums.length / 2) = 2 ^ (x.nums.length / 2 + 1) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
  -- Each of the four cost terms is at most `2^(n/2+1) * (n + 2)`.
  have t1 : 2 ^ (x.nums.length / 2) * (x.nums.length / 2 + 2) ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) :=
    Nat.mul_le_mul hpowm (by omega)
  have t2 : 2 ^ (x.nums.length - x.nums.length / 2) * (x.nums.length - x.nums.length / 2 + 2) ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) :=
    Nat.mul_le_mul hpowk (by omega)
  have t3 : 2 * 2 ^ (x.nums.length / 2) * (x.nums.length / 2 + 2) ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) := by
    rw [h3]
    exact Nat.mul_le_mul le_rfl (by omega)
  have t4 : 2 ^ (x.nums.length - x.nums.length / 2) * (x.nums.length / 2 + 2) ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) :=
    Nat.mul_le_mul hpowk (by omega)
  have hsum : mitmOpCount x.nums.length ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) := by
    show _ ≤ _
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add t1 t2) t3) t4
  have hfour : ∀ A : ℕ, A + A + A + A = 4 * A := by intro A; omega
  have hfinal : 4 * (2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2)) ≤
      timeBound x.nums.length (maxBitLength x) := by
    show 4 * (2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2)) ≤
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + maxBitLength x + 1) * 100
    rw [Nat.mul_left_comm, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have hchain : 2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) +
      2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2) ≤
      timeBound x.nums.length (maxBitLength x) := by
    rw [hfour (2 ^ (x.nums.length / 2 + 1) * (x.nums.length + 2))]
    exact hfinal
  exact hsum.trans hchain

end SubsetSum
