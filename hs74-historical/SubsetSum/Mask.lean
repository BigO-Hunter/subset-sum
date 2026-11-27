import SubsetSum.Main

/-!
# Bridge: the Finset-mask specification ↔ the inductive specification

`subsetSumsTo_mask nums t` asks for a `mask : Finset (Fin nums.length)` with
`∑ i ∈ mask, nums[i.val] = t`. This file proves it equivalent to the inductive
`subsetSumsTo nums t`, and derives the main theorem against the mask
formulation: `mitm_correct_mask`.

The proof is induction on `nums`. The cons step is `Fin (n+1)` surgery on the
mask: split off position 0 (`Finset.sum_filter_add_sum_filter_not` +
`Finset.sum_ite_eq'`) and reindex the nonzero remainder down to `Fin n` via
`reindexSucc` (`Finset.sum_bij`-free: `Finset.sum_map` along `Fin.succEmb`).
The reverse direction reindexes with `Fin.succEmb` (`Finset.sum_map`) and
inserts position 0 (`Finset.sum_insert`).

Proof-engineering note: terms elaborated inside `subsetSumsTo_mask`'s *def*
carry different auto-generated `getElem` proof arguments than terms elaborated
here, so `rw [lemma] at hsum` fails to match on an apparently identical sum.
All contact between definition-site and lemma-site terms is therefore made
with `Eq.trans` composition (unification is up to defeq, so proof arguments
are irrelevant there), never with rewriting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubsetSum

/-! ## Reindexing `Fin (n+1)` masks down to `Fin n` -/

/-- The nonzero part of a `Fin (n + 1)` mask, reindexed down to `Fin n` by
reversing `Fin.succ`. Total functions `Fin (n+1) → Fin n` do not exist for
`n = 0`, so this is built as a filter over `Finset.univ`, which is total in
`n`. -/
def reindexSucc {n : ℕ} (M : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j : Fin n => j.succ ∈ M

/-- Reindexing and mapping back by `Fin.succEmb` recovers the nonzero part. -/
theorem map_succEmb_reindexSucc {n : ℕ} (M : Finset (Fin (n + 1))) :
    (reindexSucc M).map (Fin.succEmb n) = M.filter (· ≠ 0) := by
  ext i
  simp only [reindexSucc, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, Fin.succ_ne_zero j⟩
  · rintro ⟨hiM, hinz⟩
    refine ⟨i.pred hinz, ?_, Fin.succ_pred i hinz⟩
    rw [Fin.succ_pred]
    exact hiM

/-- Getting an element by ℕ-indexed `getElem` agrees with `List.get`. -/
theorem getElem_val_eq_get (l : List ℕ) (i : Fin l.length) : l[i.val] = l.get i := rfl

/-- A nonzero position of `a :: rest` shifted down by `Fin.succEmb` holds the
corresponding position of `rest`. -/
theorem getElem_succEmb (a : ℕ) (rest : List ℕ) (j : Fin rest.length) :
    (a :: rest)[((Fin.succEmb rest.length) j).val] = rest[j.val] := by
  rw [getElem_val_eq_get, getElem_val_eq_get, Fin.coe_succEmb]
  exact List.get_cons_succ'

/-! ## The surgery lemma -/

/-- Split a mask sum over `a :: rest` into the head part (position 0) and the
tail part, reindexed to a `Fin rest.length` mask. -/
theorem sum_get_cons_split (a : ℕ) (rest : List ℕ)
    (M : Finset (Fin (rest.length + 1))) :
    ∑ i ∈ M, (a :: rest)[i.val] =
      (if (0 : Fin (rest.length + 1)) ∈ M then a else 0) +
      ∑ j ∈ reindexSucc M, rest[j.val] := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := M) (p := (· = 0))
      (f := fun i => (a :: rest)[i.val])]
  have p1 : ∑ i ∈ M.filter (· = 0), (a :: rest)[i.val]
      = if (0 : Fin (rest.length + 1)) ∈ M then a else 0 := by
    rw [Finset.sum_filter, Finset.sum_ite_eq']
    simp
  have p2 : ∑ i ∈ M.filter (· ≠ 0), (a :: rest)[i.val]
      = ∑ j ∈ reindexSucc M, rest[j.val] := by
    conv_lhs => rw [← map_succEmb_reindexSucc M, Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => getElem_succEmb a rest j
  rw [p1, p2]

/-! ## The bridge -/

/-- **Bridge theorem.** The Finset-mask formulation of Subset Sum is
equivalent to the inductive "∃ subset summing to t" formulation. -/
theorem subsetSumsTo_mask_iff (nums : List ℕ) (t : ℕ) :
    subsetSumsTo_mask nums t ↔ subsetSumsTo nums t := by
  induction nums generalizing t with
  | nil =>
    constructor
    · rintro ⟨M, hsum⟩
      have hz : ∑ i ∈ M, ([] : List ℕ)[i.val] = 0 :=
        Finset.sum_eq_zero fun i _ => Fin.elim0 i
      have key : t = 0 := hsum.symm.trans hz
      subst key
      exact .nil
    · intro h
      cases h
      exact ⟨(∅ : Finset (Fin 0)), by simp⟩
  | cons a rest ih =>
    constructor
    · rintro ⟨M, hsum⟩
      have hsplit := sum_get_cons_split a rest M
      have key := hsplit.symm.trans hsum
      have hsub : subsetSumsTo rest (∑ j ∈ reindexSucc M, rest[j.val]) :=
        (ih _).mp ⟨reindexSucc M, rfl⟩
      by_cases h0 : (0 : Fin (rest.length + 1)) ∈ M
      · rw [if_pos h0] at key
        rw [← key, Nat.add_comm]
        exact .take hsub
      · rw [if_neg h0] at key
        rw [← key]
        simpa using .skip hsub
    · intro h
      cases h with
      | skip h' =>
        obtain ⟨M, hM⟩ := (ih _).mpr h'
        refine ⟨M.map (Fin.succEmb rest.length), ?_⟩
        have hmap : ∑ i ∈ M.map (Fin.succEmb rest.length), (a :: rest)[i.val]
            = ∑ j ∈ M, rest[j.val] := by
          rw [Finset.sum_map]
          exact Finset.sum_congr rfl fun j _ => getElem_succEmb a rest j
        exact hmap.trans hM
      | take h' =>
        obtain ⟨M, hM⟩ := (ih _).mpr h'
        refine ⟨insert (0 : Fin (rest.length + 1)) (M.map (Fin.succEmb rest.length)), ?_⟩
        have hnot : (0 : Fin (rest.length + 1)) ∉ M.map (Fin.succEmb rest.length) := by
          simp [Finset.mem_map, Fin.succ_ne_zero]
        have hval : (a :: rest)[((0 : Fin (rest.length + 1))).val] = a := by simp
        have hmap : ∑ i ∈ M.map (Fin.succEmb rest.length), (a :: rest)[i.val]
            = ∑ j ∈ M, rest[j.val] := by
          rw [Finset.sum_map]
          exact Finset.sum_congr rfl fun j _ => getElem_succEmb a rest j
        refine (Finset.sum_insert hnot).trans ?_
        rw [hval, hmap, hM, Nat.add_comm]

/-! ## Main theorem against the mask formulation -/

/-- **Main theorem (mask form).** The meet-in-the-middle algorithm decides
Subset Sum as formulated with `Finset (Fin n)` masks:
`∃ mask : Finset (Fin nums.length), ∑ i ∈ mask, nums[i.val] = target`. -/
theorem mitm_correct_mask (x : Instance) :
    mitmDecide x = true ↔ subsetSumsTo_mask x.nums x.target := by
  rw [mitm_correct, ← subsetSumsTo_mask_iff]

end SubsetSum
