-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsDelta.lean.

What is here. The factor that weighs one index of a group with 1 and every other with 0, written out
as the verifier's structure of a factor; and the honest side's rule from the two parts of an index
back to the index (`grpIndex`, Johnson/Desc/K4/Honest/Units.lean) against the library's cut of an
index (`splitG`, Johnson/Road/FormsKeysWm.lean).

  `deltaFac`, `deltaFac_fits`, `facAt_delta`   the factor; it has the sizes that its group asks;
     what it weighs
  `grpGuard`, `grpIndex_add`, `grpIndex_split`   the rule read backwards: additive in its two parts;
     below the extent, and cut again into the two parts
  `halves_delta`   **the factor's two halves at a column part and a row part**
  `pickFac`, `deltaAt`, `sumIdx_delta`   the factor that a group bears where indices are picked;
     **the library's sum under such factors is its sum with the indices picked**

Limits. Tools. Every group is asked to meet the library's condition `GrpOK`
(Johnson/Road/FormsKeysWOk.lean). At any reading. Nothing on a matrix, a claim's value or a table.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Units
import Johnson.Road.FormsKeysWv
import Johnson.Road.FormsKeysFac

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading WsGrp WsFac)
open OnBytes.Road (GrpOK splitG joinG joinG_split facAt colHalf rowHalf fac_split sumIdx sumSel pt
  eqN_bool left_E)
open OnBytes.Desc.First.K4.Honest (grpIndex)

variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry of an array that is written out by a rule. -/
theorem getD_range_map {β : Type} (f : ℕ → β) (n j : ℕ) (hj : j < n) (d : β) :
    ((Array.range n).map f).getD j d = f j := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hj]
  rfl

/-- **The factor that weighs the index v with 1 and every other index with 0.** -/
def deltaFac (g : WsGrp) (v : ℕ) : WsFac :=
  if g.cls == 'E' then
    { HV := (Array.range g.o).map fun hi => if hi = v / 2 ^ g.z then oneE else zeroE
      pt := (Array.range g.z).map fun i =>
        if (v % 2 ^ g.z).testBit (g.z - 1 - i) then oneE else zeroE }
  else { AV := (Array.range g.R).map fun j => if j = v then oneE else zeroE }

/-- It has the sizes that its group asks for. -/
theorem deltaFac_fits (g : WsGrp) (v : ℕ) : (deltaFac g v).fits g = true := by
  unfold WsFac.fits deltaFac
  by_cases hE : (g.cls == 'E') = true
  · simp [hE]
  · simp [hE]

/-- **What it weighs an index with.** -/
theorem facAt_delta {g : WsGrp} (hg : GrpOK g) {v v' : ℕ} (hv' : v' < g.R) :
    facAt ρ (deltaFac g v) g v' = if v' = v then 1 else 0 := by
  rcases hg with ⟨hcls, hR, -, -⟩ | ⟨hcls, -, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    have hpos : 0 < 2 ^ g.z := Nat.pow_pos (by norm_num)
    have hhi : v' / 2 ^ g.z < g.o := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← hR]
      exact hv'
    unfold facAt deltaFac
    simp only [hE, if_true]
    rw [getD_range_map _ _ _ hhi,
      eqN_bool g.z 0 _ (c := v % 2 ^ g.z) (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) (fun s hs => by
        show ρ.val (((Array.range g.z).map fun i =>
          if (v % 2 ^ g.z).testBit (g.z - 1 - i) then oneE else zeroE).getD (0 + s) zeroE) = _
        rw [Nat.zero_add, getD_range_map _ _ _ hs]
        by_cases hb : (v % 2 ^ g.z).testBit (g.z - 1 - s) = true
        · rw [if_pos hb, if_pos hb, ρ.one]
        · rw [if_neg hb, if_neg hb, ρ.zero])]
    by_cases h : v' = v
    · subst h
      rw [if_pos rfl, if_pos rfl, if_pos rfl, ρ.one, one_mul]
    · rw [if_neg h]
      by_cases h1 : v' / 2 ^ g.z = v / 2 ^ g.z
      · have h2 : v' % 2 ^ g.z ≠ v % 2 ^ g.z := fun h2 => h (by
          rw [← Nat.div_add_mod v' (2 ^ g.z), ← Nat.div_add_mod v (2 ^ g.z), h1, h2])
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, ρ.zero, zero_mul]
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold facAt deltaFac
    simp only [hE, Bool.false_eq_true, if_false]
    rw [getD_range_map _ _ _ hv']
    by_cases h : v' = v
    · rw [if_pos h, if_pos h, ρ.one]
    · rw [if_neg h, if_neg h, ρ.zero]

/-- True unless the group is of class 'A', its index went to the columns, and the column part is no
index of the group. -/
def grpGuard (g : WsGrp) (c : ℕ) : Bool := !(g.aTaken && decide (g.R ≤ c))

/-- The index is the sum of its values at (the column part, 0) and at (0, the row part). -/
theorem grpIndex_add (g : WsGrp) (c r : ℕ) :
    grpIndex g c 0 + grpIndex g 0 r = grpIndex g c r := by
  unfold grpIndex
  by_cases hE : (g.cls == 'E') = true
  · by_cases hh : g.high = true
    · simp only [hE, hh, if_true, Nat.zero_div, Nat.zero_mul, Nat.zero_mod, Nat.zero_add,
        Nat.add_zero]
      omega
    · simp only [hE, hh, if_true, Bool.false_eq_true, if_false, Nat.zero_mul, Nat.zero_add,
        Nat.add_zero]
      omega
  · by_cases hA : g.aTaken = true
    · simp only [hE, hA, if_true, Bool.false_eq_true, if_false, Nat.add_zero]
    · simp only [hE, hA, Bool.false_eq_true, if_false, Nat.zero_add]

/-- **The rule read backwards meets the library's cut**: of a column part below 2 ^ t that passes
the guard and a row part below what the group leaves to the rows it makes an index below the extent
whose two parts they are. -/
theorem grpIndex_split {g : WsGrp} (hg : GrpOK g) {c r : ℕ} (hc : c < 2 ^ g.t) (hr : r < g.left)
    (hgd : grpGuard g c = true) : grpIndex g c r < g.R ∧ splitG g (grpIndex g c r) = (c, r) := by
  rcases hg with ⟨hcls, hR, ht, hl⟩ | ⟨hcls, ht, hl⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    have hpos : 0 < 2 ^ (g.z - g.t) := Nat.pow_pos (by norm_num)
    have hz : 2 ^ g.z = 2 ^ g.t * 2 ^ (g.z - g.t) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' ht]
    have ej : grpIndex g c r = joinG g (r / 2 ^ (g.z - g.t)) (r % 2 ^ (g.z - g.t)) c := by
      unfold grpIndex joinG
      rw [if_pos hE]
      by_cases hh : g.high = true
      · rw [if_pos hh, if_pos hh, hz]
        ring
      · rw [if_neg hh, if_neg hh, Nat.div_add_mod']
    obtain ⟨s1, s2⟩ := joinG_split hE ht (r / 2 ^ (g.z - g.t)) (Nat.mod_lt r hpos) hc
    have hi : r / 2 ^ (g.z - g.t) < g.o := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [Nat.mul_comm, ← left_E hR ht hl]
      exact hr
    rw [ej]
    refine ⟨?_, by rw [s1, Nat.div_add_mod']⟩
    rw [hR]
    exact lt_of_lt_of_le s2 (Nat.mul_le_mul_right _ hi)
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      rw [hl, if_pos h0] at hr
      obtain rfl : r = 0 := by omega
      have hcR : c < g.R := by
        unfold grpGuard at hgd
        rw [hA] at hgd
        simpa using hgd
      unfold grpIndex splitG
      simp only [hE, hA, Bool.false_eq_true, if_false, if_true]
      exact ⟨hcR, trivial⟩
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      have ht0 : g.t = 0 := by omega
      rw [ht0, pow_zero] at hc
      obtain rfl : c = 0 := by omega
      rw [hl, if_neg h0] at hr
      unfold grpIndex splitG
      simp only [hE, hA, Bool.false_eq_true, if_false]
      exact ⟨hr, trivial⟩

/-- **The factor's two halves at a column part and a row part**: 1 where the guard passes and the
two parts make the index v; 0 elsewhere. -/
theorem halves_delta {g : WsGrp} (hg : GrpOK g) (v : ℕ) {c r : ℕ} (hc : c < 2 ^ g.t)
    (hr : r < g.left) :
    colHalf ρ (deltaFac g v) g c * rowHalf ρ (deltaFac g v) g r =
      if grpGuard g c = true ∧ grpIndex g c r = v then 1 else 0 := by
  by_cases hgd : grpGuard g c = true
  · obtain ⟨h1, h2⟩ := grpIndex_split hg hc hr hgd
    have e := fac_split ρ (deltaFac g v) hg h1
    rw [h2, facAt_delta ρ hg h1] at e
    rw [e]
    by_cases h : grpIndex g c r = v
    · rw [if_pos h, if_pos ⟨hgd, h⟩]
    · rw [if_neg h, if_neg fun k => h k.2]
  · rw [if_neg fun k => hgd k.1]
    have hx : g.aTaken = true ∧ g.R ≤ c := by
      unfold grpGuard at hgd
      simpa using hgd
    have hE : (g.cls == 'E') = false := by
      have := hx.1
      unfold WsGrp.aTaken at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      rw [this.1]
      rfl
    unfold colHalf
    simp only [hE, hx.1, Bool.false_eq_true, if_false, if_true]
    rw [if_neg (by omega), zero_mul]

/-- The factor that a group bears where sel picks indices: in a group with a picked index the factor
that weighs that index alone; in another the pair's own. -/
def pickFac (sel : WsGrp → Option ℕ) (y : WsFac × WsGrp) : WsFac :=
  match sel y.2 with
  | some v => deltaFac y.2 v
  | none => y.1

theorem pickFac_some {sel : WsGrp → Option ℕ} {y : WsFac × WsGrp} {v : ℕ} (h : sel y.2 = some v) :
    pickFac sel y = deltaFac y.2 v := by
  unfold pickFac
  rw [h]

theorem pickFac_none {sel : WsGrp → Option ℕ} {y : WsFac × WsGrp} (h : sel y.2 = none) :
    pickFac sel y = y.1 := by
  unfold pickFac
  rw [h]

/-- The pairs of factors and groups, each group with the factor that it bears. -/
def deltaAt (sel : WsGrp → Option ℕ) (l : List (WsFac × WsGrp)) : List (WsFac × WsGrp) :=
  l.map fun y => (pickFac sel y, y.2)

theorem deltaAt_cons (sel : WsGrp → Option ℕ) (y : WsFac × WsGrp) (l : List (WsFac × WsGrp)) :
    deltaAt sel (y :: l) = (pickFac sel y, y.2) :: deltaAt sel l := rfl

/-- **The library's sum under such factors is its sum with the indices picked.** -/
theorem sumIdx_delta (sel : WsGrp → Option ℕ) : ∀ (l : List (WsFac × WsGrp)),
    (∀ y ∈ l, GrpOK y.2) → ∀ F : List ℕ → K,
    sumIdx ρ (deltaAt sel l) F = sumSel ρ sel l F
  | [], _, _ => rfl
  | (x, g) :: rest, hok, F => by
    have hg : GrpOK g := hok (x, g) List.mem_cons_self
    have ih := fun F' => sumIdx_delta sel rest (fun y hy => hok y (List.mem_cons_of_mem _ hy)) F'
    rw [deltaAt_cons]
    cases hs : sel g with
    | none =>
      rw [pickFac_none (y := (x, g)) hs]
      show ∑ v ∈ Finset.range g.R, facAt ρ x g v *
        sumIdx ρ (deltaAt sel rest) (fun idx => F (v :: idx)) = sumSel ρ sel ((x, g) :: rest) F
      unfold sumSel
      rw [hs]
      exact Finset.sum_congr rfl fun v _ => by rw [ih]
    | some v =>
      rw [pickFac_some (y := (x, g)) hs]
      show ∑ v' ∈ Finset.range g.R, facAt ρ (deltaFac g v) g v' *
        sumIdx ρ (deltaAt sel rest) (fun idx => F (v' :: idx)) = sumSel ρ sel ((x, g) :: rest) F
      unfold sumSel
      rw [hs]
      show _ = if v < g.R then sumSel ρ sel rest (fun idx => F (v :: idx)) else 0
      by_cases hv : v < g.R
      · rw [if_pos hv, Finset.sum_eq_single v]
        · rw [facAt_delta ρ hg hv, if_pos rfl, one_mul, ih]
        · intro v' hv' hne
          rw [facAt_delta ρ hg (Finset.mem_range.mp hv'), if_neg hne, zero_mul]
        · intro hn
          exact absurd (Finset.mem_range.mpr hv) hn
      · rw [if_neg hv]
        refine Finset.sum_eq_zero fun v' hv' => ?_
        rw [facAt_delta ρ hg (Finset.mem_range.mp hv'),
          if_neg (by have := Finset.mem_range.mp hv'; omega), zero_mul]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.getD_range_map
#print axioms ProofFile.Honest.K4.deltaFac_fits
#print axioms ProofFile.Honest.K4.facAt_delta
#print axioms ProofFile.Honest.K4.grpIndex_add
#print axioms ProofFile.Honest.K4.grpIndex_split
#print axioms ProofFile.Honest.K4.halves_delta
#print axioms ProofFile.Honest.K4.pickFac_some
#print axioms ProofFile.Honest.K4.pickFac_none
#print axioms ProofFile.Honest.K4.deltaAt_cons
#print axioms ProofFile.Honest.K4.sumIdx_delta
