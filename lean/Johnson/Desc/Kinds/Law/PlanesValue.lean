-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/PlanesValue.lean: THE LOOKUP's RUN "planes": ITS THREE CLAIMS AS PLAIN FORMS, AND WHAT THEY ARE WORTH: tools for the output head's row's clause on "planes" (Law/RowPlanes.lean); as Law/JoinValue.lean does it for "join". General in the caller: nothing of the head is in it.
OBJECT: First.Look.planeClaimsF (Johnson/Desc/First/Look/LookPlanes.lean), as K3.planesRun calls it (readers through Fl.need). USER: Law/RowPlanes.lean. LETTERS: g (what the lookup heard), lm, the caller's readers r1 r2 | forms bit pin, the world W, the columns' values v0 v1 u.
  colWeight · nCols · atForm · countForm · planeForms   the three forms, of the caller's forms: the leaves' sumcheck's row form at the planes' value at the leaves' point · "the hidden value under sBit is the planes' value at the bits' point" · the counts' sum.
  foldlM_need · planesAtF_spec · andThen_some · planeClaimsF_spec   WHERE planeClaimsF RETURNS AT READERS THAT MAY REFUSE, ITS THREE FORMS ARE planeForms AT THE FORMS READ ({} where a reader gives none: below the number of columns it gives one, else the run had refused); the tape is as it was.
  atVal · countVal · planeVals   the three VALUES with the columns' values laid in, in any commutative ring under a reading.
  planeForms_values   the three forms are worth planeVals at what the caller's forms are worth, column by column below nCols. By Psc.rowForm_value (OnBytes/Model/HideLaws.lean): the row form hangs on what is kept through its value alone.
EVERY LETTER UNDER "THERE IS": andThen_some's a G u: pinned by x F t = some (a, G, u). None in the other tops.
WHAT IT IS NOT. The ledger behind planeClaimsF (the leaves' hiding coefficients are laid by it: a late writer) is not written out: the spec gives the forms and the tape. planeVals' first value still reads the leaves' sumcheck's own start form in the world as it is (whether that form names an entry: not looked at). No draw, no error
term. Nothing on soundness.

-/
import Mathlib
import OnBytes.Model.HideLaws
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Planes

open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look (planesAtF planeClaimsF planesAddedF)

/-- The weight of column col in the planes' value at point number e. -/
def colWeight (g : Forest.Heard) (lm e col : Nat) : E :=
  mulE ((eqTab ((g.zb e).extract g.shape.kT (g.shape.kT + g.shape.cK))).getD
      (col / 2 ^ (g.shape.kT + 5 - lm)) zeroE)
    ((eqTab ((g.zb e).extract 0 (g.shape.kT + 5 - lm))).getD (col % 2 ^ (g.shape.kT + 5 - lm)) zeroE)

/-- The number of the planes' columns. -/
def nCols (g : Forest.Heard) (lm : Nat) : Nat := g.shape.NC * 2 ^ (g.shape.kT + 5 - lm)

/-- The planes' value at point number e, as a form, of the caller's forms. -/
def atForm (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Aff) : Aff :=
  (List.range (nCols g lm)).foldl (fun f col => Aff.addMul f (bit e col) (colWeight g lm e col))
    (Aff.ofConst zeroE)

/-- The counts' form. -/
def countForm (g : Forest.Heard) (lm : Nat) (pin : Nat → Aff) : Aff :=
  (List.range (nCols g lm)).foldl (fun f col => f + pin col)
    (Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))

/-- **The three forms of "planes".** -/
def planeForms (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Aff) (pin : Nat → Aff) : Array Aff :=
  #[g.leaves.rowForm oneE (Aff.scale (atForm g lm 0 bit) g.leavesA),
    Aff.slot g.sBit - atForm g lm 1 bit, countForm g lm pin]

/-- A fold of steps each of which reads one form of the caller's: where it returns, the ledger and the tape are as they were, and the value is the plain fold at the forms read. -/
theorem foldlM_need (r : Nat → Option Aff) (step : Aff → Nat → Aff → Aff) :
    ∀ (l : List Nat) (a y : Aff) (F G : Fork) (t u : Tape),
      (l.foldlM (fun (f : Aff) col => (do
        let x ← Fl.need (r col)
        pure (step f col x) : Fl Aff)) a) F t = some (y, G, u) →
      G = F ∧ u = t ∧ y = l.foldl (fun f col => step f col ((r col).getD {})) a
  | [], a, y, F, G, t, u, h => by
    have h' : (some (a, F, t) : Option (Aff × Fork × Tape)) = some (y, G, u) := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    exact ⟨h'.2.1.symm, h'.2.2.symm, h'.1.symm⟩
  | c :: l, a, y, F, G, t, u, h => by
    rw [List.foldlM_cons] at h
    cases hr : r c with
    | none =>
      have : False := by
        simp [bind, Fl.andThen, Fl.need, hr] at h
      exact this.elim
    | some x =>
      have h' : (l.foldlM (fun (f : Aff) col => (do
          let x ← Fl.need (r col)
          pure (step f col x) : Fl Aff)) (step a c x)) F t = some (y, G, u) := by
        simpa [bind, Fl.andThen, Fl.need, hr, pure, Fl.ret] using h
      obtain ⟨e1, e2, e3⟩ := foldlM_need r step l _ y F G t u h'
      refine ⟨e1, e2, ?_⟩
      rw [e3, List.foldl_cons, hr]
      rfl

/-- planesAtF at readers that may refuse: where it returns, it is atForm at the forms read. -/
theorem planesAtF_spec (g : Forest.Heard) (lm e : Nat) (r : Nat → Nat → Option Aff) (y : Aff)
    (F G : Fork) (t u : Tape)
    (h : planesAtF g lm e (fun e col => Fl.need (r e col)) F t = some (y, G, u)) :
    G = F ∧ u = t ∧ y = atForm g lm e fun e col => (r e col).getD {} :=
  foldlM_need (r e) (fun f col x => Aff.addMul f x (colWeight g lm e col)) _ _ y F G t u h

theorem andThen_some {α β : Type} (x : Fl α) (f : α → Fl β) (F : Fork) (t : Tape)
    (v : β × Fork × Tape) (h : Fl.andThen x f F t = some v) :
    ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some v := by
  unfold Fl.andThen at h
  cases hx : x F t with
  | none => rw [hx] at h; cases h
  | some w => rw [hx] at h; exact ⟨w.1, w.2.1, w.2.2, rfl, h⟩

/-- **WHAT THE RUN "planes" MAKES**: where planeClaimsF returns at the caller's readers, its three forms are planeForms at the forms read; the tape is as it was. -/
theorem planeClaimsF_spec (g : Forest.Heard) (lm : Nat) (r1 : Nat → Nat → Option Aff)
    (r2 : Nat → Option Aff) (fs : Array Aff) (F G : Fork) (t u : Tape)
    (h : planeClaimsF g lm (fun e col => Fl.need (r1 e col)) (fun col => Fl.need (r2 col)) F t
      = some (fs, G, u)) :
    u = t ∧ fs = planeForms g lm (fun e col => (r1 e col).getD {}) fun col => (r2 col).getD {} := by
  unfold planeClaimsF at h
  obtain ⟨_, F0, t0, h0, h⟩ := andThen_some _ _ F t _ h
  have e0 : F0 = F ∧ t0 = t := by
    unfold Fl.must at h0
    split at h0
    · simp only [Option.some.injEq, Prod.mk.injEq] at h0
      exact ⟨h0.2.1.symm, h0.2.2.symm⟩
    · cases h0
  rw [e0.1, e0.2] at h
  obtain ⟨a0, F1, t1, h1, h⟩ := andThen_some _ _ F t _ h
  obtain ⟨f1, g1, k1⟩ := planesAtF_spec g lm 0 r1 a0 F F1 t t1 h1
  rw [f1, g1] at h
  obtain ⟨a1, F2, t2, h2, h⟩ := andThen_some _ _ F t _ h
  obtain ⟨f2, g2, k2⟩ := planesAtF_spec g lm 1 r1 a1 F F2 t t2 h2
  rw [f2, g2] at h
  obtain ⟨cn, F3, t3, h3, h⟩ := andThen_some _ _ F t _ h
  obtain ⟨f3, g3, k3⟩ := foldlM_need r2 (fun f _ x => f + x) _ _ cn F F3 t t3 h3
  rw [f3, g3] at h
  obtain ⟨rw4, F4, t4, h4, h⟩ := andThen_some _ _ F t _ h
  -- the leaves' claim
  unfold Fl.pscRow at h4
  obtain ⟨_, F5, t5, h5, h4⟩ := andThen_some _ _ F t _ h4
  have e5 : t5 = t := by
    unfold Fl.must at h5
    split at h5
    · simp only [Option.some.injEq, Prod.mk.injEq] at h5
      exact h5.2.2.symm
    · cases h5
  obtain ⟨_, F6, t6, h6, h4⟩ := andThen_some _ _ F5 t5 _ h4
  have e6 : t6 = t5 := by
    unfold Fl.change at h6
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp h6
    simp only [Prod.mk.injEq] at e
    exact e.2.2.symm
  have h4' : (some ((g.leaves.rowForm oneE (Aff.scale a0 g.leavesA),
      { g.leaves with rowMade := true }), F6, t6) : Option ((Aff × Psc) × Fork × Tape))
      = some (rw4, F4, t4) := h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h4'
  have hfin : (some (#[rw4.1, Aff.slot g.sBit - a1, cn], F4, t4) :
      Option (Array Aff × Fork × Tape)) = some (fs, G, u) := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hfin
  refine ⟨by rw [← hfin.2.2, ← h4'.2.2, e6, e5], ?_⟩
  rw [← hfin.1, ← h4'.1, k1, k2, k3]
  rfl

/-! ## Values -/

section Value
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- The planes' value at point number e, of the columns' values v. -/
def atVal (g : Forest.Heard) (lm e : Nat) (v : Nat → K) : K :=
  ((List.range (nCols g lm)).map fun col => ρ.val (colWeight g lm e col) * v col).sum

/-- The counts' value, of the columns' values u. -/
def countVal (g : Forest.Heard) (lm : Nat) (u : Nat → K) : K :=
  ρ.val (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)) + ((List.range (nCols g lm)).map u).sum

/-- **The three forms' values, WITH THE COLUMNS' VALUES LAID IN**: v0, v1: a column's value at the leaves' point and at the bits' point; u: its count. None of the caller's forms is read any more; the world is read at the leaves' slots, at sBit, and by the leaves' sumcheck's own start form. -/
def planeVals (g : Forest.Heard) (lm : Nat) (v0 v1 u : Nat → K) : List K :=
  [sumFrom (fun j x => ρ.val x * W.slot j) g.leaves.first g.leaves.walk.1 +
      ρ.val g.leaves.eps * ρ.val g.leaves.walk.2 *
        (ρ.val g.leaves.target - g.leaves.start.value ρ W) +
      ρ.val g.leaves.eps * (ρ.val g.leavesA * atVal ρ g lm 0 v0) -
      (ρ.val g.leaves.claim - ρ.val g.leaves.eps * ρ.val oneE),
    W.slot g.sBit - atVal ρ g lm 1 v1, countVal ρ g lm u]

theorem fold_addMul_value (b : Nat → Aff) (w : Nat → E) : ∀ (l : List Nat) (a : Aff),
    (l.foldl (fun f col => Aff.addMul f (b col) (w col)) a).value ρ W =
      a.value ρ W + (l.map fun col => ρ.val (w col) * (b col).value ρ W).sum
  | [], a => by simp
  | c :: l, a => by
    rw [List.foldl_cons, fold_addMul_value b w l, Aff.value_addMul, List.map_cons, List.sum_cons]
    ring

theorem fold_add_value (b : Nat → Aff) : ∀ (l : List Nat) (a : Aff),
    (l.foldl (fun f col => f + b col) a).value ρ W =
      a.value ρ W + (l.map fun col => (b col).value ρ W).sum
  | [], a => by simp
  | c :: l, a => by
    rw [List.foldl_cons, fold_add_value b l, Aff.value_add, List.map_cons, List.sum_cons]
    ring

theorem atForm_value (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Aff) :
    (atForm g lm e bit).value ρ W = atVal ρ g lm e fun col => (bit e col).value ρ W := by
  unfold atForm atVal
  rw [fold_addMul_value, Aff.value_ofConst, ρ.zero, zero_add]

theorem countForm_value (g : Forest.Heard) (lm : Nat) (pin : Nat → Aff) :
    (countForm g lm pin).value ρ W = countVal ρ g lm fun col => (pin col).value ρ W := by
  unfold countForm countVal
  rw [fold_add_value, Aff.value_ofConst]

theorem atVal_congr (g : Forest.Heard) (lm e : Nat) (v v' : Nat → K)
    (h : ∀ col, col < nCols g lm → v col = v' col) : atVal ρ g lm e v = atVal ρ g lm e v' := by
  unfold atVal
  congr 1
  exact List.map_congr_left fun col hc => by rw [h col (List.mem_range.mp hc)]

theorem countVal_congr (g : Forest.Heard) (lm : Nat) (u u' : Nat → K)
    (h : ∀ col, col < nCols g lm → u col = u' col) : countVal ρ g lm u = countVal ρ g lm u' := by
  unfold countVal
  congr 2
  exact List.map_congr_left fun col hc => h col (List.mem_range.mp hc)

/-- **THE THREE FORMS ARE WORTH planeVals AT WHAT THE CALLER's FORMS ARE WORTH**, column by column, below the number of the planes' columns. -/
theorem planeForms_values (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Aff) (pin : Nat → Aff)
    (v0 v1 u : Nat → K) (h0 : ∀ col, col < nCols g lm → (bit 0 col).value ρ W = v0 col)
    (h1 : ∀ col, col < nCols g lm → (bit 1 col).value ρ W = v1 col)
    (hu : ∀ col, col < nCols g lm → (pin col).value ρ W = u col) :
    (planeForms g lm bit pin).toList.map (fun f => f.value ρ W) = planeVals ρ W g lm v0 v1 u := by
  unfold planeForms planeVals
  simp only [List.map_cons, List.map_nil]
  rw [Psc.rowForm_value, Aff.value_scale, Aff.value_sub, Aff.value_slot, atForm_value, atForm_value,
    countForm_value, atVal_congr ρ g lm 0 _ v0 h0, atVal_congr ρ g lm 1 _ v1 h1,
    countVal_congr ρ g lm _ u hu]

end Value

end VerifiableInference.Desc.Kinds.Head.Law.Planes

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Planes.planeClaimsF_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Planes.planeForms_values
