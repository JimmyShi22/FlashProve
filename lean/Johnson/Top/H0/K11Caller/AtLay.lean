-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/AtLay.lean: the place of the merge from a layout of the program's, with no premise left on the layout.

    unitOK_of      a unit with OnBytes.Road.UnitOK (Johnson/Road/FormsKeysWOk.lean) that lies within W is in order (unitOK, Coef.lean)
    ofLay_unit, ofLay_in, ofLay_pos   every unit of a layout out of wsLayOf has UnitOK and lies within W (both by OnBytes.Road.unitOK_of_layout, Johnson/Road/FormsKeysWLay.lean); such a layout has a column bit
    Place.ofLay    a layout out of wsLayOf, the number of claims, each claim's unit as a number below the number of units
    Letters.plain  the plain member of the letters: St := In E n, read as it is; Rd := True. Jm, nm, wAt, cAt stay arguments
    GFirst         the record of the first group's stretch (Cb.Pv.Lay.WFirstL)
So at every model's shape at which wsLayOf does not refuse there is a value of WeightsL E whose summand is Coef.lean's text.

-/
import Johnson.Top.H0.K11Caller.Caller
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes.Model
open OnBytes.Road (UnitOK Runs)

theorem chainB_of_runs : ∀ (gs : List WsGrp) (cb : ℕ), Runs gs cb → chainB gs cb = true
  | [], _, _ => rfl
  | g :: gs, cb, h => by
    simp only [chainB, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h.1, chainB_of_runs gs _ h.2⟩

theorem endOf_eq : ∀ (gs : List WsGrp) (cb : ℕ), endOf gs cb = cb + (gs.map (·.t)).sum
  | [], cb => by simp [endOf]
  | g :: gs, cb => by
    simp only [endOf, List.map_cons, List.sum_cons]
    rw [endOf_eq gs]
    omega

/-- A unit with OnBytes.Road.UnitOK that lies within W is in order. -/
theorem unitOK_of {lay : WsLay} {u : WsUnit} (U : UnitOK lay.lk u) (h : u.off + u.rows ≤ lay.m0) : unitOK lay u = true := by
  simp only [unitOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨chainB_of_runs _ _ U.runs, by rw [endOf_eq, U.ncb]; omega⟩, U.le⟩, h⟩

section OfLay
variable {s : WsShape} {p3 : Bool} {lkW : ℕ} {lay : WsLay}

/-- Every unit of a layout out of wsLayOf has OnBytes.Road.UnitOK. -/
theorem ofLay_unit (h : wsLayOf s p3 lkW = .ok lay) (i : ℕ) (u : WsUnit) (hu : lay.U[i]? = some u) : UnitOK lay.lk u := by
  obtain ⟨h1, h2⟩ := OnBytes.Road.unitOK_of_layout h
  rw [h1]
  exact (h2 u (Array.mem_of_getElem? hu)).1

/-- Every unit of a layout out of wsLayOf lies within W. -/
theorem ofLay_in (h : wsLayOf s p3 lkW = .ok lay) (i : ℕ) (u : WsUnit) (hu : lay.U[i]? = some u) : u.off + u.rows ≤ lay.m0 :=
  ((OnBytes.Road.unitOK_of_layout h).2 u (Array.mem_of_getElem? hu)).2

/-- A test in a do-block: "if c then throw e", and on. -/
theorem guard_ok {ε β : Type} {c : Prop} [Decidable c] {e : ε} {f : PUnit → Except ε β} {b : β}
    (h : (if c then (throw e : Except ε PUnit) >>= f else pure PUnit.unit >>= f) = .ok b) : ¬ c ∧ f PUnit.unit = .ok b := by
  split at h
  · exact absurd h (by simp [bind, Except.bind])
  · exact ⟨‹_›, h⟩

/-- A layout out of wsLayOf has a column bit. -/
theorem ofLay_pos (h : wsLayOf s p3 lkW = .ok lay) : 0 < lay.lk := by
  rw [(OnBytes.Road.unitOK_of_layout h).1]
  unfold wsLayOf at h
  obtain ⟨_, h⟩ := guard_ok h
  obtain ⟨h2, _⟩ := guard_ok h
  simp only [tokenFactorTaken, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, Decidable.not_not] at h2
  omega

/-- **The place from a layout of the program's.** -/
def Place.ofLay (lay : WsLay) (h : wsLayOf s p3 lkW = .ok lay) (n : ℕ) (ui : Fin n → Fin lay.U.size) : Place where
  lay := lay
  n := n
  ui := fun a => (ui a).val
  ok := fun a => ⟨lay.U[(ui a).val], by simp, unitOK_of (ofLay_unit h (ui a).val _ (by simp)) (ofLay_in h (ui a).val _ (by simp))⟩

end OfLay

/-- The plain member of the letters. -/
def Letters.plain {E : Type} [Field E] [Fintype E] (P : Place) (Jm : Type) [Fintype Jm] (nm : Fin P.n → Jm)
    (wAt : Cb.PIdx (Cb.ldPartFmt E P.lay.lk (fun _ => 2) ++ [Cb.pDummy E 1]) → Jm) (cAt : Jm) : Letters E P where
  Jm := Jm
  St := In E P.n
  rd := id
  nm := nm
  wAt := wAt
  cAt := cAt
  Rd := fun _ _ => True

/-- **The record of the first group's stretch** (Cb.Pv.Lay.WFirstL: one scalar more is sent in the round of the draw): the record G, and the new claim's summand fe: the same text at the
unit uiE (the embedding's) and the factors fsE; its field dege is the same theorem. Letters, the link's law's: fsE (the new claim's factors, out of the state), rhs (the other side of the
identity), mkE (the name of the sent scalar's mask entry). Which place the new claim has among the program's claims is NOT held here. -/
def GFirst {E : Type} [Field E] [Fintype E] (P : Place) (T : Letters E P) (uiE : ℕ) (okE : ∀ u, P.lay.U[uiE]? = some u → unitOK P.lay u = true)
    (fsE : T.St → List (Fac E)) (rhs : T.St → (P.Cell ⊕ T.Jm → E) → E) (mkE : T.Jm) : Cb.Pv.Lay.WFirstL E where
  toWeightsL := G P T
  fe := fun st m z => summand P uiE (fsE st) (fun rc => m (.inl rc)) z
  dege := fun st m => deg_summand P uiE (fsE st) (fun rc => m (.inl rc)) okE
  rhs := rhs
  mkE := .inr mkE

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.unitOK_of
#print axioms VerifiableInference.Desc.First.K11Caller.ofLay_pos
#print axioms VerifiableInference.Desc.First.K11Caller.Place.ofLay
#print axioms VerifiableInference.Desc.First.K11Caller.GFirst
