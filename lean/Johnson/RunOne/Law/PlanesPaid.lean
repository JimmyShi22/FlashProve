-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/PlanesPaid.lean: THE RUN
"planes" DOES NOT READ WHICH DEBTS ARE MARKED: the layer runs planesG at the record's ledger with
the first debt marked (G.paid g.owedObjects); three sentences in other files speak of closedAt at
the record's OWN ledger G: the second's yes from the first's, with the same claims.

Main names:
  hide_paid, hideSteps_paid, hideRun_paid: putting values under slots and marking a debt commute.
  pscRow_paid: Fl.pscRow's yes at F.paid i gives its yes at F, with the same answer and tape, and
    the ledger behind is that one with the debt marked.
  closed_of_paid: planesG f g (G.paid i) [] = some (pl, H', u) gives closedAt f g G = some (pl, G')
    with H' = G'.paid i.

Object: planesG (Johnson/Desc/First/Look/K3LookupGeneral.lean); closedAt
(Johnson/Desc/Key/KeyK3Items.lean). User: the tie at the fields r1_5 and r1_11.
Limits. Nothing on the claims' truth. Nothing on soundness.

-/
import Johnson.RunOne.Law.PlanesInv
import Johnson.Desc.Key.KeyK3Items

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.PlanesPaid
open OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params
open OnBytes.Model (Fork Aff Psc)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw

theorem hide_paid (F : Fork) (i j : ℕ) (y c : E) :
    (F.paid i).hide j y c = (F.hide j y c).map (·.paid i) := by
  unfold Fork.hide
  by_cases h : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) = true
  · rw [if_pos h, if_pos (show (decide (j < (F.paid i).ns) &&
      (F.paid i).gotF.size == (F.paid i).ns && !(F.paid i).gotF.getD j true) = true from h)]
    rfl
  · rw [if_neg h, if_neg (show ¬ (decide (j < (F.paid i).ns) &&
      (F.paid i).gotF.size == (F.paid i).ns && !(F.paid i).gotF.getD j true) = true from h)]
    rfl

theorem hideSteps_paid (c : E) (i : ℕ) : ∀ (l : List E) (a : ℕ) (F : Fork),
    l.foldlM (Fork.hideStep c) (a, F.paid i) =
      (l.foldlM (Fork.hideStep c) (a, F)).map fun x => (x.1, x.2.paid i)
  | [], _, _ => rfl
  | y :: l, a, F => by
    rw [List.foldlM_cons, List.foldlM_cons]
    have e1 : Fork.hideStep c (a, F.paid i) y =
        ((F.hide a y c).map (·.paid i)).map fun H => (a + 1, H) := by
      show ((F.paid i).hide a y c).map _ = _
      rw [hide_paid]
    have e2 : Fork.hideStep c (a, F) y = (F.hide a y c).map fun H => (a + 1, H) := rfl
    rw [e1, e2]
    cases F.hide a y c with
    | none => rfl
    | some H => exact hideSteps_paid c i l (a + 1) H

/-- **Putting a run of values under slots and marking a debt commute.** -/
theorem hideRun_paid (F : Fork) (i a : ℕ) (v : Array E) (c : E) :
    (F.paid i).hideRun a v c = (F.hideRun a v c).map (·.paid i) := by
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, hideSteps_paid]
  cases v.toList.foldlM (Fork.hideStep c) (a, F) with
  | none => rfl
  | some x => rfl

/-- Fl.pscRow's yes, from its test on the sumcheck's record and the run's yes. -/
theorem pscRow_fwd {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {t : Tape}
    (hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true)
    (hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Fl.pscRow p S0 kept F t = some ((p.rowForm S0 kept, { p with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  rw [bind_eq (must_ok hb F t), bind_eq (a := ()) (G := G) (u := t) (by
    show (F.hideRun _ _ _).map _ = _
    rw [hG]
    rfl)]
  rfl

/-- Fl.pscRow's yes at a ledger with a debt marked. -/
theorem pscRow_paid {p : Psc} {S0 : E} {kept : Aff} {F H : Fork} {i : ℕ} {t u : Tape}
    {x : Aff × Psc} (h : Fl.pscRow p S0 kept (F.paid i) t = some (x, H, u)) :
    ∃ G', Fl.pscRow p S0 kept F t = some (x, G', u) ∧ H = G'.paid i := by
  unfold Fl.pscRow at h
  replace h := bind_some h
  obtain ⟨_, G1, u1, h1, h⟩ := h
  obtain ⟨hb, rfl, rfl⟩ := must_some h1
  replace h := bind_some h
  obtain ⟨_, G2, u2, h2, h⟩ := h
  obtain ⟨h3, rfl⟩ := change_some h2
  rw [hideRun_paid] at h3
  cases hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) with
  | none =>
    rw [hG] at h3
    cases h3
  | some G' =>
    rw [hG] at h3
    obtain rfl : G'.paid i = G2 := Option.some.inj h3
    cases pure_some h
    exact ⟨G', pscRow_fwd hb hG, rfl⟩

/-- **The record's own ledger closes with the same claims.** -/
theorem closed_of_paid {f : Face} {g : HeardG} {G H' : Fork} {i : ℕ} {pl : List PlaneClaim}
    {u : Tape} (h : planesG f g (G.paid i) [] = some (pl, H', u)) :
    ∃ G', VerifiableInference.Desc.Key.closedAt f g G = some (pl, G') ∧ H' = G'.paid i := by
  unfold planesG at h
  replace h := bind_some h
  obtain ⟨⟨row, p'⟩, G1, u1, h1, h⟩ := h
  obtain ⟨G', h2, rfl⟩ := pscRow_paid h1
  cases pure_some h
  refine ⟨G', ?_, rfl⟩
  unfold VerifiableInference.Desc.Key.closedAt planesG
  rw [bind_eq h2]
  rfl

end Johnson.RunOne.Law.PlanesPaid

#print axioms Johnson.RunOne.Law.PlanesPaid.hide_paid
#print axioms Johnson.RunOne.Law.PlanesPaid.hideSteps_paid
#print axioms Johnson.RunOne.Law.PlanesPaid.hideRun_paid
#print axioms Johnson.RunOne.Law.PlanesPaid.pscRow_fwd
#print axioms Johnson.RunOne.Law.PlanesPaid.pscRow_paid
#print axioms Johnson.RunOne.Law.PlanesPaid.closed_of_paid
