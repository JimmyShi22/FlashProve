-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPartsBear.lean: THE OUTPUT HEAD's FILLING OF THE LETTER headPart
(Law/HeadCutsK6.lean: headPartK6, at the hidden trace P5J.hidAtSeat) BEARS A TURN OF PADS OFF THE
TENANTS OF GROUP 24: two witnesses that share every message by its number, the token, the cells and
every pad off a list L of tenants, where no tenant of group 24 is in L, give each part one truth
value, one way. One theorem, by the cases of Law/ReadsSideK6.lean's constrK6_side.

WRITTEN OUT: the premise hT is the text of "PadsTurn L w w'" (Johnson/Top/H0/K2Ties/PadsTurn.lean:
for every component c that is no pad of a tenant of L: sameQ c w w'): not called by name here.

WHAT IT IS NOT. An implication. THAT NO TENANT OF GROUP 24 IS IN L (at L := what is kept of an
earlier segment) IS A PREMISE: on the table's numbers: not this file's. At a tenant of group 24
itself nothing is said: there the parts read the tenant's message with its seat's pad. Nothing on
soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsSideK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers Comp)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated sameQ)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE HEAD's PARTS BEAR A TURN OF PADS OFF GROUP 24.** -/
theorem headPartK6_bears {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (tokV : Tok → Fin ppref.V) (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (hK : PutKeeps put) (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (L : List (Nat × Nat))
    (hdis : ∀ x ∈ N.group 24, x ∉ L) (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hT : ∀ c : Comp, (∀ x ∈ L, c ≠ .pad x.1 x.2) → sameQ c w w') (p : P5J.TPart) (i : Cm.Idx)
    (a : P × P5J.TS) (y : Strs)
    (h : headPartK6 cs arr msR N s seat Wp pl tab put
      (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH p i a y w) :
    headPartK6 cs arr msR N s seat Wp pl tab put
      (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH p i a y w' := by
  have hG : OneOn arr (N.group 24) w w' := fun x hx =>
    ⟨hT (.msg (arr x.1 x.2)) (fun _ _ e => by cases e),
      hT (.pad x.1 x.2) fun z hz e => hdis x hx (by
        injection e with e1 e2
        have : x = z := Prod.ext e1 e2
        rw [this]
        exact hz)⟩
  have hcells : w.cells = w'.cells := hT .cells fun _ _ e => by cases e
  have htok : w.tok = w'.tok := hT .tok fun _ _ e => by cases e
  have hO := ownQ_same cs arr msR N s seat w w' hG
  obtain ⟨c1, c2⟩ := comp_of_cut cs arr msR N s seat Wp pl w w' (by unfold ownCut; rw [hO])
  have hcomp : (compCut cs arr msR N s seat Wp pl w).1 =
      (compCut cs arr msR N s seat Wp pl w').1 := by
    unfold compCut compOf ownCut
    rw [hO, hcells]
  cases p with
  | lookDigits => exact h
  | idn =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .idn c1
      c2 (fun _ => hO) (Or.inl rfl) h
  | rider =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .rider c1
      c2 (fun _ => hO) (Or.inr (Or.inl rfl)) h
  | small =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .small
      c1 c2 (fun _ => hO) (Or.inr (Or.inr rfl)) h
  | lookCalls =>
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokV w.tok)).val w
        .lookCalls := h
    show partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokV w'.tok)).val w' .lookCalls
    rw [← htok, ← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells hcomp]
    exact h3
  | lookCallsHeard =>
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokH a)).val w
        .lookCalls := h
    show partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokH a)).val w' .lookCalls
    rw [← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells hcomp]
    exact h3

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headPartK6_bears
