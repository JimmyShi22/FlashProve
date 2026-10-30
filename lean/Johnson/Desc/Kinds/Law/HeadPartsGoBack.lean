-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean: THE OUTPUT HEAD's FILLING OF THE LETTER headPart
(Law/HeadCutsK6.lean: headPartK6) GOES BACK over every relation between two verifier's states that
keeps the request's reader, and, for the one part that reads it, the reader of the heard reply. One
theorem, by Law/HeadCutsK6.lean's headPartK6_blind.

WRITTEN OUT: the conclusion is the text of "GoesBack rel (headPart p i)" as another file
has it (Johnson/Desc/Sound/ItemsRide.lean: GoesBack rel phi := for all a y b y' w: rel a y b y' and
phi b y' w give phi a y w): that file is not imported here.

WHAT IT IS NOT. An implication. That a relation keeps the two readers is not shown here. At
the parts other than lookCallsHeard nothing is asked of the reader of the heard reply. Nothing on
soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE HEAD's PARTS GO BACK.** -/
theorem headPartK6_goesBack {P : Type} (tab : Nat → Nat)
    (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V)
    (rel : P × P5J.TS → Strs → P × P5J.TS → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (p : P5J.TPart)
    (htok : p = .lookCallsHeard → ∀ a y b y', rel a y b y' → tokH a = tokH b) (i : Cm.Idx) :
    ∀ a y b y' w, rel a y b y' →
      headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i b y' w →
      headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w := by
  intro a y b y' w hr h
  rw [← Came.headPartK6_blind cs arr msR N s seat Wp pl tab put H tokH p i a b y y' w
    (hreq a y b y' hr).symm fun hp => (htok hp a y b y' hr).symm]
  exact h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack
