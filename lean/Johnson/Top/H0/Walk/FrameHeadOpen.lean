-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameHeadOpen.lean: THE PREMISE `HeadOpen` OF THE FIELD "items" AT THE LINK's
FRAME's STEPS (Johnson/Top/H0/Walk/FrameItemsOpen.lean), WHERE THE COMPOSED MEANING's PARAMETER
headPart IS THE OUTPUT HEAD's OWN FILLING `headPartK6` (Johnson/Desc/Kinds/Law/HeadCutsK6.lean).
Statements and proofs: a join of lemmas of Walk/ and of Johnson/Desc/Kinds/Law/.
  `headOpen_of_req`: over every relation R that keeps the request's reader of the filling, where the
    part "lookCallsHeard" of the output head's segment is not open behind: `HeadOpen 𝔇 Op R`. One
    call of `headPartK6_goesBack` (Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean) a part: its second
    premise, on the reader of the heard reply, is asked at that part alone.
  `headOpen_same`: at a step that leaves the verifier's state (the chain's front; "laid").
  `headOpen_kept`: at a step that gives `Kept`, from `ReadKept`.
  `headOpen_cleared`, `headOpen_clear_row`: at an accepting "cleared"; at the "cleared" of a row of
    the frame's own list.
With it the text of "goes back" that HeadPartsGoBack.lean writes out is held against `GoesBack`
(Johnson/Desc/Sound/ItemsRide.lean) by Lean.
Limits. That a real filling of 𝔇.headPart is `headPartK6` at some letters, with a request's reader
that is 𝔇.H's, is a premise. That "lookCallsHeard" is open at none of the frame's borders is a fact
on the table: a premise. `ReadKept` is a premise. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameItemsOpen
import Johnson.Desc.Kinds.Law.HeadPartsGoBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 headPartK6_goesBack)
open Inst.Model (ppref)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (sz : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (tab : ℕ → ℕ) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
  (H' : P5J.HidAt X P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT) rows cols)
  (tokH : P × S → Fin ppref.V)

/-- **The output head's own filling goes back wherever its item is open**, over a relation that
keeps the request's reader. -/
theorem headOpen_of_req
    (hhp : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H' tokH)
    (Op : Item → Prop) (hOp : ¬ Op (.constr (headLink X) .lookCallsHeard))
    (R : P × S → Strs → P × S → Strs → Prop)
    (hreq : ∀ a y b y', R a y b y' → H'.req a = H'.req b) : HeadOpen 𝔇 Op R := by
  intro p hp i
  rw [hhp]
  exact headPartK6_goesBack cs arr msR N sz seat X pl tab put H' tokH R hreq p
    (fun e => absurd (e ▸ hp) hOp) i

/-- At a step that leaves the verifier's state. -/
theorem headOpen_same
    (hhp : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H' tokH)
    (Op : Item → Prop) (hOp : ¬ Op (.constr (headLink X) .lookCallsHeard))
    (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : ℕ)
    (In : P × S → Strs → Prop) : HeadOpen 𝔇 Op (StepRel rel base In) :=
  headOpen_of_req 𝔇 cs arr msR N sz seat pl tab put H' tokH hhp Op hOp _ fun a y b y' h => by
    have hb : b = a := Prod.ext h.1 (hrel _ _ h.2.1)
    rw [hb]

/-- At a step that gives `Kept`. -/
theorem headOpen_kept
    (hhp : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H' tokH)
    (hH : H'.req = 𝔇.H.req)
    (Op : Item → Prop) (hOp : ¬ Op (.constr (headLink X) .lookCallsHeard))
    (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Kept s t) (base : ℕ)
    (In : P × S → Strs → Prop) (K : ReadKept 𝔇 base) : HeadOpen 𝔇 Op (StepRel rel base In) :=
  headOpen_of_req 𝔇 cs arr msR N sz seat pl tab put H' tokH hhp Op hOp _ fun a y b y' h => by
    rw [hH]
    exact (read3_of_kept 𝔇 rel hrel base In K).req a y b y' h

/-- At an accepting "cleared". -/
theorem headOpen_cleared
    (hhp : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H' tokH)
    (hH : H'.req = 𝔇.H.req)
    (Op : Item → Prop) (hOp : ¬ Op (.constr (headLink X) .lookCallsHeard)) (L : LinkPub)
    (counts : S → Except String Unit) (left : S → Option WsForkOut) (lay : WsLay)
    (lin : Params.LinShape) (base : ℕ) (In : P × S → Strs → Prop) (K : ReadKept 𝔇 base) :
    HeadOpen 𝔇 Op (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In) :=
  headOpen_kept 𝔇 cs arr msR N sz seat pl tab put H' tokH hhp hH Op hOp _
    (fun s t h => kept_cleared L counts left lay lin s t h) base In K

/-- At the "cleared" of a row of the frame's own list. -/
theorem headOpen_clear_row
    (hhp : 𝔇.headPart = headPartK6 cs arr msR N sz seat X pl tab put H' tokH)
    (hH : H'.req = 𝔇.H.req)
    (Op : Item → Prop) (hOp : ¬ Op (.constr (headLink X) .lookCallsHeard))
    {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : ℕ}
    (h : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (base : ℕ)
    (In : P × S → Strs → Prop) (K : ReadKept 𝔇 base) :
    HeadOpen 𝔇 Op (StepRel (Yes f.clear) base In) := by
  obtain ⟨L, counts, left, e⟩ : ∃ L counts left,
      f.clear = clearWith L counts left (Seat.rowOf W first) := by
    rcases Seat.framesOf_arms h hf with ⟨Y, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ |
      ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩
    · subst e
      exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
  rw [e]
  exact headOpen_cleared 𝔇 cs arr msR N sz seat pl tab put H' tokH hhp hH Op hOp L counts left
    W.layers.wsLay first.lin base In K

end

#print axioms headOpen_of_req
#print axioms headOpen_same
#print axioms headOpen_kept
#print axioms headOpen_cleared
#print axioms headOpen_clear_row

end Johnson.Desc.First.Walk.Tied
