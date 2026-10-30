-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/LeftAt.lean: THE CODE SWITCH (K2): FROM A BLOCK's ACCEPTING STEP (`StepYes`,
Johnson/Top/H0/Walk/Reach.lean) AT A PLACE OF THE KIND TO THE LIBRARY's `Left`
(Johnson/Top/H0/K2Ties/Left.lean: what an accept of the code switch leaves of the verifier's state),
AT THE KIND's THREE SORTS OF PLACE. No definition, and no law of its own on the state: calls of the
library's laws, in the form of the payers of `K2Keeps` (Johnson/Desc/K2/Honest/KeepsAt.lean), BINDER
FOR BINDER, so that a caller of one of these turns a name alone. Over the library alone.

  `k2Left_head_of_yes` with `k2Left_finish_of_yes`: a yes of the head's place's block · of the block
                    behind the last segment ⊢ `Left s s'`
  `k2Left_link_of` THE PAYER at a segment's first place: from the accepting step of ANY block whose
                    yes is a yes of the kind's own decision: a named premise
  `k2Left_link` with `k2Left_link_named`: so: at the kind's own block · at that block under another
                    name and place
  `k2Left_head` with `k2Left_finish`: THE PAYERS at the two other sorts: from the accepting step of
                    ANY block whose yes is a yes of the place's block with no mark behind: a named
                    premise
  `k2Left_head_guarded` with `k2Left_finish_guarded`: so: at the place's block under the guard on
                    the mark (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean)

By, the library's: `left_of_yes`, `Left.trans` (Johnson/Top/H0/K2Ties/Left.lean) · `left_headOpen`,
`left_finishFront`, `left_finishBehind` (K2Ties/Doors.lean) · `stepYes_decide`
(Johnson/Top/H0/Walk/ReachInv.lean) · `guardMark_yes` (Johnson/Desc/ProofFile/Law/MarkGuard.lean).
NEAR, NOT CALLED: `left_of_sits` (Johnson/P1K2R/MoreLeft.lean) with `sits_under_link`,
`sits_under_head`, `sits_under_finish` (Johnson/P1K2R/SitsStep.lean): `Left` from an accept of a
block that sits over the kind's own behind a door: at the blocks as a lot lays them (`under`,
retyped) · `left_first`, `left_bare_hear`, `left_bare_back` (Johnson/P1K2R/SharesE.lean,
MoreLeft.lean): at the pure description's own lots · `left_of_seat` (K2Ties/Doors.lean): at the
chain's own piece. WHAT `Left` HANDS ON stands in the library: `seat_left`, `shape_left`,
`agree_left`, `pile_back` (K2Ties/Pile.lean).

Limits. THE PREMISE ON WHERE THE PLACE STANDS (`p.stands = …`) IS SPENT NOWHERE, AND OF hm's TWO
HALVES AT THE TWO OTHER SORTS THE FIRST ALONE: they stand for the form's sake. A seat may lay more
around a place's block than the guard on the mark: the payers with a named premise take that as
their premise and do not walk it. At a segment's first place a step of another text is joined behind
the kind's block (the frame's): `left_opened` (K2Ties/Doors.lean) is the library's law for it: not
called here. A frame fact: it says what the texts do not write, not that a yes means a test. Nothing
on any property.
-/
import Johnson.Top.H0.K2Ties.Doors
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.ProofFile.Law.MarkGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith bindOk HeadPar headOpenQ headOpened
  finishPlace finishFrontQ finishBehindQ)
open VerifiableInference.Desc.First.K2Ties (Left left_of_yes left_headOpen left_finishFront
  left_finishBehind)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open _root_.Tw.K2 (sendByL8)

variable {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

/-! ## At a yes of the two other sorts' whole blocks -/

/-- A yes of the head's place's block. -/
theorem k2Left_head_of_yes {Cl : Type} (n : String) (pl : Place) (P : HeadPar)
    (h : ((codeSwitchKind p : Block S Cl).andThen n (headOpened n pl P)).decide s rs gs = .ok s') :
    Left s s' := by
  obtain ⟨m, h₁, h₂⟩ := bindOk (x := (codeSwitchKind p : Block S Cl).decide s
    (rs.take (codeSwitchKind p : Block S Cl).rounds.length) (gs.take (codeSwitchKind p : Block S Cl).openings)) h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  have h₂' : headOpenQ P m = .ok s' := h₂
  exact (left_of_yes h₁').trans (left_headOpen h₂')

/-- A yes of the block behind the last segment. -/
theorem k2Left_finish_of_yes {Cl : Type}
    (h : (finishPlace p : Block S Cl).decide s rs gs = .ok s') : Left s s' := by
  simp only [finishPlace, Block.andThen, VerifiableInference.Desc.roundlessBlock] at h
  obtain ⟨s₂, h₂, h₃⟩ := bindOk h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h₂
  have h₁' : finishFrontQ s = .ok s₁ := h₁
  have h₂' : decideWith sendByL8 p s₁ _ _ = .ok s₂ := h₂
  have h₃' : finishBehindQ s₂ = .ok s' := h₃
  exact (left_finishFront h₁').trans ((left_of_yes h₂').trans (left_finishBehind h₃'))

/-! ## The payers, from a block's accepting step: binder for binder as `K2Keeps`' payers -/

/-- At a segment's first place. hm: a yes of the block is a yes of the kind's own decision. -/
theorem k2Left_link_of {Cl : Type} {ft : Nat} {blk : Block S Cl} (_hp : p.stands = .link)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t → decideWith sendByL8 p s rs gs = .ok t)
    (h : StepYes ft blk s s') : Left s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  exact left_of_yes (hm s rs gs s' e)

/-- From the kind's own block's accepting step. -/
theorem k2Left_link {Cl : Type} {ft : Nat} (hp : p.stands = .link)
    (h : StepYes ft (codeSwitchKind p : Block S Cl) s s') : Left s s' :=
  k2Left_link_of hp (fun _ _ _ _ e => e) h

/-- The same under another name and place. -/
theorem k2Left_link_named {Cl : Type} {ft : Nat} (hp : p.stands = .link) (n : String) (pl : Place)
    (h : StepYes ft ({ (codeSwitchKind p : Block S Cl) with name := n, place := pl }) s s') : Left s s' :=
  k2Left_link_of hp (fun _ _ _ _ e => e) h

/-- At the head's place. hm: a yes of the block is a yes of the place's block, with no mark behind.
-/
theorem k2Left_head {Cl : Type} {ft : Nat} {blk : Block S Cl} (_hp : p.stands = .head) (n : String)
    (pl : Place) (P : HeadPar)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t →
      ((codeSwitchKind p : Block S Unit).andThen n (headOpened n pl P)).decide s rs gs = .ok t ∧
        t.failed = none)
    (h : StepYes ft blk s s') : Left s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  exact k2Left_head_of_yes n pl P (hm s rs gs s' e).1

/-- Behind the last segment. -/
theorem k2Left_finish {Cl : Type} {ft : Nat} {blk : Block S Cl} (_hp : p.stands = .finish)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t →
      (finishPlace p : Block S Unit).decide s rs gs = .ok t ∧ t.failed = none)
    (h : StepYes ft blk s s') : Left s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  exact k2Left_finish_of_yes (hm s rs gs s' e).1

/-- At the head's place's block under the guard on the mark. -/
theorem k2Left_head_guarded {ft : Nat} (hp : p.stands = .head) (n : String) (pl : Place)
    (P : HeadPar)
    (h : StepYes ft (ProofFile.guardMark ((codeSwitchKind p : Block S ProofFile.Cl).andThen n (headOpened n pl P))) s s') :
    Left s s' :=
  k2Left_head hp n pl P (fun _ _ _ _ e => ProofFile.Law.guardMark_yes.1 e) h

/-- At the block behind the last segment under the guard on the mark. -/
theorem k2Left_finish_guarded {ft : Nat} (hp : p.stands = .finish)
    (h : StepYes ft (ProofFile.guardMark (finishPlace p : Block S ProofFile.Cl)) s s') : Left s s' :=
  k2Left_finish hp (fun _ _ _ _ e => ProofFile.Law.guardMark_yes.1 e) h

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.k2Left_head_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_finish_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_link_of
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_link
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_link_named
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_head
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_finish
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_head_guarded
#print axioms VerifiableInference.Desc.K2.Honest.k2Left_finish_guarded
