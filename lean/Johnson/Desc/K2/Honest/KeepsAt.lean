-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/KeepsAt.lean: THE CODE SWITCH (K2): WHAT AN ACCEPTING STEP AT A PLACE OF THE
KIND LEAVES OF THE VERIFIER's STATE, IN ONE FORM FOR THE KIND's THREE SORTS OF PLACE: a sentence on
the place's numbers, the state in front (s) and the state behind (s'); its payers FROM A BLOCK's
ACCEPTING STEP (`StepYes`, Johnson/Top/H0/Walk/Reach.lean); and what it hands to whoever must pass
a place of the kind. Definitions; statements with their proofs. Over
Johnson/Desc/K2/Honest/Keeps.lean, which has the three sorts' sentences, and the library's law on
older messages' ledgers at these very blocks (Johnson/P1L20R/RoomKeepK2.lean).

  `K2Keeps`         THE ONE FORM. At every sort: OF EVERY MESSAGE THAT WAS THERE IN FRONT THE LEDGER
                    IS AS IT WAS, AND IF IT WAS A MEMBER OF NO GROUP IT IS A MEMBER OF NONE
                    (`P1L20.Off`). And, by where the place stands:
                    at a segment's first place   `K2KeepsLink`. OF THE MARK NO MORE THAN "AS IT
                                                 WAS": there a step of another text is joined
                                                 behind the kind's block
                    at the head's place          `K2PlaceHead`, AND NO MARK STANDS BEHIND
                    behind the last segment      `K2PlaceFinish`, AND NO MARK STANDS BEHIND
  `K2Keeps.common`  at every sort `K2Common`
  `k2Keeps_link_of`, `k2Keeps_link`   THE PAYER at a segment's first place: from the accepting step
                    of ANY block whose yes is a yes of the kind's own decision: a named premise; so:
                    of the kind's own block
  `k2Keeps_link_named`   so: of the kind's own block under another name and place, as the kind's
                    lot lays it (Johnson/Desc/ProofFile/Lot/K2.lean)
  `k2Keeps_head`, `k2Keeps_finish`   THE PAYERS at the two other sorts: from the accepting step of
                    ANY block whose yes is a yes of the place's block with no mark behind: a named
                    premise
  `k2Keeps_head_guarded`, `k2Keeps_finish_guarded`   so: at the place's block under the guard on the
                    mark (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean)
WHAT IT HANDS ON:
  `K2Keeps.pile`    the pile is as long as it was; the number of the index masks' message is as it
                    was
  `K2Keeps.ledger`  where the index masks' message has a ledger in front, it has the same behind
  `K2Keeps.outOfGroups`   where it has one and is a member of no group in front, it is a member of
                    none behind
  `K2Keeps.here`    at a segment's first place the chain stands where it stood

NEAR, NOT CALLED: the library's `Left` (Johnson/Top/H0/K2Ties/Left.lean; what it shares with
`K2Common`: Keeps.lean's head) from an accept at the kind's places: `left_of_seat`
(Johnson/Top/H0/K2Ties/Doors.lean) · `left_of_sits`, `left_bare_back` (Johnson/P1K2R/MoreLeft.lean)
· `left_first`, `left_bare_hear` (Johnson/P1K2R/SharesE.lean). Johnson/Desc/K2/Honest/LeftAt.lean
has `Left` from `StepYes`, binder for binder as the payers here.

Limits. A seat may lay more around a place's block than the guard on the mark: the two payers take
that as their premise and do not walk it. At the head's place and behind the last segment the chain
does NOT stand where it stood. Nothing on the ledger of a message that is sent in this very step. A
frame fact: it says what the texts do not write, not that a yes means a test. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Keeps
import Johnson.P1L20R.RoomKeepK2
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.ProofFile.Law.MarkGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith HeadPar headOpened finishPlace)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open Johnson.Desc.First.Walk.Law (ledgerAt)
open P1L20 (Off NoMem link_off head_off finish_off outOfGroupsB outOfGroupsB_iff)
open _root_.Tw.K2 (sendByL8)

/-- **THE ONE FORM.** -/
def K2Keeps (p : P2) (s s' : S) : Prop :=
  (∀ o, o < s.st.oracles.size → Off o s.st s'.st) ∧
    match p.stands with
    | .link => K2KeepsLink s s'
    | .head => K2PlaceHead s s' ∧ s'.failed = none
    | .finish => K2PlaceFinish s s' ∧ s'.failed = none

variable {p : P2} {s s' : S}

theorem K2Keeps.common (k : K2Keeps p s s') : K2Common s s' := by
  obtain ⟨_, k⟩ := k
  cases hp : p.stands <;> rw [hp] at k
  · exact k.1
  · exact k.1.1
  · exact k.1.1

/-! ## The payers -/

/-- At a segment's first place. hm: a yes of the block is a yes of the kind's own decision. -/
theorem k2Keeps_link_of {Cl : Type} {ft : Nat} {blk : Block S Cl} (hp : p.stands = .link)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t → decideWith sendByL8 p s rs gs = .ok t)
    (h : StepYes ft blk s s') : K2Keeps p s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  have e' := hm s rs gs s' e
  refine ⟨fun o ho => link_off hp e' ho, ?_⟩
  rw [hp]
  exact k2KeepsLink_of_yes hp e'

/-- From the kind's own block's accepting step. -/
theorem k2Keeps_link {Cl : Type} {ft : Nat} (hp : p.stands = .link)
    (h : StepYes ft (codeSwitchKind p : Block S Cl) s s') : K2Keeps p s s' :=
  k2Keeps_link_of hp (fun _ _ _ _ e => e) h

/-- The same under another name and place. -/
theorem k2Keeps_link_named {Cl : Type} {ft : Nat} (hp : p.stands = .link) (n : String) (pl : Place)
    (h : StepYes ft ({ (codeSwitchKind p : Block S Cl) with name := n, place := pl }) s s') : K2Keeps p s s' :=
  k2Keeps_link_of hp (fun _ _ _ _ e => e) h

/-- At the head's place. hm: a yes of the block is a yes of the place's block, with no mark behind.
-/
theorem k2Keeps_head {Cl : Type} {ft : Nat} {blk : Block S Cl} (hp : p.stands = .head) (n : String)
    (pl : Place) (P : HeadPar)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t →
      ((codeSwitchKind p : Block S Unit).andThen n (headOpened n pl P)).decide s rs gs = .ok t ∧
        t.failed = none)
    (h : StepYes ft blk s s') : K2Keeps p s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  obtain ⟨e', hf⟩ := hm s rs gs s' e
  refine ⟨fun o ho => head_off hp e' ho, ?_⟩
  rw [hp]
  exact ⟨k2PlaceHead_of_yes hp n pl P e', hf⟩

/-- Behind the last segment. -/
theorem k2Keeps_finish {Cl : Type} {ft : Nat} {blk : Block S Cl} (hp : p.stands = .finish)
    (hm : ∀ s rs gs t, blk.decide s rs gs = .ok t →
      (finishPlace p : Block S Unit).decide s rs gs = .ok t ∧ t.failed = none)
    (h : StepYes ft blk s s') : K2Keeps p s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  obtain ⟨e', hf⟩ := hm s rs gs s' e
  refine ⟨fun o ho => finish_off hp e' ho, ?_⟩
  rw [hp]
  exact ⟨k2PlaceFinish_of_yes hp e', hf⟩

/-- At the head's place's block under the guard on the mark. -/
theorem k2Keeps_head_guarded {ft : Nat} (hp : p.stands = .head) (n : String) (pl : Place)
    (P : HeadPar)
    (h : StepYes ft (ProofFile.guardMark ((codeSwitchKind p : Block S ProofFile.Cl).andThen n (headOpened n pl P))) s s') :
    K2Keeps p s s' :=
  k2Keeps_head hp n pl P (fun _ _ _ _ e => ProofFile.Law.guardMark_yes.1 e) h

/-- At the block behind the last segment under the guard on the mark. -/
theorem k2Keeps_finish_guarded {ft : Nat} (hp : p.stands = .finish)
    (h : StepYes ft (ProofFile.guardMark (finishPlace p : Block S ProofFile.Cl)) s s') : K2Keeps p s s' :=
  k2Keeps_finish hp (fun _ _ _ _ e => ProofFile.Law.guardMark_yes.1 e) h

/-! ## What it hands on -/

theorem K2Keeps.pile (k : K2Keeps p s s') :
    s'.out.pending.length = s.out.pending.length ∧ s'.out.indexMasks = s.out.indexMasks := by
  rw [k.common.2.1]
  exact ⟨rfl, rfl⟩

/-- The index masks' message's ledger. -/
theorem K2Keeps.ledger (k : K2Keeps p s s') {l : OnBytes.Ledger} (h : ledgerAt s = some l) :
    ledgerAt s' = some l := by
  have hlt : s.out.indexMasks < s.st.oracles.size := by
    by_cases hlt : s.out.indexMasks < s.st.oracles.size
    · exact hlt
    · unfold ledgerAt at h
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
      cases h
  unfold ledgerAt at h ⊢
  rw [k.pile.2, (k.1 _ hlt).1]
  exact h

/-- It stays out of every group. -/
theorem K2Keeps.outOfGroups (k : K2Keeps p s s') {l : OnBytes.Ledger} (hl : ledgerAt s = some l)
    (h : outOfGroupsB s = true) : outOfGroupsB s' = true := by
  have hlt : s.out.indexMasks < s.st.oracles.size := by
    by_cases hlt : s.out.indexMasks < s.st.oracles.size
    · exact hlt
    · unfold ledgerAt at hl
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hl
      cases hl
  have h0 : NoMem s.out.indexMasks s.st := fun i G hG =>
    outOfGroupsB_iff.1 h G (Array.mem_of_getElem? hG)
  refine outOfGroupsB_iff.2 fun G hG => ?_
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hG
  rw [k.pile.2]
  exact (k.1 _ hlt).2 h0 i G (by rw [Array.getElem?_eq_getElem hi, e])

/-- At a segment's first place the chain stands where it stood. -/
theorem K2Keeps.here (k : K2Keeps p s s') (hp : p.stands = .link) : s'.here = s.here := by
  obtain ⟨_, k⟩ := k
  rw [hp] at k
  exact k.2

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_link_of
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_link
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_link_named
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_head
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_finish
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_head_guarded
#print axioms VerifiableInference.Desc.K2.Honest.k2Keeps_finish_guarded
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps.ledger
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps.outOfGroups
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps.common
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps.pile
#print axioms VerifiableInference.Desc.K2.Honest.K2Keeps.here
