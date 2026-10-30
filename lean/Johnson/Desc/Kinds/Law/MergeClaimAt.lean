-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/MergeClaimAt.lean: the output head's own claim on the committed weights, as a
term of the carried record behind the head's own rounds' block.

The kind's decision (Kinds/HeadFrame.lean: decideBy) computes, of its letters and of what it heard,
one claim on the committed weights (Kinds/HeadCells.lean: forTheMerge) and hands it to the seat's
setWeightClaim. AT THE SEAT AT THE CARRIED RECORD (Johnson/Stored/HeadSeatAt.lean) THAT FUNCTION
LEAVES THE RECORD AS IT IS: THE CLAIM IS LAID NOWHERE. The claim that the merge takes is made later,
by another text, of the same record's fields. So that the two can be held against each other, the
kind's claim is named here as a function of the record.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  mergeClaimOf g H: the kind's claim at letters g and at what was heard H: the very term that
      decideBy hands to setWeightClaim.
  mergeClaimAt W s': the same off a record, through the seat's own readers (given; heard); nothing
      where either gives nothing.
  decide_hands: where a decision by decideBy goes on: the letters, what was heard, the two layings,
      and THE CLAIM THAT setWeightClaim IS HANDED, by its term. (Law/RowAtDecide.lean's decide_hears
      says the same with that claim under "there is", pinned by nothing.)
  mergeClaim_behind: behind a yes of the head's block at the carried record, from a well laid ledger
      and canonical rounds: mergeClaimAt W s' is there, and it is the claim that was handed and
      dropped.
  WeightAt W s' c mask: the sentence on that claim in what the block's law opens: WeightTrue
      (Law/K06Statement.lean) at the letters that the seat's readers give at s' and at s' own
      ledger.
  opened_weight: K6Out W s' d gives WeightAt W s' d.1.toCells d.2.

Every letter under "there is", and the clause that pins it. decide_hands: g by given; H and F by the
hearing's return; s1, s2 by the two layings. mergeClaim_behind: g by given at s and at s'; H and F
by the hearing's return (H also by the seat's reader heard at s'); s2 by the equation for s'.
WeightAt: g, H by the two readers at s'. What it does not say. THAT ANY LATER TEXT MAKES THE SAME
CLAIM. That WeightAt holds: it has no payer. Nothing on chance. Nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPins
import Johnson.Desc.Kinds.Law.HeardBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S)

/-- **The kind's claim on the committed weights**, at letters g and at what was heard H. -/
def mergeClaimOf (g : Given) (H : HeardAll) : SumOnMatrix :=
  (fun (_ : Given) (_ : Behind) => forTheMerge) g ⟨H.1, H.2.1, H.2.2⟩

/-- **The same off a record**, through the seat's own readers. -/
def mergeClaimAt (W : OnBytes.Model.Verify.Public) (s' : S) : Option SumOnMatrix :=
  (given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s').toOption.bind fun g =>
    ((seatAt W.hS (readsOf W)).heard s').map fun H => mergeClaimOf g H

/-- **The sentence on that claim in what the block's law opens.** -/
def WeightAt (W : OnBytes.Model.Verify.Public) (s' : S) (c : Cells) (mask : Nat → E) : Prop :=
  ∃ (g : Given) (H : HeardAll),
    given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' = .ok g ∧
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (let _ : Heard := H.2.2
     WeightTrue c ((seatAt W.hS (readsOf W)).ledger s') mask noEnt)

namespace Came

/-- **Where a decision goes on: what setWeightClaim is handed, by its term.** -/
theorem decide_hands {S' : Type} {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Seat S'} {s s' : S'}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (s1 s2 : S'),
      given p L s = .ok g ∧ hear g (L.ledger s) rs = some (H, F, []) ∧
      L.setLedger s F = .ok s1 ∧ L.setHeard s1 H = .ok s2 ∧
      s' = L.setWeightClaim s2 (weights g ⟨H.1, H.2.1, H.2.2⟩) := by
  unfold decideBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i g hg
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i v hv
        obtain ⟨H, F, left⟩ := v
        split at h
        · simp at h
        · rename_i u hu
          have hl : left = [] := by
            unfold need at hu
            split at hu
            · rename_i hb
              exact List.isEmpty_iff.1 hb
            · simp at hu
          subst hl
          split at h
          · simp at h
          · rename_i s1 h1
            split at h
            · simp at h
            · rename_i s2 h2
              simp only [Except.ok.injEq] at h
              refine ⟨g, H, F, s1, s2, hg, ?_, h1, h2, h.symm⟩
              unfold named at hv
              split at hv
              · rename_i y hy
                simp only [Except.ok.injEq] at hv
                rw [← hv]; exact hy
              · simp at hv

/-- **Behind a yes of the head's block: the kind's claim, off the record, is the claim that was
handed to the seat and dropped.** -/
theorem mergeClaim_behind (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rs) :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (s2 : S),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rs = some (H, F, []) ∧
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' = .ok g ∧
      (seatAt W.hS (readsOf W)).heard s' = some H ∧
      s' = (seatAt W.hS (readsOf W)).setWeightClaim s2 (mergeClaimOf g H) ∧
      mergeClaimAt W s' = some (mergeClaimOf g H) := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge)
      (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s rs = .ok s' := hd
  obtain ⟨g, H, F, s1, s2, hg, hh, e1, e2, hs'⟩ := decide_hands hd'
  obtain ⟨_, bH, bG, _⟩ := seatBack_at W.hS (readsOf W) (workOf W) s g rs [] F H
    (mergeClaimOf g H) s1 s2 hg hWL hcan hh e1 e2
  have hs2 : s' = (seatAt W.hS (readsOf W)).setWeightClaim s2 (mergeClaimOf g H) := hs'
  rw [← hs2] at bH bG
  refine ⟨g, H, F, s2, hg, hh, bG.trans hg, bH, hs2, ?_⟩
  unfold mergeClaimAt
  rw [bG, hg, bH]
  rfl

/-- **What the block's law opens holds the sentence on that claim.** -/
theorem opened_weight (W : OnBytes.Model.Verify.Public) (s' : S) (d : Pinned)
    (h : K6Out W s' d) : WeightAt W s' d.1.toCells d.2 := by
  obtain ⟨⟨g, H, hg, hH, hO⟩, _⟩ := h
  exact ⟨g, H, hg, hH, hO.1⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_hands
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.mergeClaim_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.opened_weight
