-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SampleReach.lean: the two invariants on the messages' stored sample rows that
the code switch's law spends (SampleGoodS: SampleChainS.lean; AnsweredStored: AnsweredStored.lean),
SPENT FROM "REACHED" (Walk/Reach.lean): at a state of the verifier that the chain's own blocks, each
under the test on the words (`below`), hand on from the start. A law file; no running text imports
it.

"Reached" is taken at the WRAPPED list (bs.map below), as Walk/ReachAt.lean's RchAt takes it: a step
of `below b` holds the test on the words, which gives that the rounds' drawn elements are in
canonical form: what the code switch's keeping of SampleGoodS leans on.

  keepsD_below     a block that keeps P on rounds with OkDrawn keeps it, under `below`, on all
                   rounds: by below_yes (Johnson/Desc/Sound/PieceYes.lean) and okDrawn_of_view.
  prop_of_reach    general in the property: where every block in front of the border keeps it and
                   it holds at the start, it holds at every reached state.
  inv_of_reach, goodS_of_reach, ans_of_reach   at RowsInv Q, SampleGoodS, AnsweredStored.
  KeepsBoth l, both_of_reach   the keepers' table as ONE named premise; both invariants in one
                   call.
Limits. KeepsBoth at the description's own first chain, in front of a code switch, is each kind's
files' to pay; K2's lot is paid (keepsInv_pureAt with keepsS_k2; keepsAns_pureAt). The two starts
are premises here: goodS_start and answered_first pay them at the description's start. Nothing on
soundness.

-/
import Johnson.Top.H0.K2Hands.AnsweredStored
import Johnson.Top.H0.K2Hands.SampleChainS
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (below below_yes)
open VerifiableInference.Desc.Keeps1
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Cl : Type}

theorem keepsD_below {P : S → Prop} {b : Block S Cl} (h : KeepsD OkDrawn P b) :
    KeepsD (fun _ => True) P (below b) := by
  intro s s' rs gs _ hy hs
  obtain ⟨hv, hd⟩ := below_yes b s s' rs gs hy
  exact h s s' rs gs (okDrawn_of_view hv) hd hs

/-- General in the property. -/
theorem prop_of_reach {Z : Type} {P : S → Prop} {ft : Nat} {bs : List (Block S Cl)}
    {start : Z → S} {k : Nat} {z : Z} {s : S} (hb : ∀ b ∈ bs.take k, KeepsD OkDrawn P b)
    (h0 : P (start z)) (h : Reach ft (bs.map below) start k (z, s)) : P s := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  refine fold_keeps (R := fun _ => True) (P := P) (fun _ _ => trivial) ft _ _ s rs [] cols []
    (fun c hc => ?_) (fun _ _ => trivial) hf h0
  rw [← List.map_take] at hc
  obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hc
  exact keepsD_below (hb b hbm)

variable {Z : Type} {ft : Nat} {bs : List (Block S Cl)} {start : Z → S} {k : Nat} {z : Z} {s : S}

theorem inv_of_reach {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}
    (hb : ∀ b ∈ bs.take k, KeepsInv Q b) (h0 : RowsInv Q (start z).st)
    (h : Reach ft (bs.map below) start k (z, s)) : RowsInv Q s.st :=
  prop_of_reach (P := Inv Q) hb h0 h

theorem goodS_of_reach (hb : ∀ b ∈ bs.take k, KeepsInv QGoodS b) (h0 : SampleGoodS (start z).st)
    (h : Reach ft (bs.map below) start k (z, s)) : SampleGoodS s.st :=
  inv_of_reach (Q := QGoodS) hb h0 h

theorem ans_of_reach (hb : ∀ b ∈ bs.take k, KeepsAns b) (h0 : AnsweredStored (start z).st)
    (h : Reach ft (bs.map below) start k (z, s)) : AnsweredStored s.st :=
  prop_of_reach (P := Ans) (fun b hm => (hb b hm).mono fun _ _ => trivial) h0 h

/-- **The keepers' table, as one premise**: every block of the list keeps both invariants. -/
structure KeepsBoth (l : List (Block S Cl)) : Prop where
  good : ∀ b ∈ l, KeepsInv QGoodS b
  ans : ∀ b ∈ l, KeepsAns b

/-- **Both, in one call.** -/
theorem both_of_reach (hb : KeepsBoth (bs.take k)) (h1 : SampleGoodS (start z).st)
    (h2 : AnsweredStored (start z).st) (h : Reach ft (bs.map below) start k (z, s)) :
    SampleGoodS s.st ∧ AnsweredStored s.st :=
  ⟨goodS_of_reach hb.good h1 h, ans_of_reach hb.ans h2 h⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.both_of_reach
#print axioms VerifiableInference.Desc.First.K2.keepsD_below
