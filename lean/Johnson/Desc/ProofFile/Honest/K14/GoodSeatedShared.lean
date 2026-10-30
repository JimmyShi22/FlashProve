-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/GoodSeatedShared.lean: kind K14: CONDITIONAL. good_rows
(Honest/K14/GoodSeated.lean) AT ANY LETTERS WHOSE LIST OF MEMBERS IS THE CARRIED SHARED CHAIN's FLAT
LIST AT THE PLANNER's OWN PARAMETERS qAt Zp Np (hL), UNDER FOUR MORE PREMISES ON PUBLIC DATA. Such a
list has the form FlatOf (flatOf_carried). The shared chain's letters at the IOP as written in Lean
(lettersShared, Honest/Thread/SharedHead.lean) have that list by unfolding (at_bs,
Honest/K14/AskedAtShared.lean: the same right side): the statement does not name them, and is wider.
That the library makes its eight is no premise: it follows from the list's own tests on the plan
(the library's eight_of_pass). (So too in a like statement at what onlineDescription returns, in a file that
is not part of this tree.)

  good_rows_shared   **where the letters' list is that list (hL), every member of it passes its test
                  on the plan and the two tests on the shapes accept at qAt Zp Np: k14Rows returns
                  rows of that plan and that list, at the four places in order; and at each, at a
                  book that passes noneSpent there, Side.seated returns a side of that list, and
                  Good holds of it as one term, AT THE LETTERS False**, at whatever falls and at
                  every pre; every other field of the letters is free

FIVE PREMISES: hL, on the letters' list; and four on public data: every member's own test on the
plan (hp) · linOk (hok) · sendingsFit (hfit) · noneSpent. NONE OF THE FOUR IS SHOWN AT ANY PUBLIC
FILE. What other files of this folder, none of them imported here, show of them, each under a
premise and not at a file: linOk follows from hp, the premise beside it
(Honest/K14/AtFillingMore.lean: linOk_carried), so hok is a spare premise; under the library's head
(P5J.AtMgA, Johnson/P5J/MgAtAll.lean) linOk and sendingsFit hold at these very parameters
(Honest/K14/SendingsAtFilling.lean: linOk_at_head; Honest/K14/SendingsAtHead.lean: sendings_at_head,
and in the goals' scope from LaidAt: sendings_of_laid). The members' tests on the plan and noneSpent
stay premises. THE FIELDS plays AND acc HOLD FROM A FALSE PREMISE AND SHOW NOTHING; what is shown is
fits, exact and fresh, with all the limits of Honest/K14/GoodCalls.lean.

What is not claimed. Any of the four premises at a public file. Nothing on what is or is not hidden;
no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.GoodSeated
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.K14.Law.K14SitsPlan
import Johnson.Desc.K14.Law.SplitGiven

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (TS)
open Desc.K14 (St)
open Desc.K14.Honest (flatOf_carried)
open Desc.K14.Law (eight_of_pass own_pass_carried split_given)
open ProofFile.Honest.Small (noneSpent)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {Bk₀ : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X)

/-- CONDITIONAL. **good_rows, AT THE LETTERS False, at any letters L whose list of members is the
carried shared chain's flat list at qAt Zp Np (hL)**, where every member of the list passes its test
on the plan (hp), linOk (hok) and sendingsFit (hfit) accept there, and the book passes noneSpent at
the row's place. At the letters False Good's fields plays and acc hold from a false premise and show
nothing. The shared chain's letters at the IOP as written in Lean have that list (at_bs,
Honest/K14/AskedAtShared.lean); the statement does not name them. It holds at every pre: pre is tied
to no description; at each pre this says no more than the law on ExactMember beneath
(Honest/K14/GoodSeated.lean). -/
theorem good_rows_shared {Pb : Type}
    (L : SharedThread.Letters Bk₀ St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt)
    (hL : L.bs = ((Desc.K14.chainOf Zp.p.chains (qAt Zp Np) (tests Np) last).retype
      (Cl' := ProofFile.Cl)).blocksInOrder)
    (hp : ∀ b ∈ L.bs, b.planOk = true)
    (hok : OnBytes.linOk (qAt Zp Np).codes (qAt Zp Np).S = true)
    (hfit : sendingsFit (qAt Zp Np) = true) (weights : W₀ → Weights) :
    ∃ rs : List (Unlettered Empty (Common W₀ Rc TableKey) X₀ Pb),
      k14Rows (qAt Zp Np) L.bs weights = .ok rs ∧
      rs.map (·.place) = [place 1, place 4, place 7, place 8] ∧
      ∀ r ∈ rs, ∀ (fs : List (Fall St)) (φ : Face Empty (Common W₀ Rc TableKey) Pb) (Bk : ProverCoinCounts)
        (ord : List Place) (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)),
        noneSpent Bk { place := r.place, part := 0 } = true →
        ∃ σ, Side.seated L.bs r.place r.row fs = some σ ∧
          Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
            r.bud := by
  rw [hL] at hp ⊢
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ :=
    eight_of_pass Zp.p.chains (qAt Zp Np) (tests Np) last hp
  have h8 : b8.planOk = true := by
    have key := own_pass_carried Zp.p.chains (qAt Zp Np) (tests Np) last hp
    unfold Desc.K14.blocksOr at key
    rw [hb] at key
    exact key b8 (by simp)
  have hS := split_given _ b1 b2 b3 b4 b5 b6 b7 b8 hb h8
  have Fl := flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
    (tests Np) last hb
  exact ⟨_, k14Rows_flat Fl hb hok hfit weights, ownRows_four _ weights hS,
    fun r hr fs φ Bk ord chain firstTree pre hB =>
      good_rows_some Fl hb _ rfl weights r hr fs φ Bk ord chain firstTree pre hB⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.good_rows_shared
