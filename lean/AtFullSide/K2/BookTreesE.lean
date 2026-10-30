-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookTreesE.lean: a helper of AtFullSide/K2/BookTrees.lean: WHAT IS PUBLIC OF A SENDER
THAT A CODE SWITCH READS: under the head `P5J.AtMg` and the opening each sender's plan with its number
IS one of the 76 written pairs (`sendersWritten`, BookTreesC.lean), and a public test on these, put to
Lean's kernel once, says: the plan passes its own test · its codes are the written ones · its number
lies in the first chain · sub-protocol number b states just as many oracle messages as the plan lays
trees.

  `senderPlanFits P b`   the test on one sender
  `senders_plan_fit`     it says yes at all 76: by the kernel
  `senders_plan_fit_fails`   a control: it says no where the opening's plan is asked at number 5
  `sender_is_written`    under the head and the opening: (P, b) is a member of the written list
  `sender_plan_at_head`  the end: the three clauses of `sender_plan`
-/
import AtFullSide.K2.BookTreesC
import Johnson.Desc.K1.Own
import Johnson.IMR.EndFive
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K1 (Par firstPar parLater parL noL gpOf qFull gpFull laterFull
  LikeFull firstPar_full parLater_full planOkOwn)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open Johnson.G (codesFull2)
open OnBytes.Maker (WholeD)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest (treesTo)
open ProofFile.Honest.K2 (SwitchPlace switchPar switchPlaces)
open ProofFile.Honest.K2.Law (switchNo placesW places_at_head treesTo_at_head)

/-- **The test on one sender's plan.** -/
def senderPlanFits (P : Par) (b : Nat) : Bool :=
  planOkOwn P && decide (P.codes = codesFull2) && decide (b < 358) &&
    decide (treesTold toldFull (b + 1) = treesTold toldFull b + P.trees.length)

set_option maxRecDepth 1000000 in
/-- **It says yes at all the written senders.** -/
theorem senders_plan_fit : (sendersWritten.all fun x => senderPlanFits x.1 x.2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can fail**: the opening's plan (two trees) at number 5, which states one. -/
theorem senders_plan_fit_fails : senderPlanFits (firstPar qFull gpFull) 5 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **Under the head and the opening a sender's plan with its number is a written pair.** The
premise on P and b is the body of `SenderAt` (AtFullSide/K2/BookTrees.lean). -/
theorem sender_is_written (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : Par} {b : Nat}
    (hP : (P = firstPar Bs.G₀.first (gpOf Zp) ∧ b = 2) ∨
      (∃ l d, l < 25 ∧ P = parL Zp Bs.G₀ l d ∧ b = noL l d) ∨
      ∃ p₀ ∈ switchPlaces Zp Bs.G₀, P = switchPar p₀ ∧ b = switchNo p₀) :
    (P, b) ∈ sendersWritten := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hF : LikeFull Bs.G₀.first := by
    rw [O.first]
    exact VerifiableInference.Desc.K13.Law.likeFull_in_scope h.scope h.laid.pub hy
  have hg : gpOf Zp = gpFull :=
    VerifiableInference.Desc.K13.Law.gpOf_in_scope h.scope h.laid.pub hy
  rcases hP with ⟨rfl, rfl⟩ | ⟨l, d, hl, rfl, rfl⟩ | ⟨p₀, hp₀, rfl, rfl⟩
  · rw [firstPar_full hF, hg]
    exact List.mem_cons_self
  · have hm : (laterFull l d, noL l d) ∈ sendersWritten :=
      List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨l, List.mem_range.2 hl, List.mem_map.2 ⟨d, by cases d <;> simp, rfl⟩⟩))
    have e : parL Zp Bs.G₀ l d = laterFull l d := by
      cases d with
      | true =>
        show parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l true + 1) 2 = _
        rw [parLater_full hF, hg]
        rfl
      | false =>
        show parLater Bs.G₀.first (gpOf Zp) l (IM.k1Ix l false + 1) 1 = _
        rw [parLater_full hF, hg]
        rfl
    rw [e]
    exact hm
  · rw [places_at_head h O] at hp₀
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨p₀, hp₀, rfl⟩))

/-- **What is public of a sender**, under the head and the opening. -/
theorem sender_plan_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : Par} {b : Nat}
    (hP : (P = firstPar Bs.G₀.first (gpOf Zp) ∧ b = 2) ∨
      (∃ l d, l < 25 ∧ P = parL Zp Bs.G₀ l d ∧ b = noL l d) ∨
      ∃ p₀ ∈ switchPlaces Zp Bs.G₀, P = switchPar p₀ ∧ b = switchNo p₀) :
    planOkOwn P = true ∧ P.codes = codesFull2 ∧
      ∃ blk : Block TS ProofFile.Cl, cF.blocksInOrder[b]? = some blk ∧
        (blk.oracles.flatMap id).length = P.trees.length := by
  have k : senderPlanFits P b = true :=
    List.all_eq_true.1 senders_plan_fit (P, b) (sender_is_written h O hP)
  unfold senderPlanFits at k
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    decide_eq_true_eq] at k
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := k
  have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.scope O
  have hb : b < cF.blocksInOrder.length := by omega
  refine ⟨k1, k2, cF.blocksInOrder[b], List.getElem?_eq_getElem hb, ?_⟩
  have e := ProofFile.Honest.treesTo_succ (List.getElem?_eq_getElem hb)
  rw [treesTo_at_head h O, treesTo_at_head h O] at e
  omega

end AtFullSide.K2

#print axioms AtFullSide.K2.senders_plan_fit
#print axioms AtFullSide.K2.senders_plan_fit_fails
#print axioms AtFullSide.K2.sender_is_written
#print axioms AtFullSide.K2.sender_plan_at_head
