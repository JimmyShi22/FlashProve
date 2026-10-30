-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/Facts338.lean: THREE FACTS ALONG "REACHED" UNDER THE ONE HEAD: the list of
commitment trees is in order, it fits, and the pending single rows' oracle messages are sent: IN THE
LETTERS OF THE THREE PREMISES bookInOrder, bookFits, rowsSent of the next token's kind's law
(Johnson/Desc/Kinds/Law/K07KindOfFacts.lean: k07_kind_of_facts). Two theorems; calls alone.


  facts_at_rch       from P5J.AtMg at `OnBytes.secondHashFunction`: the three, at every border and every switch
  **facts338_at_head**   from P5J.AtMgA: the three premises, to the letter (border 338, switch 23)

CALLED: bookInOrder_field and bookFits_field (Johnson/IMR/AtReach.lean), rowsSent_field
(Johnson/IMR/RowsSent.lean), fold_of_below and bookHas_fold (Johnson/IMR/AtReachFits.lean);
flat_planOk_at
(Johnson/Desc/Last/FourAtHead.lean); reach_raw (Johnson/Top/H0/Walk/Reach.lean); ft_at_switch
(Johnson/P1L20R/FtAtSwitch.lean). "Reached": P5J.AtMg.rch (Johnson/P5J/FourAtMg.lean): its first
half is "reached by the wrapped sub-protocols' steps" by unfolding.
NOT SPENT: the fence "no mark"; "the public part is a typed instance's".
What is not claimed. That a head can be had at any public files. Nothing at another hash than the
older one. The kind's law itself. No member. No soundness.

-/
import Johnson.IMR.AtReachFits
import Johnson.Desc.Last.FourAtHead
import Johnson.P1L20R.FtAtSwitch
import Johnson.P5J.FourAtMg
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2 (par9)
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The three facts along "reached", at every border and every switch, from the head.** -/
theorem facts_at_rch (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m k : ℕ) :
    (∀ a, h.rch k a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Zp m)).firstTree a.1.2 =
        true) ∧
    (∀ a, h.rch k a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) ∧
    (∀ a, h.rch k a → a.1.2.failed = none →
      ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := VerifiableInference.Desc.Last.flat_planOk_at h
  have hr : ∀ a, h.rch k a →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) k a.1 :=
    fun _ u => u.1
  refine ⟨fun a u hm => ?_, fun a u hm => ?_, fun a u hm => ?_⟩
  · rw [P1L20.ft_at_switch h.laid.pub m]
    exact Meaning.K2.bookInOrder_field O hp (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
      (fun a => a) (fun _ _ w => w) k a.1 (reach_raw (hr a u)) hm
  · exact Meaning.K2.bookFits_field O hp (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
      (fun a => a) (fun _ _ w => w) k a.1 (reach_raw (hr a u)) hm
  · exact Meaning.K2.rowsSent_field O hp
      (fun k a => Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) k a)
      (fun a => a) (Meaning.K2.fold_of_below (fun _ _ w => w))
      (fun k a w =>
        let ⟨_, _, _, _, f⟩ := Meaning.K2.fold_of_below (Rch := fun k a =>
          Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) k a)
          (at_ := fun a => a) (fun _ _ w => w) k a w
        Meaning.K2.bookHas_fold h.scope h.reads O hp f)
      k a.1 (hr a u) hm

/-- **The three premises of k07_kind_of_facts, to the letter.** -/
theorem facts338_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Zp 23)).firstTree a.1.2 =
        true) ∧
    (∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) ∧
    (∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size) :=
  facts_at_rch h.toAtMg 23 338

end IM

#print axioms IM.facts_at_rch
#print axioms IM.facts338_at_head
