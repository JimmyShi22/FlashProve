-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/SeatsApartAtHead.lean

Under the library's head AtMg (Johnson/P5J/AtMg.lean), with no further premise: the seats off the
request's layout are apart: SeatsApart (Johnson/Goal/HonestTrace/SeatsApartOfLayout.lean) at the
head's own values: At.X Zp, the library's sizes, the layout At.layout Zp and the numbering At.num Zp
of the witness's messages.
This file states no goal.

Main theorems:
* "numsApartAt_of_named": for lists of the plan's seats ps₁ and ps with every member of ps₁ in ps,
  and numbers N whose field sent is that of P5T.numbersOf ps₁: where the test P5J.seatsNamedC
  accepts at P5T.numOfPlan ps and P5T.arrOf ps, NumsApartAt holds at P5T.numOfPlan ps.
* "seatsApart_at_mg": under h : AtMg o Z D r Zp Np cF: SeatsApart at the head's own values.
* "seatsApart_at_head": the same under AtMgA (Johnson/P5J/MgAtAll.lean), which extends AtMg.

How. seatsApart_of_layout takes four premises. Meaning.laidThere is the head's field plan.laid. The
programs' test on the layout accepts by pub_layoutOk (Johnson/IMR/LayoutOkPub.lean) at the head's
field laid.pub; the library has the same under AtMgA (AtMgA.three, Johnson/P5J/K03OneOwnAt.lean; at
the concrete earlier hash Q38.lawful_at_head, Johnson/HB/LLHARD/Q38J/LawfulAtHead.lean). LabelsApart
is labelsApart_in_scope at the fields scope, reads and pubOne; that the library's sizes follow the
plans is Meaning.follows_of_core (Johnson/Goal/Meaning/HidPlanNM.lean) at Hd.core_of_scope
(Johnson/Goal/Meaning/ScopeCore.lean). NumsApartAt comes from the field plan.named: the test says
that the number of a named array's message has just one tenant in its sub-proof's group; a tenant of
a group is a seat of the plan's list (P5T.group_mem, Johnson/P5T/GroupsByMake.lean); whatever seat
has the number of a message has that message's key (P5T.key_of_num, Johnson/P5T/KeyBack.lean); two
seats with one number have one key (P5T.arrOf_key, Johnson/P5T/ArrApart.lean).

Limits. This file shows no member of AtMg. The library has members of AtMgA at the concrete earlier
hash: under the scope, the reader's return and protocolDataWellFormed (head_of_live,
Johnson/Goal/Meaning/ServedChains.lean), and, with no premise, at the stored full-size files
VerifierAndGoals.storedPublicFiles (headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean: the side library; its own
Limits say what it is worth). Neither is called here. At another earlier hash no member is shown.
The full size alone, as the head. The seats of symbols in main rows alone: nothing on mask rows or
pads. It says that no two seats inside the sizes name one place. That messages with prescribed
symbols at the seats can then be written is not stated here; this file writes none.

Not claimed: that an honest prover's messages hold anything; anything on what a verifier accepts;
any property of the protocol.

-/
import Johnson.Goal.HonestTrace.SeatsApartOfLayout
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.P5J.MgAtAll
import Johnson.IMR.LayoutOkPub
import Johnson.P5J.SeatsNamedC
import Johnson.P5T.GroupsByMake
import Johnson.P5T.KeyBack
import Johnson.P5T.ArrApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes.Road
open Cb.Pv.Tail (Size)
open Meaning (labAt ownerK ownerA nameOf fLay)
open OnBytes.Params (ReqLayout ReqArray)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)
open OnBytes.Maker (WholeD)

/-- **Where the test seatsNamedC accepts at the plan's own numbering, the numbers are apart.** -/
theorem numsApartAt_of_named {X : Model.Verify.Public} {s : ℕ → Size} {layout : ReqLayout}
    {ps₁ ps : List P5T.PSeat} {N : Numbers} (hS : N.sent = (P5T.numbersOf ps₁).sent)
    (sub : ∀ p ∈ ps₁, p ∈ ps)
    (C : P5J.seatsNamedC X s layout (P5T.numOfPlan ps) (P5T.arrOf ps) N = true) :
    NumsApartAt X s layout (P5T.numOfPlan ps) := by
  have key : ∀ m < 25, ∀ a < (s m).NM, ∀ A : ReqArray,
      arrayOf layout (ownerK (labAt X m a)) (nameOf (ownerA (labAt X m a))) = some A →
      ∃ p : P5T.PSeat, (ps.find? fun q => q.j == p.j && q.t == p.t) = some p ∧
        P5T.arrOf ps p.j p.t = P5T.numOfPlan ps (ownerK (labAt X m a)) A.message := by
    intro m hm a ha A hA
    unfold P5J.seatsNamedC at C
    have C2 := List.all_eq_true.1 (List.all_eq_true.1 C m (List.mem_range.2 hm)) a
      (List.mem_range.2 ha)
    simp only [hA] at C2
    unfold namedOnce at C2
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 (beq_iff_eq.1 C2)
    have hxm : x ∈ (N.group m).filter fun x =>
        P5T.arrOf ps x.1 x.2 == P5T.numOfPlan ps (ownerK (labAt X m a)) A.message := by
      rw [hx]
      exact List.mem_singleton.2 rfl
    obtain ⟨hg, he⟩ := List.mem_filter.1 hxm
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 (P5T.group_mem N ps₁ hS m x hg)
    have hin : p₀ ∈ ps := sub p₀ (List.mem_filter.1 hp₀).1
    cases hf : ps.find? (fun q => q.j == p₀.j && q.t == p₀.t) with
    | none =>
      have hn := List.find?_eq_none.1 hf p₀ hin
      simp at hn
    | some p =>
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      refine ⟨p, ?_, ?_⟩
      · rw [hp.1, hp.2]
        exact hf
      · rw [hp.1, hp.2]
        exact beq_iff_eq.1 he
  intro m hm a ha m' hm' a' ha' A A' hA hA' e
  obtain ⟨p, hf, hn⟩ := key m hm a ha A hA
  obtain ⟨p', hf', hn'⟩ := key m' hm' a' ha' A' hA'
  have k1 := P5T.key_of_num ps p hf _ _ hn
  have k2 := P5T.key_of_num ps p' hf' _ _ hn'
  have k3 := P5T.arrOf_key ps p.j p.t p'.j p'.t p p' hf hf' (hn.trans (e.trans hn'.symm))
  have e4 := k1.symm.trans (k3.trans k2)
  exact ⟨congrArg (fun q => q.2.1) e4, congrArg (fun q => q.2.2) e4⟩

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head the seats off the layout are apart.** -/
theorem seatsApart_at_mg (h : P5J.AtMg o Z D r Zp Np cF) :
    SeatsApart (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (fLay (P5J.At.layout Zp) (P5J.At.num Zp)) := by
  have ok : OnBytes.reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true :=
    Meaning.K2.pub_layoutOk h.laid.pub
  have sub : ∀ p ∈ P5J.At.pseats Zp, p ∈ P5J.At.pseatsAll Zp := by
    intro p hp
    unfold P5J.At.pseatsAll P5T.planSeatsAll
    exact List.mem_append_left _ (List.mem_append_left _ hp)
  exact seatsApart_of_layout h.plan.laid ok
    (numsApartAt_of_named (ps₁ := P5J.At.pseats Zp) (ps := P5J.At.pseatsAll Zp)
      (N := P5J.At.N Zp cF) rfl sub h.plan.named)
    (labelsApart_in_scope h.scope h.reads h.pubOne
      (Meaning.follows_of_core h.pubOne (Hd.core_of_scope h.scope h.reads h.pubOne)))

/-- The same under the head with what is handed in. -/
theorem seatsApart_at_head {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x) :
    SeatsApart (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp))
      (fLay (P5J.At.layout Zp) (P5J.At.num Zp)) := seatsApart_at_mg h.toAtMg

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.numsApartAt_of_named
#print axioms OnBytes.HonestTrace.seatsApart_at_mg
#print axioms OnBytes.HonestTrace.seatsApart_at_head
