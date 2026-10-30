-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/HeadAtConst.lean: the code switch's law at the closed constant
(P5J.mgAtAll): TWO OF K2Owes' FIELDS (Johnson/Top/H0/K2Ties/T5.lean): headBack AND headBears, AT THE
CONSTANT's OWN headPart.
  headBack_at    where Left (K2Ties/Left.lean) holds between two states, the constant's headPart
                 goes back, at any two strings: ONE CALL: headPart_atAll_reply
                 (Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean): of the state headPart reads the heard
                 reply alone, and Left keeps what is put out. The premise on the cells is not spent.
                 No premise beside the head
  hdis_written   at the written numbers: no tenant of the head's group (24) is among the tenants
                 that any of the 25 switches keeps: by decide +kernel. (The finish's switch keeps
                 none.)
  hdis_rejects   a negative test, by the kernel: group 23 against the tenants that the switch out of
                 it keeps
  headBears_at   the constant's headPart bears a turn of the pads that a switch lays:
                 Came.headPartK6_bears (Johnson/Desc/Kinds/Law/HeadPartsBear.lean) at the constant's
                 letters, ITS PREMISE hdis («the pads that turn lie off group 24») PAID by
                 hdis_written along WrittenAt.lean's AtWritten (group · keptOf). At a place pl whose
                 switch leads out of one of the 25 groups (hm)
UNDER WHAT. headBack_at: the head and nothing else, at every letter o for the second hash function.
headBears_at: the head, AtWritten (in scope · laid · the pin madePinnedAt) and hm.
LIMITS. The full size alone (headBears_at). A member of the head is proved at storedPublicFiles and zGap alone
(at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.Desc.Kinds.Law.HeadCutsAtAll
import Johnson.Desc.Kinds.Law.HeadPartsBear
import Johnson.Top.H0.K2Ties.Left
import Johnson.Top.H0.K2Ties.Constr
import Johnson.Top.H0.K2Ties.WrittenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Kinds.Head.Law
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open P5T (N0Full)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **headBack AT THE CONSTANT.** -/
theorem headBack_at (h : AtMgA o Z D r Zp Np cF x) :
    ∀ (z : ProofFile.InstPub) q i (s s' : VerifiableInference.Desc.First.S) (y y' : Strs) w,
      Left s s' → y'.cell = y.cell → h.𝔇.headPart q i (z, s') y' w →
        h.𝔇.headPart q i (z, s) y w :=
  fun z q i s s' y y' w L _ hp =>
    (headPart_atAll_reply h q i z s s' y y' w (by rw [L.out])) ▸ hp

set_option maxRecDepth 1000000 in
/-- **No tenant of the head's group is among the kept tenants of any switch**, at the written
numbers. -/
theorem hdis_written :
    ((List.range 25).all fun m =>
      (N0Full.group 24).all fun t => !(N0Full.keptOf m).contains t) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: group 23 against the tenants that the switch out of it keeps. -/
theorem hdis_rejects :
    ((N0Full.group 23).all fun t => !(N0Full.keptOf 23).contains t) = false := by decide +kernel

/-- **headBears AT THE CONSTANT**, at a place whose switch leads out of one of the 25 groups. -/
theorem headBears_at (h : AtMgA o Z D r Zp Np cF x) (A : AtWritten Zp cF) (pl : Place)
    (hm : pl.link.getD P5J.fullLinks.length - 1 < 25) :
    HeadBears h.𝔇.headPart (laysPads h.𝔇.N P5J.fullLinks pl) := by
  intro p i a y w w' hT hp
  have hdis : ∀ t ∈ (P5J.At.N Zp cF).group 24,
      t ∉ laysPads (P5J.At.N Zp cF) P5J.fullLinks pl := by
    intro t ht hl
    rw [A.group 24] at ht
    unfold laysPads at hl
    split at hl
    · simp at hl
    · split at hl
      · rw [A.keptOf] at hl
        have h1 := List.all_eq_true.1
          (List.all_eq_true.1 hdis_written _ (List.mem_range.2 hm)) t ht
        simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h1
        exact h1 hl
      · simp at hl
  exact Came.headPartK6_bears (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
    (P5J.At.N Zp cF) (_root_.Meaning.sizesOf (P5J.At.X Zp))
    (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)
    (plAt (P5J.At.num Zp 24 0) 0) (P5J.At.tabH x) P5J.At.put P5J.tokVOf _ _ h.plan.hN h.plan.hG
    P5J.tokHOf Came.putReq_keeps (InScope.ok_in_scope h.scope h.reads h.pubOne _) _ hdis w w' hT
    p i a y hp

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.headBears_at

#print axioms VerifiableInference.Desc.First.K2Ties.headBack_at
#print axioms VerifiableInference.Desc.First.K2Ties.hdis_written
#print axioms VerifiableInference.Desc.First.K2Ties.hdis_rejects
