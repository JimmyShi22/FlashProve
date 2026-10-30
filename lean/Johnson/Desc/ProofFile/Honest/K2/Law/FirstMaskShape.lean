-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FirstMaskShape.lean: the kind "the code switch" (K2): A PUBLIC
TIE FOR THE ASSEMBLY UNDER THE HEAD, AT THE FIRST SEGMENT: THE SHAPE OF ITS FOLD's FRESH MASK.
Honest/K2/Law/FirstShapes.lean and ShapesAtFront.lean have the fresh mask's shape at a link into
which a switch leads: the shape of the last message of that switch's sending. The first segment's
fresh mask has a sender of the kind K1: here the like, against the segment's own public data: the
last message of its first sending. One definition (a test on public data); four theorems. Public
data alone: no coin, no witness, no Script.

  `mask0ShapeTie` THE TEST: the written list of the chain's messages' shapes has, at the written
                    plan's number of link 0's fresh mask, the shape of the last message of the
                    segment's first sending
  `mask0ShapeTieW, mask0ShapeTieW_can_fail` it accepts at the first written segment; at the number
                    in front it rejects, and a shape stands there. By Lean's kernel
  `mask0_shape_at_head` UNDER THE HEAD: so at the chain's own list and the plan's own number
  `mask0_shape_getD` as the carried claim's premises write it: at a statement with the oracle
                    messages of a state reached without a mark, where the number is stated

Limits. The full size and the format's second hash function alone. That the last message of the segment's
first sending is a message of K1's opening is not said here: Honest/K2/Law/K1SendersTies.lean
(`mask_tie_at_head`) says it. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ShapesAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.K1SendersTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (shape_at_no)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The test**, on public data. -/
def mask0ShapeTie (Sg : SegmentPub) : Bool :=
  VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
      VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull 0]? ==
    (Sg.sent.headD #[]).back?.map (·.shape)

set_option maxRecDepth 1000000 in
/-- **It accepts at the first written segment**, whose first sending has a last message. By Lean's
kernel. -/
theorem mask0ShapeTieW :
    ((segsW.take 1).all fun Sg => mask0ShapeTie Sg && !(Sg.sent.headD #[]).isEmpty) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can fail**: at the number in front it rejects: there the list holds a shape, and it is
another. -/
theorem mask0ShapeTieW_can_fail :
    ((segsW.take 1).all fun Sg =>
      (VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
          VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull 0 - 1]?).isSome &&
        !(VerifiableInference.Desc.First.K2Hands.MList[VerifiableInference.Desc.First.Close.maskNo
            VerifiableInference.Desc.First.Close.seatsPlanW P5T.psFull 0 - 1]? ==
          (Sg.sent.headD #[]).back?.map (·.shape))) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD**: the chain's list of messages' shapes has, at the plan's own number of link
0's fresh mask, the shape of the last message of the first segment's first sending. -/
theorem mask0_shape_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) :
    (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)[
        VerifiableInference.Desc.First.Close.maskNo
        (P5J.At.seats Zp) (P5J.At.pseats Zp) 0]? =
      some ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape := by
  rw [segments_at_head h O] at hS
  have k := List.all_eq_true.1 mask0ShapeTieW Sg (mem_take_one hS)
  rw [Bool.and_eq_true] at k
  obtain ⟨k1, k2⟩ := k
  have e3 : VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1 =
      VerifiableInference.Desc.First.K2Hands.MList := by
    rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1]
    exact VerifiableInference.Desc.First.K2Hands.MW_eq
  have hne : 0 < (Sg.sent.headD #[]).size := by
    rcases Nat.eq_zero_or_pos (Sg.sent.headD #[]).size with e | e
    · rw [Array.isEmpty_iff_size_eq_zero.2 e] at k2
      cases k2
    · exact e
  rw [e3, h.maskNo_is 0, eq_of_beq k1, Array.back?, Array.getElem?_eq_getElem (by omega),
    Option.map_some, Array.getD, dif_pos (by omega)]
  rfl

/-- **THE FIRST SEGMENT's FRESH MASK's SHAPE, AS THE CARRIED CLAIM's PREMISES WRITE IT.** -/
theorem mask0_shape_getD (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {k : Nat}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    (ho : VerifiableInference.Desc.First.Close.maskNo (P5J.At.seats Zp) (P5J.At.pseats Zp) 0 <
      a.1.2.st.oracles.size)
    {St : OnBytes.Statement} (hSt : St.oracles = a.1.2.st.oracles) :
    (St.oracles.getD (VerifiableInference.Desc.First.Close.maskNo (P5J.At.seats Zp)
      (P5J.At.pseats Zp) 0) default).shape =
      ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape := by
  rw [hSt]
  exact getD_shape_of_map (shape_at_no (h.fold_full.msgShapes k a hr hu) ho
    (mask0_shape_at_head h.toAtMg O hS))

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.mask0ShapeTie
#print axioms ProofFile.Honest.K2.Law.mask0ShapeTieW
#print axioms ProofFile.Honest.K2.Law.mask0ShapeTieW_can_fail
#print axioms ProofFile.Honest.K2.Law.mask0_shape_at_head
#print axioms ProofFile.Honest.K2.Law.mask0_shape_getD
