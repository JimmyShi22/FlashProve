-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanAtTwoRadii.lean: THE FIELD planAt OF LLT25.PlanOk₃ (hP), UNDER THE HEAD, AT THE
STAGES OF THE REQUEST's OWN TEST: OF THE TWELVE CLAUSES THAT THE FIELD seats DOES NOT GIVE ONLY THE
TWO RADII STAY. ONE THEOREM: A JOIN OF THREE FILES: Johnson/P2LawR/PlanAtIndex.lean's planAt_field_i
(over planAt_field_w), with hz := AtMg.sized_at_head
(Johnson/P2LawR/IndexAtHead.lean) and hDI := AtMg.depth_index (Johnson/P2LawR/IndexDepthAtHead.lean)
at the field seats and the member's shape. At every o.
  **AtMg.planAt_two_radii**   the field planAt in its own text, from the head, Written, the named
      tests, the description's planOk and data, the fields seats · oneSeat · mineW · mineI, AND
      hRW · hRI: our radB at W's member and at the index masks' member.
Limits. IT MAY NOT BE SAID HERE THAT planAt IS MET: the two radii are premises of this file;
P5J.AtMg.two_radii (Johnson/P2LawR/TwoRadiiAtHead.lean) has them under the head, at OnBytes.secondHashFunction.
Written, the named tests and the four fields are premises: whether each can be had from the head is
others' to say: not held here. NO MEMBER: that a head can be had is not said. The full size
alone. At the door's asksAt2 alone.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.

-/
import Johnson.P2LawR.PlanAtIndex
import Johnson.P2LawR.IndexDepthAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open LLT25 (vAt mineOf)
open ToldDesc (p14At)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE FIELD planAt UNDER THE HEAD: THE TWO RADII ALONE STAY.** -/
theorem AtMg.planAt_two_radii (h : AtMg o Z D r Zp Np cF) {Xi Xi' : Type} (G : FileDescription Xi)
    (G' : FileDescription Xi') {x : LinSized} (hx : realSized = some (x, codesFull2))
    (hw : Written Zp x) (hT : Sh.Tests (Sh.planAt Zp Np G)) (file : String) (D' : WholeD)
    (hp : G'.planOk = true) (hd : G'.data file = .ok D') (key : ℕ → ℕ) (ft : ℕ)
    (ms₁ : List Mem) (N₁ : Numbers) (a b : ℕ × ℕ)
    (hS : SeatsFit (p14At Zp).codes G' (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)))
    (h1 : ∀ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)), ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)), seatOf x = seatOf y → x = y)
    (hW : ∃ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)), seatOf x = (vAt Zp N₁).w ∧
      (x.1.l.get x.2).1 = (vAt Zp N₁).wShape)
    (hI : ∃ x ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)), seatOf x = (vAt Zp N₁).index ∧
      (x.1.l.get x.2).1 = (vAt Zp N₁).indexShape)
    (hRW : ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.w)).all
        fun y => radB (p14At Zp).codes H2K.Member.rWFull st y) = true)
    (hRI : ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.index)).all
        fun y => radB (p14At Zp).codes H2K.Member.rWFull st y) = true) :
    ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Zp Np G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
        (Sh.layO (Sh.planAt Zp Np G)) a b)), ∀ st rest,
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      LLT25.PlanAt (p14At Zp).codes G' (frameAt D' (allOf D') key ft) H2K.Member.rWFull st y := by
  refine P2Law.PlanIndex.planAt_field_i Zp Np G G' hx hw h.sized_at_head h.laid.places hT file D'
    hp hd key ft ms₁ N₁ a b _ hS h1 hW hI hRW hRI ?_
  intro st rest hst y hy1 es
  have hboth : y ∈ ms₁.filter fun y =>
      decide (y.1.seat y.2 = N₁.w) || decide (y.1.seat y.2 = N₁.index) :=
    List.mem_filter.2 ⟨hy1, by rw [decide_eq_true es, Bool.or_true]⟩
  have hm := List.mem_append_left ((Sh.ms (Sh.planAt Zp Np G)).filter fun x =>
    decide (x.1.seat x.2 = (numbersSh (Sh.t₁ (Sh.planAt Zp Np G)) (Sh.layU (Sh.planAt Zp Np G))
      (Sh.layO (Sh.planAt Zp Np G)) a b).tenant .oOmega)) hboth
  exact h.depth_index G' y (hS y hm) (P2Law.PlanIndex.shape_at_I Zp N₁ _ h1 hI y hm es) st rest hst

end P5J

#print axioms P5J.AtMg.planAt_two_radii
