-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtMgRAtHead.lean: THE HEAD WITH THE FACTS ON EVERY REACHED STATE (AtMgR, Johnson/P5J/AtMgR.lean) HAS A MEMBER UNDER THE HEAD OF THE CLOSED CONSTANT (AtMgA, Johnson/P5J/MgAtAll.lean) AND ONE NAMED TEST. Four theorems. A joining: by calls alone: it adds no strength of its own.
  Why. A kind's law at the head asks a member of AtMgR at its own "reached": the one premise there that is no closed test.
  madeRow_at_head     under AtMg: the row on the made plan accepts (PlanWritten.madeRow Zp = true): pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean: where the value is laid, the pin on the made plan accepts) · pinnedAt_row and key_in_scope_pure (in scope the key is the full size's).
  atMgR_at_head       STATED ONCE, GENERAL IN Rch: at every "reached" that gives the bare RchAt (F0T …): ∃ L, AtMgR … Rch (fun a => a.1) L. BY the join of the facts (atMgR_madeRow, Johnson/P5J/FoldJ3Whole.lean); L by the head's own field opts.laid.
  atMgR_rch_at_head   at the tower's h.toAtMg.rch.
  atMgR_rchU_at_head  at "reached and no mark".
ONE PREMISE STAYS IN FRONT, BY NAME: hs : FillP1.startB Zp ‹the planner's first chain's oracle messages' shapes› ‹the index masks' number› = true: a closed test on the public part; it stands in no head but AtMgR's own field start; evaluated true at both sizes, negative tests rejecting (runs, no theorem).
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. At Rch := never every fact is free: the weight lies in the meant "reached". Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FoldJ3Whole
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the row on the made plan accepts.** -/
theorem madeRow_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    VerifiableInference.PlanWritten.madeRow Zp = true := by
  have hp := (pins_of_laid h.scope h.laid).1
  rw [VerifiableInference.PlanWritten.pinnedAt_row,
    if_pos (VerifiableInference.PlanWritten.key_in_scope_pure h.scope h.laid.pub)] at hp
  exact hp

/-- **THE HEAD WITH THE FACTS ON EVERY REACHED STATE, FROM THE HEAD: GENERAL IN "REACHED".** -/
theorem atMgR_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    {Str : Type}
    (Rch : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str →
      Prop)
    (hR : ∀ k a, Rch k a → RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L := by
  obtain ⟨L, hl⟩ := At.laid_some Zp h.opts.laid
  exact ⟨L, atMgR_madeRow h.toAtMg Rch hR hl hs (madeRow_at_head h.toAtMg)⟩

/-- At the tower's "reached". -/
theorem atMgR_rch_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L :=
  atMgR_at_head h hs h.toAtMg.rch fun _ _ hr => hr.1

/-- At "reached and no mark". -/
theorem atMgR_rchU_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true) :
    ∃ L, AtMgR OnBytes.secondHashFunction Z D r Zp Np cF
      (fun k a => h.toAtMg.rch k a ∧ ¬ a.1.2.failed ≠ none) (fun a => a.1) L :=
  atMgR_at_head h hs _ fun _ _ hr => hr.1.1

end P5J

#print axioms P5J.madeRow_at_head
#print axioms P5J.atMgR_at_head
#print axioms P5J.atMgR_rch_at_head
#print axioms P5J.atMgR_rchU_at_head
