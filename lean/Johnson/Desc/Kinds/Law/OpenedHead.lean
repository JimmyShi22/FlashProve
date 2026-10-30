-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedHead.lean: "OPENED AT THE TRUTH", THE OUTPUT HEAD's OWN HALF: the converse of the reading that the head's
laws make. Where the cells are honest and the hidden scalars that the head's sumcheck left ARE THE TRUE ONES,
the six forms of the block's runs "policy" and "logits" are worth 0 at the hidden scalars and the sent reads,
and the claim on the weights is true. No chance in it. FOR A MEMBER OF K06_law: an honest tape plugs in at
the letters HeadTruth.claimed | end0 | end1 | ok1 | row.
  HeadTruth   WHAT IS ASKED OF WHAT WAS HEARD, at a ledger G, a mask row and sent entries, BY LETTERS:
       claimed   2^lPd times the claimed sum's hidden scalar is the true sum (trueSum c);
       end0      the first end value's hidden scalar is act's table at the challenges (rH, rs);
       end1      the second's is UH's table there; ok1: its variable's constant is written canonically (at a
                 hearing's return the variable is a bare slot: Law/CoveredAt.lean's heard_slots: constant 0);
       row       the sumcheck's own form, on the end values as shown, is worth 0.
  HonestHead  WHAT IS ASKED OF THE CELLS: the two guests are 0 at every position's corner (CornerGuests); the two
       plain sums are 0 (meanAt, countAt). All three are fields or consequences of HeadLaw.lean's CellRel.
  opened_head     under these, the tests on the request, WeightsOk, |zt| = lt and true reads:
       WeightTrue ∧ every form of policy is worth 0 ∧ every form of logitForms is worth 0.
WHAT IT IS NOT. Nothing on soundness. THAT ANY TAPE MEETS HeadTruth IS NOT SHOWN HERE (the honest hearing is other
files' to show). That honest cells exist is not shown here. The normalization's 29 forms: not here. "join": not here.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Clamp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Heard] [Reads]

/-- The hidden scalars that the head's sumcheck left are the true ones, and its own form is worth 0. -/
structure HeadTruth (c : Cells) (G : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) : Prop where
  claimed : (2 ^ lPd : E) * atWorld G mask ent logits.claimed.var = trueSum c
  end0 : rd (atWorld G mask ent (logits.end_ 0).var) = (Finset.range T).sum fun t =>
    (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fA c t k
  end1 : rd (atWorld G mask ent (logits.end_ 1).var) = (Finset.range T).sum fun t =>
    (Finset.range d).sum fun k => rd (eq rH t) * rd (eq rs k) * fU c t k
  ok1 : okE (logits.end_ 1).var.const = true
  row : atWorld G mask ent (logits.left ((logits.end_ 0).shown * (logits.end_ 1).shown)) = 0

omit [FinalNorm.In] [In] [Heard] [Reads] in
/-- The cells are honest, as far as the head's own six forms ask. -/
structure HonestHead (c : Cells) : Prop where
  guests : CornerGuests c
  mean : meanAt c = 0
  count : countAt c = 0

/-- **OPENED AT THE TRUTH: THE HEAD's OWN HALF.** -/
theorem opened_head (c : Cells) (G : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E)
    (hreq : Request.ok = true) (hy : y < V) (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt)
    (hreads : TrueReads c G mask ent) (hc : HonestHead c) (hh : HeadTruth c G mask ent) :
    WeightTrue c G mask ent ∧ (∀ f, f ∈ policy → atWorld G mask ent f = 0) ∧
      ∀ f, f ∈ logitForms → atWorld G mask ent f = 0 := by
  obtain ⟨_, g2, g3, g4, g5⟩ := k06Glue c G mask ent hreq hy hw hzt hreads hh.claimed
  obtain ⟨c1, c2, _⟩ := corners c ptOf hreq hy hzt
  refine ⟨?_, ?_, ?_⟩
  · -- the claim on the weights
    unfold WeightTrue
    apply eq_of_rd (okE_atWorld G mask ent _ hh.ok1) (okE_sumTo _ _)
    rw [weights_eq c hreq hy]
    exact hh.end1
  · intro f hf
    simp only [policy, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · rw [g4]; exact hc.mean
    · rw [g5]; exact hc.count
    · rw [g2]
      apply zero_of_rd (okE_clipAt c ptOf)
      rw [c1]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [(hc.guests t (Finset.mem_range.mp ht)).1, rd_zero, mul_zero]
    · rw [g3]
      apply zero_of_rd (okE_tableAt c ptOf)
      rw [c2]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [(hc.guests t (Finset.mem_range.mp ht)).2, rd_zero, mul_zero]
  · intro f hf
    rw [logitForms_clamp c] at hf
    have hT := trueAll_clamp c hreads
    have hf' : f = logits.left ((logits.end_ 0).shown * (logits.end_ 1).shown) ∨
        f = (letI := clamp c; (logits.end_ 0).var -
          sumTo d fun k => eq rs k • FinalNorm.actAt (entry .actAtLogits) k) := by
      simpa [logitForms] using hf
    rcases hf' with rfl | rfl
    · exact hh.row
    · apply zero_of_rd (okE_atWorld G mask ent _ (okE_addMul _ _ _))
      rw [rd_atWorld]
      have he : ∀ r i, vW (worldE G mask ent) ((clamp c).entry r i) = rd (readAt c r.of i) :=
        fun r i => by rw [← rd_atWorld]; exact congrArg rd (hT r i)
      have hv := @actForm_valueW _ _ _ _ _ _ _ (clamp c) c (worldE G mask ent) he
      have h0 := hh.end0
      rw [rd_atWorld] at h0
      exact hv.trans (by rw [h0, sub_self])

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.opened_head
