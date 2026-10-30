-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySamples.lean: THEOREMS. **TWO PREMISES OF THE TABLES' FILES' ROWS 1.0 · 1.1 · 1.17, PAID**: one.given.plan.samples = 1 in scope · planOkOwn at the three sendings' places, off the description's test on the plan.
OBJECT. X.Y.k.oneTime.given.plan.samples (which Key.groundParOf lays into the three sendings' numbers as gp.samples: Johnson/Desc/Key/One.lean:70) · K1.planOkOwn at parIdx X | parMsg X | parW X msg (KeySendAtDesc.lean). USER. The tables' files' r1_17 and its kin. LETTERS. X · N · P;
Zp · Z · cfg · m in the scope's form.
  samples_is          (Key.descriptionFromSource X N P).planOk = true → X.Y.k.oneTime.given.plan.samples = X.Y.k.oneTime.ranges.message.shape.answers: fileOk's clause «the lookups' own message's answers are the plan's samples» (Johnson/Desc/Key/FileOk.lean:72-74, third of shapeClauses)
  answers_full        keyFull.ranges.x.message.shape.answers = 1: by the kernel · answers_not: a control: it is not 0, not 2
  samples_of_ranges   so, where the ranges are the written value's (the second of the five equations): samples = 1
  samples_in_scope    **in scope: X.Y.k.oneTime.given.plan.samples = 1** (five_in_scope, called)
  planOwn_idx | planOwn_msg | planOwn_w     **(Key.descriptionFromSource X N P).planOk = true → K1.planOkOwn at the place**
NOTE. The laws on the sendings (SendAsks, KeySendAtDesc.lean · asksB, KeySendAsksB.lean) do not read gp.samples: asksB_reads: codes · parts · work alone; Par.seeds is read off the parts' shapes. What is not claimed. Nothing on soundness.

-/
import Johnson.RunOne.KeySendScope
import Johnson.RunOne.KeySendAtDesc
import Johnson.RunOne.KeyPayD
import Johnson.Desc.RunLaws

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (planOkOwn)
open Lk6.AtPlan (keyFull)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **The plan's samples are the lookups' own message's answers**: a clause of the description's fileOk. -/
theorem samples_is (hp : (descriptionFromSource X N P).planOk = true) : X.Y.k.oneTime.given.plan.samples = X.Y.k.oneTime.ranges.message.shape.answers := by
  have Q := ((descriptionFromSource X N P).planOk_ok).1 hp
  have h := (Johnson.RunOne.KeyPay.fileOkD_of Q.fileOk).more
    ("the lookups' own message's answers are the plan's samples", X.Y.k.oneTime.ranges.message.shape.answers == X.Y.k.oneTime.given.plan.samples) (by simp [shapeClauses])
  exact (beq_iff_eq.1 h).symm

theorem answers_full : keyFull.ranges.x.message.shape.answers = 1 := by decide +kernel

/-- A control: the same term is not 0 and not 2. -/
theorem answers_not : keyFull.ranges.x.message.shape.answers ≠ 0 ∧ keyFull.ranges.x.message.shape.answers ≠ 2 := by decide +kernel

theorem samples_of_ranges (hp : (descriptionFromSource X N P).planOk = true) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) : X.Y.k.oneTime.given.plan.samples = 1 := by
  rw [samples_is hp, hr]
  exact answers_full

/-- **In scope the plan's samples are 1.** -/
theorem samples_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (descriptionFromSource X N P).planOk = true) : X.Y.k.oneTime.given.plan.samples = 1 :=
  samples_of_ranges hp (Johnson.RunOne.Law.KeyInScope.five_in_scope hZ hP hm hX hp).2.1

/-- A bared block's test on the plan holds the block's own. -/
theorem plan_of_bare {S Cl : Type} {b : Block S Cl} (h : (bareOf b).planOk = true) : b.planOk = true := by
  have h' : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := h
  exact (Bool.and_eq_true _ _ ▸ h').1

/-- **planOkOwn at the three places, off the description's test on the plan.** -/
theorem planOwn_idx (hp : (descriptionFromSource X N P).planOk = true) : planOkOwn (parIdx X) = true :=
  planOwn_idxAt _ _ _ (plan_of_bare ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? (idx_at (X := X) (N := N) (P := P)))).1)

theorem planOwn_msg (hp : (descriptionFromSource X N P).planOk = true) : planOkOwn (parMsg X) = true :=
  planOwn_msgAt _ _ _ (plan_of_bare ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? (msg_at (X := X) (N := N) (P := P)))).1)

theorem planOwn_w (hp : (descriptionFromSource X N P).planOk = true) {msg : Array OracleNotice} (hm : linMessageW X.Y.k.oneTime.lin = some msg) : planOkOwn (parW X msg) = true := by
  obtain ⟨bw, hb⟩ : ∃ bw : Block FirstState Claim, sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw := by
    unfold sendW
    rw [hm]
    exact ⟨_, rfl⟩
  exact planOwn_wAt hm hb (plan_of_bare ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? (w_at (X := X) (N := N) (P := P) hb))).1)

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.planOwn_w
#print axioms Johnson.RunOne.KeySendGood.samples_is
#print axioms Johnson.RunOne.KeySendGood.answers_full
#print axioms Johnson.RunOne.KeySendGood.answers_not
#print axioms Johnson.RunOne.KeySendGood.samples_of_ranges
#print axioms Johnson.RunOne.KeySendGood.samples_in_scope
#print axioms Johnson.RunOne.KeySendGood.planOwn_idx
#print axioms Johnson.RunOne.KeySendGood.planOwn_msg
