-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FrontAtFK.lean: It stands on Johnson/RunOne/Sound/.
THE PROMISE IN FRONT OF THE FIRST LINK, AT THE KEY FILE'S OWN
DESCRIPTION: the two steps of FrontSteps.lean at the blocks 0 and 1 of the first chain's own flat
list, from the description's own start; and, at every three public files in the goals' scope, from
the yes of the key file's piece at the fixed digest, with no premise on public numbers left.

Main names:
  fk_step₀: the yes of block 0, from the description's start, gives Half.
  fk_step₁: from Half, the yes of block 1 gives Front.
  fk_border₂: Front gives what the row at border 2 promises of the record: PromL 0, no rows, no
    claims on keys.
  front_at_fixed: THE THREE, IN SCOPE, FROM Key.keyDataAndDecisionAtFixedDigest's YES.

Object: (FK X N P).start₁ and the blocks 0 and 1 of (FK X N P).first.blocksInOrder (fk_idx_at, fk_msg_at:
Johnson/RunOne/Sound/KeyMapAtFK.lean).
User: front_at_o (ReadAtO.lean). The three are what a law on the seats 0 and 1 needs in order to
hand the condition of the row at border 2 on (rowJ at lookup 0, JoinKeyD.lean: its promise and its
two lengths; its fourth part, the decoder's condition, is not touched here).
Letters: Ex, what else the promise keeps: it must hold of the record behind block 1.

Limits. The steps ask that the block is shown two rounds. One size in scope. Nothing on soundness.

-/
import Johnson.RunOne.Law.FrontSteps
import Johnson.RunOne.Law.AtFreeCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FrontAtFK
open OnBytes OnBytes.Params OnBytes.Model.Verify
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source sourceClauses)
open Johnson.RunOne.Sound (FK fk_idx_at fk_msg_at)
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.FrontSteps

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime

/-- The index-mask message counts an answer: the clause "idx" of the test on the file. -/
theorem fk_idx_answers (h : (FK X N P).planOk = true) : X.Y.k.oneTime.indexMasks.shape.answers ≠ 0
    := by
  have e := List.all_eq_true.1 (fk_clauses X N P h).1
    ("idx", X.Y.k.oneTime.indexMasks.shape.mainRows == 0 && X.Y.k.oneTime.indexMasks.shape.maskRows
        != 0 &&
        decide (1 ≤ X.Y.k.oneTime.indexMasks.shape.answers) &&
        decide (X.Y.k.oneTime.indexMasks.shape.maskCode < X.Y.k.oneTime.codes.mask.size))
    (by simp [sourceClauses])
  simp only [Bool.and_eq_true, decide_eq_true_eq] at e
  have := e.1.2
  omega

/-- **Block 0, from the description's start.** -/
theorem fk_step₀ (hp : (FK X N P).planOk = true) (b : Block FirstState Claim)
    (hb : (FK X N P).first.blocksInOrder[0]? = some b) (q : (FK X N P).XiPub) {t : FirstState}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : b.decide ((FK X N P).start₁ q) [r₁, r₂] gs = .ok t) : Half one t := by
  obtain ⟨g, hg⟩ := fk_idx_at X N P
  obtain rfl := Option.some.inj (hg.symm.trans hb)
  exact idx_step (fk_idx_answers X N P hp) h

/-- **Block 1.** -/
theorem fk_step₁ (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (b : Block FirstState Claim)
    (hb : (FK X N P).first.blocksInOrder[1]? = some b) {s t : FirstState} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hs : Half one s)
    (h : b.decide s [r₁, r₂] gs = .ok t) : Front one t := by
  obtain ⟨g, hg⟩ := fk_msg_at X N P
  obtain rfl := Option.some.inj (hg.symm.trans hb)
  exact msg_step hs ha h

/-- **What the row at border 2 promises of the record.** -/
theorem fk_border₂ (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
        X.Y.k.oneTime.indexMasks.shape)
    {Ex : FirstState → Prop} {t : FirstState} (h : Front one t) (hE : Ex t) :
    t.base.rows.length = 0 ∧ t.base.keys.length = 0 ∧
      PromL one X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof one) 0
        X.Y.k.oneTime.ranges.lookups.length (ledOf X.Y.k.oneTime.codes
            X.Y.k.oneTime.ranges.message.shape)
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) Ex 0 t := by
  refine ⟨?_, ?_, front_promL h (fk_admitted X N P hp) hR hE⟩
  · rw [h.base]
    rfl
  · rw [h.base]
    rfl

/-- The lookups' own message counts an answer, at the written sizes of a key of full size. -/
theorem answers_full : Lk6.AtPlan.keyFull.ranges.x.message.shape.answers ≠ 0 := by decide +kernel

/-- **THE PROMISE IN FRONT OF THE FIRST LINK, IN SCOPE, FROM THE YES OF THE KEY FILE'S PIECE AT THE
FIXED DIGEST.** -/
theorem front_at_fixed {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {D : OnBytes.Maker.WholeD}
    {r : VerifiableInference.Desc.Key.KeyRun}
    (h : VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest Z Zp.lay = .ok (D, r)) :
    ∃ X N P, (FK X N P).planOk = true ∧ (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧
      (∀ (b : Block FirstState Claim) (q : (FK X N P).XiPub) (t : FirstState) (r₁ r₂ : Fmt.RoundView)
        (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[0]? = some b →
        b.decide ((FK X N P).start₁ q) [r₁, r₂] gs = .ok t → Half X.Y.k.oneTime t) ∧
      (∀ (b : Block FirstState Claim) (s t : FirstState) (r₁ r₂ : Fmt.RoundView)
        (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[1]? = some b →
        Half X.Y.k.oneTime s → b.decide s [r₁, r₂] gs = .ok t → Front X.Y.k.oneTime t) ∧
      ∀ (Ex : FirstState → Prop) (t : FirstState), Front X.Y.k.oneTime t → Ex t →
        t.base.rows.length = 0 ∧ t.base.keys.length = 0 ∧
          PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
            (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
            (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
            (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) Ex 0 t := by
  obtain ⟨m, X, N, P, hm, hX, hp, hD, hr⟩ := Johnson.RunOne.Law.KeyInScope.laid_parts h
  have hp' : (FK X N P).planOk = true := hp
  obtain ⟨-, -, hR⟩ := seat_in_scope (N := N) (P := P) hZ hP hm hX hp'
  have ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0 := by
    obtain ⟨v, hv⟩ := Lk6.AtPlan.inScope_policy hZ
    rw [hv] at hP
    have hk := key_at_chains hP (madeAt_parts hm).2.1
    rw [(five_at hm hX hp').2.1, hk]
    exact answers_full
  exact ⟨X, N, P, hp, hD, hr, fun b q t r₁ r₂ gs hb hd => fk_step₀ X N P hp' b hb q hd,
    fun b s t r₁ r₂ gs hb hs hd => fk_step₁ X N P ha b hb hs hd,
    fun Ex t hf hE => fk_border₂ X N P hp' hR hf hE⟩

end Johnson.RunOne.Law.FrontAtFK

#print axioms Johnson.RunOne.Law.FrontAtFK.fk_idx_answers
#print axioms Johnson.RunOne.Law.FrontAtFK.fk_step₀
#print axioms Johnson.RunOne.Law.FrontAtFK.fk_step₁
#print axioms Johnson.RunOne.Law.FrontAtFK.fk_border₂
#print axioms Johnson.RunOne.Law.FrontAtFK.answers_full
#print axioms Johnson.RunOne.Law.FrontAtFK.front_at_fixed
