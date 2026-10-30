-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/WalkAtFK.lean: It stands on Johnson/RunOne/Sound/.
THE RECORD'S HALF OF THE LINKS' ROWS ALONG THE KEY FILE'S OWN FIRST CHAIN,
FROM ITS START: block by block, each step from that block's yes at rounds that fit: the two sendings
(FrontSteps.lean) and the six blocks of each lookup's link (Walk.lean), at the terms of
LinksAtO.lean: the two ledgers as the sendings open them, the index-mask message's number 0, nothing
else kept.

Main names:
  RecK X l j s: RecL at these terms.
  RecAt X k s: at border k: 0: the chain's start · 1: Half · 2 + 6 l + j: RecK X l j.
  fk_walk: THE STEP: RecAt X k s, block k's yes from s to s' at rounds that fit ⊢
    RecAt X (k + 1) s', for every k below 2 + 6 · (the number of lookups).

Object: the blocks 0 … 1 + 6 · (the number of lookups) of (FK X N P).first.blocksInOrder.
User: RecOfHist.lean: a record that was reached by
the blocks' steps from the start has RecAt, by induction over fk_walk.
Letters: X, N, P. Premises: the description's tests on the plan · RoomFor · the lookups' own message
counts an answer (both in scope: AllAtO.lean).

Limits. Nothing on the decoder's condition or on the rows' relations. Nothing on soundness.

-/
import Johnson.RunOne.Law.Walk
import Johnson.RunOne.Law.AllAtO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.WalkAtFK
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block roundsFit noDigest)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source chainStart)
open Johnson.RunOne.Sound (FK H₁ fk_idx_at fk_msg_at fk_link_at)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.FrontAtFK
open Johnson.RunOne.Law.AllAtO
open Johnson.RunOne.Law.Walk

variable (X : Source)

/-- RecL at the key file's own terms. -/
abbrev RecK (l j : ℕ) (s : FirstState) : Prop :=
  RecL X.Y.k.oneTime X.set X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
      X.Y.k.oneTime)
    (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime))
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape))
    (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
        X.Y.k.oneTime))
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape)) 0
    (PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) fun _ => True) l j s

/-- **The record's half at border k of the first chain.** -/
def RecAt (k : ℕ) (s : FirstState) : Prop :=
  if k = 0 then s = chainStart X.Y.k.oneTime.codes {}
  else if k = 1 then Half X.Y.k.oneTime s
  else RecK X ((k - 2) / 6) ((k - 2) % 6) s

theorem recAt_link (l j : ℕ) (hj : j < 6) (s : FirstState) :
    RecAt X (2 + (6 * l + j)) s ↔ RecK X l j s := by
  unfold RecAt
  rw [if_neg (by omega), if_neg (by omega)]
  have e1 : (2 + (6 * l + j) - 2) / 6 = l := by omega
  have e2 : (2 + (6 * l + j) - 2) % 6 = j := by omega
  rw [e1, e2]

variable {X} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **THE STEP.** -/
theorem fk_walk {Fr : Frame} (y : Fr.E.Str) (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (k : ℕ)
    (hk : k < 2 + 6 * X.Y.k.oneTime.ranges.lookups.length) (b : Block FirstState Claim)
    (hb : (FK X N P).first.blocksInOrder[k]? = some b) (s s' : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hf : roundsFit b.rounds rs = true)
    (hr : RecAt X k s) (hy : b.decide s (rs.map noDigest) gs = .ok s') : RecAt X (k + 1) s' := by
  have hW := fk_admitted X N P hp
  have hid : X.Y.k.oneTime.ranges.messageId ≠ 0 := by
    rw [fk_messageId X N P hp]
    exact Nat.one_ne_zero
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · rcases Nat.lt_or_ge k 1 with h1 | h1
    · obtain rfl : k = 0 := by omega
      obtain ⟨r₁, r₂, rfl⟩ := fk_two₀ X N P b hb hf
      obtain ⟨g, hg⟩ := fk_idx_at X N P
      obtain rfl := Option.some.inj (hg.symm.trans hb)
      have hs : s = chainStart X.Y.k.oneTime.codes {} := hr
      subst hs
      exact idx_step (fk_idx_answers X N P hp) hy
    · obtain rfl : k = 1 := by omega
      obtain ⟨r₁, r₂, rfl⟩ := fk_two₁ X N P b hb hf
      have hF := fk_step₁ X N P ha b hb (show Half X.Y.k.oneTime s from hr) hy
      obtain ⟨a1, a2, a3⟩ := fk_border₂ X N P hp hR (Ex := fun _ => True) hF trivial
      exact (recAt_link X 0 0 (by omega) s').2 ⟨a1, a2, a3⟩
  · obtain ⟨l, j, hj, rfl⟩ : ∃ l j, j < 6 ∧ k = 2 + (6 * l + j) :=
      ⟨(k - 2) / 6, (k - 2) % 6, Nat.mod_lt _ (by omega), by omega⟩
    have hl : l < X.Y.k.oneTime.ranges.lookups.length := by omega
    have hc := (fk_link_at X N P l j hj _ (look_at X.Y.k.oneTime l hl)).symm.trans hb
    have step := link_walk (set := X.set) (n := X.Y.k.oneTime.ranges.lookups.length) y
      (promise_ledgers hid (kept_true _ _ _ _)) l hl
      (Lk6.adm_of_tests _ _ _ (tests_at hW hl).2.1 (tests_at hW hl).2.2)
      (d_le (tests_at hW hl).2.1) (tests_at hW hl).2.1 (tests_at hW hl).2.2 (tests_at hW hl).1
      (layout_of_admitted hW) j hj b hc s s' _ gs ((recAt_link X l j hj s).1 hr) hy
    rcases Nat.lt_or_ge (j + 1) 6 with h6 | h6
    · have e : 2 + (6 * l + j) + 1 = 2 + (6 * l + (j + 1)) := by omega
      rw [e]
      exact (recAt_link X l (j + 1) h6 s').2 step
    · obtain rfl : j = 5 := by omega
      have e : 2 + (6 * l + 5) + 1 = 2 + (6 * (l + 1) + 0) := by omega
      rw [e]
      exact (recAt_link X (l + 1) 0 (by omega) s').2 step

end Johnson.RunOne.Law.WalkAtFK

#print axioms Johnson.RunOne.Law.WalkAtFK.recAt_link
#print axioms Johnson.RunOne.Law.WalkAtFK.fk_walk
