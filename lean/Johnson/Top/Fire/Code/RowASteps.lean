-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowASteps.lean: THE KEY FILE's FIRST CHAIN: THE STATE's SIDE OF THE PROMISE, CARRIED OVER BLOCKS 16 AND 17 BY THE BLOCKS' YESES ALONE: THE TWO STEPS THAT «aSide_of_hist» LACKS: so that the members at borders 16 | 17 | 18 need NO Bool on the state.
The form is `StepInv b (ASide one at_ k) (ASide one at_ (k + 1))`, written out sign for sign (`ASide one at_ k s`, Johnson/RunOne/KeyASide.lean: four conjuncts; `StepInv b A B`, ReachedInv.lean: ∀ s s' rs gs, roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' → A s → B s'): neither name is imported here: the two statements are what that term unfolds to.
  (step16_state HAS MOVED, not a sign turned, to RunOne/KeyStep16.lean, with idx0_of_shape | pinned_16)
  astep16        **the step at 16**, at every block that decides as the batching's seat: FROM: at most noId stages · PubPile one
  astep17        **the step at 17**, at every block that decides and declares as W's sending: FROM: Public117 · wAt one + 1 < noId · at_ 2 = (stages + 1, 0): by laid17_at · shape_send17 · Laid17.placeOld | placeW | order
IT IMPORTS Johnson/RunOne/KeyStep16.lean AND Johnson/RunOne/KeyRow117.lean ALONE: IT DOES NOT STAND OVER ROW 1.16's LAW (Johnson/Desc/K13/Law/RowBatt.lean and what stands on it), WHICH ALONE SPENDS THE PREMISE OF goodIn_any (by report: else aSide_of_hist's fold would inherit it by import). Johnson/Desc/K13/Law/GoodAny.lean ITSELF LIES BENEATH BY IMPORT, for its definitions alone (KeyBattBy.lean), which are one in its two forms.
OBJECT: the first chain's state at borders 16 · 17 · 18 · USER: aSide_of_hist's «gaps» at 16 | 17 · LETTERS: one N sent groups · at_ · b. Nothing on soundness.
-/
import Johnson.RunOne.KeyStep16
import Johnson.RunOne.KeyRow117

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open Johnson.RunOne.KeyRows1

/-- **`StepInv b (ASide one at_ 16) (ASide one at_ 17)`**, written out. -/
theorem astep16 (one : OneTime) (at_ : Where) (N : Pieces) (sent : ℕ) (hst : one.ranges.stages.length ≤ noId) (HP : PubPile one)
    (b : Block FirstState Claim) (hd : b.decide = (batchTableRows (Cl := Claim) (fun x : LookupRecord => x.keys) one N sent).decide) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s = true ∧ Placed (plan₁ one).orc (fun o => s.d.book.place[o]?) id at_ (pinned (open₁ 2 16)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 16 ∧ 16 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (16 + 1) s' = true ∧ Placed (plan₁ one).orc (fun o => s'.d.book.place[o]?) id at_ (pinned (open₁ 2 (16 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (16 + 1) ∧ (16 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) := by
  intro s s' rs gs _ hy ⟨h1, h2, h3, _⟩
  rw [hd] at hy
  obtain ⟨g1, g2, g3⟩ := step16_state one N sent hst HP s s' _ gs hy
  refine ⟨g1 h1, fun k hk => ?_, g3 h3, fun h => absurd h.2 (by decide)⟩
  have hk' : k ∈ pinned (open₁ 2 16) := by
    rw [pinned_16]
    exact pinned_at17 ▸ hk
  obtain ⟨o, t, ho, ht, e⟩ := h2 k hk'
  exact ⟨o, t, ho, by rw [g2]; exact ht, e⟩

/-- **`StepInv b (ASide one at_ 17) (ASide one at_ 18)`**, written out. -/
theorem astep17 (one : OneTime) (at_ : Where) (N : Pieces) (sent : ℕ) (groups : List (List ℕ)) (Pb : Public117 one N groups) (hsm : wAt one + 1 < noId)
    (hat : at_ 2 = (one.ranges.stages.length + 1, 0)) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (b : Block FirstState Claim) (hd : b.decide = bw.decide) (hr : b.rounds = K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂])) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 17 s = true ∧ Placed (plan₁ one).orc (fun o => s.d.book.place[o]?) id at_ (pinned (open₁ 2 17)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 17 ∧ 17 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (17 + 1) s' = true ∧ Placed (plan₁ one).orc (fun o => s'.d.book.place[o]?) id at_ (pinned (open₁ 2 (17 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (17 + 1) ∧ (17 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) := by
  intro s s' rs gs hf hy ⟨h1, h2, h3, _⟩
  have H := laid17_at one N sent groups Pb bw hb b hd s s' rs gs (hr ▸ hf) hy h1 h3
  refine ⟨shape_send17 one hsm s s' H h1, fun k hk => ?_, H.order, fun h => absurd h.2 (by decide)⟩
  have hk' : k ∈ [0, 2] := pinned_at18 ▸ hk
  rcases (by simpa using hk' : k = 0 ∨ k = 2) with rfl | rfl
  · obtain ⟨o, t, ho, ht, e⟩ := h2 0 (by rw [pinned_at17]; exact List.mem_singleton.2 rfl)
    obtain rfl : 0 = o := Option.some.inj ho
    exact ⟨0, t, rfl, (H.placeOld 0 (by unfold wAt; omega)).trans ht, e⟩
  · exact ⟨wAt one, (one.ranges.stages.length + 1, 0), rfl, H.placeW, hat⟩

end LPFD

#print axioms LPFD.astep16
#print axioms LPFD.astep17
