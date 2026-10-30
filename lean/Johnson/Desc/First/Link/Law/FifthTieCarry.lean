-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieCarry.lean: THE PREMISE `CarryOpen` OF `t5_quiet`
(FifthTie.lean) AT THE SHUTTING, the one of K9's places at which "carry" rides: paid AT ALL 25
SHUTTINGS, at the carried word's sentence as filled (`K2Caller.carryAtZ`,
CarryClosed.lean), by the rules of Johnson/Top/H0/Walk/FrameCarryBack.lean (the switch at
a link) and FrameCarryEnds.lean (at the output head's link; at the finish). A joining.


What is said.
  `restLike_shutB`, `wayLike_shutB`: an accepting step of a sub-protocol each of whose accepting
    steps is the shutting's has `RestLike`, and `WayLike` at `rest` (`shut_inv`,
    Johnson/Desc/First/Batch/Law/ShutLaw.lean; `restLike_shut`, `wayLike_shut`, called).
  `carryOpen_shut`: `CarryOpen 𝔇 Op (StepRel (BlockYes b₅) base In)` where every item that rides is
    spent by a switch that stands at a link (23 of the 25).
  `carryOpen_shutZ`: **THE SAME WHEREVER THE SWITCH STANDS**: the fence is asked at the state that
    the way in `doorZ Z m` returns; where the switch stands at the head's link: neither state
    stands there.

Limits. The fence, and "neither state stands at the head's link", are premises, had from what is
known in front. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTie
import Johnson.Top.H0.Walk.FrameCarryEnds
import Johnson.Desc.First.Batch.Law.ShutLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2Caller (carryAtZ rest doorZ)
open Johnson.Desc.First.Walk.Tied

/-- **The shutting's accepting step has `RestLike`.** -/
theorem restLike_shutB {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (s t : S) (h : BlockYes b₅ s t) : RestLike s t := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨L, hL, rfl⟩ := shut_inv pw piece ft s rs cols t k (hb₅ _ _ _ _ _ h)
  refine restLike_shut (Cl := Cl) pw piece (rs := []) (gs := []) ?_
  show (do
    let L ← VerifiableInference.Desc.K9.there "K9.in-a-segment" s.link?
    pure (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) : Except String S) = _
  rw [hL]
  rfl

/-- **`CarryOpen` AT THE SHUTTING.** -/
theorem carryOpen_shut {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Z : ProofFile.Pub) (layF : ByteArray)
    (h𝔇 : 𝔇.cr1 = carryAtZ Z layF) (Op : Item → Prop) {Cl : Type} (pw : Where) (piece : ℕ)
    (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (base : ℕ) (In : P × S → Strs → Prop)
    (hp : ∀ m, Op (.carry m) → (ProofFile.pAtK2 Z m).stands = .link)
    (hF : ∀ m, Op (.carry m) → ∀ p s y, In (p, s) y → CarryFence Z m base (rest s)) :
    CarryOpen 𝔇 Op (StepRel (BlockYes b₅) base In) := by
  intro m hm
  rw [h𝔇]
  exact carry_goesBack_of Z layF m (hp m hm) _ (restLike_shutB pw piece b₅ hb₅) base In (hF m hm)

/-- The shutting's accepting step has `WayLike` at `rest`. -/
theorem wayLike_shutB {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (s t : S) (h : BlockYes b₅ s t) : WayLike (rest s) (rest t) := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨L, hL, rfl⟩ := shut_inv pw piece ft s rs cols t k (hb₅ _ _ _ _ _ h)
  refine wayLike_shut (Cl := Cl) pw piece (rs := []) (gs := []) ?_
  show (do
    let L ← VerifiableInference.Desc.K9.there "K9.in-a-segment" s.link?
    pure (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) : Except String S) = _
  rw [hL]
  rfl

/-- **`CarryOpen` AT THE SHUTTING, WHEREVER THE SWITCH THAT SPENDS THE ITEM STANDS.** -/
theorem carryOpen_shutZ {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Z : ProofFile.Pub) (layF : ByteArray)
    (h𝔇 : 𝔇.cr1 = carryAtZ Z layF) (Op : Item → Prop) {Cl : Type} (pw : Where) (piece : ℕ)
    (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (base : ℕ) (In : P × S → Strs → Prop)
    (hH : ∀ m, Op (.carry m) → (ProofFile.pAtK2 Z m).stands = .head → ∀ p s t y, BlockYes b₅ s t →
      In (p, s) y → (∀ a, s.here ≠ .head a) ∧ ∀ a, t.here ≠ .head a)
    (hF : ∀ m, Op (.carry m) → ∀ p s y s', In (p, s) y → doorZ Z m s = some s' →
      CarryFence Z m base s') :
    CarryOpen 𝔇 Op (StepRel (BlockYes b₅) base In) := by
  intro m hm
  rw [h𝔇]
  cases hs : (ProofFile.pAtK2 Z m).stands with
  | link =>
    exact carry_goesBack_of Z layF m hs _ (restLike_shutB pw piece b₅ hb₅) base In
      fun p s y hI => hF m hm p s y (rest s) hI (by unfold doorZ; rw [hs])
  | head =>
    exact carry_goesBack_head Z layF m hs _ (wayLike_shutB pw piece b₅ hb₅) base In (hH m hm hs)
      (hF m hm)
  | finish =>
    exact carry_goesBack_finish Z layF m hs _ (wayLike_shutB pw piece b₅ hb₅) base In (hF m hm)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.restLike_shutB
#print axioms VerifiableInference.Desc.LinkJoin.carryOpen_shut
#print axioms VerifiableInference.Desc.LinkJoin.wayLike_shutB
#print axioms VerifiableInference.Desc.LinkJoin.carryOpen_shutZ
