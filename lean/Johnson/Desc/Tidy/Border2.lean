--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Tidy/Border2.lean: **in front of the request's own proximity test, on the third chain,
the statement is tidy** (`Tidy`, Johnson/Desc/Means/Walk.lean: in order; the open rows' kinds; no
sample row on a message that is not sampled; sampled members): out of a yes of the first chain from
its empty statement, a yes of the shared chain from its empty statement, the third chain's start at
the two ends, and a yes of its first two blocks. One theorem that joins three: `first_tidy` and
`shared_tidy` (Johnson/Desc/Tidy/Chains.lean) and `tidy_border2_at` (Johnson/Desc/Tidy/Third.lean).
Main names:
  `OursStill b`: b is one of this house's blocks of the first chain that leave the statement as it
    is: the two quiet steps; the chain's last block. `oursStill_steps`.
  `behind_steps`: a quiet step laid behind another block as one block keeps what that block keeps.
  `ended_st`: the shared chain's end, as a later chain reads it, holds the last record's statement.
  `tidy_last_border2`: **the theorem.** THE PREMISES THAT ARE NOT PROVED HERE, BY NAME: hb₁'s third
    arm: every block of the first chain's list that is none of ours keeps "tidy in front, tidy
    behind" at a yes of its step · ht: the shared chain's proximity tests' blocks do.
OF THE PLAN: hp₁, hp₂: the blocks' tests on the plan pass. OF THE
    DESCRIPTION: that its chains are such lists.

What is not claimed. These premises. Nothing on the own test's block. Nothing on soundness.

-/
import Johnson.Desc.Tidy.Chains
import Johnson.Desc.Tidy.Still
import Johnson.Desc.Tidy.Third

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes
open OnBytes.Means (Tidy)
open VerifiableInference.Desc.Ground (By TidyStay)
open VerifiableInference.Desc.Keeps (Steps Fits Decides steps_of_decides steps_of_fits andThen_fits
  layers_still head_still firstEnd_still)

/-- This house's blocks of the first chain that leave the statement as it is. -/
inductive OursStill : Block S Unit → Prop
  | layers (P : K8.ReadsQuiet.PG) : OursStill (K8.ReadsQuiet.layers P)
  | head (P : K8.ReadsQuiet.PH) : OursStill (K8.ReadsQuiet.head P)
  | last (piece : Nat) (front : List (Block S Unit)) : OursStill (firstEnd piece front)

theorem oursStill_steps {b : Block S Unit} (h : OursStill b) :
    Steps (By TidyStay fun s : S => s.st) b := by
  cases h with
  | layers P => exact steps_of_decides (layers_still (fun _ x => x) P)
  | head P => exact steps_of_decides (head_still (fun _ x => x) P)
  | last piece front => exact steps_of_decides (firstEnd_still (fun _ x => x) piece front)

/-- A block without a round that leaves the statement, laid behind another block as one block. -/
theorem behind_steps (n : String) (own q : Block S Unit) (hq0 : q.rounds = [])
    (ho : Fits (By TidyStay fun s : S => s.st) own)
    (hq : Decides (By TidyStay fun s : S => s.st) q) :
    Steps (By TidyStay fun s : S => s.st) (own.andThen n q) :=
  steps_of_fits (andThen_fits _ (fun _ _ _ x y z => y (x z)) n own q hq0 ho hq)

end VerifiableInference.Desc.First

namespace Desc.K14

/-- The shared chain's end, as a later chain reads it, holds the last record's statement. -/
theorem ended_st {d : St} {e : OnBytes.Proof.SharedEnd} (h : ended d = some e) : e.st = d.st := by
  unfold ended at h
  dsimp only at h
  split at h
  · rw [← Option.some.inj h]
  · cases h

end Desc.K14

namespace VerifiableInference.Desc.Third.Law
open OnBytes
open OnBytes.Means (Tidy)
open VerifiableInference.Desc.Ground (By TidyStay)
open VerifiableInference.Desc.Keeps (Steps Decides)
open VerifiableInference.Desc.First (OursFirst OursStill oursFirst_steps oursStill_steps first_tidy)

/-- **In front of the request's own proximity test the statement is tidy.** -/
theorem tidy_last_border2 {Cl XiPub : Type}
    -- the first chain
    (name₁ : String) (ft₁ : Nat) (bs₁ : List (Block First.S Unit))
    (hb₁ : ∀ b ∈ bs₁, OursFirst b ∨ OursStill b ∨ Steps (By TidyStay fun s : First.S => s.st) b)
    (hp₁ : ∀ b ∈ bs₁, b.planOk = true) (a₁ e₁ : First.S) (v₁ : Fmt.View)
    (h₁ : chainAt name₁ ft₁ bs₁ a₁ v₁ = .ok e₁) (codes₁ : Codes)
    (hs₁ : a₁.st = { codes := codes₁, oracles := #[], groups := #[] })
    -- the shared chain
    (c : Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    (ht : ∀ b ∈ tests, Steps (By TidyStay fun d : _root_.Desc.K14.St => d.st) b)
    (hl : Decides (By TidyStay fun d : _root_.Desc.K14.St => d.st)
      (last (_root_.Desc.K14.blocksOr P ++ tests)))
    (hp₂ : ∀ b ∈ (_root_.Desc.K14.chainOf c P tests last).blocksInOrder, b.planOk = true)
    (name₂ : String) (ft₂ : Nat) (a₂ d₂ : _root_.Desc.K14.St) (v₂ : Fmt.View)
    (h₂ : chainAt name₂ ft₂ (_root_.Desc.K14.chainOf c P tests last).blocksInOrder a₂ v₂ = .ok d₂)
    (codes₂ : Codes) (hs₂ : a₂.st = { codes := codes₂, oracles := #[], groups := #[] })
    (e₂ : Proof.SharedEnd) (he : _root_.Desc.K14.ended d₂ = some e₂)
    -- the third chain
    (p : P₁₄) (x : XiPub) (s₀ s₁ s₂ : S₃) (h0 : startAtEnds p x e₁ e₂ = .ok s₀)
    (own : Block S₃ Cl) (rs rs' : List Fmt.RoundView) (gs gs' : List (List (Nat × List UInt64)))
    (h1 : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s₁)
    (h2 : (takenSources own).decide s₁ rs' gs' = .ok s₂) : Tidy s₂.st := by
  have T₁ : Tidy e₁.st := first_tidy name₁ ft₁ bs₁
    (fun b hm => (hb₁ b hm).elim Or.inl fun k => Or.inr (k.elim oursStill_steps id)) hp₁ a₁ e₁ v₁ h₁
    codes₁ hs₁
  have T₂ : Tidy d₂.st := _root_.Desc.K14.shared_tidy c P tests last ht hl hp₂ name₂ ft₂ a₂ d₂ v₂ h₂
    codes₂ hs₂
  refine tidy_border2_at p x e₁ e₂ s₀ s₁ s₂ h0 own rs rs' gs gs' h1 h2 T₁ ?_
  rw [_root_.Desc.K14.ended_st he]
  exact T₂.inOrder

end VerifiableInference.Desc.Third.Law
