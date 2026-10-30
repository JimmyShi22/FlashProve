-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SpineWide.lean: THE RULE "ONE RELATION AT EVERY BOUNDARY"
(Johnson/Desc/Sound/Spine.lean) WITH A WIDER DOOR FOR WHAT RIDES PAST A BLOCK: the debt for a rider
is asked only where EVERY item that is open behind the block holds. Definitions, small lemmas and
the rule, with their proofs.

Why. `Piece.Frames` asks, for an item i that rides past a block: where the block says yes from a to
b, and i holds at (b, w), i holds at a. It is asked at every a inside the promise. The rule spends
it only under "every open item holds at (b, w)". Where one of the open items says something of the
record itself (no mark is set), that is more in hand: a rider's lemma may then use it, and need not
be shown at records at which no witness behind can stand.

Main names:
  `Piece.FramesIn p on on' means O In Out`: as `Piece.Frames`, with "every item that is open behind
    the block holds at (b, w)" in the place of "i holds at (b, w)".
  `Piece.Frames.wide`: `Frames` gives `FramesIn`.
  `EachOwnIn`: a row's debt with `FramesIn`. `EachOwn.wide`: `EachOwn` gives it.
  `spineStepIn`, **`spineRuleIn`**: `EachOwnIn` gives `EachGoodIn` at the relations "every open item
    holds": the conclusion of `spineRule`, to the letter.

Limits: those of Spine.lean. What a rider's lemma may now use is what the OPEN ITEMS say at (b, w):
nothing is gained where no open item speaks of the record. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- What is owed for the items that ride past the block, where all that is open behind it holds. -/
def Piece.FramesIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In Out : ι → Prop) : Prop :=
  ∀ a τ b w i, on a → p.ior.red.out a τ = some b → on' b →
    relAt means (fun j => (O j ∧ ¬ In j) ∨ Out j) b w → O i → ¬ In i →
    means i a (p.ext a τ w)

theorem Piece.Frames.wide {p : Piece C F S Cl W} {on on' : S × F.E.Str → Prop}
    {means : ι → S × F.E.Str → W → Prop} {O In : ι → Prop} (h : p.Frames on on' means O In)
    (Out : ι → Prop) : p.FramesIn on on' means O In Out :=
  fun a τ b w i ha hb hon hall hi hin => h a τ b w i ha hb hon hi hin (hall i (Or.inl ⟨hi, hin⟩))

/-- Every block of a row has both, at its number. -/
def EachOwnIn (on : ℕ → S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop)
    (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    p.Own (on k) (on (k + 1)) means (In k) (Out k) ∧
      p.FramesIn (on k) (on (k + 1)) means (openAfter In Out O₀ k) (In k) (Out k) ∧
      EachOwnIn on means In Out O₀ (k + 1) l

theorem EachOwn.wide (on : ℕ → S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop)
    (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (k : ℕ), EachOwn on means In Out O₀ k l →
      EachOwnIn on means In Out O₀ k l
  | [], _, _ => trivial
  | _ :: l, k, h => ⟨h.1, h.2.1.wide _, EachOwn.wide on means In Out O₀ l (k + 1) h.2.2⟩

theorem spineStepIn (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In Out : ι → Prop)
    (ho : p.Own on on' means In Out) (hf : p.FramesIn on on' means O In Out) :
    p.GoodIn on on' (relAt means O) (relAt means fun i => (O i ∧ ¬ In i) ∨ Out i) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (ho a ha)
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  refine ⟨hon, fun w hall i hi => ?_⟩
  by_cases hin : In i
  · exact hw w (fun j hj => hall j (Or.inr hj)) i hin
  · exact hf a τ b w i ha hb hon hall hi hin

/-- **The relations "every open item holds" join, with the wider door for the riders.** -/
theorem spineRuleIn (on : ℕ → S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop)
    (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (k : ℕ), EachOwnIn on means In Out O₀ k l →
      EachGoodIn on (fun j => relAt means (openAfter In Out O₀ j)) k l
  | [], _, _ => trivial
  | p :: l, k, h =>
    ⟨spineStepIn p _ _ means _ _ _ h.1 h.2.1, spineRuleIn on means In Out O₀ l (k + 1) h.2.2⟩


end VerifiableInference.Desc.Sound
