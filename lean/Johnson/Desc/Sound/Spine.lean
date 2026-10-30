-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Spine.lean: ONE RELATION AT EVERY BOUNDARY OF A CHAIN, MADE BY A FUNCTION: "every
open item holds". Definitions, one statement written as `def … : Prop`, and its proof.

Why. The rule of composition (Johnson/Desc/Sound/ChainRule.lean, GoodIn.lean) takes, as letters, a
condition and a relation at every boundary, and asks of each block a law between the two at its
sides. For the rule to fire, the relation behind a block and the relation in front of the next have
to be ONE TERM. With some hundred boundaries that cannot be agreed in pairs. So the relation is made
by a function of what each block closes and opens.

What is said. An ITEM is a named claim; `means i a w`: what item i says of a statement a and a
witness w. Block number k CLOSES the items `In k` and OPENS the items `Out k` (an item in both is
context: it is read, and stays). `openAfter`: the items that are open at boundary k: those open at
the start, less what was closed, with what was opened. `relAt`: every item of a set holds.
`Piece.Own`: WHAT IS OWED FOR A BLOCK ITSELF: the block has `GoodIn` from "the items that it closes
hold" to "the items that it opens hold". `Piece.Frames`: what is owed for the items that only ride
past: where the block says yes inside the promise, an open item that it does not close, if it holds
behind at w, holds in front at the extractor's value. `SpineRule`: if every block of a row has both,
the row has `EachGoodIn` at the relations "every open item holds".

Whose the thought is. The shape (items; In and Out; the open set computed; frame facts by the sort
of item) is a design sketch of this project (a text not in this library);
it was not checked in Lean. The proof of a step is `GoodInBeside`'s.

Limits. (1) A rule: `means`, `In`, `Out` and the conditions are letters. (2) AN ITEM LEAVES THE OPEN
SET ONLY THROUGH `In`: the block that closes it owes it in front. (3) Nothing asks that an item's
meaning reads no later draw: that is each item's matter.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- The items that are open at boundary k. -/
def openAfter (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) : ℕ → ι → Prop
  | 0 => O₀
  | k + 1 => fun i => (openAfter In Out O₀ k i ∧ ¬ In k i) ∨ Out k i

/-- Every item of a set holds. -/
def relAt (means : ι → S × F.E.Str → W → Prop) (O : ι → Prop) : S × F.E.Str → W → Prop :=
  fun a w => ∀ i, O i → means i a w

/-- **What is owed for a block itself**: from the items that it closes to those that it opens. -/
def Piece.Own (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) : Prop :=
  p.GoodIn on on' (relAt means In) (relAt means Out)

/-- What is owed for the items that ride past the block. -/
def Piece.Frames (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In : ι → Prop) : Prop :=
  ∀ a τ b w i, on a → p.ior.red.out a τ = some b → on' b → O i → ¬ In i → means i b w →
    means i a (p.ext a τ w)

/-- Every block of a row has both, at its number. -/
def EachOwn (on : ℕ → S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop)
    (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    p.Own (on k) (on (k + 1)) means (In k) (Out k) ∧
      p.Frames (on k) (on (k + 1)) means (openAfter In Out O₀ k) (In k) ∧
      EachOwn on means In Out O₀ (k + 1) l

/-- **The relations "every open item holds" join by construction.** -/
def SpineRule : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ℕ → ι → Prop) (O₀ : ι → Prop)
    (l : List (Piece C F S Cl W)) (k : ℕ),
    EachOwn on means In Out O₀ k l →
    EachGoodIn on (fun j => relAt means (openAfter In Out O₀ j)) k l

theorem spineStep (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In Out : ι → Prop)
    (ho : p.Own on on' means In Out) (hf : p.Frames on on' means O In) :
    p.GoodIn on on' (relAt means O) (relAt means fun i => (O i ∧ ¬ In i) ∨ Out i) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (ho a ha)
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  refine ⟨hon, fun w hall i hi => ?_⟩
  by_cases hin : In i
  · exact hw w (fun j hj => hall j (Or.inr hj)) i hin
  · exact hf a τ b w i ha hb hon hi hin (hall i (Or.inl ⟨hi, hin⟩))

theorem spineRule : SpineRule := by
  intro S Cl W ι C F on means In Out O₀ l
  induction l with
  | nil => exact fun _ _ => trivial
  | cons p l ih =>
    intro k h
    exact ⟨spineStep p _ _ means _ _ _ h.1 h.2.1, ih (k + 1) h.2.2⟩

end VerifiableInference.Desc.Sound
