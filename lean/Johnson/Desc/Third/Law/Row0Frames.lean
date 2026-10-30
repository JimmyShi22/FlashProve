-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Frames.lean: WHAT IS OWED FOR THE ITEMS THAT RIDE PAST THE LAST CHAIN's
FIRST BLOCK (Piece.Frames, Johnson/Desc/Sound/Spine.lean), at a piece whose block is a lift to a
pair of what was handed to the chain and the chain's own record: a yes of such a piece leaves what
was handed as it is. So an item that rides is kept, GIVEN that its meaning, at one handed part, goes
back from the strings behind the piece to the strings in front. With the clause of
Johnson/Desc/Third/Law/Row0Own.lean this is the table's whole demand at the block. Theorems.

  out_fst              where the piece puts out a statement, what was handed is as it was.
  row0_frames          **the items that ride.**
  row0_each            the two conjuncts of the table's demand at the block, together: the fence,
                       the words and the two readers of the witness read what was handed (the
                       pair's first part), which out_fst keeps.
OBJECT   Block.lift's text (out_fst); (batchLinearConstraintsSecondPart p).decide (row0_each).
USER     out_fst: make_wrap | make_retype (Johnson/Desc/Third/Law/Row0AtTable.lean). row0_frames AND
         row0_each ARE FORERUNNERS of rowZero, general in the table: nobody calls them.
LETTERS  the table's.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
What is not claimed. THAT AN ITEM's MEANING GOES BACK OVER THE STRINGS (hm) IS A PREMISE: behind a
piece the strings are what its stage leaves, so an item in letters may hold behind and fail in
front: it is had of items that read the strings through the stored table and the trees below the
piece's base alone. All that Johnson/Desc/Third/Law/Row0Own.lean does not claim.

-/
import Johnson.Desc.Third.Law.Row0Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece relAt below)
open _root_.Run.PQ (CK)

variable {U T Cl W ι : Type} {C : CK} {F : Frame}

/-- Where the piece puts out a statement, what was handed is as it was. -/
theorem out_fst (pc : Piece C F (U × T) Cl W) (B : Block T Cl)
    (hb : pc.b = Block.lift Prod.snd (fun x s => (x.1, s)) B) (a b : (U × T) × F.E.Str)
    (τ : Iop.Tr (OnBytes.Maker.uLT C pc.ds)) (h : pc.ior.red.out a τ = some b) :
    b.1.1 = a.1.1 := by
  obtain ⟨_, rs, gs, hd⟩ := pc.out_of_decide a τ b h
  rw [hb] at hd
  exact lift_fst B a.1 b.1 rs gs hd

/-- **The items that ride past the block.** -/
theorem row0_frames (pc : Piece C F (U × T) Cl W) (B : Block T Cl)
    (hb : pc.b = Block.lift Prod.snd (fun x s => (x.1, s)) B) (hext : ∀ a τ w, pc.ext a τ w = w)
    (on on' : (U × T) × F.E.Str → Prop) (means : ι → (U × T) × F.E.Str → W → Prop)
    (O In : ι → Prop)
    (hm : ∀ i, O i → ¬ In i → ∀ a τ b w, on a → pc.ior.red.out a τ = some b → on' b →
      b.1.1 = a.1.1 → means i b w → means i a w) :
    pc.Frames on on' means O In := by
  intro a τ b w i ha hout hb' hO hI hw
  rw [hext]
  exact hm i hO hI a τ b w ha hout hb' (out_fst pc B hb a b τ hout) hw

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- The two conjuncts of the table's demand at the block, together. -/
theorem row0_each (p : P₁₄) (pc : Piece C F (U × S₃) Cl W)
    (hb : pc.b = Block.lift Prod.snd (fun x s => (x.1, s)) (below (batchLinearConstraintsSecondPart p)))
    (hext : ∀ a τ w, pc.ext a τ w = w) (Ok : U → S₃ → S₃ → Prop)
    (words : U → S₃ → W → Words K) (omW wv : U → W → Nat → K)
    (hR : ∀ u, Reads p (Ok u) (words u) (omW u) (wv u))
    (on on' : (U × S₃) × F.E.Str → Prop) (means : ι → (U × S₃) × F.E.Str → W → Prop)
    (O In Out : ι → Prop)
    (h0 : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide a.1.2 rs gs = .ok b.1.2) →
      Says p a.1.2 b.1.2 → Ok a.1.1 a.1.2 b.1.2)
    (h1 : ∀ a s', on a → (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide a.1.2 rs gs = .ok s') →
      AtDot p a.1.2 ∧ Names a.1.2)
    (h2 : ∀ a τ b, on a → pc.ior.red.out a τ = some b →
      (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide a.1.2 rs gs = .ok b.1.2) →
      Says p a.1.2 b.1.2 → on' b)
    (h3 : ∀ b w, on' b → relAt means Out b w → RowsHold ρ b.1.2 (words b.1.1 b.1.2 w))
    (h4 : ∀ a w, on a → RowsHold ρ a.1.2 (words a.1.1 a.1.2 w) →
      DotSem ρ p (omW a.1.1) (wv a.1.1) a.1.2 w → relAt means In a w)
    (hm : ∀ i, O i → ¬ In i → ∀ a τ b w, on a → pc.ior.red.out a τ = some b → on' b →
      b.1.1 = a.1.1 → means i b w → means i a w) :
    pc.Own on on' means In Out ∧ pc.Frames on on' means O In :=
  ⟨row0_own ρ p (fun x : U × S₃ => x.2) (fun x : U × S₃ => x.1) pc
      (by rw [hb]; exact yesOf_wrap _) hext Ok words omW wv hR on on'
      (fun a τ b _ h => out_fst pc _ hb a b τ h) means In Out h0 h1 h2 h3 h4,
    row0_frames pc _ hb hext on on' means O In hm⟩

end VerifiableInference.Desc.Third.Law
