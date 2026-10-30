-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/CutRowAt.lean: a law on the maker `cutRow` (Johnson/Desc/Sound/Tiles.lean).
WHAT A CUT PIECE HOLDS BESIDE ITS BLOCK AND ITS STRETCH.

The setting. `cutRow rest putBack i₀ base ds b l` (Johnson/Desc/Sound/Tiles.lean, of the rule of
composition's files) cuts a chain's data at the blocks' rounds; `rest i ds` gives piece i its
extractor and errors, at its stretch.

What is said. `cutRow_rest`: the piece number i has the errors and the extractor that `rest (i₀ +
i)` gives at the piece's own stretch; and what is put back behind it is nothing, or `putBack`.

Limits. A fact on the maker.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesCutProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame} {S Cl W : Type}

theorem cutRow_rest (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView) :
    ∀ (l : List (Block S Cl)) (b : Block S Cl) (i₀ base : ℕ) (ds : List RDT) (i : ℕ)
      (p : Piece C F S Cl W),
      ((cutRow rest putBack i₀ base ds b l).1 :: (cutRow rest putBack i₀ base ds b l).2)[i]? =
        some p →
      p.err = (rest (i₀ + i) p.ds).err ∧ p.ext = (rest (i₀ + i) p.ds).ext ∧
        (p.back = [] ∨ p.back = putBack)
  | [], b, i₀, base, ds, 0, p, h => by
    obtain rfl : pieceOf b base ds putBack (rest i₀ ds) = p := Option.some.inj h
    exact ⟨rfl, rfl, Or.inr rfl⟩
  | [], _, _, _, _, _ + 1, _, h => by cases h
  | b' :: l, b, i₀, base, ds, 0, p, h => by
    obtain rfl : pieceOf b base (ds.take b.rounds.length) [] (rest i₀ (ds.take b.rounds.length)) =
      p := Option.some.inj h
    exact ⟨rfl, rfl, Or.inl rfl⟩
  | b' :: l, b, i₀, base, ds, i + 1, p, h => by
    have ih := cutRow_rest rest putBack l b' (i₀ + 1) (base + nTrees (ds.take b.rounds.length))
      (ds.drop b.rounds.length) i p h
    have e : i₀ + 1 + i = i₀ + (i + 1) := by omega
    rw [e] at ih
    exact ih

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.cutRow_rest
