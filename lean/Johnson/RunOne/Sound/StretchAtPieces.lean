-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/StretchAtPieces.lean: a joining of Johnson/Desc/Sound/Stretch.lean and
Johnson/Desc/Sound/PaidAtDesc.lean. AT THE PIECES THAT THE RULES ARE CALLED AT, A PIECE'S STRETCH IS
THE DATA OF ITS OWN BLOCK'S DECLARED ROUNDS.

The setting. `stretchOfData` (Johnson/Desc/Sound/Stretch.lean, of the rule of composition's files)
says it of every `Three` whose pieces are the maker's. `piecesAt`
(Johnson/Desc/Sound/PaidAtDesc.lean) is the value at which the key file's rule is called.

What is said. `stretchAtPieces`: for every description F and D with `F.data file = .ok D`: along
every piece p of `piecesAt`'s three rows: round by round, as far as the data go: the entry is the
declared round's; the kind is that of the entry's name; the items, the stored parts are the declared
round's; the trees opened are the declared ones by their numbers through the file; as many trees are
sent as the entry says roots (`RoundIs`). (Which block a piece holds: `block_at`,
Johnson/Desc/Sound/KeySeatsAt.lean.)

Limits. Those of Stretch.lean: the shapes of the trees that a round sends are not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)

theorem stretchAtPieces {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (C : CK)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (h₁ : F.first.blocksInOrder = b₁ :: l₁) (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁) (rest₂) (rest₃) (d wEnd : W) :
    let T := piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (∀ p ∈ T.p₁ :: T.l₁, Along (RoundIs (numAt D.t₁ D.t₂ 0)) p.b.rounds p.ds) ∧
      (∀ p ∈ T.p₂ :: T.l₂, Along (RoundIs (numAt D.t₁ D.t₂ 1)) p.b.rounds p.ds) ∧
      ∀ p ∈ T.p₃ :: T.l₃, Along (RoundIs (numAt D.t₁ D.t₂ 2)) p.b.rounds p.ds :=
  stretchOfData Xi F file D hD C _ _ _ _ _ _ _ W _ (held b₁) (l₁.map held) (held b₂) (l₂.map held)
    (held b₃) (l₃.map held) rest₁ rest₂ rest₃ sealRound
    (by rw [h₁]; exact held_map_rounds (b₁ :: l₁)) (by rw [h₂]; exact held_map_rounds (b₂ :: l₂))
    (by rw [h₃]; exact held_map_rounds (b₃ :: l₃))
    (ofCuts_isCut C D (allOf D) 0 0 F.lastChainFirstTreeNumber _ _ _ _ _ _ rest₁ rest₂ rest₃ sealRound
      (besideAt F d wEnd))

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.stretchAtPieces
