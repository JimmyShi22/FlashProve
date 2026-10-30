-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PiecesAtMake.lean: WHAT A LAW AT THE TABLE ASKS OF THE THREE ROWS OF PIECES HOLDS
AT THE MAKER's OWN ROWS, BY THEIR MAKE: general in the IOP as written in Lean (`FileDescription`): no
kind of sub-protocol is named. Two theorems.

Why. The assembled law of a kind of sub-protocol (for K4: `k04_law_of`) takes, on the rows T of
pieces, that T holds the IOP's own sub-protocols (`OfDesc`), that T is the maker's cut at the list
of all trees `allOf D` (`Three.IsCut`), and that the first row's family of extractors and error
bounds is at the cap (`AtCap`). Whoever spends such a law hands it the maker's own rows, `piecesAt
… (restCap e₁) (restCap e₂) (restCap e₃) …` (Johnson/Desc/Sound/PaidAtDesc.lean,
BoundsAtCap.lean). At these rows all three hold by make: so of the law's premises on the rows only
two facts on the IOP are left: its data at a file are D, and its last sub-protocol seals.
  `pieces_at_make`: **the three premises on the rows**: by `paidAtDesc` (first
  conjunct), `ofCuts_isCut` (Johnson/Desc/Sound/TilesMaker.lean) and `atCap_restCap`.
  `rows_at_make`: so, by `rows_of_cut` (PieceMakers.lean): the first row is tiled, its rounds are
  the data's first chain's, its first piece's base is 0, every piece's error bounds are the cap.
What it speaks of. The one family of values that a spender hands: nothing is assumed of T beyond
its definition.
Limits. The three heads (each chain's flat list is b :: l) are asked: they are free by the make of
a chain's flat list, which always has a first member; that is not shown here. The two facts on the
IOP (the data; `sealLast`) are asked: the verifier's accepting gives them
(Johnson/Road/K4/PiecesOfLaid.lean). No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.PieceMakers
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.TilesMaker
import Johnson.Desc.Sound.BoundsAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound

section
variable {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (hD : F.data file = .ok D)
  (hs : F.sealLast = true) (C : CK)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (q₁ : F.first.blocksInOrder = b₁ :: l₁) (q₂ : F.shared.blocksInOrder = b₂ :: l₂) (q₃ : F.second.blocksInOrder = b₃ :: l₃)
  (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
    Iop.Tr (uLT C ds) → W → W)
  (e₂ : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁) × F.S₂) × (frameAt D (allOf D) D.key₂ 0).E.Str → Iop.Tr (uLT C ds) → W → W)
  (e₃ : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str →
    Iop.Tr (uLT C ds) → W → W)
  (d wEnd : W)

include hD hs q₁ q₂ q₃

/-- **The three premises on the rows, at the maker's own rows.** -/
theorem pieces_at_make :
    OfDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd) ∧
      (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).IsCut
        (held b₁) (l₁.map held) (held b₂) (l₂.map held) (held b₃) (l₃.map held) (restCap e₁)
        (restCap e₂) (restCap e₃) sealRound ∧
      AtCap (restCap e₁) :=
  ⟨(paidAtDesc Xi W F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ (restCap e₁) (restCap e₂)
      (restCap e₃) d wEnd).1,
    ofCuts_isCut C D (allOf D) 0 0 F.lastChainFirstTreeNumber (held b₁) (l₁.map held) (held b₂) (l₂.map held)
      (held b₃) (l₃.map held) (restCap e₁) (restCap e₂) (restCap e₃) sealRound
      (besideAt F d wEnd),
    atCap_restCap e₁⟩

/-- **All the lines on the first row, at the maker's own rows.** -/
theorem rows_at_make :
    Tiled (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁
        (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₁ ∧
      rowData (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁
        (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₁ =
          D.ds₁ ∧
      (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁.base =
        0 ∧
      ∀ q ∈ (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁ ::
          (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₁,
        q.err = Err.cap 128 (uLT C q.ds) := by
  obtain ⟨hO, hc, ha⟩ :=
    pieces_at_make F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁ e₂ e₃ d wEnd
  exact rows_of_cut F file D hD hs _ hO _ _ _ _ _ _ _ _ _ sealRound hc ha

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pieces_at_make
#print axioms OnBytes.Road.K4.rows_at_make
