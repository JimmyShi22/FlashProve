-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceMakers.lean: WHAT THE MAKER's OWN ROWS HAVE BY THEIR MAKE: where three rows
of pieces hold a description's blocks and ARE THE MAKER's CUT of the description's data, at a
family of extractors and errors that is at the cap: the first row is tiled, its rounds are the
data's first chain's, its first piece's base is 0, and every piece's errors are the cap. General
in the description: no kind is named. Two theorems.
Why. A kind's law at the table asks four or five lines on the rows T of pieces (tiled, rounds,
base, cap). At a general T that holds the description's blocks (`OfDesc`) none of them follows:
`err` and `base` are free fields of a piece. Whoever spends such a law takes the maker's own rows
(`piecesAt`,
Johnson/Desc/Sound/PaidAtDesc.lean; `ofCuts_isCut`, Johnson/Desc/Sound/TilesMaker.lean): so the
lines shrink to "T is the cut, at a rest that is at the cap", which that spender has by make.
  `cap_at_cut`: a member of a row that is the maker's cut, at a rest at the cap, has the cap's
  errors: `cutRow_err` (Johnson/Road/K4/PieceAtCut.lean) at a number of the row.
  `rows_of_cut`: **all the lines at once**: off `fitsOfData`
  (Johnson/Desc/Sound/TilesDataProofs.lean), whose three premises "the blocks' declared rounds are
  the description's" are drawn here from `OfDesc` and the cut (`cutBlocks`).
A member. `piecesAt` (Johnson/Desc/Sound/PaidAtDesc.lean) meets both `OfDesc` (`paidAtDesc`'s
first conjunct) and `IsCut` (`ofCuts_isCut`): the two do not pull. AT THAT MEMBER THREE OF THE
FOUR LINES ARE HAD ALREADY: `paidAtDesc`'s second conjunct is `Fits` (tiled, rounds, base).
WHAT THIS FILE ADDS: the same at EVERY rows R that are the cut, not at that filling alone; and the
cap. (The pair pins one letter: `OfDesc.back₁` and the cut's first line give r = the sealing
round.)
Limits. THE WHOLE CUT IS ASKED (`Three.IsCut`: all three rows), not the first row's line alone,
and THE LIST OF ALL TREES IS `allOf D`: so `fitsOfData` has it. The description's last block must
seal (`sealLast`: a Bool on the plan). Nothing on what a block decides. No probability: no
soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.PieceAtFits
import Johnson.Desc.Sound.TilesDataProofs
import Johnson.Desc.Sound.TilesCutProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Sound

/-- **A member of the maker's row, at a rest at the cap, has the cap's errors.** -/
theorem cap_at_cut {T Cl W : Type} {C : CK} {F : Frame} {p : Piece C F T Cl W}
    {l : List (Piece C F T Cl W)} {b₁ : Block T Cl} {l₁ : List (Block T Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest C F T W ds} {back : List Fmt.RoundView} {i base : ℕ}
    {ds : List RDT} (hc₁ : (p, l) = cutRow rest₁ back i base ds b₁ l₁) (hcap : AtCap rest₁) {k : ℕ}
    {q : Piece C F T Cl W} (hq : (p :: l)[k]? = some q) : q.err = Err.cap 128 (uLT C q.ds) :=
  cutRow_err rest₁ hcap back l₁ b₁ i base ds q (by rw [← hc₁]; exact List.mem_of_getElem? hq)

/-- **All the lines on the first row at once, at the maker's own rows.** -/
theorem rows_of_cut {Xi W : Type} {C : CK} (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) (hs : G.sealLast = true) {X₁ X₂ : Type}
    (R : ThreeAt C D (allOf D) G X₁ X₂ W) (hO : OfDesc G R) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃
    (r : Fmt.RoundView) (hc : R.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (hcap : AtCap rest₁) :
    Tiled R.p₁ R.l₁ ∧ rowData R.p₁ R.l₁ = D.ds₁ ∧ R.p₁.base = 0 ∧
      ∀ q ∈ R.p₁ :: R.l₁, q.err = Err.cap 128 (uLT C q.ds) := by
  have e₁ : (R.p₁ :: R.l₁).map (·.b) = b₁ :: l₁ := by
    have := cutBlocks C _ _ _ W rest₁ [r] l₁ b₁ 0 0 D.ds₁
    rw [← hc.c₁] at this
    exact this
  have e₂ : (R.p₂ :: R.l₂).map (·.b) = b₂ :: l₂ := by
    have := cutBlocks C _ _ _ W rest₂ [] l₂ b₂ 0 D.t₁ D.ds₂
    rw [← hc.c₂] at this
    exact this
  have e₃ : (R.p₃ :: R.l₃).map (·.b) = b₃ :: l₃ := by
    have := cutBlocks C _ _ _ W rest₃ [] l₃ b₃ 0 (D.t₁ + D.t₂) D.ds₃
    rw [← hc.c₃] at this
    exact this
  have g₁ : (b₁ :: l₁).map (·.rounds) = G.first.blocksInOrder.map (·.rounds) := by
    rw [← e₁, hO.b₁, List.map_map, List.map_map]
    rfl
  have g₂ : (b₂ :: l₂).map (·.rounds) = G.shared.blocksInOrder.map (·.rounds) := by
    rw [← e₂, hO.b₂, List.map_map, List.map_map]
    rfl
  have g₃ : (b₃ :: l₃).map (·.rounds) = G.second.blocksInOrder.map (·.rounds) := by
    rw [← e₃, hO.b₃, List.map_map, List.map_map]
    rfl
  have hF := fitsOfData Xi G file D hD hs C _ _ _ _ _ _ _ W R b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r
    g₁ g₂ g₃ hc
  exact ⟨hF.tiled₁, hF.data₁, hF.base₁, fun q hq =>
    cutRow_err rest₁ hcap [r] l₁ b₁ 0 0 D.ds₁ q (by rw [← hc.c₁]; exact hq)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cap_at_cut
#print axioms OnBytes.Road.K4.rows_of_cut
