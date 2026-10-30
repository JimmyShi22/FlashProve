-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PiecesOfLaid.lean: WHAT A LAW AT THE TABLE ASKS OF THE ROWS OF PIECES, OUT OF ONE
PREMISE: "THE VERIFIER's OWN VALUE IS LAID" (`P5J.LaidAt`, Johnson/P5J/LaidOpens.lean). Kind-free:
no kind of sub-protocol is named. One definition, two theorems.
Why. The counted form of a kind's law is: in scope → `LaidAt` → the named tests on the public
parameters → the fold's facts → the law. The assembled law of K4 (`k04_law_of`) still takes six
premises on the rows T of pieces and on the IOP as written in Lean: `OfDesc` · its data at a file
are D · `sealLast` · the whole `IsCut` at `allOf D` · `AtCap` · `blocksOk` of the first chain. All
six come of `LaidAt`, at the rows that a spender hands (the maker's own, at the cap).
  `pieces_of_planOk`: at any IOP as written in Lean whose test `planOk` passes and whose data at a
  file are D: `sealLast`, `blocksOk` of the first chain, and the three premises on the maker's own
  rows: by `planOk_parts` (Johnson/Desc/Sound/PieceLaid.lean) and `pieces_at_make`
  (Johnson/Road/K4/PiecesAtMake.lean).
  `pieces_of_laid`: **out of `LaidAt`, at its own term `F0T o Z N c`**, the three flat lists'
  heads found by `LaidAt.heads`: no premise on the IOP is left.
Limits. The full size's value alone (`LPFD.Full`), as `LaidAt` has it. That D is the frame's data
(D.at a) is not said. It opens; it pays no law. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidOpens
import Johnson.Road.K4.PiecesAtMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Chain FileDescription blocksOk)
open VerifiableInference.Desc.Sound
open P5J (LaidAt F0T)

/-- What a law asks of the IOP as written in Lean and of the maker's own rows of pieces. -/
def PiecesPaid {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) : Prop :=
  F.data file = .ok D ∧ F.sealLast = true ∧ blocksOk F.first.blocksInOrder = true ∧
    ∃ b₁ l₁ b₂ l₂ b₃ l₃, F.first.blocksInOrder = b₁ :: l₁ ∧ F.shared.blocksInOrder = b₂ :: l₂ ∧
      F.second.blocksInOrder = b₃ :: l₃ ∧
      ∀ (W : Type) (C : CK) e₁ e₂ e₃ (d wEnd : W),
        OfDesc F
            (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd) ∧
          (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).IsCut
            (held b₁) (l₁.map held) (held b₂) (l₂.map held) (held b₃) (l₃.map held) (restCap e₁)
            (restCap e₂) (restCap e₃) sealRound ∧
          AtCap (restCap e₁)

/-- At any IOP as written in Lean whose test `planOk` passes and whose data at a file are D. -/
theorem pieces_of_planOk {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hp : F.planOk = true) (hD : F.data file = .ok D)
    (hh : (∃ b l, F.first.blocksInOrder = b :: l) ∧ (∃ b l, F.shared.blocksInOrder = b :: l) ∧
      ∃ b l, F.second.blocksInOrder = b :: l) : PiecesPaid F file D := by
  obtain ⟨k₁, _, _, hs⟩ := planOk_parts F hp
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := hh
  exact ⟨hD, hs, k₁, b₁, l₁, b₂, l₂, b₃, l₃, q₁, q₂, q₃, fun W C e₁ e₂ e₃ d wEnd =>
    pieces_at_make F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁ e₂ e₃ d wEnd⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
  {Z : ProofFile.Pub} {N : H2U.Places4} {c : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Out of "the value is laid", at its own term.** -/
theorem pieces_of_laid (L : LaidAt o pol lay KL D r Z N c) :
    PiecesPaid (F0T o Z N c) "proof file" D :=
  pieces_of_planOk _ _ D L.planOk L.data (LaidAt.heads o Z N c)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pieces_of_planOk
#print axioms OnBytes.Road.K4.pieces_of_laid
