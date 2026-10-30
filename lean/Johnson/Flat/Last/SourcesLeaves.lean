-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/SourcesLeaves.lean: THE PIECE OF THE LAST CHAIN AT WHICH THE TAKEN TREES' SOURCES
ARE HELD AGAINST THE BOOK HANDS THE WHOLE RECORD ON AS IT IS, AND ITS YES SAYS "TIED". Statements
and proofs: A COMPOSITION OF LEMMAS THAT LIE; it names no table.

Why. At row 1 of the last chain's table of joints what is left of the block's own law
(`RowOneOwed`, Johnson/Desc/Sound/QuietRows.lean) begins with "where it says yes the record goes on
as it is". That is `Piece.LeavesOut id` (Johnson/Desc/Sound/ExtHeard.lean). Here it is had at the
block's own text.

Main names (namespace `VerifiableInference.Desc.Sound`).
  `takenSources_leaves`: the block's decision leaves the whole record. By `takenSources_exact`
    (Johnson/Desc/Third/Law/Sources.lean).
  `leaves_id_seat`: GENERAL: a block that leaves its whole record, with the test "every word is
    below the prime" in front (`below`), laid at the second place of a pair as the pieces' maker
    lays it (`OfDesc.b₃`, Johnson/Desc/Sound/DescThree.lean): it leaves the whole pair. By
    `leavesBelow` (Johnson/Desc/Sound/ExtHeardProofs.lean), `leavesLift`, `leavesLiftIn`
    (Johnson/Desc/Sound/FoldHeardProofs.lean).
  **`sources_same`**: a piece whose block is that block so laid: `Piece.LeavesOut id`: whatever its
    stretch, extractor and errors. By `leavesOutOfBlock`.
  **`sources_tied`**: where that piece's reduction puts out, `Tied own` holds of the chain's own
    record in front.

Limits. Nothing on the strings (see QuietRows.lean's head: they turn from the base on). That the
piece at place 1 of a description's last chain IS this block so laid is the maker's law (`OfDesc`)
and the description's text: not used here. What "Tied" is worth: Sources.lean's own limits.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.Law.Sources
import Johnson.Desc.Sound.ExtHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Third (S₃ takenSources)
open VerifiableInference.Desc.Third.Law (Tied takenSources_exact)

/-- The block's decision leaves the whole record. -/
theorem takenSources_leaves {Cl : Type} (own : Block S₃ Cl) : (takenSources own).Leaves id :=
  fun s rs gs s' h => ((takenSources_exact own s rs gs s').1 h).1

/-- **A block that leaves its whole record, as the pieces' maker lays it, leaves the whole
pair.** -/
theorem leaves_id_seat {P S Cl : Type} (b : Block S Cl) (h : b.Leaves id) :
    ((below b).lift Prod.snd fun (t : P × S) s => (t.1, s)).Leaves id := by
  intro t rs gs t' H
  have h₁ : t'.1 = t.1 :=
    leavesLift S (P × S) Cl P Prod.fst Prod.snd (fun t s => (t.1, s)) (below b) (fun _ _ => rfl) t
      rs gs t' H
  have h₂ : t'.2 = t.2 :=
    leavesLiftIn S (P × S) Cl S id Prod.snd (fun t s => (t.1, s)) (below b) (fun _ _ => rfl)
      (leavesBelow S Cl S id b h) t rs gs t' H
  exact Prod.ext h₁ h₂

variable {P Cl W : Type} {C : CK} {F : Frame}

/-- **THE RECORD GOES ON AS IT IS.** -/
theorem sources_same (own : Block S₃ Cl) (x : Piece C F (P × S₃) Cl W)
    (hx : x.b = (below (takenSources own)).lift Prod.snd fun t s => (t.1, s)) :
    x.LeavesOut id :=
  leavesOutOfBlock (P × S₃) Cl W (P × S₃) C F id x
    (hx ▸ leaves_id_seat (takenSources own) (takenSources_leaves own))

/-- **ITS YES SAYS "TIED".** -/
theorem sources_tied (own : Block S₃ Cl) (x : Piece C F (P × S₃) Cl W)
    (hx : x.b = (below (takenSources own)).lift Prod.snd fun t s => (t.1, s))
    (a b : (P × S₃) × F.E.Str) (τ : Iop.Tr (uLT C x.ds)) (hb : x.ior.red.out a τ = some b) :
    Tied own a.1.2 := by
  obtain ⟨s', k, hst, -⟩ := foldConsOk (chainAtOk (pieceOk x a τ b hb))
  obtain ⟨gs, hd⟩ := stepOk hst
  rw [hx] at hd
  obtain ⟨s, hs, -⟩ := mapOk (x := (below (takenSources own)).decide a.1.2 _ gs) hd
  have hs' : (if viewWordsBelowPrime ⟨_, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
      then (takenSources own).decide a.1.2 _ gs else .error "a word is not below the prime") =
        .ok s := hs
  split at hs'
  · exact ((takenSources_exact own _ _ _ _).1 hs').2
  · exact nomatch hs'

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.takenSources_leaves
#print axioms VerifiableInference.Desc.Sound.leaves_id_seat
#print axioms VerifiableInference.Desc.Sound.sources_same
#print axioms VerifiableInference.Desc.Sound.sources_tied
