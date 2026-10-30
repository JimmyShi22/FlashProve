-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/ThroughClose.lean: the closing of a segment (K10): the lot with the closings alone is
natural in its reader of the input. A lot "read through" (`HLot.thru`, Honest/Thru.lean) is the lot whose parts read a
wider input by a map into the input that they were written for. Here: `seatLotC` read through `Local.thru g rd` is
`seatLotC` at the readers composed with that map.

  `closeBat_through`  the part for the round "BAT", which sends nothing, read through, is itself
  `foldShell_through`    the fold's part read through is the fold's part at the job carried over (`CloseJob.over`)
  `andThen_through`       two parts as one, read through, are the two read through, as one
  `closePart_through`     so for the closing's part
  `seatedJob_through`     the seated job carried over by `Local.thru g rd` is the seated job at the readers composed with it
  **`seatLotC_through`**   the lot's halves, read through, are the halves of the lot at the composed readers

Limits. Equations of definitions; nothing is said of what a part sends.
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (SegmentPub segmentsOf)

section
variable {V V' W W' X : Type}

/-- The part for the round "BAT", read through, is itself. -/
theorem closeBat_through (see : V' → V) (wit : W' → W) :
    (closeBatPart : Part V W X).thru see wit = closeBatPart := rfl

/-- The fold's part read through is the fold's part at the job carried over. -/
theorem foldShell_through (see : V' → V) (wit : W' → W) (tot : Bool) (J : CloseJob W) (F : FoldWords) :
    (foldShellT tot J F : Part V W X).thru see wit = foldShellT tot (J.over wit) F := by
  simp only [Part.thru, Part.lift, foldShellT, List.map_cons, List.map_map]
  rfl

/-- Two parts as one, read through, are the two parts read through, as one. -/
theorem andThen_through (see : V' → V) (wit : W' → W) (p q : Part V W X) :
    (p.andThen q).thru see wit = (p.thru see wit).andThen (q.thru see wit) := by
  simp only [Part.thru, Part.lift, Part.andThen, List.map_append, List.map_map, List.length_map]
  rfl

/-- The closing's part read through is the closing's part at the fold read through. -/
theorem closePart_through (see : V' → V) (wit : W' → W) (fold : Part V W X) :
    (closePart fold).thru see wit = closePart (fold.thru see wit) := by
  unfold closePart
  rw [andThen_through, closeBat_through]

end

variable {W₀ W₀' Rc Rc' Xi Tr X : Type}

/-- The seated job carried over by the map of inputs is the seated job at the readers composed with that map. -/
theorem seatedJob_through (g : W₀' → W₀) (rd : Rc' → Rc) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr)
    (segs : List SegmentPub) (stAt : StAtOf Xi) (pub : ClosePub) :
    (seatedJob readers rows lay addrs segs stAt pub).over (Local.thru g rd) =
      seatedJob (readers ∘ Local.thru g rd) rows lay addrs segs stAt pub := rfl

/-- **The lot with the closings alone is natural in its reader of the input.** -/
theorem seatLotC_through (g : W₀' → W₀) (rd : Rc' → Rc) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : Pub) (G : Ground) :
    ((seatLotC (X := X) readers rows stAt).thru (Local.thru g rd) (Local.thru g rd)).halves Z G =
      (seatLotC (X := X) (readers ∘ Local.thru g rd) rows stAt).halves Z G := by
  show ((seatLotC (X := X) readers rows stAt).halves Z G).map
      (Placed.thru (Local.thru g rd) (Local.thru g rd)) = _
  rw [seatLotC_halves, seatLotC_halves, List.map_map]
  refine List.map_congr_left fun Q _ => ?_
  show (⟨closePlace Q, [Part.thru (Local.thru g rd) (Local.thru g rd) (closePart (foldShellT true
      (seatedJob readers rows G.first.layout (addrsAt Z G) ((segmentsOf Z G).take (Q.link + 1)) stAt
        ⟨Q, borneAt Z Q⟩) foldWords))]⟩ : Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
    ⟨closePlace Q, [closePart (foldShellT true
      (seatedJob (readers ∘ Local.thru g rd) rows G.first.layout (addrsAt Z G)
        ((segmentsOf Z G).take (Q.link + 1)) stAt ⟨Q, borneAt Z Q⟩) foldWords)]⟩
  rw [closePart_through, foldShell_through, seatedJob_through]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closeBat_through
#print axioms ProofFile.Honest.K10.foldShell_through
#print axioms ProofFile.Honest.K10.andThen_through
#print axioms ProofFile.Honest.K10.closePart_through
#print axioms ProofFile.Honest.K10.seatedJob_through
#print axioms ProofFile.Honest.K10.seatLotC_through
