-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SeatLotC.lean: the closing of a segment (K10): the lot's honest side with the closings
alone: `seatLotT` (Honest/K10/SeatLotT.lean) without K9's own halves. One definition with code; four short lemmas.
`closeLotAt` (Honest/AtPureWiderK10.lean) lays its halves, where the library's first chain at Z is
made (else no side), as the eleventh list of `widerFillOwnC`.

Why. The sealed lot that lays K9's members lays K10's closings too, so an honest lot for the closings bears that lot's
name. `seatLotT` is `K9.batLot` at the closings: it lays a half at each of K9's batchings beside them. A filling that is
to have no side at K9's places wants the closings alone.

  `seatLotC readers rows stAt`   the lot: the sealed lot's name; its halves are `seatClosings …` at the cured, total
                   part
  `seatLotC_name`      its name is the sealed lot's own (`k9Ninth Z`)
  `seatLotC_halves`    its halves, written out: `closingsT_are`'s right side
  `seatLotT_is`        `seatLotT`'s halves are K9's own, then `seatLotC`'s
  `seatLotC_kinds`     every half of it stands at a place of the kind K10

Limits. stAt is a letter: which filler may be laid is not said here (Honest/K10/StAt.lean and StAtZero.lean have the
rulings). The laws on the lot's places (Honest/K10/LotPlaces.lean, LotAll.lean) speak of the closings' halves and of
`seatLotT`'s whole list; none is restated here. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SeatLotT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (KindName)
open ProofFile.Honest.K2 (segmentsOf)

variable {W₀ Rc Xi Tr X : Type}

/-- **The lot's honest side with the closings alone.** -/
def seatLotC (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := (K9.batLot (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (X := X) fun _ _ => []).name
    halves := fun Z g => seatClosings (closeIn readers rows stAt) borneAt (foldAtT Z g) Z g }

/-- The name is the sealed lot's own. -/
theorem seatLotC_name (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : Pub) :
    (seatLotC (X := X) readers rows stAt).name = (k9Ninth Z).name := rfl

/-- Its halves, written out. -/
theorem seatLotC_halves (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : Pub)
    (G : Ground) :
    (seatLotC (X := X) readers rows stAt).halves Z G =
      (closePars Z).map fun P =>
        closeHalf (fun pub => foldShellT true (seatedJob readers rows G.first.layout (addrsAt Z G)
          ((segmentsOf Z G).take (pub.par.link + 1)) stAt pub) foldWords) ⟨P, borneAt Z P⟩ :=
  closingsT_are readers rows stAt Z G

/-- `seatLotT`'s halves are K9's own, then these. -/
theorem seatLotT_is (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : Pub)
    (G : Ground) :
    (seatLotT (X := X) readers rows stAt).halves Z G =
      K9.batHalves Z ++ (seatLotC (X := X) readers rows stAt).halves Z G := rfl

/-- Every half of it stands at a place of the kind K10. -/
theorem seatLotC_kinds (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : Pub)
    (G : Ground) : ∀ x ∈ (seatLotC (X := X) readers rows stAt).halves Z G, x.place.kind = KindName.K10 := by
  intro x hx
  rw [seatLotC_halves] at hx
  obtain ⟨P, -, rfl⟩ := List.mem_map.1 hx
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatLotC
#print axioms ProofFile.Honest.K10.seatLotC_name
#print axioms ProofFile.Honest.K10.seatLotC_halves
#print axioms ProofFile.Honest.K10.seatLotT_is
#print axioms ProofFile.Honest.K10.seatLotC_kinds
