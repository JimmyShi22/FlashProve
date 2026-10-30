-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsAny.lean: from a seat to the table's tie, whatever the kind. One theorem, a
joining: what Johnson/P5K3R/SitsTied.lean does for the kind "lookup", without the kind.

Why. For each kind that the proof file's written description seats alone at a place, the
files of Johnson/IMR/ show: the entry of the first chain's flat list is the lot's block
under the seat's wrappers (`IM.LaidAlone`). The step from there to the tie that the chain of
promises asks is the same for every such kind. Here it is typed once.

Main names:
  `tied_of_alone`: for three rows of pieces that hold the blocks of the description made of the
    first chain c: where entry k of c's flat list is b, b is the block b' under the seat's wrappers
    alone at an address that is not of the kind K7, and q is the piece at k of the first row: if
    `SeatLaws` holds at b' and the table's extractor lays nothing at this row, then q, with that
    extractor, is tied at the table's own words.

Limits: it serves the rows that lay nothing, and the blocks that are seated alone (no block joined
behind). K7's address is left out: there the guard on the reply's seat leaves the decision free, and
the lemma on a yes has another form (`IM.yes_alone_K7`). `SeatLaws` is a premise. Nothing on
soundness; nothing on hiding.


-/
import Johnson.P5K3R.SitsTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)
open ProofFile (Cl)

/-- **A block that is seated alone is tied at the table, where its kind's four (`SeatLaws`) hold at
the lot's block.** -/
theorem tied_of_alone {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat}
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) {k : ℕ} {b b' : Block S Cl} {name : String} {a : Place}
    (hflat : c.blocksInOrder[k]? = some b) (hA : IM.LaidAlone ProofFile.sameReply b b' name a)
    (hk : a.kind ≠ KindName.K7)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (H : SeatLaws links ps k q N Mg b') :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (onQ N Mg links ps (fun a => a) k)
      (onQ N Mg links ps (fun a => a) (k + 1)) (relAt (meansQ N Mg fun a => a) (insQ links ps k))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps k)) := by
  exact tiedBy_of_seatLaws links ps k b' b q
    ⟨IM.alone_underR hA, fun s rs gs t hy => ((IM.yes_alone hA hk s t rs gs).1 hy).2.1⟩
    (OfDesc.pieceAt hT hq hflat) N Mg E hE H

end K3Lot
