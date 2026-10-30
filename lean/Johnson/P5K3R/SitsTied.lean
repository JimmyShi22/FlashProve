-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsTied.lean: the kind "lookup" at the table of joints, at the proof file's written
description: one theorem, a joining.

Why. The chain of promises asks of every block of the first chain a tie at the table's own words
(`TiedBy`). Owed by a kind's files: its row at a piece over the carried record that holds the strict
reading of any block that narrows the kind's own constant and whose yes bears no mark. Here that
form is carried to the piece that the rule for a file holds at each of the kind's fifty places.

Main names:
  `SeatLaws links ps k q N Mg Bst` (Johnson/Desc/Sound/TiedSeat.lean): the four things that a
    kind's files owe at a seat, in one sentence: the row's own law at the table; what rides, in the
    tie's fenced form; a mark stays; "decodes" rides. Each over every block B' that narrows Bst and
    whose yes bears no mark, and every value of the public part.
  `k03_tied`: at the letters that the walk through the maker hands out, in scope, for three rows of
    pieces that hold the description's blocks: for every link l below 25 and both lookups, at the
    number k := 14 l + i + 2: if `SeatLaws` holds at whatever block the kind's own text returns at
    the driver's address, and the table's extractor lays nothing at this row, then the piece at k,
    with that extractor, is tied at the table's own words.

Limits: a joining of rules. `SeatLaws` is a premise: it is shown here at no filling of the table's
meaning and at no place. The table's letters (the numbers, the meaning, the list of segments, the
list of places) are free. The rest as in Johnson/P5K3R/SitsPiece.lean. Nothing on soundness; nothing
on hiding.


-/
import Johnson.P5K3R.SitsPiece
import Johnson.Desc.Sound.TiedSeat

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

/-- **The kind's fifty pieces are tied at the table, where its four (`SeatLaws`) hold at the
constant.** -/
theorem k03_tied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (l : ℕ) (hl : l < 25) (digits : Bool)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + IM.k3Ix l digits + 2]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (H : ∀ b', VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W)
        Bs.G₀.W Z.first.codes Z.first.shape (IM.k3Place l digits) = some b' →
      SeatLaws links ps (14 * l + IM.k3Ix l digits + 2) q N Mg b') :
    TiedBy N Mg links ps (fun a => a) (14 * l + IM.k3Ix l digits + 2) (q.withMap E)
      (onQ N Mg links ps (fun a => a) (14 * l + IM.k3Ix l digits + 2))
      (onQ N Mg links ps (fun a => a) (14 * l + IM.k3Ix l digits + 2 + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps (14 * l + IM.k3Ix l digits + 2)))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps (14 * l + IM.k3Ix l digits + 2))) := by
  obtain ⟨b, b', h3, hqb, hn, hm⟩ := k03_piece hS hR O hT l hl digits hq
  exact tiedBy_of_seatLaws links ps _ b' b q ⟨hn, hm⟩ hqb N Mg E hE (H b' h3)

end K3Lot
