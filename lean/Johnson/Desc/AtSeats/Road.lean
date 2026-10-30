-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13SitsSealed
import Johnson.Desc.Sound.TiedLift
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.MergeNarrow
/-
THE ROAD FROM A KIND's TIE AT THE TABLE TO THE TIE OF THE DESCRIPTION's OWN PIECE, KIND-FREE. By tiedBy_of_part
(Johnson/Desc/Sound/TiedLift.lean), below_narrows (MergeNarrow.lean) and OfDesc.pieceAt (AtDriver.lean). No SeatLaws. NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)

/-- **Kind-free: from a kind's tie to the description's piece.** -/
theorem tiedAt_of_seatTie {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) {k : ℕ} {e : Block S Cl} (hflat : c.blocksInOrder[k]? = some e)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c')
    (H : ∀ z : ProofFile.InstPub, TiedAt N Mg links ps (fun s : S => (z, s)) k (pc (below e))) :
    TiedAt N Mg links ps (fun a => a) k (q.withMap E) := by
  have H' : ∀ z : ProofFile.InstPub, TiedAt N Mg links ps (fun s : S => (z, s)) k
      (⟨below e, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) := fun z => by
    rw [hQ]
    exact H z
  choose o o' R R' h using H'
  exact (tiedBy_of_part N Mg links ps k q _ (OfDesc.pieceAt hT hq hflat) E hE o o' R R' h).tiedAt

/-- «below e» is under whatever e is under. -/
theorem below_underR {e Bst : Block S Cl} (hu : e.UnderR Bst) : (below e).UnderR Bst :=
  Block.UnderR.trans ⟨(below_narrows e).1, (below_narrows e).2⟩ hu


def k13AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K13 || (i == 355 && decide (a = ⟨1, none, 3, .K13⟩))
    | none => true

set_option maxRecDepth 1000000 in
theorem k13AllB_full : k13AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem k13_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K13) : i = 355 ∧ a = ⟨1, none, 3, .K13⟩ := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k13AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [hk] at h1
    exact absurd h1 (by decide)
  · obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h1
    exact ⟨by simpa using h5, of_decide_eq_true h6⟩


end VerifiableInference.Desc.K13.Law
