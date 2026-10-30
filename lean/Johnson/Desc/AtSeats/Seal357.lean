-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.Road
import Johnson.Desc.K13.Law.AtTableSeal
/-
THE SEAL's TIE AT THE PROOF FILE's WRITTEN DESCRIPTION, IN THE FORM THAT THE JOIN OF THE KIND «frame» ASKS: number 357 of
358, place ⟨1, none, 5, frame⟩. From K13_sits at the seal (k13_sits_flat357: no premise), the tie at the table firstEnd_tied_seat
(Johnson/Desc/K13/Law/AtTableSeal.lean: at any block UnderR First.firstEnd, at every z, AT ANY LETTERS OF THE PIECE) and the road.
WHAT IS ASKED OF N AND Mg: RowSeal · FillSeal: that tie's own two premises, unturned. NO SOUNDNESS.
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

/-- **The seal is tied.** -/
theorem seal_tied357 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[357]? = some q) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (p : Place)
    (hRow : RowSeal N Mg.more linksFull (flatPlacesOf linksFull true) 357 p)
    (hF : FillSeal N Mg q.base (openAt linksFull (flatPlacesOf linksFull true) 357)
      fun i => openAfter (insQ linksFull (flatPlacesOf linksFull true))
          (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull) 357 i ∧
        ¬ insQ linksFull (flatPlacesOf linksFull true) 357 i) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 357 (q.withMap E) := by
  obtain ⟨e, hflat, _, hu⟩ := k13_sits_flat357 hS hR O
  have hu' : e.UnderR (First.firstEnd 5 ([] : List (Block S Cl))) :=
    hu.trans ⟨rfl, fun _ _ _ _ h => h⟩
  exact tiedAt_of_seatTie hT hflat hq linksFull _ N Mg E hE
    (fun c' => (pieceSeal (W := W) _ 5 [] q.base q.ds q.back q.err).seat c') (fun _ => rfl)
    fun z => firstEnd_tied_seat _ 5 [] q.base q.ds q.back q.err (below e) (below_underR hu') z N Mg
      linksFull _ 357 p hRow hF

end VerifiableInference.Desc.K13.Law
