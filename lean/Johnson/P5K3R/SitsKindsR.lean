-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsKindsR.lean: the kind "lookup" (K3): ITS SHARE OF THE CHAIN OF PROMISES IN THE SECOND FORM
(`KindTiedR`, Johnson/Desc/Sound/TiedR.lean: "reached" in hand in each tie), at the IOP as written
in Lean for the proof file, in the goals' scope, at the full size's written lists.

Main name:
  `k03_kindTiedR`: where the kind's four hold in the second form (`SeatLawsR`) at the
    constant of each of the fifty places: `KindTiedR … KindName.K3`.

The first form's text (SitsKinds.lean: `k03_kindTied`) with `tiedByR_of_seatLawsR` in the place of
`tiedBy_of_seatLaws`: where the kind stands (`k03_places_full`) and that the piece holds the seated
sub-protocol (`k03_piece`) are called as they lie.

Limits: `SeatLawsR` at the fifty is a premise. N, Mg, Rch and E are letters. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.P5K3R.SitsKinds
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf)
open ProofFile (Cl)

/-- **The kind K3's share, second form.** -/
theorem k03_kindTiedR {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ l, l < 25 → ∀ d : Bool, ∀ a b w, E (14 * l + IM.k3Ix l d + 2) a b w = w)
    (H : ∀ l, l < 25 → ∀ (d : Bool) q, (T.p₁ :: T.l₁)[14 * l + IM.k3Ix l d + 2]? = some q →
      ∀ b', VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W)
          Bs.G₀.W Z.first.codes Z.first.shape (IM.k3Place l d) = some b' →
        SeatLawsR linksFull (flatPlacesOf linksFull true) (14 * l + IM.k3Ix l d + 2) q N Mg Rch
          b') :
    KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁) KindName.K3 := by
  intro i q a hq ha hk
  obtain ⟨l, hl, d, rfl, -⟩ := k03_places_full i a ha hk
  obtain ⟨b, b', h3, hqb, hn, hm⟩ := k03_piece hS hR O hT l hl d hq
  exact tiedByR_of_seatLawsR linksFull _ _ b' b q ⟨hn, hm⟩ hqb N Mg Rch (E _) (hE l hl d)
    (H l hl d q hq b' h3)

end K3Lot

#print axioms K3Lot.k03_kindTiedR
