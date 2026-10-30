-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/KindTiedRIs.lean: KindTiedR' (Johnson/P1K8R/TiedReach.lean) IS
KindTiedR (Johnson/Desc/Sound/TiedR.lean), BY THE MAKE: so K8's share of the chain of promises in
the form with Rch ENDS IN THE TABLE's OWN NAME, the one in which the counted laws end.
  kindTiedR_iff    KindTiedR' N Mg links ps Rch E l K ↔ KindTiedR N Mg links ps Rch E l K := Iff.rfl.
  k08_kindTiedR5   k08_kindTiedR's premises ⟹ KindTiedR … K8.
IT ALSO IMPORTS Johnson/Desc/Sound/TiedSeatR.lean BESIDE Johnson/Top/H0/TiedAtSeatR.lean (beneath `TiedReach`): that Lean loads the two together shows that they declare no name twice.
LIMITS. Those of `TiedReach`: Rch is a letter; K8OwesR is shown at no filling. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.TiedReach
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P1K8T

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open ProofFile (Cl)

/-- KindTiedR' is KindTiedR, by definition. -/
theorem kindTiedR_iff {Pp Cl' W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : ℕ → (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (Pp × S) Cl' W)) (K : KindName) :
    KindTiedR' N Mg links ps Rch E l K ↔ KindTiedR N Mg links ps Rch E l K := Iff.rfl

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, IN THE TABLE's OWN SECOND FORM.** -/
theorem k08_kindTiedR5 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
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
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w)
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8OwesR N Mg linksFull (flatPlacesOf linksFull true) Rch (ixOf l) q
        (ProofFile.k8ParW Z Bs.G₀ Xl l)) :
    KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁) KindName.K8 :=
  k08_kindTiedR hS hR O hT N Mg Rch E hE H

end P1K8T

#print axioms P1K8T.kindTiedR_iff
#print axioms P1K8T.k08_kindTiedR5
