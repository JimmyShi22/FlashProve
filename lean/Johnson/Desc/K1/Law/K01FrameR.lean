-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01FrameR.lean: THE KIND K1's SHARE IN THE SECOND FORM OF THE CHAIN OF PROMISES, FROM THE TIES OF ITS 52 PIECES: k01_law_frame's like (K01LawTied.lean) with TiedAtR in TiedAt's place: the kind's places are the fifty later sendings, link 0's first sending (2) and W's
commitment (356): k01_places_full [kernel]. The end is KindTiedR … KindName.K1, unfolded: its text is written out.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf)
open ProofFile (Cl)
open IM (k1Ix)

variable {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
variable {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}

theorem k01_law_frameR (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (HL : ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + k1Ix l d + 2)
        (q.withMap (E (14 * l + k1Ix l d + 2))))
    (H0 : ∀ q, (T.p₁ :: T.l₁)[2]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 2 (q.withMap (E 2)))
    (HW : ∀ q, (T.p₁ :: T.l₁)[356]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 356 (q.withMap (E 356))) :
    ∀ i q a, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf linksFull true)[i]? = some a →
      a.kind = KindName.K1 → TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch i (q.withMap (E i)) := by
  intro i q a hq ha hk
  rcases k01_places_full i a ha hk with ⟨l, hl, d, rfl, -⟩ | h | h
  · exact HL l hl d q hq
  · subst h
    exact H0 q hq
  · rw [wNo_eq] at h
    subst h
    exact HW q hq

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_law_frameR
