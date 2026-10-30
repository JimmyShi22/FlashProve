-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopJoint.lean: THE JOINT BETWEEN THE TABLE OF JOINTS' FIRST RELATION AND THE RULES FOR
A PROOF FILE. One theorem. NO RESULT ON THE PROTOCOL.

What is said. The table's first relation is the integer model's `firstMeans` at what the witness
hides (`firstAt`, Johnson/P5J/MeansQ.lean). Both roads to the proof file's named hypothesis on
soundness ask, at the first border, the object's relation at the request with the witness's token
put in (`firstRel`, Johnson/Flat/TiesSheet.lean). `firstRel_of_firstAt`: **`firstAt` gives
`firstRel`**, at the full size's frame (`kcReq N pp E`), by
`frameRel_of_firstMeans` and `inRange_of_letters` (Johnson/Goal/Meaning/Row.lean); under two
    equations on the
letters: what H.dec and H.req read off the chain's statement are the decoder's value and the
request. (The statement also takes hR, h and A : Hd.PublicCore X.P.)
`colsAt`: the committed matrix's number of columns: so that H.dec's type is the decoder's.

Limits: H (hid, dec, req) is a letter; LS (what the layers' 24 sub-proofs say) is a premise here: a
theorem (`layersSay`, Johnson/Goal/Meaning/LayersSay.lean), not imported. It is spent in
Johnson/P5J/TopMeans.lean (the road with extractors) and TopPlain.lean (the plain road). Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MeansQ
import Johnson.Flat.ProofOfData

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.Sound
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ

/-- The number of columns of the committed matrix at the full size's frame. -/
abbrev colsAt (N : MatrixNums) : ℕ := 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v)

/-- **THE JOINT: the table's first relation, which is the integer model's `firstMeans`, gives the
first relation that the rule for a proof file asks (`firstRel`)**, at the full size's frame. a: a
statement of the first chain; b: the file's statement. hd, hp: what the table's two readers read off
the chain's first record are the decoder's value and the request's public part. -/
theorem firstRel_of_firstAt (LS : LayersSay) {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
    {P W S₁ : Type} {all : List LeftT} (H : HidAt X P W N.rows (colsAt N)) (ft : ℕ)
    (get : S₁ → P × TS) (a : S₁ × (EAll (DP.at frS.P.T.a) all).Str) (w : W)
    (b : ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec) ×
      (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (hd : H.dec (get a.1)
      (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) a.2) =
      (kcReq N pp E).conf.D b.2 b.1.2)
    (hp : H.req (get a.1) = b.1.1)
    (hw : firstAt (D := DP.at frS.P.T.a) (all := all) pp putReq H ft get a w) :
    firstRel (kcReq N pp E) DP putReq (fun w => (H.hid w).tok) (fun _ => ()) b w := by
  intro M hM
  unfold firstAt at hw
  rw [hd, hp] at hw
  exact frameRel_of_firstMeans LS hR h A hw M hM
    (inRange_of_letters (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DP b.2 b.1.2 M
      hM)

#print axioms firstRel_of_firstAt

end P5J
