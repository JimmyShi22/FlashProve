-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/HandsK10W.lean: K10's 25 OF THE 358 «Hands» IN THE LETTERS OF THE JOIN: AT ITS WRITTEN LISTS linksW | placesW | nAt, AT THE SEATED SUB-PROTOCOL, FROM JUST WHAT ITS FORM FlatCase.close (Johnson/IMR/FlatCases.lean) HAS IN HAND AT j = 1. Statements and proofs.
  lw_is · pw_is · na_is   LW = IM.linksW (BY THE KERNEL: LW maps IM.subAt over the 25 numbers, linksW maps IM.subW) · PW = IM.placesW · nA l = IM.nAt l. (CloseShare.lean's head had these «by reading».)
  k10_share_W       InScope P · readFiles P = .ok pp · IM.Open … · hb: ∀ l < 25, p, Q, k, b, x: (K9.closeOf p Q)[1]? = some x → LaidAlone ProofFile.sameReply b x.retype b.name (cAt l (subAt l) 1 k) →
                    IM.HandsR OutFence (N.withTold IM.placesW (toldC c)) IM.linksW IM.placesW (fun k s => ePubAt (pubAll D bs) moreAll IM.linksW IM.placesW k (z, s)) ft (14 * l + IM.nAt l + 4 + 1) b.
  k10_share_W_at    the same at every fence Fk that gives OutFence at K10's 25 numbers (IM.HandsR.weaker): so at «reached», once «at a reached state the index masks' message is a member of no group» lies.
LIMITS. HandsK10At.lean's stand: THE FENCE IS OWED; hb is a premise; D, bs, z, N are letters; the numbers are N.withTold placesW (toldC c), not a free N. FlatCases.lean itself is not imported (it has no object on this ground): that the premises here are FlatCase.close's own at j = 1 is by reading of its text. No soundness statement.

-/
import Johnson.LPFK10R.HandsK10At
import Johnson.IMR.WrittenList

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place Oracle KindName)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll ePubAt)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile (Cl)
open IM

theorem lw_is : LW = IM.linksW := by decide +kernel

theorem pw_is : PW = IM.placesW := by
  show VerifiableInference.Desc.First.flatPlacesOf LW true = _
  rw [lw_is]
  rfl

theorem na_is (l : Nat) : nA l = IM.nAt l := rfl

section
variable {Pz : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
  {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K10's 25 in the join's own letters, at the seated sub-protocol.** -/
theorem k10_share_W (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (D : PubData)
    (bs : Pub → Pz × S → Bool) (z : Pz) (hb : ∀ q (s s' : S), bs q (z, s') = bs q (z, s))
    (N : Numbers) (ft : Nat) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (k : KindName) (b : Block S Cl)
      (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      LaidAlone ProofFile.sameReply b x.retype b.name (cAt l (subAt l) 1 k) →
      IM.HandsR OutFence (N.withTold IM.placesW (toldC c)) IM.linksW IM.placesW
        (fun k s => ePubAt (pubAll D bs) moreAll IM.linksW IM.placesW k (z, s)) ft
        (14 * l + IM.nAt l + 4 + 1) b := by
  intro l hl p Q k b x ex hla
  have H := close_k10R_at hS hR O D bs z hb N ft l hl p Q x ex
  rw [pw_is, lw_is] at H
  exact IM.HandsR.under H (alone_underR hla)

/-- The same at every fence that gives the fence spent here. -/
theorem k10_share_W_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (D : PubData)
    (bs : Pub → Pz × S → Bool) (z : Pz) (hb : ∀ q (s s' : S), bs q (z, s') = bs q (z, s))
    (N : Numbers) (ft : Nat) (Fk : Nat → S → Prop)
    (hF : ∀ l < 25, ∀ s, Fk (14 * l + IM.nAt l + 4 + 1) s →
      ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (k : KindName) (b : Block S Cl)
      (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      LaidAlone ProofFile.sameReply b x.retype b.name (cAt l (subAt l) 1 k) →
      IM.HandsR Fk (N.withTold IM.placesW (toldC c)) IM.linksW IM.placesW
        (fun k s => ePubAt (pubAll D bs) moreAll IM.linksW IM.placesW k (z, s)) ft
        (14 * l + IM.nAt l + 4 + 1) b :=
  fun l hl p Q k b x ex hla =>
    IM.HandsR.weaker (hF l hl) (k10_share_W hS hR O D bs z hb N ft l hl p Q k b x ex hla)

end

end LPFK10

#print axioms LPFK10.lw_is
#print axioms LPFK10.pw_is
#print axioms LPFK10.k10_share_W
#print axioms LPFK10.k10_share_W_at
