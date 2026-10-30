-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Paid.lean: THE KEY FILE's ROW 1.16: THE PUBLIC THREE (stretch · declared · len) PAID BY A THEOREM AT EVERY X N P: the plain test stretch16B FALLS (no test, no evaluation).
  declared_of_as    rounds that stand in RoundAsG to the kind K13's own battRounds have the law's Declared, the stretch's form and the length (the three names' kinds by the kernel)
  (last_of_seal stands in RowStretch.lean)
  public_of_data    **stretch · declared · len, PAID**: from hdata · q₁ · hl · hw · sealLast: by RowStretch.stretch_of_data₁ (over roundsOfData) · block16 · seat_rounds
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Book
import Johnson.Top.Fire.Code.RowStretch
import Johnson.RunOne.KeyBattFacts
import Johnson.RunOne.KeyYes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1

theorem plain_of_kind {d : RDT} {nm : String} (h1 : Fmt.kindOf nm ≠ some .sealed) (h2 : Fmt.kindOf nm ≠ some .seeds) (h : Fmt.kindOf nm = some d.kind) : K13.Law.PlainKind d :=
  ⟨fun e => h1 (e ▸ h), fun e => h2 (e ▸ h)⟩

theorem declared_of_as (P : K13.Where) (st : List RDT) (h : List.Forall₂ RoundAsG st (K13.battRounds P)) :
    ∃ dZ d0 ds, st = dZ :: d0 :: ds ∧ K13.Law.Declared P dZ d0 ds ∧ ds.length = P.lin.kCol := by
  unfold K13.battRounds at h
  cases h with
  | cons hZ t =>
    cases t with
    | cons h0 t2 =>
      obtain ⟨e, ha⟩ := forall₂_replicate _ _ _ t2
      exact ⟨_, _, _, rfl, ⟨e.symm, ⟨hZ.1, plain_of_kind (nm := "BAT-sigma") (by decide) (by decide) hZ.2.1⟩, ⟨h0.1, plain_of_kind (nm := "PSC epsilon") (by decide) (by decide) h0.2.1⟩,
        fun d hd => ⟨(ha d hd).1, plain_of_kind (nm := "PSC round") (by decide) (by decide) (ha d hd).2.1⟩⟩, e⟩

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


/-- **stretch · declared · len, paid.** -/
theorem public_of_data (x₀ x₁ : Lookup) (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    ∃ dZ d0 ds, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds ∧
      K13.Law.Declared (where116 X) dZ d0 ds ∧ ds.length = (where116 X).lin.kCol := by
  have hlong := long_of X N P c₁ k₁ x₀ x₁ hl bw hw q₁
  obtain ⟨bn, hbn⟩ : ∃ bn, (c₁ :: k₁)[16]? = some bn := ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons]; omega)⟩
  have hb : bn = seat116 X := block16 (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bn (by rw [← q₁] at hbn; exact hbn)
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal (Fk X N P) hs c₁ k₁ q₁) 16 hlong bn hbn
  rw [hb] at has
  have hr : (seat116 X).rounds = K13.battRounds (where116 X) := seat_rounds _ _ _ _
  rw [hr] at has
  obtain ⟨dZ, d0, ds, e, hD, hk⟩ := declared_of_as _ _ has
  exact ⟨dZ, d0, ds, (cutDs_held k₁ 16 _ c₁).trans e, hD, hk⟩

end

end LPFD

#print axioms LPFD.declared_of_as
#print axioms LPFD.public_of_data
