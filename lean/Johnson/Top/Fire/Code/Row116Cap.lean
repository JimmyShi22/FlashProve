-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Cap.lean: THE KEY FILE's ROW 1.16: ITS LAST DEBT hle (the law's errors are at most the maker's rest's), CUT INTO WHAT IS THIS FILE's AND WHAT IS LEFT TO THE KIND K13's FILES.
  (pairs_of_as HAS MOVED, not a sign turned, to RowStretch.lean)
  stretch116_as     the maker's stretch at block 16 stands in RoundAsG to K13.battRounds (where116 X): AT EVERY X N P (what public_of_data spends, handed out)
  stretch116_pairs  **THIS FILE's HALF, PAID AT EVERY X N P**: the stretch's (entry, kind) pairs ARE those of the kind's own twenty-odd rounds at the seat's numbers: no test, no evaluation
  BelowAt116        THE OTHER HALF, LEFT TO THE KIND's FILES, AS A NAMED PREMISE: at every stretch with these pairs the law's errors errK rows k are shares of at most 2⁻¹ ^ 128. (It is held at the key file's WRITTEN rounds and numbers by Lean's kernel: k13_rounds_key | k13_at_cap_key: Johnson/Goal/Numbers/K13RoundsAt.lean | K13CapAt.lean: the stretch there is tied to the written list dryKeyFull.1 from 18828 on: that this list's pairs are these, at keyFull's numbers, is one closed fact: key_batt.)
  (Where this and lean/THEOREM.md differ, the page holds.)
  hle_of            hle FROM: AtCap rest₁ (capRest, KeyPublicAtSeat.lean, has it by rfl) · BelowAt116 · the five public premises: by Err.le_cap_of_below_inv (Iop/ErrCap.lean)
  k13_called_116    **THE CALL**: the kind K13's law CALLED at the key file's own block 16, at the key's own lens, over FirstState, with no letter of the law left; and the number, from BelowAt116
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Whole
import Johnson.Desc.Sound.BoundsAtCap

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
open Johnson.RunOne.KeyRows23 (CellOnly)

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


theorem stretch116_as (x₀ x₁ : Lookup) (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    List.Forall₂ RoundAsG (cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16) (K13.battRounds (where116 X)) := by
  have hlong := long_of X N P c₁ k₁ x₀ x₁ hl bw hw q₁
  obtain ⟨bn, hbn⟩ : ∃ bn, (c₁ :: k₁)[16]? = some bn := ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons]; omega)⟩
  have hb : bn = seat116 X := block16 (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bn (by rw [← q₁] at hbn; exact hbn)
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal (Fk X N P) hs c₁ k₁ q₁) 16 hlong bn hbn
  rw [hb] at has
  have hr : (seat116 X).rounds = K13.battRounds (where116 X) := seat_rounds _ _ _ _
  rw [hr] at has
  rw [cutDs_held k₁ 16 _ c₁]
  exact has

/-- **This file's half.** -/
theorem stretch116_pairs (x₀ x₁ : Lookup) (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    (cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16).map (fun d => (d.entry, some d.kind)) =
      (K13.battRounds (where116 X)).map (fun r => (r.entry, Fmt.kindOf r.entry.name)) :=
  pairs_of_as _ _ (stretch116_as X N P DK c₁ k₁ x₀ x₁ bw q₁ hl hw hs hdata)

/-- **The other half, left to the kind K13's files**: at every stretch with the kind's own pairs at the seat's numbers the law's errors are shares of at most 2⁻¹ ^ 128. -/
def BelowAt116 : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, some d.kind)) = (K13.battRounds (where116 X)).map (fun r => (r.entry, Fmt.kindOf r.entry.name)) →
    Err.Below ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem hle_of (x₀ x₁ : Lookup) (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁) (hB : BelowAt116 X) :
    ∀ dZ d0 ds, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds →
      Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err := by
  intro dZ d0 ds hst
  have hp := stretch116_pairs X N P DK c₁ k₁ x₀ x₁ bw q₁ hl hw hs hdata
  rw [hst] at hp
  rw [hcap 16 (dZ :: d0 :: ds)]
  exact Err.le_cap_of_below_inv 128 _ (hB dZ d0 ds hp)

/-- **THE CALL, WHOLE: THE KEY's K13 INSTANCE AT THE KEY's OWN LENS**, in the form of K13Called (Johnson/Goal/Numbers/K13CalledAt.lean), but OVER FirstState, at Key.descriptionFromSource X N P's own block 16, AND WITH NO LETTER OF THE LAW LEFT: there are the stretch's rounds dZ d0 ds, which ARE the maker's stretch at block 16, such that the piece of the held seat at the law's own errors is GoodIn from the tables' promise at 16 to that at 17, at the tables' own relations; and its errors are shares of at most 2⁻¹ ^ 128. FROM: the premises of r1_16_whole, with the base outright in hb₁'s place and AtCap rest₁ · BelowAt116 in hle's. (AtCap is taken because Owed116, which good116_of takes whole, bears the field «le»; GoodIn itself does not spend it.) -/
theorem k13_called_116 (x₀ x₁ : Lookup) (bw : Block FirstState Claim) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hbase : (at_ 0).1 < cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hst : (oneAt X).ranges.stages.length ≤ noId) (HP : PubPile (oneAt X)) (hsame : R.same = sameGl)
    (hcap : AtCap rest₁) (hB : BelowAt116 X) :
    ∃ dZ d0 ds, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds ∧
      (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).GoodIn (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16) (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17)
        (R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 16) (R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 17) ∧
      Err.Below ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hcoll : CollCell coll := fun y y' r e => (hc y y' r e).1
  obtain ⟨dZ, d0, ds, hst', hD, hk⟩ := public_of_data X N P DK c₁ k₁ x₀ x₁ bw q₁ hl hw hs hdata
  have hle := hle_of X N P DK c₁ k₁ rest₁ x₀ x₁ bw q₁ hl hw hs hdata hcap hB dZ d0 ds hst'
  have W := weight116_of X N P DK c₁ k₁ rest₁ B at_ R coll hsame dZ d0 ds hle
  have HS := seatFacts116_paid X N P DK B at_ R coll hG hst HP
  have hp := stretch116_pairs X N P DK c₁ k₁ x₀ x₁ bw q₁ hl hw hs hdata
  rw [hst'] at hp
  exact ⟨dZ, d0, ds, hst', good116_of X N P DK c₁ k₁ rest₁ B at_ R coll x₀ x₁ dZ d0 ds (rw116 X R)
    { hl := hl, long := long_of X N P c₁ k₁ x₀ x₁ hl bw hw q₁, stretch := hst', declared := hD, len := hk, det := W.det
      back := back_of X N P DK c₁ k₁ B at_ R coll dZ d0 ds HS hbase, stays := stays_of X N P DK c₁ k₁ B at_ R coll dZ d0 ds HS hcoll hbase
      pileGives := W.pileGives, givesClaims := W.givesClaims, le := W.le }, hB dZ d0 ds hp⟩

end

end LPFD

#print axioms LPFD.k13_called_116
#print axioms LPFD.stretch116_pairs
#print axioms LPFD.hle_of
