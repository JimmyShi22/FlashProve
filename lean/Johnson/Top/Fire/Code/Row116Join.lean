-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Join.lean: THE KEY FILE's ROW 1.16: THE JOIN: BelowAt116 X, THE KIND's HALF OF THE ROW's LAST DEBT OF NUMBERS (hle), DERIVED AT where116 X FROM THREE FACTS (Goal/Numbers/K13CapAt.lean: k13_at_cap_key · key_batt · key_pending_loop) BY where116's THREE EQUATIONS: lin: a premise here (in scope by one_full) · rows: batchWhere writes the count as sumT over the lookups' parts: key_pending_loop, at the ranges' equation · work: the structure's default: rfl.
  pair_inj          (x.1, some x.2) is injective
  belowAt116_full   **PROVED**: (oneAt X).ranges = keyFull.ranges.x → (oneAt X).lin = keyFull.once.shape → BelowAt116 X
  r1_16_scope       the field r1_16 with three premises of r1_16_whole paid from these two equations: hst · PubPile (pub_of_full) · hle (hle_of at belowAt116_full); the others stay in front: q₁ · hl · hw · hc · hG · hb₁ · hs · hdata · hsame · hcap
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Cap
import Johnson.Top.Fire.Code.Row116PubFull
import Johnson.Goal.Numbers.K13CapAt

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

open Lk6.AtPlan (keyFull)

theorem pair_inj {α β : Type} : Function.Injective (fun x : α × β => (x.1, some x.2)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq, Option.some.injEq] at h
  exact Prod.ext h.1 h.2

/-- **THE JOIN.** -/
theorem belowAt116_full (X : Source) (h1 : (oneAt X).ranges = keyFull.ranges.x) (h2 : (oneAt X).lin = keyFull.once.shape) : BelowAt116 X := by
  intro dZ d0 ds hp
  have r : (where116 X).rows = keyFull.ranges.pending := by
    show OnBytes.sumT ((oneAt X).ranges.lookups.map (·.parts.length)) = _
    rw [h1]
    exact K13.Law.key_pending_loop
  have l : (where116 X).lin = keyFull.once.shape := h2
  have w : (where116 X).work = (0, 0, 0) := rfl
  have e : ((dZ :: d0 :: ds).map (fun d : RDT => (d.entry, d.kind))).map (fun x => (x.1, some x.2)) =
      (K13.Law.stretch Johnson.G.dryKeyFull.1 18828 20).map (fun x => (x.1, some x.2)) := by
    rw [List.map_map]
    exact hp.trans (K13.Law.key_batt (where116 X) r l w).symm
  have e' := List.map_injective_iff.2 pair_inj e
  have hk : 2 + (where116 X).lin.kCol = 20 := by rw [l, K13.Law.key_pending.2.2]
  exact (K13.Law.k13_at_cap_key (where116 X) r l w dZ d0 ds (by rw [hk]; exact e')).2.1

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



/-- **The field r1_16, with hst, PubPile and hle paid from the two equations in scope.** -/
theorem r1_16_scope (x₀ x₁ : Lookup) (bw : Block FirstState Claim)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[16]? = some p → ∀ j ∈ pinned (open₁ 2 16), (at_ j).1 < p.base)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hsame : R.same = sameGl) (hcap : AtCap rest₁)
    (h1 : (oneAt X).ranges = keyFull.ranges.x) (h2 : (oneAt X).lin = keyFull.once.shape) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16 :=
  r1_16_whole X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll x₀ x₁ bw q₁ hl hw hc hG hb₁ hs hdata
    (pub_of_full (oneAt X) h1 h2).1 (pub_of_full (oneAt X) h1 h2).2 hsame
    (hle_of X N P DK c₁ k₁ rest₁ x₀ x₁ bw q₁ hl hw hs hdata hcap (belowAt116_full X h1 h2))

end

end LPFD

#print axioms LPFD.belowAt116_full
#print axioms LPFD.r1_16_scope
