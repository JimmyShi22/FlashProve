-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Gives15Is.lean: ROW 1.15 OF THE KEY FILE's TABLES: gives_15_at (K12Gives15.lean) MEETS Gives15 (K12Facts15M.lean): the last premise of r1_15_scope_cap | r1_15_in_scope. One statement; its proof is one term.
OBJECT. Gives15 X N P DK c₁ k₁ rest₁ B at_ R on stageRad rd: the field «gives» of the structure Left15JG, at the numbering by label nlAt (rangesParams N) 0 and the radii fun s => stageRad s.st, under "the piece's declared rounds are dB :: dt".
USER. The last join at row 1.15.
  gives15_at_fill: at the tables' files' filling (BK · atSix · RK tab), at the promise that keeps the history (OnH), at the written proximity test's own radii (radRng). gives_15_at does not spend "the declared rounds are dB :: dt": it is the stronger.
THAT THE TERM TYPECHECKS IS THE CHECK BY LEAN THAT THE TWO FILES' STATEMENTS OF THE FIELD ARE ONE.
Limits. Its premises are gives_15_at's, with the two letters laid; hfacts is shown of nothing here. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Gives15
import Johnson.RunOne.Law.K12Facts15M
import Johnson.RunOne.Law.K12Facts15S

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
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
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

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

open Johnson.Pack
open Johnson.Top.H (csKey)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.RunOne.KeyRows23 (numSix atSix seatAt smOnlyK)
open Johnson.RunOne.KeyRows1 (plan₁)
open H2K.Pin (tabP)
open OnBytes.Means (OpenKinds)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open Johnson.RunOne.Law.K12Law15At Johnson.RunOne.Law.K12Back15

variable (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)
  (oNo : Mem → ℕ) (mem : ℕ → Option Mem)
  (rdT : (x : Mem) → ((sigOf csKey x.1.l).om x.2).Msg → Part → ℕ → GE)

/-- **The field «gives», in K12Facts15M.lean's form (Gives15), at the filling.** -/
theorem gives15_at_fill (hpl : (descriptionFromSource X N P).planOk = true) (hft : N.nums.firstTree = 0) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hR : VerifiableInference.Desc.K3.KeyLaw.RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape)
    (hans : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hK : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → OpenKinds a.2.d.st)
    (hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1)
    (told : ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true)
    (rd : ℕ → ℕ)
    (hfacts : ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) (fun s => K12Facts15.radRng s.st) rd) (t, a.2) →
      ∀ rs gs b, (held (Johnson.RunOne.Sound.bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b →
      CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) (fun s => K12Facts15.radRng s.st) (smpK oNo) mem (· = x₁) t a.2 a.1 (strsOf (FR DK) a.2))
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (hbase : ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (atSix k).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15)) :
    Gives15 X N P DK c₁ k₁ rest₁ (BK X decT recOf) atSix (RK tab) (OnH X N P DK (BK X decT recOf) atSix (RK tab) coll) K12Facts15.radRng rd :=
  fun dB dt _ => gives_15_at X N P DK c₁ k₁ rest₁ decT recOf tab coll oNo mem rdT dB dt hpl hft hl hn hR hans hoNo hmem hrd hK hseed
    hlog told (nlAt (rangesParams N) 0) (fun s => K12Facts15.radRng s.st) rd hfacts hcoll hbase

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.gives15_at_fill
