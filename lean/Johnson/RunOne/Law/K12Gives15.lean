-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Gives15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE FIELD «gives» OF THE STRUCTURE Left15JG, AT THE PROMISE THAT KEEPS THE HISTORY (OnH), AT THE TABLES' FILES' OWN FILLING (baseK · atSix · kreadFam): THE TWO HALVES JOINED. One statement; its proof is ONE TERM: gives_of_halvesH (K12Left15H.lean) at the laid table tbl15 (K12Law15At.lean), fed with fwd_15 (K12Fwd15.lean) and back_15_at (K12Back15.lean). IT MOVES THE WEIGHT INTO hfacts AND NAMED PUBLIC PREMISES; IT PAYS NONE.
OBJECT. gives_of_halvesH's conclusion: its text, cut by a program, with the filling's letters laid. THAT THE TERM TYPECHECKS IS THE CHECK BY LEAN THAT fwd_15's AND back_15_at's CONCLUSIONS ARE gives_of_halvesH's TWO PREMISES.
USER. Whoever fills Left15JG at the filling.
THE PREMISES, AND WHOSE EACH IS. On the list of rounds and the IOP as written in Lean (our files: the plan, the description): hpl · hft (the maker's literal 0: a caller has it from "N is the maker's") · hl · hn · hR · hans. The caller's letters: hoNo · hmem · hrd. Off the history, in their payers' own forms: hK · hseed. What the IOP as written in Lean tells of tree 1: hlog · told. On the tables' letter coll: hcoll. hbase: the trees of the pins open at border 15 (0 and 1) lie below the maker's base at piece 15. THE WEIGHT: hfacts: CoreFacts at every state in front at which the sub-protocol accepts.
PAID HERE BY CALLS: SmOnly at the filling (smOnlyK, Johnson/RunOne/KeyFillSmOnly.lean) · "the filling's numbering is the plan's" (rfl).
Limits. hfacts is shown of nothing here. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Fwd15
import Johnson.RunOne.Law.K12Back15
import Johnson.RunOne.KeyFillSmOnly

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

/-- **The field «gives» at row 1.15, at the filling: the two halves joined.** -/
theorem gives_15_at (dB : RDT) (dt : List RDT) (hpl : (descriptionFromSource X N P).planOk = true) (hft : N.nums.firstTree = 0) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (hR : VerifiableInference.Desc.K3.KeyLaw.RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape)
    (hans : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hrd : ∀ x m part i, rdT x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hK : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → OpenKinds a.2.d.st)
    (hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y)
    (hlog : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1)
    (told : ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true)
    (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (hfacts : ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2) →
      ∀ rs gs b, (held (Johnson.RunOne.Sound.bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b →
      CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) (nuOf (rangesParams N) nl t) rad (smpK oNo) mem (· = x₁) t a.2 a.1 (strsOf (FR DK) a.2))
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (hbase : ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (atSix k).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15)) :
    ∀ a τ b, (OnH X N P DK (BK X decT recOf) atSix (RK tab) coll) 15 a →
      (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
      (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
        (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) →
      (OnH X N P DK (BK X decT recOf) atSix (RK tab) coll) 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab)) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab)) 15 a) :=
  gives_of_halvesH X N P DK c₁ k₁ rest₁ (BK X decT recOf) atSix (RK tab) coll dB dt nl rad rd (tbl15 X N P DK oNo mem rdT) hbase
    (fwd_15 X N P DK (BK X decT recOf) atSix (RK tab) coll hpl hft hl
      (smOnlyK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) rfl hcoll)
    (back_15_at X N P DK decT recOf tab coll oNo mem rdT hpl hl hn hR hans
      (smOnlyK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) hoNo hmem hrd hK hseed hlog told nl rad rd hfacts)

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.gives_15_at
