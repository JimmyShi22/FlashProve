-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtBase.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE TABLES' READING, SEATS AND READER WRITTEN TERMS, NOT LETTERS.
Main names.
  `baseAt X decT recOf`: the tables' one reading: `baseK` (Johnson/RunOne/KeyFillSeed.lean) at the written codes, the six real messages, their numbers and seats, and the first chain's own plan's numbers. `readAt tab`: the tables' reader of the witness: `kreadFam` (Johnson/RunOne/KeyFillBaseAt.lean) at the same. The seats are `atSix` (typed by hand there).
  `FirstFour`: what is left of `FirstLeft` (KeyPublicAtSeat.lean) when arr and reads are paid: recAt · coll · dec · held, word for word.
  `The21AtBase A E X N P DK`: `The21Handed` with B := `baseAt`, at_ := `atSix`, R := `readAt`: beside the 21 laws: off · FirstFour · CellOnly coll · the four bases.
  `atSix_in_scope`: in scope the six seats are 0 · 1 · `treeOfW` (the number that the description's own table of what is owed names for W's tree) and the three numbers behind it [one fact of the kernel's at the written key]; that these three are the shared chain's trees is a reading, shown nowhere.
  `handed_of_base`: it gives `The21Handed`: orc by rfl; arr twice, reads twice and ReadsL by theorems of Johnson/RunOne/KeyFillBaseAt.lean and KeyFillSeed.lean (arrOk_six₁ · arrOk_six₂ · readsPinned_fam · readsLK): called.
OBJECT: `Key.descriptionFromSource X N P` · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: A · E; under the ∃: Cells · Rec · decT · recOf · tab · enc · rad · coll · off₂ · off₃ · ρ · cellsOf.
Limits. NO LAW IS PAID. Each of the 21 laws is owed AT THESE TERMS: a law that needs another reading has no place here; `The21Handed` stays beside. (Where
this and lean/THEOREM.md differ, the page holds.) `atSix` is the full size's. That the description's trees lie at these seats is shown here only so far as `atSix_in_scope` goes: against the table `owed`, which the payer's `owedOk` holds against the blocks' own lists; the four bases ask more. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.KeyFillSeed
import Johnson.RunOne.KeyFillBaseAt

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
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (baseK kreadFam atSix numSix arrOk_six₁ arrOk_six₂ readsPinned_fam readsLK)

/-- **The tables' one reading, written.** -/
abbrev baseAt {Cells Rec : Type} (X : Source) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) :
    BaseSt Cells Fill.Tab (Σ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Smp) Rec :=
  baseK Johnson.Top.H.csKey six numSix atSix decT recOf (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc

/-- **The tables' reader of the witness, written.** -/
abbrev readAt {Cells : Type} (tab : Cells → ℕ → ℕ → OnBytes.F) : KRead Cells Fill.Tab := kreadFam Johnson.Top.H.csKey six numSix atSix tab

section
variable {Cells M Smp Rec : Type} (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec)
  (one : OnBytes.Params.OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)
  {RecT Y U I : Type} (inst : RecT → Xi) (s₀ : Xi → FirstState) (str : Y → Fr.E.Str) (ρ : RecT → Rec)
  (collT : Y → RecT → Prop) (dcdT : Y → RecT → Option U) (heldT : U → Option I) (cellsOf : U → Cells)

/-- **What is left of `FirstLeft`** when arr and reads are paid: four fields, word for word. -/
structure FirstFour : Prop where
  recAt : ∀ r, G.recOf (inst r, s₀ (inst r)) = some (ρ r)
  coll : ∀ r y, coll (strsOf Fr (str y)) (ρ r) → collT y r
  dec : ∀ r y c, G.decT (strsOf Fr (str y)).cell (ρ r) = some c → ∃ u, dcdT y r = some u ∧ cellsOf u = c
  held : ∀ r y u, dcdT y r = some u → (∀ l, l < Johnson.RunOne.KeyRows1.n₁ one → ∃ L, (Johnson.RunOne.KeyRows1.plan₁ one).lookups[l]? = some L ∧ InRange R.same (Johnson.RunOne.KeyRows1.plan₁ one).m L (matAt (Johnson.RunOne.KeyRows1.plan₁ one).lin (R.tab (cellsOf u)))) → (heldT u).isSome

end

/-- **WHAT IS OWED, AT THE WRITTEN READING, SEATS AND READER.** -/
def The21AtBase {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (Cells Rec : Type) (_ : Inhabited Cells)
      (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (tab : Cells → ℕ → ℕ → OnBytes.F)
      (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)
      (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decT recOf) atSix (readAt tab) enc rad coll off₂ off₃ ∧
      (∀ k ∈ [0, 2], off₃ (atSix k).1 = (atSix k).1) ∧
      FirstFour (fr₁ (DK.at frS.P.T.a)) (baseAt X decT recOf).h₁ (oneAt X) (readAt tab) coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
        (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
        (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf ∧
      CellOnly coll ∧
      (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[0]? = some p → ∀ j ∈ pinned seam, (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (atSix j).1 < p.base)

/-- **It gives what is owed at letters**: six fields are paid by the filling's own theorems. -/
theorem handed_of_base {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (h : The21AtBase A E X N P DK) : The21Handed A E X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  obtain ⟨Cells, Rec, iC, decT, recOf, tab, enc, rad, coll, off₂, off₃, ρ, cellsOf, dS, H, off, ff, hc, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩ :=
    h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  exact ⟨Cells, Fill.Tab, _, Rec, iC, ⟨fun _ _ => 0⟩, baseAt X decT recOf, atSix, readAt tab, enc, rad, coll, off₂, off₃, ρ, cellsOf, dS, H, rfl,
    arrOk_six₂ _ decT recOf _, (readsPinned_fam Johnson.Top.H.csKey six numSix atSix _ decT recOf _ tab [3, 4, 5]).2.1, off,
    ⟨ff.recAt, arrOk_six₁ _ decT recOf _, (readsPinned_fam Johnson.Top.H.csKey six numSix atSix _ decT recOf _ tab [0, 1, 2]).1, ff.coll, ff.dec, ff.held⟩,
    hc, readsLK Johnson.Top.H.csKey six numSix atSix decT recOf _, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩

theorem treeW_full (one : OnBytes.Params.OneTime) (h : one.ranges = keyFull.ranges.x) : treeOfW one = 5 := by
  unfold treeOfW
  rw [h]
  decide +kernel

/-- **The six seats against the description's own table of what is owed** (Johnson/Desc/Key/WantedLater.lean): in scope, at any digest: messages 0 and 1 sit at the first chain's trees 0 and 1 (`owedFirst`'s), W at `treeOfW`, the number that `owedShared` | `owedSecond` name for W's tree, and three numbers behind it, in a row. THAT THE SHARED CHAIN's TREE n IS THE FILE's TREE `treeOfW` + 1 + n IS A READING: it is shown nowhere. -/
theorem atSix_in_scope {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    atSix 0 = (0, 0) ∧ atSix 1 = (1, 0) ∧ atSix 2 = (treeOfW (oneAt X), 0) ∧ atSix 3 = (treeOfW (oneAt X) + 1, 0) ∧
      atSix 4 = (treeOfW (oneAt X) + 2, 0) ∧ atSix 5 = (treeOfW (oneAt X) + 3, 0) := by
  rw [treeW_full _ (one_full hZ hP hm hX hp).1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end LPFD

#print axioms LPFD.treeW_full
#print axioms LPFD.atSix_in_scope
#print axioms LPFD.FirstFour
#print axioms LPFD.The21AtBase
#print axioms LPFD.handed_of_base
