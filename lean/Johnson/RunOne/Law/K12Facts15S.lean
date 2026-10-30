-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15S.lean (the radii are the written test's own): ROW 1.15 OF THE KEY FILE's TABLES AT THE FULL SIZE: NO FACT ON THE DESCRIPTION OR THE PLAN IS A PREMISE BUT SCOPE's EQUATIONS. Statements with proofs; five evaluations in the kernel, two of them controls. IT PAYS NO FIELD OF THE TABLES: Gives15 HOLDS ALL THE WEIGHT AND IS SHOWN OF NOTHING. (Where this and lean/THEOREM.md differ, the page holds.)
OBJECT. `LPFD.The21`'s field r1_15 at the written data of a key file of full size and the planner's radii.
USER. The21's filler in the goals' scope.
LETTERS. The35.lean's; m. THE PREMISES hX hN hp data hDK hk hL ARE OTHERS' CONCLUSIONS IN SCOPE, proved elsewhere; here they stand as equations: the source and the place's numbers are made of m · the description passes its test on the plan · its data are DK's at the frame's depth · DK is the written data · the sized key is the written value · the first chain's nineteen blocks have the written numbers of rounds.

  no_bat_full, no_bat_full_no: by the kernel: none of the written data's first 18805 rounds bears the batching's name; among the first 18806 one does.
  front_len: the rounds that the first n blocks declare, counted off the list of the blocks' numbers of rounds.
  hno_scope: the test on the data that Johnson/RunOne/Law/K12Facts15B.lean's free_of takes, at the written data.
  stagesFull: the place's stages at the written value. testRng: the first of the nine written tests. radRng: the radius of each stage: that test's own, looked up by the stage's nine numbers. radRng_vals: by the kernel: at the place's four stages they are the planner's numerals (Johnson/Top/H/KeyTowers.lean).
  joh_full, joh_full_no: by the kernel: the kind's test below the Johnson radius says yes at these radii; one position beyond the greatest radius at which it says yes it says no.
  joh_scope: the field "joh".
  r1_15_scope: the field r1_15 ⇐ scope's equations · q₁ · hl · Le15 · Gives15.
Limits. That scope's equations hold is not shown here. As empty as Gives15. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15M
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Top.H.KeyTowers
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.K12.Law.CondAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open Johnson.G.OfPlan (Made)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq)
open Lk6.AtPlan (keyFull)
open Johnson.Top.H (eRng1 eRng2 eRng3 eRng4)
open Johnson.RunOne.Law.RoundsInFront
open Johnson.Bridge (TestAt testsFull tests_nine)

set_option maxRecDepth 1000000 in
theorem no_bat_full : ((dKeyFull.ds₁.take 18805).all fun d => !(d.entry.name == "BAT")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one round further the test says no. -/
theorem no_bat_full_no : ((dKeyFull.ds₁.take 18806).all fun d => !(d.entry.name == "BAT")) = false := by
  decide +kernel

theorem front_len {S Cl : Type} (bs : List (Block S Cl)) (L : List ℕ) (hL : bs.map (·.rounds.length) = L) (n : ℕ) :
    ((bs.take n).flatMap (·.rounds)).length = (L.take n).sum := by
  rw [length_inFront]
  unfold inFront
  rw [← hL, List.map_take]

/-- The written numbers of rounds of the first chain's nineteen blocks. -/
def roundsFull : List ℕ := [2, 2, 0, 0, 9581, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1]

theorem at_ds₁ (D : WholeD) (a : ℕ) : (D.at a).ds₁ = D.ds₁ := rfl

theorem hno_scope {S Cl : Type} (bs : List (Block S Cl)) (hL : bs.map (·.rounds.length) = roundsFull) (a : ℕ) :
    ∀ d ∈ (writtenKFull.at a).ds₁.take ((bs.take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false := by
  rw [front_len bs _ hL 15, show (roundsFull.take 15).sum = 18805 from by decide]
  rw [at_ds₁, writtenKFull_eq]
  intro d hd
  have h := List.all_eq_true.1 no_bat_full d hd
  cases hb : (d.entry.name == "BAT") with
  | false => rfl
  | true =>
    rw [hb] at h
    cases h

/-- The place's stages at the written value. -/
def stagesFull : List Fmt.M1.Stage := keyFull.ranges.test.stages.map H2U.stageNums

/-- The first of the nine written tests at the full size (Johnson/Bridge/TestsAtWritten.lean). That it is this place's own test is Johnson/RunOne/Law/K12Facts15LS.lean's trial_rng. -/
def testRng : TestAt := testsFull[0]'(by rw [tests_nine.1]; decide)

theorem testRng_at : testsFull[0]? = some testRng := List.getElem?_eq_getElem _

/-- The radius of each stage: the written test's own. -/
def radRng : Fmt.M1.Stage → ℕ := fun a => H2K.Pub.radOf testRng (H2K.Pub.sgOf a)

/-- They are the planner's numerals, in the stages' order. -/
theorem radRng_vals : stagesFull.map radRng = [eRng1, eRng2, eRng3, eRng4] := by decide +kernel

theorem joh_full : H2K.Pub.ok (H2K.Pub.johWalk radRng 0 stagesFull) = true := by decide +kernel

/-- A control: one position beyond the greatest radius at which the test says yes. -/
theorem joh_full_no : H2K.Pub.ok (H2K.Pub.johWalk (fun s => H2K.Pub.johMax s + 1) 0 stagesFull) = false := by
  decide +kernel

/-- (joh) -/
theorem joh_scope {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
    {m : Made} {N : H2U.PlaceNums} (hN : rangesNumbers m = .ok N)
    (h : (rangesTest laid back N : Block σ Cl).planOk = true) (hk : m.p.chains.made.sized.key = keyFull) :
    H2K.Pub.johOk (rangesParams N) radRng = true := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  have hs : (rangesParams N).nums.stages = stagesFull := by
    rw [hn, (numbers_parts hN).2.2.2.2.2, hk]
    rfl
  unfold H2K.Pub.johOk H2K.Pub.johAll
  rw [hs]
  exact joh_full

end Johnson.RunOne.Law.K12Facts15

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
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)
    (on : ℕ → (Xi × FirstState) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)


/-- **THE FIELD r1_15 OF The21, AT THE FULL SIZE, FROM SCOPE's EQUATIONS AND THE TWO PREMISES THAT HOLD THE WEIGHT.** -/
theorem r1_15_scope (file : String) (rd : ℕ → ℕ) (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a)) (hDK : DK = Johnson.G.writtenKFull)
    (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull)
    (hL : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = K12Facts15.roundsFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (le : Le15 X N P DK c₁ k₁ rest₁ K12Facts15.radRng)
    (gives : Gives15 X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll) K12Facts15.radRng rd) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 := by
  refine r1_15_of_facts X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll file K12Facts15.radRng rd m hX hN hp data q₁ hl ?_
    (K12Facts15.joh_scope hN (K12Facts15.plan_of X N P hp) hk) le gives
  rw [hDK]
  exact K12Facts15.hno_scope (c₁ :: k₁) (q₁ ▸ hL) _

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12Facts15.no_bat_full
#print axioms Johnson.RunOne.Law.K12Facts15.no_bat_full_no
#print axioms Johnson.RunOne.Law.K12Facts15.front_len
#print axioms Johnson.RunOne.Law.K12Facts15.at_ds₁
#print axioms Johnson.RunOne.Law.K12Facts15.hno_scope
#print axioms Johnson.RunOne.Law.K12Facts15.testRng_at
#print axioms Johnson.RunOne.Law.K12Facts15.radRng_vals
#print axioms Johnson.RunOne.Law.K12Facts15.joh_full
#print axioms Johnson.RunOne.Law.K12Facts15.joh_full_no
#print axioms Johnson.RunOne.Law.K12Facts15.joh_scope
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_scope
