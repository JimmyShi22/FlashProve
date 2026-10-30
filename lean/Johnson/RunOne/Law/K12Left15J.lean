-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left15J.lean: WHAT IS LEFT OF ROW 1.15 OF THE KEY FILE's TABLES, WITH THE FACTS ON CODES AND "THE ERRORS BEAR THE CHAIN's" PAID BY ONE TEST ON THE PLAN: Left15J: Left15 (Johnson/RunOne/Law/K12Left15.lean) LESS NINE FIELDS. IT PAYS NO FIELD OF THE TABLES: Left15J.gives HOLDS ALL THE WEIGHT, AND NO MEMBER OF Left15J IS SHOWN.
OBJECT. `LPFD.The21`'s field r1_15. USER. The21's filler.
LETTERS. The35.lean's.

  Left15J: 24 fields: I eleven letters · II eleven facts on the description and the plan · III le · IV gives. The radii's letter is fun s => stageRad s.st; the errors behind "BAT" are errJ (rangesParams N) stageRad dt.
  Left15J.not_last: from (behind).
  Left15J.toLeft15: under q₁ and hl: a member of Left15J gives a member of Left15: codes by codes_of_johOk (Johnson/Desc/K12/Law/CodesJoh.lean); bears: the field of the AtPlace that atPlace_row₁J (K12AtPlaceRowJ.lean) gives.
  r1_15_atJ: the field, from q₁, hl and Left15J: r1_15_at (K12Left15.lean) CALLED at toLeft15.
  Left15J.ofHalves: the field «gives» may be laid by gives_of_halves (K12GivesHalves.lean): so that theorem's conclusion IS the field's type, by Lean.
A SECOND DOOR, NOT A REPLACEMENT: Left15 stays for whoever has other errors that bear.
Limits. As empty as Left15J. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Left15
import Johnson.RunOne.Law.K12AtPlaceRowJ
import Johnson.RunOne.Law.K12GivesHalves

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
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **WHAT IS LEFT OF ROW 1.15, AT THE LIBRARY's JOHNSON LETTERS AND THE PLACE's OWN ERRORS.** `Left15` less nine fields: the five letters of the facts on codes, εt, radIs, codes, bears. Four kinds, in this order: I letters that the payer chooses · II facts on the description and the plan · III conditions on the frame's letter rest₁ · IV the weight. -/
structure Left15J where
  -- I LETTERS THAT THE PAYER CHOOSES
  /-- the file's name in a refusal's words -/
  file : String
  /-- "BAT"'s round's data, and the data of the rounds behind it -/
  dB : RDT
  dt : List RDT
  /-- what the blocks behind the test declare, but for the last round; and that round -/
  post : List _root_.Fmt.DeclaredRound
  r₀ : _root_.Fmt.DeclaredRound
  /-- the place's declared rounds as written -/
  writtenHead : WR
  writtenTail : List WR
  /-- the radius of each stage -/
  stageRad : _root_.Fmt.M1.Stage → ℕ
  /-- the error of "BAT"'s round -/
  batErr : ℕ
  /-- from a tree's label to its number through the file -/
  nl : ℕ → ℕ
  rd : ℕ → ℕ
  -- II FACTS ON THE DESCRIPTION AND THE PLAN
  /-- (data) THE FRAME's DATA ARE THE DESCRIPTION's OWN -/
  data : (Fk X N P).data file = .ok (DK.at frS.P.T.a)
  /-- (stretch) the maker's 15th stretch is written dB :: dt -/
  stretch : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 = dB :: dt
  /-- (behind) what the blocks behind the test declare ends in a round: the sealing round -/
  behind : ((c₁ :: k₁).drop 16).flatMap (·.rounds) = post ++ [r₀]
  /-- (plan) The seat's own test on the plan says yes. A payer stands in another file, from the description's own test on the plan (rng_planOk, Johnson/RunOne/KeySmpStay.lean): it is not called here -/
  plan : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true
  /-- (arm) the first fold's mask came earlier -/
  arm : (rangesParams N).nums.ownMask = false
  /-- (written) the place's declared rounds can be written -/
  written : writtenOf (rangesParams N).nums = some (writtenHead :: writtenTail)
  /-- (free) the place's first free own number is the number of roots that the 15 blocks in front declare: shown of no test by anybody -/
  free : (rangesParams N).nums.free = rootsOf (((c₁ :: k₁).take 15).flatMap (·.rounds))
  /-- (joh | batOne) the kind's two tests on the plan -/
  joh : johOk (rangesParams N) stageRad = true
  batOne : batOneOk (rangesParams N) = true
  /-- (labels) A TEST ON THE PLAN, AT THE MAKER's OWN BASE: each opening that the first switch declares: its source's number through the file is nl of its label, and lies below the base -/
  labels : LabelsPub (rangesParams N) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 0) nl (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15)
  /-- (bat) the first round's error is at least "BAT"'s count -/
  bat : batV0 (rangesParams N) stageRad * (bsRound .two dB.entry dB.kind).w ≤ batErr
  -- III A CONDITION ON THE FRAME's LETTER rest₁
  /-- (le) the law's errors lie below the maker's rest's at the 15th piece: behind "BAT" they are the counts of the place's own chain at the radii (errJ: AN εt that bears the chain's errors; that it is the least is shown by nobody) -/
  le : Err.le ((batErr, errJ (rangesParams N) stageRad dt) : Err (uLT (ckP .two) (dB :: dt))) (rest₁ 15 (dB :: dt)).err
  -- IV THE WEIGHT
  /-- (gives) ALL THE WEIGHT. IT IS THE FIELD's CONCLUSION LESS ITS PROBABILITY: the field asks "the promise behind holds at b, and a witness behind gives a witness in front" but for an error; this asks the same FOR CERTAIN, under "one tuple for all rows", which the kind's law supplies but for that error. Where: the maker's piece puts out b from a statement inside the promise, through the seat's two doors; the tuple stands at the oracles that the labels of the record's own book name, AT THE STRINGS IN FRONT. Its bare ∀ is ∀ a τ b: A NON-DEGENERATE INSTANCE IS NOT SHOWN: where the promise in front holds nowhere it is met for nothing -/
  gives : ∀ a τ b, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a →
    (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
    (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
      (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) (fun s => stageRad s.st) rd) (t, a.2)) →
    (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 a)

variable {X N P DK c₁ k₁ rest₁ B at_ R coll}

/-- From (behind): the test is not the chain's last block. -/
theorem Left15J.not_last (H : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll) : 15 < k₁.length := by
  by_contra h
  have h0 : (c₁ :: k₁).drop 16 = [] := List.drop_eq_nil_iff.2 (by simp only [List.length_cons]; omega)
  have h1 := H.behind
  rw [h0] at h1
  simp at h1

/-- **A member of Left15J gives a member of Left15.** -/
def Left15J.toLeft15 (H : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2) :
    Left15 X N P DK c₁ k₁ rest₁ B at_ R coll where
  file := H.file
  dB := H.dB
  dt := H.dt
  post := H.post
  r₀ := H.r₀
  writtenHead := H.writtenHead
  writtenTail := H.writtenTail
  stageRad := H.stageRad
  Lc := Sg.lstJ
  mC := Sg.flC
  mS := Sg.flZ
  mW := Sg.flZ
  rad := fun s => H.stageRad s.st
  batErr := H.batErr
  εt := errJ (rangesParams N) H.stageRad H.dt
  nl := H.nl
  rd := H.rd
  data := H.data
  stretch := H.stretch
  behind := H.behind
  plan := H.plan
  arm := H.arm
  written := H.written
  free := H.free
  joh := H.joh
  batOne := H.batOne
  radIs := fun _ => rfl
  codes := codes_of_johOk H.stageRad (rangesParams N) H.joh
  bears := (K12AtPlaceRow.atPlace_row₁J (Fk X N P) H.file (DK.at frS.P.T.a) H.data c₁ k₁ q₁ 15 _
      (K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl) H.not_last (rangesParams N)
      (RngAnyCl.same_k12 (A := Key.Claim) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds H.post H.r₀ H.behind H.stageRad H.dB H.dt
      H.stretch H.free (PlanPays.rng_pays H.plan).1 (PlanPays.rng_pays H.plan).2.1 (PlanPays.rng_pays H.plan).2.2.1
      (PlanPays.rng_pays H.plan).2.2.2.1 H.joh H.arm H.writtenHead H.writtenTail H.written).bears
  labels := H.labels
  bat := H.bat
  le := H.le
  gives := H.gives

variable (X N P DK c₁ k₁ rest₁ B at_ R coll)

/-- **THE FIELD r1_15 OF The21 AT THE KEY FILE's OWN DESCRIPTION, FROM WHAT IS LEFT AT THE JOHNSON LETTERS.** -/
theorem r1_15_atJ (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (H : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  r1_15_at X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁ hl (H.toLeft15 q₁ hl)

/-- «gives» laid by the two halves: it typechecks only because gives_of_halves' conclusion is the field's type. -/
def Left15J.ofHalves (H : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll)
    (tbl : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Wit Cells Unit M → M) :=
  fun hbase fwd back => ({ H with gives := gives_of_halves X N P DK c₁ k₁ rest₁ B at_ R coll H.dB H.dt H.nl (fun s => H.stageRad s.st) H.rd tbl hbase fwd back } : Left15J X N P DK c₁ k₁ rest₁ B at_ R coll)

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.Left15J.not_last
#print axioms Johnson.RunOne.Law.K12AtThe21.Left15J.toLeft15
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_atJ
#print axioms Johnson.RunOne.Law.K12AtThe21.Left15J.ofHalves
