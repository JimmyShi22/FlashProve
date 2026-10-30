-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left15G.lean: MADE BY A PROGRAM's SUBSTITUTION OUT OF K12Left15.lean: Left15 AND r1_15_at WITH THE PROMISE AS A LETTER «on».
OBJECT. The law owed at the 15th piece of the key file's first chain (LPFD.KeepsAt), at any promise «on» and the tables' claim Cl₁. USER. K12Left15JG.lean | K12Left15H.lean.
LETTERS. The35.lean's; on : the promise at a border.
WHY. The21's field r1_15 stands at On₁' := On₁ ∧ Hist₁ (the record was reached). K12Left15.lean's road goes through the promise WITHOUT the history. No field of Left15 but «gives» names the promise: so it can be a letter, and a caller may lay one that holds the history in front.
  Left15G on: Left15's 33 fields, sign for sign, with «on» for the tables' On₁ in «gives», twice. (The letter coll is named by no field.)
  Left15G.not_last: from (behind).
  r1_15_atG: KeepsAt on Cl₁ ‹the pieces› 15 from q₁, hl and Left15G on: r1_15_at's own lines, with K12AtField.keepsAt_rng_15 (general in the promise) called where r1_15_of_on was.
IT PAYS NO FIELD: NO MEMBER OF Left15G IS SHOWN.
Limits. As empty as Left15G. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12AtThe21On
import Johnson.RunOne.Law.K12PaysGameV
import Johnson.RunOne.Law.K12AtPlaceRow
import Johnson.RunOne.Law.PlanPays

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
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
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

/-- **WHAT IS LEFT OF ROW 1.15.** Four kinds, in this order: I letters that the payer chooses · II facts on the description and the plan · III conditions on the frame's letter rest₁ · IV the weight. -/
structure Left15G where
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
  /-- the letters of the facts on codes -/
  Lc : Sg → ℕ → ℕ
  mC : Sg → ℕ → ℕ
  mS : Sg → ℕ → ℕ
  mW : Sg → ℕ → ℕ
  rad : Sg → ℕ
  /-- the errors: of "BAT"'s round, and of the rounds behind it -/
  batErr : ℕ
  εt : Err (uLT (ckP .two) dt)
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
  /-- (radIs | codes | bears) the facts on codes at the radii, and that εt bears the chain's errors -/
  radIs : ∀ s, rad s = stageRad s.st
  codes : CodesAt Lc mC mS mW rad (rangesParams N).nums.stages
  bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), (rangesParams N).nums.stages = a :: rest →
    writtenOf (rangesParams N).nums = some (w0 :: l) → chainFrom (.at Lc mC mS mW rad) rest a l = some c →
    Bears c.errL εt
  /-- (labels) A TEST ON THE PLAN, AT THE MAKER's OWN BASE: each opening that the first switch declares: its source's number through the file is nl of its label, and lies below the base -/
  labels : LabelsPub (rangesParams N) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 0) nl (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15)
  /-- (bat) the first round's error is at least "BAT"'s count -/
  bat : batV0 (rangesParams N) stageRad * (bsRound .two dB.entry dB.kind).w ≤ batErr
  -- III A CONDITION ON THE FRAME's LETTER rest₁
  /-- (le) the law's errors lie below the maker's rest's at the 15th piece -/
  le : Err.le ((batErr, εt) : Err (uLT (ckP .two) (dB :: dt))) (rest₁ 15 (dB :: dt)).err
  -- IV THE WEIGHT
  /-- (gives) ALL THE WEIGHT. IT IS THE FIELD's CONCLUSION LESS ITS PROBABILITY: the field asks "the promise behind holds at b, and a witness behind gives a witness in front" but for an error; this asks the same FOR CERTAIN, under "one tuple for all rows", which the kind's law supplies but for that error. Where: the maker's piece puts out b from a statement inside the promise, through the seat's two doors; the tuple stands at the oracles that the labels of the record's own book name, AT THE STRINGS IN FRONT. Its bare ∀ is ∀ a τ b: A NON-DEGENERATE INSTANCE IS NOT SHOWN: where the promise in front holds nowhere it is met for nothing -/
  gives : ∀ a τ b, on 15 a →
    (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
    (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
      (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) →
    on 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 a)

variable {X N P DK c₁ k₁ rest₁ B at_ R coll on}

/-- From (behind): the test is not the chain's last block. -/
theorem Left15G.not_last (H : Left15G X N P DK c₁ k₁ rest₁ B at_ R on) : 15 < k₁.length := by
  by_contra h
  have h0 : (c₁ :: k₁).drop 16 = [] := List.drop_eq_nil_iff.2 (by simp only [List.length_cons]; omega)
  have h1 := H.behind
  rw [h0] at h1
  simp at h1

variable (X N P DK c₁ k₁ rest₁ B at_ R coll on)

/-- **The law owed at the 15th piece, at any promise, from what is left.** -/
theorem r1_15_atG (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (H : Left15G X N P DK c₁ k₁ rest₁ B at_ R on) :
    KeepsAt on (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  K12AtField.keepsAt_rng_15 X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ _ q₁ hl
    fun base ds back hrow => by
      obtain ⟨b, _, hp⟩ := rowAt₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 15 _ hrow
      have e1 : base = (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) := congrArg (·.base) hp
      have e2 : ds = H.dB :: H.dt := (congrArg (·.ds) hp).trans H.stretch
      have e3 : back = [] := (congrArg (·.back) hp).trans
        (cutPut_inner [sealRound] (k₁.map held) 15 (by rw [List.length_map]; exact H.not_last))
      subst e1 e2 e3
      obtain ⟨he, ha, hk, hs, -, -, -⟩ := PlanPays.rng_pays H.plan
      exact K12PaysGameV.pays_gameV (rangesParams N) _ _ _ _ _ 15 (numAt (Fk X N P).t₁ (Fk X N P).t₂ 0) H.nl
        H.Lc H.mC H.mS H.mW H.rad H.rd _ H.dB H.dt H.batErr H.εt _ H.stageRad
        (K12AtPlaceRow.atPlace_row₁ (Fk X N P) H.file (DK.at frS.P.T.a) H.data c₁ k₁ q₁ 15 _
          (K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl) H.not_last (rangesParams N)
          (RngAnyCl.same_k12 (A := Key.Claim) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds H.post H.r₀ H.behind
          H.Lc H.mC H.mS H.mW H.rad H.dB H.dt H.εt H.stretch H.free he ha hk hs H.codes H.arm H.writtenHead H.writtenTail
          H.written H.bears)
        H.radIs H.joh H.batOne H.bat H.labels H.le H.gives

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.Left15G.not_last
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_atG
