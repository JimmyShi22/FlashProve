-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TowerFree.lean: THE TOWER'S FREE LETTERS AS ONE LEAN STRUCTURE, AND ITS PIECES AND
    PLACES AS NAMED DEFINITIONS: so that the theorems at the top have WRITTEN
statements of a dozen lines. Nothing new is shown.
  `Free N DP F₀ Tok`: 21 fields (the default request d₀ is not among them: the composed meaning's
      constant lays one): the letters of the tower
    that stay "for all" at the top (beside it stand, as letters of their own: d₀, headPart,
        digitsPart, tokOf, kS₂: terms of the
    composed meaning's constant and of the seated term; Rch, Rc: the "reached" of other files):
    the two later chains' places Q₀ as they come · a default table c₀ · the two later tables'
        numbers and meanings (Ns MgS ML Pm
    PLm split Q₂) · the key file's OOD sample rP of the frame · the three lists' heads and tails (c₁
        k₁ c₂ k₂ c₃ k₃) · the pieces'
    extractors (e₁ e₂ e₃) · two default witnesses (dW wEnd).
  `tpF`: the three rows of pieces of the IOP as written in Lean, laid on the requests, each with the
      cap as its errors.
  `plRF`: the conditions and relations at the three chains, in the second form of the chain of
      promises (Rch beside the first
    table's promise; Rc inside the two later tables' own condition): SevenOfTiedR.lean's PLR, to the
        token.
  **`fourFieldsF`**: `fourFields_of_startR` (FourFieldsR.lean) in these names.
Limits. Names and one call. General in Rch and Rc. FieldsNoLaw.lean's own limits.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FourFieldsR

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

/-- **The tower's free letters.** -/
structure Free (N : MatrixNums) (DP : WholeD) {XiP : Type} (F₀ : FileDescription XiP) (Tok : Type) where
  Q₀ : PlacesAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) F₀ (Wit (CellsM N) Tok MsgT)
  c₀ : CellsM N
  Ns : NumbersS
  MgS : MeaningS F₀.S₂ (F₀.XiPub × F₀.S₁) (Wit (CellsM N) Tok MsgT)
  ML : MeaningL F₀.S₃ (Wit (CellsM N) Tok MsgT)
  Pm : PromMeaning F₀.S₂
  PLm : PromMeaningL F₀.S₂ F₀.S₃ (F₀.XiPub × F₀.S₁)
  split : Bool
  Q₂ : ℕ → ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str →
    ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop
  rP : RecFull
  c₁ : Block F₀.S₁ F₀.Cl
  k₁ : List (Block F₀.S₁ F₀.Cl)
  c₂ : Block F₀.S₂ F₀.Cl
  k₂ : List (Block F₀.S₂ F₀.Cl)
  c₃ : Block F₀.S₃ F₀.Cl
  k₃ : List (Block F₀.S₃ F₀.Cl)
  e₁ : (i : ℕ) → (ds : List RDT) → (F₀.XiPub × F₀.S₁) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT
  e₂ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁) × F₀.S₂) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT
  e₃ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃
        F₀.lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT
  dW : Wit (CellsM N) Tok MsgT
  wEnd : Wit (CellsM N) Tok MsgT

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  {XiP : Type} (F₀ : FileDescription XiP)
  (instP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → XiP) {Tok : Type}
  (getS : F₀.S₁ → TS) (reqB : F₀.XiPub → ByteArray)
  (DT : (ℕ → Option (ℕ × List UInt64)) → F₀.XiPub × TS → Option (CellsM N))
  (asked : XiP → OnBytes.E) (d₀ : TReq) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Nn :
      Numbers)
  (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)
  (Mg : VerifiableInference.Desc.First.Meaning F₀.XiPub (Wit (CellsM N) Tok MsgT))
  (ps : List Place)
  (headPart : TPart → Cm.Idx → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  (digitsPart : ℕ → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  {Xg : Type} (Gd : FileDescription Xg)
  (smp : F₀.XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (tokOf : F₀.XiPub × TS → Tok) (kS₂ : RecFull → F₀.S₂)
  (Rch : ℕ → (F₀.XiPub × F₀.S₁) ×
    (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (Rc : F₀.XiPub × F₀.S₁ → Prop) (𝔏 : Free N DP F₀ Tok)


set_option quotPrecheck false in
/-- Every tree of the file. -/
local notation "AL" => allOf (DP.at frS.P.T.a)

set_option quotPrecheck false in
/-- The three rows of pieces, each with the cap as its errors. -/
local notation "TT" => (piecesAt (ckP .two) F₀ (DP.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃
    (restCap 𝔏.e₁)
  (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)

set_option quotPrecheck false in
/-- The same pieces, at the description laid on the requests. -/
local notation "TP" => (piecesAt (ckP .two) (F₀.pull instP) (DP.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
    𝔏.c₃ 𝔏.k₃
  (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)

set_option quotPrecheck false in
/-- The chain's record as the table reads it. -/
local notation "GET" => (fun a : F₀.XiPub × F₀.S₁ => ((a.1, getS a.2) : F₀.XiPub × TS))

set_option quotPrecheck false in
/-- hid, filled. -/
local notation "HH" => (hidAtSeat X cs arr ms Nn s seat f
  (fun a => (backReq (reqB a.1)).getD d₀) (fun a y => DT y.cell a) hN hG :
  HidAt X F₀.XiPub (Wit (CellsM N) Tok MsgT) N.rows (colsAt N))

set_option quotPrecheck false in
/-- The first table's meaning. -/
local notation "MQ" => meaningQ putReq HH headPart digitsPart
  (meaningSig cs Gd arr smp ms DT (withReq reqB Mg))

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from its table. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := AL) 0 Nn MQ fullLinks ps GET
  (firstAt pp putReq HH 0 GET) 𝔏.Q₀

set_option quotPrecheck false in
/-- The first table's one extractor. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) cs Gd
  arr smp ms DT 𝔏.c₀ tokOf Nn fullLinks ps GET

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F₀.start₃ p a b).toOption

/-- **The three rows of pieces, laid on the requests.** -/
def tpF := TP

/-- **The conditions and relations at the three chains, second form.** -/
def plRF : PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃) :=
  { plTablesR TT GET Nn MQ fullLinks ps 𝔏.Ns 𝔏.MgS 𝔏.ML 𝔏.Pm 𝔏.PLm 𝔏.split 𝔏.Q₂ Rc with
    on₁ := fun k a => (QO).on₁ k a ∧ Rch k a
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0)
      (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) }

set_option maxHeartbeats 4000000 in
/-- **THE FOUR FIELDS THAT WANT NO KIND's LAW, IN THESE NAMES.** -/
theorem fourFieldsF (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq)
    (hR0 : ∀ z (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      Rch 0 ((F₀.pub (instP z), F₀.start₁ (F₀.pub (instP z))), (y, fun _ => [])))
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : F₀.shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : F₀.second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hpe : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec)
    (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    FourFields N E DP 𝔏.rP (F₀.pull instP) (tpF N E DP F₀ instP 𝔏)
      (plRF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps headPart
          digitsPart Gd
        smp tokOf Rch Rc 𝔏)
      (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) kS₂ εs :=
  fourFields_of_startR (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs arr
    ms Nn s seat f hN hG 𝔏.Q₀ Mg ps headPart digitsPart Gd smp 𝔏.c₀ tokOf 𝔏.Ns 𝔏.MgS 𝔏.ML 𝔏.Pm 𝔏.PLm
    𝔏.split 𝔏.Q₂ 𝔏.rP 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd kS₂ Rch Rc hZ rq R
        hR0 hp
    hD q₁ q₂ q₃ hpe one εs hε

end P5J

#check @P5J.tpF
#check @P5J.plRF
#print axioms P5J.fourFieldsF
