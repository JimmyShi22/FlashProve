-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FourFields.lean: A NAME FOR THE FOUR FIELDS OF THE PROOF FILE'S SEVEN
    (`RowsOfProofFile`,
Johnson/Goal/Skeleton/ProofFile.lean) THAT WANT NO LAW OF ANY KIND OF BLOCK, so that the theorems on
    them have WRITTEN
statements that can be read.
  `FourFields N E DP rP F T Pl M kS₂ εs`: at a description F of the proof file, its three rows of
      pieces T, the
    promises and relations Pl, the meaning M of what the first chain hands on, the shared chain's
        first state kS₂
    as a function of the key file's OOD sample, and a bound εs: whatever L₁, L₂, d: there are the
        three equations
    of shapes, and:
      (4) what the first chain hands on has a key that hangs on the key file's OOD sample and the
          first
          committed table alone;
      (5) a yes of the compiled description is a yes of the three chains, at the instance without
          its reply;
      (6) "tie" : a yes, what the first chain handed on, and "the promise at the start gives M" give
          the relation
          of the top: the first committed table does not decode, or it decodes to an index at which
              the
          relation holds;
      (7) each chain's own list of errors lies below εs.
    Each in the form in which `rows_at_descB` (Johnson/Goal/Skeleton/ProofRowsAtDesc.lean) takes or
        lays it.
  **`fourFields_of_start`**: `fields_4567` (FieldsNoLaw.lean) under that name.
Limits. A name and one call: nothing new is shown. The other three fields (the three chains lead)
    are not in it.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FieldsNoLaw

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

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  {XiP : Type} (F₀ : FileDescription XiP)
  (instP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → XiP) {Tok : Type}
  (getS : F₀.S₁ → TS) (reqB : F₀.XiPub → ByteArray) (DT : (ℕ → Option (ℕ × List UInt64)) → F₀.XiPub
  × TS → Option (CellsM N)) (asked : XiP → OnBytes.E) (d₀ : TReq) (cs : OnBytes.Codes) (arr : ℕ → ℕ
  → ℕ) (ms : List Mem) (Nn : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)
  (Q₀ : PlacesAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) F₀ (Wit (CellsM N) Tok MsgT))
  (Mg : VerifiableInference.Desc.First.Meaning F₀.XiPub (Wit (CellsM N) Tok MsgT))
  (ps : List Place)
  (headPart : TPart → Cm.Idx → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  (digitsPart : ℕ → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  {Xg : Type} (Gd : FileDescription Xg)
  (smp : F₀.XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (c₀ : CellsM N) (tokOf : F₀.XiPub × TS → Tok)
  (Ns : NumbersS) (MgS : MeaningS F₀.S₂ (F₀.XiPub × F₀.S₁) (Wit (CellsM N) Tok MsgT))
  (ML : MeaningL F₀.S₃ (Wit (CellsM N) Tok MsgT)) (Pm : PromMeaning F₀.S₂)
  (PLm : PromMeaningL F₀.S₂ F₀.S₃ (F₀.XiPub × F₀.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str →
    ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (rP : RecFull) (depthReq : ℕ)
  (c₁ : Block F₀.S₁ F₀.Cl) (k₁ : List (Block F₀.S₁ F₀.Cl)) (c₂ : Block F₀.S₂ F₀.Cl)
  (k₂ : List (Block F₀.S₂ F₀.Cl)) (c₃ : Block F₀.S₃ F₀.Cl) (k₃ : List (Block F₀.S₃ F₀.Cl))
  (e₁ : (i : ℕ) → (ds : List RDT) → (F₀.XiPub × F₀.S₁) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁) × F₀.S₂) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃
        F₀.lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (dW wEnd : Wit (CellsM N) Tok MsgT) (kS₂ : RecFull → F₀.S₂)

set_option quotPrecheck false in
/-- Every tree of the file. -/
local notation "AL" => allOf (DP.at frS.P.T.a)

set_option quotPrecheck false in
/-- The three rows of pieces, each with the cap as its errors. -/
local notation "TT" => (piecesAt (ckP .two) F₀ (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
  (restCap e₂) (restCap e₃) dW wEnd)

set_option quotPrecheck false in
/-- The same pieces, at the description laid on the requests. -/
local notation "TP" => (piecesAt (ckP .two) (F₀.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
  (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)

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
  (firstAt pp putReq HH 0 GET) Q₀

set_option quotPrecheck false in
/-- The first table's one extractor. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) cs Gd
  arr smp ms DT c₀ tokOf Nn fullLinks ps GET

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F₀.start₃ p a b).toOption

set_option quotPrecheck false in
/-- The plain road's conditions and relations: all three chains' from their tables. -/
local notation "PL" => ({ plTables TT GET Nn MQ fullLinks ps Ns MgS ML Pm PLm split Q₂ with
    on₁ := (QO).on₁
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) (QO).on₁ (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) } :
  PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃))

open scoped ENNReal
open _root_.Iop (Err)

/-- **THE FOUR FIELDS THAT WANT NO KIND's LAW.** (The binders stand in the definition's own head and
    name no
local notation: a notation over section variables inside a `variable` line elaborates to sorry in
    silence.) -/
def FourFields
    (F : FileDescription ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)) {X₁ X₂ W' : Type}
    (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) F X₁ X₂ W')
    (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) ×
        F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec) ×
        (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (kF : (kcReq N pp E).conf.Rec → F.S₂) (εs : ℝ≥0∞) : Prop :=
  ∀ (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str),
    ∃ h₁ h₂ h₃,
      (∀ x rec y τ b, (plainP (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf
          (DP.at frS.P.T.a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
        keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0
          ((atDesc F T).in₂ b.1, b.2) = (kF rec, y, fun _ _ => none)) ∧
      (∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty).sh),
        (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
          F.run).accept (x, rec) y τ = true →
        ((plainP (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf (DP.at
            frS.P.T.a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).links.all.out ((reqWithoutReply x, rec), y)
            τ).isSome = true) ∧
      (∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty).sh) b,
        (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
          F.run).accept (x, rec) y τ = true →
        (plainP (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf (DP.at frS.P.T.a))
            T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((reqWithoutReply x, rec), y)
          (Tr.fst (s := (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
              ByteArray.empty).c₁) (t := (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀
              rP) ByteArray.empty).c₂ ++ (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀
              rP) ByteArray.empty).c₃) τ) = some b →
        ((plainP (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf (DP.at
            frS.P.T.a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₀ ((reqWithoutReply x, rec), y) →
          (plainP (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty F (allOf (DP.at
              frS.P.T.a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).M ((reqWithoutReply x, rec), y) b) →
        (kcReq N pp E).conf.D y rec = none ∨
          ∃ i, (kcReq N pp E).conf.D y rec = some i ∧ (kcReq N pp E).conf.Rno i x ()) ∧
      (Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) εs ∧
        Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) εs ∧
        Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) εs)


set_option maxHeartbeats 4000000 in
/-- **THE FOUR, FROM FACTS THAT NAME NO KIND's LAW**: `fields_4567` under the name. -/
theorem fourFields_of_start (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq)
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = c₁ :: k₁) (q₂ : F₀.shared.blocksInOrder = c₂ :: k₂)
    (q₃ : F₀.second.blocksInOrder = c₃ :: k₃)
    (hpe : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec)
    (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    FourFields N E DP rP (F₀.pull instP) TP PL
      (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) kS₂ εs :=
  fun L₁ L₂ d =>
    fields_4567 (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs arr ms Nn s
      seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split Q₂ rP c₁ k₁
      c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ hZ rq R hp hD q₁ q₂ q₃ hpe one εs hε L₁ L₂ d

end P5J

#print axioms P5J.fourFields_of_start
