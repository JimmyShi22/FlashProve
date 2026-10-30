-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FourFieldsR.lean: `FourFields` (FourFields.lean: the four fields of the proof file's
    seven that want no law of any kind of sub-protocol) AT THE PLACES OF THE SECOND
FORM OF THE CHAIN OF PROMISES (`PLR`: Rch beside the first table's promise; Rc inside the two later
    tables' own condition:
TopTablesR.lean, SevenOfTiedR.lean).
  **`fourFields_of_startR`**: `fourFields_of_start`'s premises and hR0 (Rch 0 holds at every start
      of a typed instance)
      ⟹ FourFields … PLR ….
    Three of the four are general in the places; the tie at the start must SHOW the first promise:
        there hR0 is spent.
Limits. General in Rch and Rc: neither is named. FieldsNoLaw.lean's own limits. The other three
    fields are not in it.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FourFields
import Johnson.P5J.TopTablesR

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

variable (Rch : ℕ → (F₀.XiPub × F₀.S₁) ×
  (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop) (Rc : F₀.XiPub × F₀.S₁ → Prop)

set_option quotPrecheck false in
/-- The plain road's conditions and relations, second form through all three chains. -/
local notation "PLR" => ({ plTablesR TT GET Nn MQ fullLinks ps Ns MgS ML Pm PLm split Q₂ Rc with
    on₁ := fun k a => (QO).on₁ k a ∧ Rch k a
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0)
      (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) } :
  PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃))

set_option maxHeartbeats 4000000 in
/-- **THE FOUR, AT THE SECOND FORM's PLACES.** -/
theorem fourFields_of_startR (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq)
    (hR0 : ∀ z (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      Rch 0 ((atDesc F₀ TT).in₁ (instP z), (y, fun _ => [])))
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = c₁ :: k₁) (q₂ : F₀.shared.blocksInOrder = c₂ :: k₂)
    (q₃ : F₀.second.blocksInOrder = c₃ :: k₃)
    (hpe : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec)
    (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    FourFields N E DP rP (F₀.pull instP) TP PLR
      (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) kS₂ εs := by
  intro L₁ L₂ d
  have hp' : (F₀.pull instP).planOk = true := (FileDescription.pull_planOk instP F₀).trans hp
  obtain ⟨h₁, h₂, h₃⟩ := shapesOfData (ckP .two) F₀ "proof file" _ hD (sealLast_of_planOk F₀ hp)
    c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd
  obtain ⟨hO, hf, fit⟩ := paidAtDesc _ _ (F₀.pull instP) "proof file" _ hD
    (sealLast_of_planOk (F₀.pull instP) hp') (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ (restCap e₁)
    (restCap e₂) (restCap e₃) dW wEnd
  refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact oneKeyByMake (ckP .two) (DP.at frS.P.T.a) AL _ _ _ _ _ _ _ _ (front₀ rP) (join₀ rP)
      ByteArray.empty (F₀.pull instP) TP (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁
      h₂ h₃ kS₂ hO hf one
  · exact decides_at_desc (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty silP
      reqWithoutReply (F₀.pull instP) AL TP PLR h₁ h₂ h₃
      (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) L₁ L₂ d hO fit hpe
  · exact ties_of_tie (kcReq N pp E) DP (front₀ rP) (join₀ rP) ByteArray.empty silP
      reqWithoutReply (F₀.pull instP) AL TP PLR h₁ h₂ h₃
      (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) L₁ L₂ d () hO fit hpe
      (fun x rec y τ s₁ s₂ s₃ z hok hsil hfin hM =>
        tie_of_start (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs arr ms
          Nn s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split Q₂
          rP c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd hZ rq R x rec y τ s₁ s₂ s₃ z hok hsil hfin
          fun h0 => hM ⟨h0, hR0 _ y⟩)
  · exact below_atCap₁ (F₀.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd εs hε (atCap_restCap _) h₁
  · exact below_atCap₂ (F₀.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd εs hε (atCap_restCap _) h₂
  · exact below_atCap₃ (F₀.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
      (restCap e₂) (restCap e₃) dW wEnd εs hε (atCap_restCap _) h₃

end P5J

#print axioms P5J.fourFields_of_startR
