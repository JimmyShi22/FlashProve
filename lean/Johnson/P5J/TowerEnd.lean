-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TowerEnd.lean: THE TOWER'S END IN NAMES: `rows_of_owed` (RowsOwed.lean) with the free
    letters as the one structure `Free` (TowerFree.lean), and what is owed and what is reached as
named propositions: so that the top theorem has a written statement.
  `mqF`: the first table's meaning as the tower spells it. `exF`: the first table's one extractor.
      `rowF`: the first chain's pieces.
  `GoodF`: every piece of the first chain is tied to the table, second form (`EachTiedR` at mqF,
      exF, rowF): THE KINDS' LAWS' JOINT.
  `FiveF`: the five other rows that are laws: head_cuts · reply_leaves · shared_joint_count ·
      leads3_last_chains_table · tables_fit.
  `SevenF … d Tl`: the end: there are the three equations of shapes, and `RowsOfProofFile`
      (Johnson/Goal/Skeleton/ProofFile.lean: the proof file's seven
    fields) holds at the compiled IOP, at the places of the second form and M := `meansSome`.
  **`seven_of_owedF`**: in scope · TieStart · GoodF · FiveF · Rch at every start of a typed instance
      · Rch at the first
      chain's end gives Rc · two build equations · the list of
    rounds' accept · the data · the three heads · the open gate (hb er) ⟹ SevenF.
Limits. Names and one call: nothing new is shown. General in Rch and Rc. No member is known.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsOwed
import Johnson.P5J.TowerFree

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

open VerifierAndGoals.AtTheName

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
  (Rc : F₀.XiPub × F₀.S₁ → Prop) (𝔏 : Free N DP F₀ Tok) (depthReq : ℕ)


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

set_option quotPrecheck false in
/-- The conditions and relations at the three chains, second form. -/
local notation "PLR" => ({ plTablesR TT GET Nn MQ fullLinks ps 𝔏.Ns 𝔏.MgS 𝔏.ML 𝔏.Pm 𝔏.PLm 𝔏.split
    𝔏.Q₂ Rc with
    on₁ := fun k a => (QO).on₁ k a ∧ Rch k a
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0)
      (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) } :
  PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃))

/-- **The first table's meaning, as the tower spells it.** -/
def mqF : VerifiableInference.Desc.First.Meaning F₀.XiPub (Wit (CellsM N) Tok MsgT) := MQ

/-- The first table's one extractor. -/
def exF := EX

/-- The first chain's pieces. -/
def rowF := (atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁

/-- **Every piece of the first chain is tied to the table, second form.** -/
def GoodF : Prop :=
  EachTiedR (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) Nn MQ fullLinks
    ps GET Rch 0 (reExt EX 0 ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁))

/-- **The five other rows that are laws.** -/
structure FiveF : Prop where
  /-- the head's four parts together give the head's half in plain integers -/
  head_cuts : HeadCuts pp putReq HH headPart
  /-- every piece leaves the heard reply, but where the table lays the token -/
  reply_leaves : EachRep tokOf fullLinks ps GET f (fun b => repHeard getS b.1) (QO).on₁ 0
    ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁)
  /-- the shared chain's pieces' laws, the slots behind one key -/
  shared_joint_count : EachLawsBN
    (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F₀ TT).p₂ (atDesc F₀ TT).l₂)
    (PLR).on₂ (PLR).Q₂ (2 ^ depthReq) 0 ((atDesc F₀ TT).p₂ :: (atDesc F₀ TT).l₂)
  /-- the last chain's pieces, at its table -/
  leads3_last_chains_table : EachOwn
    (onQ₃ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₃ (TT).ft₃)
      (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.Pm 𝔏.PLm (ocR GET Nn MQ fullLinks ps Rc))
    (meansQ₃ (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.ML) insQ₃ outsQ₃ (· ∈ startLast) 0
    ((TT).p₃ :: (TT).l₃)
  /-- the three tables fit the starts and each other: twelve fields -/
  tables_fit : TablesFitR F₀.start₂ ST3 TT 𝔏.Q₀ GET Nn MQ fullLinks ps (firstAt pp putReq HH 0 GET)
      𝔏.Ns
    𝔏.MgS 𝔏.Pm 𝔏.PLm 𝔏.split 𝔏.Q₂ Rc

/-- **The end: the proof file's seven fields.** -/
def SevenF
    (d : (F₀.XiPub × F₀.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {runP : (kcReq N pp E).conf.X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp)
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) N pp) E) DK DP runK runP ds xs dec rK 𝔏.rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP ds xs
      dec rK 𝔏.rP depthReq reqWithoutReply salt K P) : Prop :=
    ∃ h₁ h₂ h₃, VerifierAndGoals.AtTheName.RowsOfProofFile (b := soundnessAnalysisDataAtFullSize Tl)
      (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ 𝔏.rP) (join₀ 𝔏.rP) ByteArray.empty silP runP)
      { w₀ := ()
        P := plainP (lettersAt (claimsReqAt (frS.toDecR frZ 402653181) N pp)
            (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) N pp) E)) DP (front₀ 𝔏.rP) (join₀ 𝔏.rP)
          ByteArray.empty (F₀.pull instP) AL TP PLR h₁ h₂ h₃
          (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS))
          (L₁At F₀.start₂ TT (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.split)
          (L₂At ST3 TT (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.ML) d
        κ₁ := _
        k₁ := fun b => keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc (F₀.pull instP) TP).p₂
          (atDesc (F₀.pull instP) TP).l₂ 0 ((atDesc (F₀.pull instP) TP).in₂ b.1, b.2)
        F₁ := fun rec y => (kS₂ rec, y, fun _ _ => none) } (soundnessAnalysisDataAtFullSize Tl).εs

set_option maxHeartbeats 4000000 in
/-- **THE PROOF FILE's SEVEN FIELDS FROM WHAT IS OWED, IN NAMES.** -/
theorem seven_of_owedF (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq)
    (G : GoodF (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
        headPart
      digitsPart Gd smp tokOf Rch 𝔏)
    (V : FiveF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
        headPart
      digitsPart Gd smp tokOf Rch Rc 𝔏 depthReq)
    (hR0 : ∀ z (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      Rch 0 ((F₀.pub (instP z), F₀.start₁ (F₀.pub (instP z))), (y, fun _ => [])))
    (hRc : ∀ b, Rch (1 + (atDesc F₀ TT).l₁.length) b → Rc b.1)
    (hpe : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec)
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : F₀.shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : F₀.second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (d : (F₀.XiPub × F₀.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : (kcReq N pp E).conf.X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
    (er : runP = gatedFileDecision b (F₀.pull instP).run)
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp)
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) N pp) E) DK DP runK runP ds xs dec rK 𝔏.rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP ds xs
      dec rK 𝔏.rP depthReq reqWithoutReply salt K P) :
    SevenF (X := X) N E DP F₀ instP getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps headPart
      digitsPart Gd smp tokOf kS₂ Rch Rc 𝔏 depthReq d Tl :=
  rows_of_owed (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs arr ms Nn s
    seat f hN hG 𝔏.Q₀ Mg ps headPart digitsPart Gd smp 𝔏.c₀ tokOf 𝔏.Ns 𝔏.MgS 𝔏.ML 𝔏.Pm 𝔏.PLm 𝔏.split
    𝔏.Q₂ 𝔏.rP depthReq 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd kS₂ Rch Rc hZ rq R
    ⟨V.head_cuts, G, V.reply_leaves, V.shared_joint_count, V.leads3_last_chains_table, V.tables_fit⟩
    hR0 hRc hpe one hp hD q₁ q₂ q₃ d hb er Tl

end P5J

#check @P5J.mqF
#check @P5J.exF
#check @P5J.rowF
#check @P5J.GoodF
#check @P5J.FiveF
#print axioms P5J.seven_of_owedF
