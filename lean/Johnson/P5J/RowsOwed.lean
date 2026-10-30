-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RowsOwed.lean: WHAT IS LEFT OF THE PROOF FILE'S SEVEN FIELDS, AS ONE LEAN STRUCTURE OF
    SIX ROWS; AND THE SEVEN FROM IT. `RowsTiedR` (SevenOfTiedR.lean) has 24
fields: eleven are facts on a start (`TieStart`, TieStart.lean: paid at the seated term (under the premise `AtMg`, AtMg.lean: `AtMg.tieStart`, MgAtConst.lean))
    · one follows
in scope (scope_core: a lemma in the library's build) · two stand in the
    letters' types (seats_named, groups_seated) · FOUR STAY PREMISES OF
`rows_of_owed` BESIDE THE SIX: Rch at every start of a typed instance
    and at the first chain's end (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean: that file's
    "reached" is meant to pay both), "the
public part does not read the reply",
    "the shared chain's first state is a function of the key file's OOD sample" (both paid
at the seated term). THE SIX THAT ARE LAWS:
  `RowsOwed`: head_cuts (the head's four parts give the head's half in plain integers) · EachGood
      (every piece of the first chain is
    tied to the table, second form: THE KINDS' LAWS) · reply_leaves (every piece leaves the heard
        reply, but where the table lays the
    token) · shared_joint_count (the shared chain's laws) · leads3_last_chains_table (the last
        chain's) · tables_fit (the three
    tables fit the starts and each other).
  **`rows_of_owed`**: in scope · TieStart · RowsOwed · Rch at every start of a typed instance · Rch
      at the first chain's
      last border gives Rc · "the public
    part does not read the reply" ·
        "the shared chain's first state is a function of the key file's OOD sample" · the list of
    rounds' accept · the data · the three heads · the open gate (hb er) ⟹ ∃ h₁ h₂ h₃,
        `RowsOfProofFile` … at PLR and M := `meansSome`.
Limits. A joining: it pays nothing. General in Rch and Rc. RowsOfTiedR.lean's own limits. No member
    is known.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsOfTiedR
import Johnson.P5J.TieStart
import Johnson.Goal.Meaning.ScopeCore

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

open VerifierAndGoals.AtTheName

variable (Rch : ℕ → (F₀.XiPub × F₀.S₁) ×
  (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop) (Rc : F₀.XiPub × F₀.S₁ → Prop)

set_option quotPrecheck false in
/-- The plain road's conditions and relations, the first chain's with Rch beside the promise. -/
local notation "PLR" => ({ plTablesR TT GET Nn MQ fullLinks ps Ns MgS ML Pm PLm split Q₂ Rc with
    on₁ := fun k a => (QO).on₁ k a ∧ Rch k a
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0)
      (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) } :
  PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃))

/-- **THE SIX ROWS THAT ARE LAWS.** -/
structure RowsOwed : Prop where
  /-- the head's four parts together give the head's half in plain integers -/
  head_cuts : HeadCuts pp putReq HH headPart
  /-- every piece of the first chain is tied to the table of joints (the chain of promises), with
  the table's extractor laid in -/
  EachGood : EachTiedR (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) Nn MQ fullLinks
    ps GET Rch 0 (reExt EX 0 ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁))
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
      (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) Pm PLm (ocR GET Nn MQ fullLinks ps Rc))
    (meansQ₃ (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) insQ₃ outsQ₃ (· ∈ startLast) 0
    ((TT).p₃ :: (TT).l₃)
  /-- the three tables fit the starts and each other: twelve fields -/
  tables_fit : TablesFitR F₀.start₂ ST3 TT Q₀ GET Nn MQ fullLinks ps (firstAt pp putReq HH 0 GET) Ns
    MgS Pm PLm split Q₂ Rc

set_option maxHeartbeats 4000000 in
/-- **THE PROOF FILE's SEVEN FIELDS FROM THE SIX ROWS.** -/
theorem rows_of_owed (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq)
    (O : RowsOwed (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Q₀ Mg ps
      headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split Q₂ depthReq c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂
      e₃ dW wEnd Rch Rc)
    (hR0 : ∀ z (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      Rch 0 ((atDesc F₀ TT).in₁ (instP z), (y, fun _ => [])))
    (hRc : ∀ b, Rch (1 + (atDesc F₀ TT).l₁.length) b → Rc b.1)
    (hpe : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec)
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = c₁ :: k₁) (q₂ : F₀.shared.blocksInOrder = c₂ :: k₂)
    (q₃ : F₀.second.blocksInOrder = c₃ :: k₃)
    (d : (F₀.XiPub × F₀.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : (kcReq N pp E).conf.X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
    (er : runP = gatedFileDecision b (F₀.pull instP).run)
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp)
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) N pp) E) DK DP runK runP ds xs dec rK rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP ds xs
      dec rK rP depthReq reqWithoutReply salt K P) :
    ∃ h₁ h₂ h₃, VerifierAndGoals.AtTheName.RowsOfProofFile (b := soundnessAnalysisDataAtFullSize Tl)
      (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP)
      { w₀ := ()
        P := plainP (lettersAt (claimsReqAt (frS.toDecR frZ 402653181) N pp)
            (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) N pp) E)) DP (front₀ rP) (join₀ rP)
          ByteArray.empty (F₀.pull instP) AL TP PLR h₁ h₂ h₃
          (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS))
          (L₁At F₀.start₂ TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) split)
          (L₂At ST3 TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) d
        κ₁ := _
        k₁ := fun b => keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc (F₀.pull instP) TP).p₂
          (atDesc (F₀.pull instP) TP).l₂ 0 ((atDesc (F₀.pull instP) TP).in₂ b.1, b.2)
        F₁ := fun rec y => (kS₂ rec, y, fun _ _ => none) } (soundnessAnalysisDataAtFullSize Tl).εs :=
  rows_of_tied_someR (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs arr ms
      Nn
    s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split Q₂ rP
        depthReq
    c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ Rch Rc hZ rq
    { scope_reads := R.scope_reads
      scope_public := R.scope_public
      scope_core := Hd.core_of_scope hZ R.scope_reads R.scope_public
      head_cuts := O.head_cuts
      EachGood := O.EachGood
      reach_at_start := hR0
      reply_leaves := O.reply_leaves
      shared_joint_count := O.shared_joint_count
      leads3_last_chains_table := O.leads3_last_chains_table
      tables_fit := O.tables_fit
      reach_at_end := hRc
      front_place_first := R.front_place_first
      start_is_the_requests := R.start_is_the_requests
      start_in_order := R.start_in_order
      start_public_items := R.start_public_items
      start_public_sentences := R.start_public_sentences
      front_no_trees := R.front_no_trees
      front_no_messages := R.front_no_messages
      requests_to_instances := R.requests_to_instances
      fin_is_canonical := R.fin_is_canonical
      public_part_free_of_reply := hpe
      shared_start_is_the_records := one
      seats_named := hN
      groups_seated := hG }
    hp hD q₁ q₂ q₃ d hb er Tl

end P5J

#check @P5J.RowsOwed
#print axioms P5J.rows_of_owed
