-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/SevenOfTables.lean: THE SEVEN FIELDS THAT ARE LEFT OF
    THE
PROOF FILE'S HYPOTHESIS ON SOUNDNESS BESIDE THE DATA (`ProofPlainSevenAtF`,
Johnson/Flat/Dec/ProofPlainLeft.lean), AT THE PROOF FILE'S OWN DESCRIPTION F₀ OVER ITS OWN
INSTANCES, WITH THE THREE CHAINS' TABLES OF JOINTS, hid, THE DECODER AND THE READERS LAID IN. One
theorem. NO RESULT ON THE PROTOCOL: a joining of rules, of whose premises no description is shown to
meet one. `RowsOfProofFile`: its premises as one
structure's fields, under the names of a list of laws owed (not in this library); `seven_of_rows`: the theorem from that structure.

  leads₁ := `leads_first_at_table` (LeadsFirst.lean): from hc, own₁ AT THE PIECES WITH THE TABLE'S
    EXTRACTOR LAID IN (`reExt`), rep₁: no premise on the letter e₁.
  leads₂: handed through (l₂).
  leads₃ := `leadsThreeAt` (Johnson/Desc/Sound/TablesGlues.lean): from own₃.
  glues := `glues_of_tables` at F₀.pull instP: from fitT and hst (`h0_at`).
  pubEarly, one: handed through.
  tie := `tie_at_table` (TieAt.lean): from hps, hst, hin, hpub, hpp, hbk, hms, hdec, eReq, eAsk,
    hfin, pubEarly.

WHAT IS LEFT: the scope (hR, h, A) · hc · own₁ · rep₁ · l₂ · own₃ · fitT · pubEarly · one · THIRTEEN
SENTENCES on the texts of F₀ and instP and on the table's letters: hps, hst, hin, hpub, hpp (the
public items that are open at the start, and their sentences, hold of a lawful first record), hbk,
hms (no tree and no message in front of the front block), hdec, eReq, eAsk, hfin, and hidAtSeat's
two public conditions hN, hG.

AS THINGS LIE THIS THEOREM SAYS NOTHING OF THE DESCRIPTION THAT IS SEATED. own₁ is a
sentence over LETTERS (the table's meaning's fields, the token's reader, the head's parts and more):
NO FILLING OF THEM IS KNOWN AT WHICH IT HAS A MEMBER THERE; at every filling that anybody has typed
or means, named grounds bar it (by reading and by runs, no theorem): the fixed text of the promise
lacks the kinds' files' public conditions; the forms' filling names slots that are filled only
inside the block that closes the item. (Of the first: in the table a public
condition that lacks comes as a filling of the meaning's field `more`: the promise's name does not
turn.)



THE READER OF THE REPLY IS `repHeard getS`: THROUGH THE ONE READING `S.heard`
(Johnson/Desc/First/StateHeard.lean), which over this base IS `out.reply`: the reply's own block
lays it. rep₁ is paid at no description.


Limits: those of the files named. Every piece carries the cap as its errors: own₁, l₂ and own₃ are
owed at the cap; no lemma here carries a kind's own errors to the cap: that is where the bits enter.
THE STATEMENT ON CODES HAS NO NAME HERE: the rounds that rest on it are swallowed in own₁, l₂ and
own₃. depthReq IS A FREE NUMBER, tied to no public file: l₂ multiplies a slot's error by 2 ^
depthReq. THE FULL SIZE ALONE (the frame's types). F₀ and instP are letters: no term at a real
description's own type of instances has been elaborated. Nothing on completeness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopTables
import Johnson.P5J.TieAt
import Johnson.P5J.LeadsFirst
import Johnson.Flat.Dec.ProofPlainLeft

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

set_option maxHeartbeats 4000000 in
/-- **THE SEVEN FIELDS, FROM THE THREE TABLES.** -/
theorem seven_of_tables (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (A : Hd.PublicCore X.P) (hc : HeadCuts pp putReq HH headPart)
    (own₁ : EachOwn
      (onQ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) Nn MQ fullLinks ps GET)
      (meansQ Nn MQ GET) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
      (reExt EX 0 ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁)))
    (rep₁ : EachRep tokOf fullLinks ps GET f (fun b => repHeard getS b.1) (QO).on₁ 0
      ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁))
    (l₂ : EachLawsBN (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F₀ TT).p₂ (atDesc F₀ TT).l₂)
      (PL).on₂ (PL).Q₂ (2 ^ depthReq) 0 ((atDesc F₀ TT).p₂ :: (atDesc F₀ TT).l₂))
    (own₃ : EachOwn
      (onQ₃ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₃ (TT).ft₃)
        (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) Pm PLm (ocEnd GET Nn MQ fullLinks ps))
      (meansQ₃ (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      ((TT).p₃ :: (TT).l₃))
    (fitT : TablesFit F₀.start₂ ST3 TT Q₀ GET Nn MQ fullLinks ps (firstAt pp putReq HH 0 GET) Ns MgS
      Pm PLm split Q₂)
    (hps : ps[0]? = some VerifiableInference.Desc.First.frontPlace) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (hst : ∀ p, VerifiableInference.Desc.First.IsStart codes (rq p) (getS (F₀.start₁ p)))
    (hin : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
      (meaningSig cs Gd arr smp ms DT Mg).inOrder
        (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) = true)
    (hpub : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
        (meaningSig cs Gd arr smp ms DT Mg).pub q (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP
    z)))) = true) (hpp : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
        (meaningSig cs Gd arr smp ms DT Mg).pubP q (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP
    z))))) (hbk : Nn.treesAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hms : Nn.msgsAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) (y, fun _ => [])).cell
          (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (eReq : ∀ z, reqB (F₀.pub (instP z)) = requestBytesOf z.1.val)
    (eAsk : ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat)
    (hfin : ∀ ξ s₁ s₂ s₃, F₀.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true)
    (pubEarly : ∀ x rec, F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec)))
    (one : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec) :
    ProofPlainSevenAtF F₀ instP (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DP rP depthReq
      reqWithoutReply c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd PL
      (fun a => meansM pp N DP F₀ AL HH GET 0 (repHeard getS) (instP a.1, a.2))
      (L₁At F₀.start₂ TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) split)
      (L₂At ST3 TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) () kS₂ :=
  ⟨leads_first_at_table N DP F₀ AL HH GET (repHeard getS) Q₀ Nn (withReq reqB Mg) ps headPart
      digitsPart cs Gd arr smp ms DT c₀ tokOf f (atDesc F₀ TT) hc own₁ rep₁ rfl,
    l₂,
    leadsThreeAt TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML Pm PLm
      (ocEnd GET Nn MQ fullLinks ps) own₃,
    glues_of_tables N DP (F₀.pull instP) AL HH GET (repHeard getS) Q₀ Nn MQ fullLinks ps TP EX Ns
      MgS ML Pm PLm split Q₂
      ⟨fitT.len₁, fitT.len₂, fitT.len₃, fitT.END, fitT.TP, fitT.SH, fitT.PW, fitT.START, fitT.SH₃,
        fitT.POf, fitT.POb, fitT.stepQ⟩
      (h0_at N E F₀ instP getS rq hst),
    pubEarly, one,
    fun x rec y _ s₁ s₂ s₃ z hok _ hf hM =>
      tie_at_table N E DP F₀ instP AL getS reqB DT asked d₀ 0 cs arr ms Nn s seat f hN hG hR h A
        (meaningSig cs Gd arr smp ms DT Mg) headPart digitsPart fullLinks ps hps rq hst hin hpub hpp
        hbk hms
        hdec eReq eAsk hfin pubEarly x rec y s₁ s₂ s₃ z hok hf hM⟩

/-- **THE PROOF FILE's ROWS**: the premises of `seven_of_tables`, one field a premise, under the
names of the list of laws owed (not in this library). THE LETTERS ARE THE
STRUCTURE's PARAMETERS (this section's variables, codes and rq), not one record. A STRUCTURE THAT
COMPILES SAYS NOTHING ON WHETHER ITS FIELDS CAN BE MET TOGETHER: no filling of the letters is known
at which `EachGood` has a member. -/
structure RowsOfProofFile (codes : OnBytes.Codes) (rq : F₀.XiPub → Array UInt32) : Prop where
  /-- the files are read -/
  scope_reads : VerifierAndGoals.readFiles Z = .ok pp
  /-- the program's public record of them -/
  scope_public : publicOf Z.pol Z.KL lay = .ok X
  /-- its core -/
  scope_core : Hd.PublicCore X.P
  /-- the head's four parts together give the head's half in plain integers -/
  head_cuts : HeadCuts pp putReq HH headPart
  /-- every piece of the first chain has its own law and lets the riders by, at the table's promises
  and items, with the table's extractor laid in -/
  EachGood : EachOwn
    (onQ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) Nn MQ fullLinks ps GET)
    (meansQ Nn MQ GET) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
    (reExt EX 0 ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁))
  /-- every piece leaves the heard reply, but where the table lays the token -/
  reply_leaves : EachRep tokOf fullLinks ps GET f (fun b => repHeard getS b.1) (QO).on₁ 0
    ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁)
  /-- the shared chain's pieces' laws, the slots behind one key -/
  shared_joint_count : EachLawsBN
    (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F₀ TT).p₂ (atDesc F₀ TT).l₂)
    (PL).on₂ (PL).Q₂ (2 ^ depthReq) 0 ((atDesc F₀ TT).p₂ :: (atDesc F₀ TT).l₂)
  /-- the last chain's pieces, at its table -/
  leads3_last_chains_table : EachOwn
    (onQ₃ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₃ (TT).ft₃)
      (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) Pm PLm (ocEnd GET Nn MQ fullLinks ps))
    (meansQ₃ (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) insQ₃ outsQ₃ (· ∈ startLast) 0
    ((TT).p₃ :: (TT).l₃)
  /-- the three tables fit the starts and each other: twelve fields -/
  tables_fit : TablesFit F₀.start₂ ST3 TT Q₀ GET Nn MQ fullLinks ps (firstAt pp putReq HH 0 GET) Ns
    MgS Pm PLm split Q₂
  /-- the list's first place is the front's -/
  front_place_first : ps[0]? = some VerifiableInference.Desc.First.frontPlace
  /-- the first chain's first record is a start at the request's words -/
  start_is_the_requests : ∀ p,
    VerifiableInference.Desc.First.IsStart codes (rq p) (getS (F₀.start₁ p))
  /-- "in order" holds at a first record without a mark -/
  start_in_order : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    (meaningSig cs Gd arr smp ms DT Mg).inOrder
      (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) = true
  /-- every public item that is open at the chain's start holds there -/
  start_public_items : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
      (meaningSig cs Gd arr smp ms DT Mg).pub q
        (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) = true
  /-- and its sentence, where it has one -/
  start_public_sentences : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
      (meaningSig cs Gd arr smp ms DT Mg).pubP q
        (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z))))
  /-- the plan's numbers: no tree and no message stand in front of the front block -/
  front_no_trees : Nn.treesAt (some VerifiableInference.Desc.First.frontPlace) = 0
  front_no_messages : Nn.msgsAt (some VerifiableInference.Desc.First.frontPlace) = 0
  /-- the map from requests to instances gives the key, the request's bytes, the asked reply -/
  requests_to_instances : (∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) (y, fun _ => [])).cell
          (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2) ∧
    (∀ z, reqB (F₀.pub (instP z)) = requestBytesOf z.1.val) ∧
    ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat
  /-- the last test's yes gives that the asked reply was heard -/
  fin_is_canonical : ∀ ξ s₁ s₂ s₃, F₀.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true
  /-- the public part does not hang on the reply -/
  public_part_free_of_reply : ∀ x rec,
    F₀.pub (instP (reqWithoutReply x, rec)) = F₀.pub (instP (x, rec))
  /-- the shared chain's first record is a function of the key file's record -/
  shared_start_is_the_records : ∀ x rec, F₀.start₂ (F₀.pub (instP (x, rec))) = kS₂ rec
  /-- hid's first public condition (ALSO A PARAMETER: the other fields' types hold its proof)
  -/
  seats_named : SeatsNamed arr Nn s seat
  /-- hid's second (the like) -/
  groups_seated : GroupsSeated ms Nn


/-- **THE SEVEN FIELDS, FROM THE PROOF FILE's ROWS**: `seven_of_tables`, its premises taken as one
structure. -/
theorem seven_of_rows {codes : OnBytes.Codes} (rq : F₀.XiPub → Array UInt32)
    (R : RowsOfProofFile (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs
      arr ms Nn s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split
      Q₂ depthReq c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ codes rq) :
    ProofPlainSevenAtF F₀ instP (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DP rP depthReq
      reqWithoutReply c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd PL
      (fun a => meansM pp N DP F₀ AL HH GET 0 (repHeard getS) (instP a.1, a.2))
      (L₁At F₀.start₂ TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) split)
      (L₂At ST3 TT (tiedNumbers Nn Ns) (tiedMeaning GET MQ MgS) ML) () kS₂ :=
  seven_of_tables N E DP F₀ instP getS reqB DT asked d₀ cs arr ms Nn s seat f hN hG Q₀ Mg ps
    headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split Q₂
      rP depthReq c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ R.scope_reads R.scope_public R.scope_core
    R.head_cuts R.EachGood R.reply_leaves R.shared_joint_count R.leads3_last_chains_table
    R.tables_fit R.front_place_first rq R.start_is_the_requests R.start_in_order
    R.start_public_items R.start_public_sentences R.front_no_trees R.front_no_messages
    R.requests_to_instances.1 R.requests_to_instances.2.1 R.requests_to_instances.2.2
    R.fin_is_canonical R.public_part_free_of_reply R.shared_start_is_the_records

end P5J

#print axioms P5J.seven_of_tables
#print axioms P5J.seven_of_rows
