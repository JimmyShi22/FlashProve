-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopTables.lean: THE PLAIN ROAD'S END THEOREM WITH ALL THREE CHAINS' TABLES LAID IN: THE
THREE GLUES ARE NO PREMISE ANY MORE. One record of premises, one definition (`plTables`: the second
and the third chain's conditions and relations off their tables), two theorems. NO RESULT ON THE
PROTOCOL: rules, of whose premises no description of the protocol is shown to meet one.
What is said.
  `TablesFit`: the named premises under which the three tables fit together at the chains' ends, as
    other files state them (Johnson/Desc/Sound/TieEnd.lean, TablesGlues.lean): three lengths; END
    (what is open behind the first chain's last block is what the shared chain takes over); TP, PW
    (the stored table's promise and pin, read by the two chains' readers); SH, SH₃ (two tests on the
    records that the starts make, asked inside the promises); START (the last chain's start says
    yes at no marked record); POf, POb (one tree's promise and pin between the acting part's
    strings and the whole); stepQ (each relation of the shared chain gives the table's promise
    behind and carries "there is a witness" to the front).
  `glues_of_tables`: AT A DESCRIPTION OVER ANY TYPE OF INSTANCES: **the record `Glues` WHOLE, AS A
    TERM**: g₁ by `glue_first_at_means` from the two halves of the first joint; g₂, g₃ by
    `glueTwoAt`, `glueThreeAt` (TablesGlues.lean).
  `proofSound_plain_of_tables`: **THE END THEOREM**: `proofSound_plain_of_own` with G so paid, and
    e₃ by `leadsThreeAt` (TablesGlues.lean) from what the last chain's kinds' files owe (own₃).

WHAT IS LEFT ON THE PLAIN ROAD: own₁, own₃ (the kinds' laws at two tables) · e₂ (the shared chain's,
for many slots behind one key) · extq, rep₁, htok · hc · `TablesFit` · h0 · first_border_on, hd, hp,
pubEarly, finReply, oneKey (facts on the description and on the letters that read it) · hO, hf, fit
· three bounds · the scope (hR, h, A) · AND, INSIDE THE RECORD H, `H.seams`. e₂ HAS NO PAYER AT THIS
WRITING: our own rule for it was empty at the shared chain's front block and is withdrawn; a mend
in other files is what is meant there. LETTERS THAT NOTHING HERE TIES TO THE DESCRIPTION: Q₂ (stepQ
wants it strong, e₂ wants it weak: at "false" e₂ asks that every shared block refuses, at "true"
stepQ fails; MEANT IS WHAT LIES BETWEEN: the shared chain's own relation of a block's two
statements: a thought, shown of no chain) · key · Ns · MgS · ML · Pm · PLm. TP and PW run over every
statement, with no promise: payable where the first chain's decoder reads the public part alone.

Limits: those of TopTable.lean and of the tables' files. THE TRUTHS L₁, L₂ ARE "there is a
witness": the token is carried on the first chain alone. Nothing on completeness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopTable
import Johnson.Desc.Sound.TablesGlues

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

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

section Fit
variable {C : CK} {D : WholeD} {all : List LeftT} {Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type}
  (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
  (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
  (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
  (get : P × S₁' → P₀ × VerifiableInference.Desc.First.S) (N₁ : Numbers)
  (Mg₁ : VerifiableInference.Desc.First.Meaning P₀ W) (links : List ModelPart) (ps : List Place)
  (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
  (Mg : MeaningS S₂' (P × S₁') W) (ML : MeaningL S₃' W) (Pm : PromMeaning S₂')
  (PLm : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool)
  (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop)

/-- **The named premises under which the three tables fit together at the chains' ends.** -/
structure TablesFit : Prop where
  len₁ : 1 + T.l₁.length = ps.length
  len₂ : 1 + T.l₂.length = (sharedPlaces split).length
  len₃ : 1 + T.l₃.length = lastPlaces.length
  END : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i →
    i ∈ endFirst
  TP : ∀ b : (P × S₁') × (EAll D all).Str,
    Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
    Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))
  SH : ∀ b : (P × S₁') × (EAll D all).Str,
    (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b →
    Pm.shape 0 (start₂ b.1.1) = true
  PW : ∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
    Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
    Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w
  START : ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → (tiedMeaning get Mg₁ Mg).unmarked1 (p, s₁)
  SH₃ : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ (1 + T.l₂.length) b →
    start₃ b.1.1.1 b.1.1.2 b.1.2 = some s → PLm.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true
  POf : ∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
    (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
      (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
    (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm b.1.2
      (strsOf (frameAt D all D.key₃ T.ft₃) b.2)
  POb : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : W),
    (ItemS.pin .oOmega).holdsSh (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) b.1.2
      (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
    muQ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w
  stepQ : ∀ k a b, Q₂ k a b →
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ (k + 1) b w) →
        ∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ k a w)

/-- The plain road's conditions and relations at the second and the third chain, from their tables;
the first chain's two fields are laid over by whoever calls it. -/
def plTables : PPlaces D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') where
  on₁ := fun _ _ => True
  Q₁ := fun _ _ _ => True
  on₂ := onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂
  Q₂ := Q₂
  on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm
    PLm (ocEnd get N₁ Mg₁ links ps)
  Q₃ := stepQ₃ T (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) ML Pm PLm
    (ocEnd get N₁ Mg₁ links ps)

end Fit

section Plain

variable {pp : ScalesAndPolicy} {X : Model.Verify.Public} (N : MatrixNums) (DP : WholeD) {Xi : Type}
  (F : FileDescription Xi) (all : List LeftT) {W P : Type} (H : HidAt X P W N.rows (colsAt N))
  (get : F.XiPub × F.S₁ → P × TS) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F W) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
  {X₁ X₂ : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Ex : ℕ → (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → W → W)
  (Ns : NumbersS) (MgS : MeaningS F.S₂ (F.XiPub × F.S₁) W) (ML : MeaningL F.S₃ W)
  (Pm : PromMeaning F.S₂) (PLm : PromMeaningL F.S₂ F.S₃ (F.XiPub × F.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str →
    ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F.start₃ p a b).toOption

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from its table. -/
local notation "QM" => placesM (D := DP.at frS.P.T.a) (all := all) T.ft₁ Nn Mg links ps get
  (firstAt pp putReq H T.ft₁ get) Q₀

set_option quotPrecheck false in
/-- The relation of a block's two statements on the first chain. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁)
  (QM).on₁ (QM).R₁ Ex (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1)

set_option quotPrecheck false in
/-- The second and the third chain's, from their tables. -/
local notation "PT" => plTables T get Nn Mg links ps Ns MgS ML Pm PLm split Q₂

set_option quotPrecheck false in
/-- All three. -/
local notation "PL" => ({ PT with on₁ := (QM).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PLAIN ROAD'S THREE GLUES, AS ONE TERM, AT THE THREE TABLES.** -/
theorem glues_of_tables
    (fitT : TablesFit F.start₂ ST3 T Q₀ get Nn Mg links ps (firstAt pp putReq H T.ft₁ get) Ns MgS Pm
      PLm split Q₂)
    (h0 : ∀ x, repS (F.pub x, F.start₁ (F.pub x)) = none) :
    Glues (atDesc F T) PL (meansM pp N DP F all H get T.ft₁ repS)
      (L₁At F.start₂ T (tiedNumbers Nn Ns) (tiedMeaning get Mg MgS) split)
      (L₂At ST3 T (tiedNumbers Nn Ns) (tiedMeaning get Mg MgS) ML) :=
  ⟨glue_first_at_means N DP F all H get T.ft₁ repS Q₀ Nn Mg links ps Ex T PT
      (L₁At F.start₂ T (tiedNumbers Nn Ns) (tiedMeaning get Mg MgS) split)
      (onZeroOfEnd _ _ _ _ _ _ _ _ _ _ _ _ _ F.start₂ T Q₀ get Nn Mg links ps
        (firstAt pp putReq H T.ft₁ get) Ns MgS Pm split fitT.len₁ fitT.TP fitT.SH)
      (fun b hL => hL.elim fun w hw =>
        ⟨w, relEndOfZero _ _ _ _ _ _ _ _ _ _ _ _ _ F.start₂ T Q₀ get Nn Mg links ps
          (firstAt pp putReq H T.ft₁ get) Ns MgS Pm split fitT.len₁ fitT.END fitT.PW b w hw⟩)
      h0,
    glueTwoAt _ _ _ _ _ _ _ _ _ _ _ _ F.pub F.start₁ F.start₂ ST3 T (tiedNumbers Nn Ns)
      (tiedMeaning get Mg MgS) ML Pm PLm (ocEnd get Nn Mg links ps) split Q₂ fitT.stepQ fitT.len₂
      fitT.START fitT.SH₃ fitT.POf fitT.POb,
    glueThreeAt _ _ _ _ _ _ _ _ _ _ _ _ F.pub F.start₁ F.start₂ ST3 T (tiedNumbers Nn Ns)
      (tiedMeaning get Mg MgS) ML Pm PLm (ocEnd get Nn Mg links ps) fitT.len₃⟩

end Plain

#print axioms glues_of_tables

section End

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  (F : FileDescription ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)) (all : List LeftT)
  {P Cells Tok : Type} (H : HidAt X P (Wit Cells Tok MsgT) N.rows (colsAt N))
  (get : F.XiPub × F.S₁ → P × TS) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F (Wit Cells Tok MsgT)) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P (Wit Cells Tok MsgT)) (ps : List Place)
  (headPart : TPart → Cm.Idx → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (digitsPart : ℕ → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (cs : OnBytes.Codes) {Xi : Type} (Gd : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × TS → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (ms : List VerifiableInference.Desc.Sound.Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × TS → Option Cells) (c₀ : Cells)
  (tokOf : P × TS → Tok) (f : Tok → Fin ppref.V)
  (DK : WholeD) {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k)
  (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silK : (kcReq N pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding (kcReq N pp E).conf.Rec frS.P.T.a) (n : ℕ) {X₁ X₂ κ : Type}
  (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ (Wit Cells Tok MsgT))
  (Ns : NumbersS) (MgS : MeaningS F.S₂ (F.XiPub × F.S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL F.S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning F.S₂)
  (PLm : PromMeaningL F.S₂ F.S₃ (F.XiPub × F.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str →
    ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → κ)
  (Pv : (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL n
    reqWithoutReply none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                    eL n reqWithoutReply none) Pv)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                     eL n reqWithoutReply none) Pv)

set_option quotPrecheck false in
/-- The table's meaning: its parts the integer model's own clauses; ITS SIX LETTERS ON THE READING
OF THE ORACLES FILLED AT THE VERY EIGHT LETTERS AT WHICH THE EXTRACTOR DECODES (`meaningSig`). -/
local notation "MQ" => meaningQ putReq H headPart digitsPart
  (meaningSig cs Gd arr smp ms decT Mg)

set_option quotPrecheck false in
/-- The number that the first chain's frame bears, at the filling. -/
local notation "FT" => (atDesc F T).ft₁

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := all) FT Nn MQ fullLinks ps get
  (firstAt pp putReq H FT get) Q₀

set_option quotPrecheck false in
/-- The table's one extractor, as a function of a block's two statements and the witness behind. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) cs Gd
  arr smp ms decT c₀ tokOf Nn fullLinks ps get

set_option quotPrecheck false in
/-- The relation of a block's two statements, at the table's extractor. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) (QO).on₁
  (QO).R₁ EX (TokStep EX (fun w => (H.hid w).tok) fun b => repS b.1)

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F.start₃ p a b).toOption

set_option quotPrecheck false in
/-- The second and the third chain's conditions and relations, from their tables. -/
local notation "PT" => plTables T get Nn MQ fullLinks ps Ns MgS ML Pm PLm split Q₂

set_option quotPrecheck false in
/-- The truth behind the first chain: there is a witness at the shared chain's first border. -/
local notation "LL1" => L₁At F.start₂ T (tiedNumbers Nn Ns) (tiedMeaning get MQ MgS) split

set_option quotPrecheck false in
/-- The truth behind the second chain: the like at the last chain's first border. -/
local notation "LL2" => L₂At ST3 T (tiedNumbers Nn Ns) (tiedMeaning get MQ MgS) ML

set_option quotPrecheck false in
/-- The plain road's conditions and relations: all three chains' from their tables. -/
local notation "PL" => ({ PT with on₁ := (QO).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PROOF FILE'S NAMED HYPOTHESIS ON SOUNDNESS, AT A DESCRIPTION'S OWN DECISION, ON THE PLAIN
ROAD, WITH ALL THREE CHAINS' TABLES LAID IN**: the three glues and the last chain's premise are no
premises any more. -/
theorem proofSound_plain_of_tables (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hc : HeadCuts pp putReq H headPart)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fit : RowFit (DP.at frS.P.T.a) all all)
    (own₁ : EachOwn
      (onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) Nn MQ fullLinks ps get)
      (meansQ Nn MQ get) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (extq : EachExtQ cs Gd arr smp ms decT c₀ tokOf Nn fullLinks ps get 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (rep₁ : EachRep tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (htok : (fun w => (H.hid w).tok) = fun w : Wit Cells Tok MsgT => f w.tok)
    (e₂ : EachLeadsBN key (PL).on₂ (PL).Q₂ n 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (own₃ : EachOwn
      (onQ₃ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₃ T.ft₃) (tiedNumbers Nn Ns)
        (tiedMeaning get MQ MgS) Pm PLm (ocEnd get Nn MQ fullLinks ps))
      (meansQ₃ (tiedNumbers Nn Ns) (tiedMeaning get MQ MgS) ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      (T.p₃ :: T.l₃))
    (fitT : TablesFit F.start₂ ST3 T Q₀ get Nn MQ fullLinks ps (firstAt pp putReq H T.ft₁ get) Ns
      MgS Pm PLm split Q₂)
    (h0 : ∀ x, repS (F.pub x, F.start₁ (F.pub x)) = none)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      (QO).on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) (y, fun _ => [])) =
        (kcReq N pp E).conf.D y x.2)
    (hp : ∀ x, H.req (get (F.pub x, F.start₁ (F.pub x))) = reqWithoutReply x.1)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (finReply : ∀ x rec s₁ s₂ s₃, F.fin (x, rec) s₁ s₂ s₃ = true →
      repS (F.pub (x, rec), s₁) = some (dropReq x))
    (F₁ : (kcReq N pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (kcReq N pp E) DP tFp tJp t3p F all T PL h₁ h₂ h₃
        (meansM pp N DP F all H get FT repS) LL1 LL2 d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) U.εs)
    (b₂ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) U.εs)
    (b₃ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               runK silP F.run eL n reqWithoutReply none) Pv Tl U) :=
  proofSound_plain_of_own N E DP F all H get repS Q₀ Nn Mg ps headPart digitsPart cs Gd arr smp ms
    decT c₀ tokOf f DK tFk tJk t3k tFp tJp t3p silK runK silP eL n T PT h₁ h₂ h₃ LL1 LL2 d key Pv Tl
    U hR h A hc hO hf fit own₁ extq rep₁ htok e₂
    (leadsThreeAt T (tiedNumbers Nn Ns) (tiedMeaning get MQ MgS) ML Pm PLm
      (ocEnd get Nn MQ fullLinks ps) own₃)
    (glues_of_tables N DP F all H get repS Q₀ Nn MQ fullLinks ps T EX Ns MgS ML Pm PLm split Q₂
      fitT h0)
    first_border_on hd hp pubEarly finReply F₁ oneKey b₁ b₂ b₃

end End

#print axioms proofSound_plain_of_tables

end P5J
