-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeLeft.lean: `AtMg.Three` FROM WHAT IS LEFT OF IT, ONCE THE FIELDS THAT HAVE A PAYER
ARE PAID.

`AtMg.Three h 𝔇₀ 𝔏` (Johnson/P5J/KindsLaterAtMg.lean) asks three rows: head_cuts, reply_leaves and
tables_fit. The last is the structure `TablesFitR` of twelve fields (Johnson/P5J/TopTablesR.lean).
This file pays, inside, each of the fourteen that has a payer which can be called here. It states
what is left, each field under its own name and in its own letters.

PAID INSIDE (7 of fourteen), at the second hash function `OnBytes.secondHashFunction`:
  START: `AtMg.start_field` (Johnson/P5J/StartFieldAtMg.lean); no premise.
  SH: `AtMg.sh_of_start` (Johnson/P5J/KeyFitsAtMg.lean); from the one fact hk.
  END: `end_at_ps` (Johnson/P5J/EndFieldFits.lean); no premise.
  len₁ · len₂: `OnBytes.Road.Tables.len₁_of` | `len₂_of` (Johnson/Road/Tables/TablesLen.lean); from
    the head and q₁ q₂ q₃; len₂ also from hsp.
  len₃: `ToldDesc.third_length` (Johnson/ToldDescR/LengthsAtTable.lean); from the head and q₁ q₂ q₃.
  reply_leaves: `reply_leaves_at_mg` (Johnson/P5J/ReplyLeavesAtMg.lean); from q₁ q₂ q₃.
PREMISES THAT THESE LEAVE: hk · q₁ q₂ q₃ (each chain's flat list is 𝔏's head and tail) · hsp
(𝔏.split = true).

LEFT (7 of fourteen):
  head_cuts · TP · PW · SH₃ · POf · POb · stepQ

  `TablesLeft`: the fields of `TablesFitR` that are left.
  `TablesLeft.toR`: with the paid ones it gives `TablesFitR`. `TablesFitR.toLeft`: the way back.
  `ThreeLeftF`: what is left of `ThreeF`, at its letters.
  `AtMg.ThreeLeft`: the same at the letters of `AtMg.Three`.
  **`AtMg.three_of_left`**: what is left gives `AtMg.Three`.
  `AtMg.left_of_three`: `AtMg.Three` gives what is left, so `ThreeLeft` asks nothing new.
  The same at the closed constant (`AtMgA`): Johnson/P5J/ThreeLeftAtAll.lean.

How it is made. A program cuts the fields' texts, the letters and the local notations out of
TopTablesR.lean and Johnson/P5J/TowerEnd.lean, and the head's letters out of KindsLaterAtMg.lean.
One comment of a notation is reworded; no letter of Lean's parts.
When a further field gets a payer, the file is cut anew with that field paid inside.
So it is one file that shrinks, not a row of files.

Limits. A joining: it pays no field by itself. No member of `ThreeLeft` is known.
It is general in 𝔏: at which 𝔏 the fields that are left can be met is not said here.
If `TablesFitR` or `ThreeF` turns, `toR` and `three_of_left` fail to compile: a drift that changes a
field's meaning cannot pass.
No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.KindsLaterAtMg
import Johnson.P5J.KeyFitsAtMg
import Johnson.P5J.StartFieldAtMg
import Johnson.Road.Tables.TablesLen
import Johnson.ToldDescR.LengthsAtTable
import Johnson.P5J.EndFieldFits
import Johnson.P5J.ReplyLeavesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

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
open VerifiableInference.Desc (Chain KindName)
open Desc.K14 (p14Of beforePointOf first)

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
  (Rc : P × S₁' → Prop)

/-- **The fields of `TablesFitR` that are left**, to the letter. -/
structure TablesLeft : Prop where
  TP : ∀ b : (P × S₁') × (EAll D all).Str,
    Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
    Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))
  PW : ∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
    Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
    Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w
  SH₃ : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂ (1 + T.l₂.length) b →
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
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ (k + 1) b w) →
        ∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ k a w)

variable {start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc}

/-- What is left and what is paid give the twelve. -/
theorem TablesLeft.toR
    (t : TablesLeft start₂ start₃ T get N₁ Mg₁ links ps Ns Mg Pm PLm split Q₂ Rc)
    (len₁ : 1 + T.l₁.length = ps.length)
    (len₂ : 1 + T.l₂.length = (sharedPlaces split).length)
    (len₃ : 1 + T.l₃.length = lastPlaces.length)
    (END : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i →
    i ∈ endFirst)
    (SH : ∀ b : (P × S₁') × (EAll D all).Str,
    (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b → Rc b.1 →
    Pm.shape 0 (start₂ b.1.1) = true)
    (START : ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → (tiedMeaning get Mg₁ Mg).unmarked1 (p, s₁)) :
    TablesFitR start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc :=
  ⟨len₁, len₂, len₃, END, t.TP, SH, t.PW, START, t.SH₃, t.POf, t.POb, t.stepQ⟩

/-- The twelve hold what is left. -/
theorem TablesFitR.toLeft
    (t : TablesFitR start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc) :
    TablesLeft start₂ start₃ T get N₁ Mg₁ links ps Ns Mg Pm PLm split Q₂ Rc :=
  ⟨t.TP, t.PW, t.SH₃, t.POf, t.POb, t.stepQ⟩

end Fit

section Tower
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
/-- The first chain's state as the table reads it. -/
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

/-- **What is left of `ThreeF`.** -/
structure ThreeLeftF : Prop where
  /-- the head's four parts together give the head's half in plain integers -/
  head_cuts : HeadCuts pp putReq HH headPart
  /-- the three tables fit the starts and each other: the fields that are left -/
  tables_left : TablesLeft F₀.start₂ ST3 TT GET Nn MQ fullLinks ps
    𝔏.Ns 𝔏.MgS 𝔏.Pm 𝔏.PLm 𝔏.split 𝔏.Q₂ Rc

end Tower

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- What is left of `AtMg.Three`, at its own letters. -/
def AtMg.ThreeLeft (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  ThreeLeftF (pp := ppAtFiles Z.pol Z.KL) (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s)
      (fun q : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp)
    h.rc 𝔏

/-- **`AtMg.Three` from what is left of it.** -/
theorem AtMg.three_of_left (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (hk : ∀ z : LPFD.Full.XF × RecFull, 𝔏.Pm.shape 0
      (first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hsp : 𝔏.split = true)
    (V : h.ThreeLeft 𝔇₀ 𝔏) : h.Three 𝔇₀ 𝔏 :=
  ThreeF.mk V.head_cuts
    (reply_leaves_at_mg h 𝔏 q₁ q₂ q₃ _)
    (V.tables_left.toR
      (OnBytes.Road.Tables.len₁_of h.scope h.reads h.laid (h.ofDesc 𝔏 q₁ q₂ q₃))
      (by rw [hsp]; exact OnBytes.Road.Tables.len₂_of h.scope h.laid (h.ofDesc 𝔏 q₁ q₂ q₃))
      (ToldDesc.third_length h.laid.value (h.ofDesc 𝔏 q₁ q₂ q₃))
      (end_at_ps)
      (fun b _ hr => h.sh_of_start 𝔏 hk b.1 hr)
      (h.start_field 𝔇₀ 𝔏))

/-- `ThreeLeft` asks nothing that `Three` did not ask. -/
theorem AtMg.left_of_three (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (V : h.Three 𝔇₀ 𝔏) : h.ThreeLeft 𝔇₀ 𝔏 :=
  ThreeLeftF.mk V.head_cuts V.tables_fit.toLeft

end P5J

#print axioms P5J.TablesLeft.toR
#print axioms P5J.TablesFitR.toLeft
#print axioms P5J.AtMg.three_of_left
#print axioms P5J.AtMg.left_of_three
