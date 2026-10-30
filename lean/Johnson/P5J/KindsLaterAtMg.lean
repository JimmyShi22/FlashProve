-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/KindsLaterAtMg.lean: the proof file's rows with ALL THREE chains' laws asked kind by
kind. Of the five rows that `rows_at_mg` (Johnson/P5J/RowsAtMg.lean) asks beside the first chain's
kinds (`FiveF`, Johnson/P5J/TowerEnd.lean), two are laws of whole chains: `shared_joint_count` (the
shared chain) and `leads3_last_chains_table` (the last chain). Here each is replaced by one share
for each kind (Johnson/Desc/Sound/KindsLater.lean). Names, and calls of rules. The section's
variables and notations are TowerEnd.lean's own text, taken over by program.

  `SharedKindF … K`: every piece of the shared chain at a place of kind K in `sharedPlaces 𝔏.split`
    has its law for a batch of 2 ^ depthReq slots, between the shared table's condition `onQ₂` at
    its border and the relation 𝔏.Q₂ at its number, at its own error bounds.
  `LastKindF … K`: every piece of the last chain at a place of kind K in `lastPlaces` has its own
    law and keeps the items that ride past, at the last table's terms (`onQ₃`, `meansQ₃`).
  `ThreeF`: the three rows of `FiveF` that are left: head_cuts, reply_leaves, tables_fit.
  `fiveF_of_kinds`: ThreeF and all shares give FiveF. PAID HERE, from tables_fit: as many pieces as
    places (len₂, len₃), and the hand-over of the shared table's condition (stepQ's first half).
  `kinds_of_fiveF`: FiveF gives every share: the cut loses nothing.
  `AtMg.KindShared`, `AtMg.KindLast`, `AtMg.Three`: the same at the head `AtMg`'s letters.
  `rows_at_mg_kinds`: `rows_at_mg` with h.Five replaced by h.Three, four shares of the shared chain
    (frame, K1, K12, K14) and three of the last chain (frame, K12, K14).
  `AtMg.five_of_kinds`, `AtMg.five_of_all`, `AtMg.kinds_of_five`: h.Five from h.Three and the
    shares, and back.
  `AtMg.KindAll`, `rows_at_mg_all`: one premise for each kind: its shares of all three chains.

h.rch and h.rc read no letter of 𝔏; the first chain's share in `AtMg.KindAll` and in the two end
theorems is `AtMg.KindR`.

Limits. A joining of rules: it pays no law, and no member of a share or of h.Three is known. 𝔇₀ and
𝔏 are letters; 𝔏.Q₂, the relation in the shared chain's shares, is one of them, bound by
tables_fit.stepQ alone. `frame` is no kind of sub-protocol: two places of the shared chain's list
and two of the last chain's have it, and their shares are asked here like a kind's.
RowsAtMg.lean's own limits. No soundness follows. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Sound.KindsLater

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

open VerifiableInference.Desc (KindName)

/-- **One kind's share of the shared chain's laws.** -/
def SharedKindF (K : KindName) : Prop :=
  KindLawsBN (keyAt Prod.snd (DP.at frS.P.T.a).t₁ (atDesc F₀ TT).p₂ (atDesc F₀ TT).l₂)
    (onQ₂ (tiedNumbers Nn 𝔏.Ns) 𝔏.Pm (ocR GET Nn MQ fullLinks ps Rc) 𝔏.split (TT).p₂ (TT).l₂)
    𝔏.Q₂ (2 ^ depthReq) (sharedPlaces 𝔏.split) ((atDesc F₀ TT).p₂ :: (atDesc F₀ TT).l₂) K

/-- **One kind's share of the last chain's laws.** -/
def LastKindF (K : KindName) : Prop :=
  KindOwn
    (onQ₃ (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₃ (TT).ft₃)
      (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.Pm 𝔏.PLm (ocR GET Nn MQ fullLinks ps Rc))
    (meansQ₃ (tiedNumbers Nn 𝔏.Ns) (tiedMeaning GET MQ 𝔏.MgS) 𝔏.ML) insQ₃ outsQ₃ (· ∈ startLast)
    lastPlaces ((TT).p₃ :: (TT).l₃) K

/-- **The three rows that are left of the five.** -/
structure ThreeF : Prop where
  /-- the head's four parts together give the head's half in plain integers -/
  head_cuts : HeadCuts pp putReq HH headPart
  /-- every piece leaves the heard reply, but where the table lays the token -/
  reply_leaves : EachRep tokOf fullLinks ps GET f (fun b => repHeard getS b.1) (QO).on₁ 0
    ((atDesc F₀ TT).p₁ :: (atDesc F₀ TT).l₁)
  /-- the three tables fit the starts and each other: twelve fields -/
  tables_fit : TablesFitR F₀.start₂ ST3 TT 𝔏.Q₀ GET Nn MQ fullLinks ps (firstAt pp putReq HH 0 GET)
      𝔏.Ns
    𝔏.MgS 𝔏.Pm 𝔏.PLm 𝔏.split 𝔏.Q₂ Rc

/-- **The five rows, from the three and the two later chains' laws kind by kind.** -/
theorem fiveF_of_kinds
    (V : ThreeF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp tokOf Rc 𝔏)
    (H₂ : ∀ K, SharedKindF (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp Rc 𝔏 depthReq K)
    (H₃ : ∀ K, LastKindF (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp Rc 𝔏 K) :
    FiveF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp tokOf Rch Rc 𝔏 depthReq where
  head_cuts := V.head_cuts
  reply_leaves := V.reply_leaves
  shared_joint_count :=
    eachLawsBN_of_kinds _ _ _ _ (sharedPlaces 𝔏.split) _
      (by
        have e : 1 + (TT).l₂.length = (sharedPlaces 𝔏.split).length := V.tables_fit.len₂
        show (TT).l₂.length + 1 ≤ _
        omega) H₂
      fun i _ _ a b _ hq => (V.tables_fit.stepQ i a b hq).1
  leads3_last_chains_table :=
    eachOwn_of_kinds _ _ _ _ _ lastPlaces _
      (by
        have e : 1 + (TT).l₃.length = lastPlaces.length := V.tables_fit.len₃
        show (TT).l₃.length + 1 ≤ _
        omega) H₃
  tables_fit := V.tables_fit

/-- **The cut loses nothing.** -/
theorem kinds_of_fiveF
    (V : FiveF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp tokOf Rch Rc 𝔏 depthReq) :
    ThreeF (pp := pp) (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp tokOf Rc 𝔏 ∧
      (∀ K, SharedKindF (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp Rc 𝔏 depthReq K) ∧
      ∀ K, LastKindF (X := X) N DP F₀ getS reqB DT d₀ cs arr ms Nn s seat f hN hG Mg ps
      headPart digitsPart Gd smp Rc 𝔏 K :=
  ⟨⟨V.head_cuts, V.reply_leaves, V.tables_fit⟩,
    kindLawsBN_of_each _ _ _ _ _ _ V.shared_joint_count,
    kindOwn_of_each _ _ _ _ _ _ _ V.leads3_last_chains_table⟩

end Tower

section Head

open VerifiableInference.Desc (Chain KindName)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Kind K's share of the shared chain's laws, at the head's letters.** -/
def AtMg.KindShared (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (K : KindName) : Prop :=
  SharedKindF (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s) (fun q
      : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp)
    h.rc 𝔏 depthReq K

/-- **Kind K's share of the last chain's laws, at the head's letters.** -/
def AtMg.KindLast (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName) : Prop :=
  LastKindF (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s) (fun q
      : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp)
    h.rc 𝔏 K

/-- The three rows that are left of the five, at the head's letters. -/
def AtMg.Three (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  ThreeF (pp := ppAtFiles Z.pol Z.KL) (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s) (fun q
      : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    h.rc 𝔏

/-- **h.Five, from h.Three and seven shares by name.** -/
theorem AtMg.five_of_kinds (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Three 𝔇₀ 𝔏)
    (s₀ : h.KindShared 𝔇₀ 𝔏 depthReq .frame) (s₁ : h.KindShared 𝔇₀ 𝔏 depthReq .K1)
    (s₁₂ : h.KindShared 𝔇₀ 𝔏 depthReq .K12) (s₁₄ : h.KindShared 𝔇₀ 𝔏 depthReq .K14)
    (t₀ : h.KindLast 𝔇₀ 𝔏 .frame) (t₁₂ : h.KindLast 𝔇₀ 𝔏 .K12) (t₁₄ : h.KindLast 𝔇₀ 𝔏 .K14) :
    h.Five 𝔇₀ 𝔏 depthReq :=
  fiveF_of_kinds (Rch := h.rch) (V := V)
    (H₂ := kindLawsBN_of_four _ _ _ _ _ _ s₀ s₁ s₁₂ s₁₄)
    (H₃ := kindOwn_of_three _ _ _ _ _ _ t₀ t₁₂ t₁₄)

set_option maxHeartbeats 4000000 in
/-- **What is left of the seven at the verifier's own value: every chain's laws kind by kind, and
three rows.** -/
theorem rows_at_mg_kinds (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.KindR 𝔇₀ 𝔏 K)
    (s₀ : h.KindShared 𝔇₀ 𝔏 depthReq .frame) (s₁ : h.KindShared 𝔇₀ 𝔏 depthReq .K1)
    (s₁₂ : h.KindShared 𝔇₀ 𝔏 depthReq .K12) (s₁₄ : h.KindShared 𝔇₀ 𝔏 depthReq .K14)
    (t₀ : h.KindLast 𝔇₀ 𝔏 .frame) (t₁₂ : h.KindLast 𝔇₀ 𝔏 .K12) (t₁₄ : h.KindLast 𝔇₀ 𝔏 .K14)
    (V : h.Three 𝔇₀ 𝔏)
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (EAll (D.at frS.P.T.a)
        (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : (kcReq numsFull (ppAtFiles Z.pol Z.KL) (At.EAt Z)).conf.X × RecFull → PQ.View → PQ.View
        → PQ.View → Bool}
    (er : runP = gatedFileDecision b ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL)) (At.EAt Z))
          DK D runK runP ds xs dec rK 𝔏.rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
        (At.EAt Z) DK D runK runP ds xs
      dec rK 𝔏.rP depthReq reqWithoutReply salt K P) :
    h.Seven 𝔇₀ 𝔏 depthReq d Tl :=
  rows_at_mg h 𝔇₀ 𝔏 depthReq q₁ q₂ q₃ kinds
    (h.five_of_kinds 𝔇₀ 𝔏 depthReq V s₀ s₁ s₁₂ s₁₄ t₀ t₁₂ t₁₄) d hb er Tl

/-- **ONE LAW FOR EACH KIND: kind K's shares of all three chains.** The first chain's is
`AtMg.KindR` (RowsAtMg.lean): the share that the tower takes; `AtMg.Kind` gives it. -/
def AtMg.KindAll (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (K : KindName) : Prop :=
  h.KindR 𝔇₀ 𝔏 K ∧ h.KindShared 𝔇₀ 𝔏 depthReq K ∧ h.KindLast 𝔇₀ 𝔏 K

/-- **h.Five, from h.Three and one premise for each kind.** -/
theorem AtMg.five_of_all (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Three 𝔇₀ 𝔏)
    (kinds : ∀ K, h.KindAll 𝔇₀ 𝔏 depthReq K) : h.Five 𝔇₀ 𝔏 depthReq :=
  h.five_of_kinds 𝔇₀ 𝔏 depthReq V (kinds .frame).2.1 (kinds .K1).2.1 (kinds .K12).2.1
    (kinds .K14).2.1 (kinds .frame).2.2 (kinds .K12).2.2 (kinds .K14).2.2

/-- **The cut loses nothing, at the head**: h.Five gives h.Three and every later share. -/
theorem AtMg.kinds_of_five (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Five 𝔇₀ 𝔏 depthReq) :
    h.Three 𝔇₀ 𝔏 ∧ (∀ K, h.KindShared 𝔇₀ 𝔏 depthReq K) ∧ ∀ K, h.KindLast 𝔇₀ 𝔏 K :=
  kinds_of_fiveF (Rch := h.rch) (V := V)

set_option maxHeartbeats 4000000 in
/-- **The same with one premise for each kind.** -/
theorem rows_at_mg_all (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.KindAll 𝔇₀ 𝔏 depthReq K) (V : h.Three 𝔇₀ 𝔏)
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (EAll (D.at frS.P.T.a)
        (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : (kcReq numsFull (ppAtFiles Z.pol Z.KL) (At.EAt Z)).conf.X × RecFull → PQ.View → PQ.View
        → PQ.View → Bool}
    (er : runP = gatedFileDecision b ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL)) (At.EAt Z))
          DK D runK runP ds xs dec rK 𝔏.rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
        (At.EAt Z) DK D runK runP ds xs
      dec rK 𝔏.rP depthReq reqWithoutReply salt K P) :
    h.Seven 𝔇₀ 𝔏 depthReq d Tl :=
  rows_at_mg_kinds h 𝔇₀ 𝔏 depthReq q₁ q₂ q₃ (fun K => (kinds K).1)
    (kinds .frame).2.1 (kinds .K1).2.1 (kinds .K12).2.1 (kinds .K14).2.1
    (kinds .frame).2.2 (kinds .K12).2.2 (kinds .K14).2.2 V d hb er Tl

end Head

end P5J

#print axioms P5J.fiveF_of_kinds
#print axioms P5J.kinds_of_fiveF
#print axioms P5J.AtMg.five_of_kinds
#print axioms P5J.AtMg.five_of_all
#print axioms P5J.AtMg.kinds_of_five
#print axioms P5J.rows_at_mg_kinds
#print axioms P5J.rows_at_mg_all
