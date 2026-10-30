-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RowsAtMg.lean: WHAT A KIND'S COUNTED LAW BUYS, AND WHAT IS LEFT OF THE PROOF FILE'S
    SEVEN FIELDS AT THE VERIFIER'S OWN VALUE: WITH WRITTEN STATEMENTS, under the one head `AtMg`
    (AtMg.lean), at the
composed meaning's constant `mgAt` (MgAtConst.lean), "reached" named (`RchAt`, ReachAt.lean:
    the families step by the wrapped sub-protocols).
  `headLink_in_scope`: in scope the head's segment has the number 24 (by
      `Meaning.scope_plans`: profile 4, twelve groups). (headLink_scope, K03PlanOf.lean, says
    the same, by a text of ours, not in this repository; its file is not in this file's cone.)
  **`mgAt_is_mq`**: THE CONSTANT mgAt h 𝔇₀ IS THE MEANING AT WHICH THE TOWER STANDS (`mqF`,
      TowerEnd.lean, at the seated term's letters): by
    `mgAll_is_tower` (MgAll.lean). (`mgAt_is_tower`, MgAtConst.lean, says the
        like at its own spelling, under headLink = 24 as a premise.)
  `AtMg.Kind h 𝔇₀ 𝔏 K`: kind K's share of the chain of promises, second form, AT mgAt: `KindTiedR`
      (Johnson/Desc/Sound/TiedR.lean) at the first chain's own
    pieces, the table's own extractor and RchAt: THE FORM IN WHICH A KIND's FILES END ITS LAW.
  **`good_of_kinds`**: all kinds' shares (h.KindR), the three lists' heads and hlen ⟹ `GoodF` at
      these letters: the tower's field EachGood. The hand-on of "reached" is paid here, kind-free
    (`rchAt_hand`).
  `AtMg.Five` · `AtMg.Seven`: `FiveF` · `SevenF` at these letters.
  **`rows_at_mg`**: AtMg → the three lists' heads → (∀ K, h.KindR 𝔇₀ 𝔏 K) → h.Five 𝔇₀ 𝔏 depthReq →
      the open gate (hb er) → h.Seven …: every other premise of `seven_of_owedF` is paid: the eleven
    facts on a start (`AtMg.tieStart`), "reached" at every start (`rchAt_zero`), Rch at the first
        chain's
        end (as many pieces as sub-protocols: `OfDesc`), the two build
    equations, the list of rounds' accept, the data.
THE RIDER BESIDE "REACHED" IS h.typed ("the public part is a typed instance's": ∃ z, p
    = (instanceAsPlainRecord z).pub): h.rch and h.rc read no letter of 𝔏;
    at the start the rider is ⟨z, rfl⟩. The field SH of
`tables_fit` has h.rc b.1 in hand: its payer: `AtMg.sh_of_start` (KeyFitsAtMg.lean), from one fact
    on the shared chain's first state at a typed key.

AND: `AtMg.KindR`: kind K's share AT h.rch: WHAT `good_of_kinds` AND `rows_at_mg` TAKE: a kind
    whose law needs the typed instance can pay it; `AtMg.Kind` (at bare RchAt)
    gives it for nothing (`AtMg.Kind.toR`). THE COUNTED FIELD, AT THE CLOSED CONSTANT:
    RowsAtAll.lean.










    The constant's H
stands at the label's form of the seats (seatBy (fLay …)).
THE ORDER OF PREMISES IN A KIND's LAW: in scope → the value is laid → the named tests on the list
    of rounds accept [ALL THREE ARE FIELDS OF AtMg] → the facts along the fold
[they stand in NO statement of this file: a law that spends one takes it as a premise in front of
    its h.Kind: AtMgR (AtMgR.lean) extends AtMg by them] → h.Kind 𝔇₀ 𝔏 K.
WHERE EMPTINESS CAN STILL ENTER: no premise here names a struck public item; but a kind's PROOF of
    h.Kind is empty if it calls, at mgAt, a first-form structure that asks one.
At a kind without a place in At.ps, h.Kind is free.
Limits. A JOINING: IT PAYS NO LAW. No member of h.Kind or h.Five is known. Whether AtMg can be met
    at the release's own files is not shown here. 𝔇₀ (the composed meaning's
fields that are still letters) and 𝔏 are letters. The full size alone. No soundness follows.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FourAtMg
import Johnson.P5J.TowerEnd
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.Sound.TiedRMono

set_option autoImplicit false
set_option relaxedAutoImplicit false
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
open VerifiableInference.Desc (Chain KindName)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_zero rchAt_hand block_at piece_step)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **In scope the head's segment has the number 24.** -/
theorem headLink_in_scope {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : headLink X = 24 := by
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hZ hR h
  unfold headLink
  rw [p4, ng]
  rfl

/-- The first table's meaning as the tower spells it, at the seated term's letters. -/
def AtMg.mq (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :=
  mqF (X := At.X Zp) numsFull (F0T o Zp Np cF) (fun q : ProofFile.InstPub => q.request) (dtK
            (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) (h.𝔇 𝔇₀).headPart
        (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp)

/-- **THE CONSTANT IS THE MEANING AT WHICH THE TOWER STANDS.** -/
theorem mgAt_is_mq (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :
    mgAt h 𝔇₀ = h.mq 𝔇₀ :=
  mgAll_is_tower (𝔇 := h.𝔇 𝔇₀) (Mg := mgBase) (headLink_in_scope h.scope h.reads h.pubOne)

/-- The first table's one extractor, at the seated term's letters. -/
def AtMg.ex (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :=
  exF numsFull D (F0T o Zp Np cF) (fun s => s) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) (At.cs Zp)
      (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) At.ps (F0T o Zp Np cF) (At.smp Zp) At.tokOf 𝔏

/-- The first chain's pieces, at the seated term. -/
def AtMg.row (_ : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :=
  rowF numsFull D (F0T o Zp Np cF) 𝔏

/-- **KIND K's SHARE, AT THE CONSTANT: THE FORM IN WHICH A KIND's FILES END ITS LAW.** -/
def AtMg.Kind (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName) : Prop :=
  KindTiedR (At.N Zp cF) (mgAt h 𝔇₀) fullLinks At.ps (RchAt (F0T o Zp Np cF)) (h.ex 𝔏) (h.row 𝔏) K

/-- **KIND K's SHARE WITH THE RIDER IN HAND**: the same, at h.rch: "reached" AND the public part is
    a typed instance's. IT ASKS LESS THAN `AtMg.Kind` (more is in hand in each tie): the tower takes
    THIS. -/
def AtMg.KindR (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName) : Prop :=
  KindTiedR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.N Zp cF) (mgAt h 𝔇₀) fullLinks At.ps h.rch (h.ex 𝔏) (h.row 𝔏) K

/-- A kind whose law ends at bare "reached" has the share with the rider in hand for nothing. -/
theorem AtMg.Kind.toR {h : AtMg o Z D r Zp Np cF} {nR : ℕ}
    {𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)}
    {𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok} {K : KindName} (k : h.Kind 𝔇₀ 𝔏 K) :
    h.KindR 𝔇₀ 𝔏 K :=
  KindTiedR.mono (fun _ _ h' => h'.1) k

/-- The tower's field EachGood, at these letters. -/
def AtMg.Good (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  GoodF (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s) (fun q
      : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    h.rch 𝔏

/-- The five other rows that are laws, at these letters. -/
def AtMg.Five (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) : Prop :=
  FiveF (pp := ppAtFiles Z.pol Z.KL) (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s) (fun q
      : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    h.rch h.rc 𝔏 depthReq

/-- The end at the verifier's own value: the proof file's seven fields. -/
def AtMg.Seven (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ)
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (EAll (D.at frS.P.T.a)
        (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a))).Str)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {runP : (kcReq numsFull (ppAtFiles Z.pol Z.KL) (At.EAt Z)).conf.X × RecFull → PQ.View → PQ.View
        → PQ.View → Bool}
    {P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
      (relationsAndEncodingOfClaims (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL)) (At.EAt Z))
          DK D runK runP ds xs dec rK 𝔏.rP
      depthReq reqWithoutReply salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) numsFull (ppAtFiles Z.pol Z.KL))
        (At.EAt Z) DK D runK runP ds xs
      dec rK 𝔏.rP depthReq reqWithoutReply salt K P) : Prop :=
  SevenF (X := At.X Zp) numsFull (At.EAt Z) D (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord (fun s => s) (fun q
                     : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    (ksK o Zp Np cF) h.rch h.rc 𝔏 depthReq d Tl

/-- The seated term's pieces are the pieces of its own lists. -/
theorem AtMg.ofDesc (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    OfDesc (F0T o Zp Np cF) (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂
        𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd) :=
  (paidAtDesc _ (Wit (CellsM numsFull) At.Tok MsgT) (F0T o Zp Np cF) "proof file" _
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (F0T o Zp Np cF) h.laid.planOk) (ckP .two) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ q₁
        q₂
    q₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd).1

set_option maxHeartbeats 4000000 in
/-- **WHAT THE KINDS' COUNTED LAWS BUY: ALL KINDS' SHARES AT THE CONSTANT GIVE THE TOWER's FIELD.**
    hlen: no more pieces than places in
the table's list (`tables_fit` has the equation). -/
theorem good_of_kinds (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hlen : (h.row 𝔏).length ≤ At.ps.length) (kinds : ∀ K, h.KindR 𝔇₀ 𝔏 K) : h.Good 𝔇₀ 𝔏 := by
  have hT := h.ofDesc 𝔏 q₁ q₂ q₃
  have g := eachTiedR_of_kinds
    (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (At.N Zp cF)
    (mgAt h 𝔇₀) fullLinks At.ps h.rch (h.ex 𝔏) (h.row 𝔏)
      hlen
    kinds
    (fun i q hq a τ b hr hb => by
      obtain ⟨B, hB⟩ := block_at hT hq
      refine ⟨rchAt_hand hT hq hb hr.1, ?_⟩
      have e : b.1.1 = a.1.1 := (piece_step q B (OfDesc.pieceAt hT hq hB) a b τ hb).1
      exact (congrArg h.typed e).mpr hr.2)
  rw [mgAt_is_mq] at g
  exact g

set_option maxHeartbeats 4000000 in
/-- **WHAT IS LEFT OF THE SEVEN AT THE VERIFIER's OWN VALUE: THE KINDS' SHARES AND FIVE ROWS.** -/
theorem rows_at_mg (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.KindR 𝔇₀ 𝔏 K) (V : h.Five 𝔇₀ 𝔏 depthReq)
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
    h.Seven 𝔇₀ 𝔏 depthReq d Tl := by
  have hT := h.ofDesc 𝔏 q₁ q₂ q₃
  have hl0 : ((piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)).l₁.length + 1 = (F0T o Zp
          Np cF).first.blocksInOrder.length := by
    have e := congrArg List.length hT.b₁
    simpa using e
  have hl : 1 + (atDesc (F0T o Zp Np cF) (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁
      𝔏.k₁ 𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)).l₁.length =
      (F0T o Zp Np cF).first.blocksInOrder.length := by
    show 1 + ((piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)).l₁.length = _
    omega
  have e1 : 1 + ((piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)).l₁.length = At.ps.length
          := (FiveF.tables_fit V).len₁
  have hlen : (h.row 𝔏).length ≤ At.ps.length := by
    show ((piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)).l₁.length + 1 ≤ _
    omega
  exact seven_of_owedF (Z := Z) (lay := some Z.lay) (X := At.X Zp) numsFull (At.EAt Z) D (F0T o Zp
      Np cF)
    LPFD.Full.instanceAsPlainRecord (fun s => s) (fun q : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF
                             h.plan.shape 0) ProofFile.Inst.asked At.d₀
    (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X
            Zp))) tokVOf
        h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (h.𝔇
        𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    (ksK o Zp Np cF) h.rch h.rc 𝔏 depthReq h.scope
    (fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request) (h.tieStart D 𝔇₀)
    (good_of_kinds h 𝔇₀ 𝔏 q₁ q₂ q₃ hlen kinds) V
    (fun z y => ⟨rchAt_zero _ _, z, rfl⟩) (fun b hb' => ⟨by
      show Reach 0 _ _ _ b.1
      rw [← hl]
      exact hb'.1, hb'.2⟩)
    (pub_free_at_term (At.EAt Z) o Zp Np cF) (fun _ _ => rfl) h.laid.planOk
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data) q₁ q₂ q₃ d hb er Tl

end P5J

#print axioms P5J.headLink_in_scope
#print axioms P5J.mgAt_is_mq
#print axioms P5J.AtMg.Kind.toR
#print axioms P5J.good_of_kinds
#print axioms P5J.rows_at_mg
