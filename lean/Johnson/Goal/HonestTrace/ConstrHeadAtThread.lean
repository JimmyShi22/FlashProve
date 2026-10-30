-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/HonestTrace/ConstrHeadAtThread.lean

Conditional lemmas under h : AtMgA ..., at a served request and under ScriptTies
(Johnson/Goal/HonestTrace/ConstrAtThread.lean): at the field "thread" of lettersHead
(Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean) the sentence of the items constr 24 p, for p
among idn, lookCalls, rider and small, holds of the witness that the Script Q makes; and so, with
constr_at_thread, the sentence of all 100 items constr m p with m < 25. The type T of the input's
own trace is a letter. No member of AtMgA and none of ScriptTies is shown here.
This file states no goal.
It imports two modules under Johnson/Goal/ directly: Johnson/Goal/HonestTrace/ConstrAtThread.lean
and Johnson/Goal/HonestTrace/ConstrHeadAtTrace.lean.

Main theorems:
* "constr_head_at_thread": under h, ServesAt (At.X Zp) i x and ScriptTies Z Zp cF Q k v i x, for p
  in parts4: "means v (Item.constr 24 p)" holds at the pair (v.x.pub, s), the strings y and the
  witness Q.wit k v ds, for every state s, all y and every list ds.
* "items_constr_head_at_thread": the same as Thread.Items at the one item, at a value mm of Mid
  whose input meets ScriptTies.
* "constr_all_at_thread", "items_constr_all_at_thread": the two forms at every m < 25 and p in
  parts4.

Beside h, ServesAt and ScriptTies the theorems take the bounds on p and on m, and nothing else.
constr_head (Johnson/Goal/HonestTrace/ConstrHeadAtTrace.lean) leaves three of the nine premises on
public data of parts_of_headOrd (Johnson/Desc/K6/Honest/Law/Back/PartsOfHeadOrd.lean) open, and here
they are had: rows ≤ hRef and cols ≤ 2^kRef at the committed table's numbers by evaluation, as in
headCuts_atAll (Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean); that the table of the exponential is the
library's EX by tab_of_B (Johnson/Desc/Kinds/Law/TabIsEX.lean) at tabIsEX_in_scope
(Johnson/Desc/Kinds/Law/TabIsEXInScope.lean), whose premise on the lookup's place is h's field
headAt. The three premises on the files are h's fields scope, reads and pubOne. Of ScriptTies all
three fields are read: cells (the decoded table holds i, and it is the witness's own cells by the
text of Script.wit), req and syms.

Limits. These are conditional lemmas, and joinings. THIS FILE SHOWS NO MEMBER OF AtMgA. The library
has one at every Z in scope at which the goals' reader returns and the test protocolDataWellFormed accepts
(head_of_live, Johnson/Goal/Meaning/ServedChains.lean; protocolDataWellFormed, Johnson/Goal/Description/Live.lean,
wants the verifier's three values laid and, of them, an accept of dataWellFormedAtFullSizeDepth), and, in its side library,
members with no premise at two stored sets of full-size public files: VerifierAndGoals.storedPublicFiles
(headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean) and VerifierAndGoals.zGap (headMember_zGap,
AtFullSide/Top/HeadMemberAtGap.lean). None of these theorems is called here. NO MEMBER OF ScriptTies
IS SHOWN, HERE OR ELSEWHERE IN THE LIBRARY: so this file is not shown to speak of any Script. The
sentence is that field's: constrQAt at the put, H, headPart and digitsPart of h.𝔇, with the constant
decoder "some (Q.cells v)" in the place of h.𝔇's own. That it is the sentence of mgAtAll h is not
shown here. By the text of start (Johnson/Desc/First/Borders.lean) at the 25 links these are the
items constr that are open at the chain's start; three more items are open there: unmarked, pinW and
pile. The theorems speak of the witness Q.wit k v ds alone: they do not give RidesPastAt, which is
asked at every witness (ridesPastAt_constr, Johnson/Goal/HonestTrace/ConstrAtThread.lean). The items
of the parts lookDigits and lookCallsHeard, and every item that is no Item.constr, are not treated
here. w₁, the last argument of lettersHead, is arbitrary: it enters the field "valid" alone. The
limits of the theorems that are called come with them: the full size alone; at the concrete earlier
hash. The limits of Johnson/Goal/HonestTrace/ConstrAtThread.lean on ScriptTies come with it.

Not claimed: that an honest prover's witness meets any relation; anything on what a verifier
accepts; any property of the protocol. No property of a release, of a verifier or of a prover is
claimed.
-/
import Johnson.Goal.HonestTrace.ConstrAtThread
import Johnson.Goal.HonestTrace.ConstrHeadAtTrace
import Johnson.Desc.Kinds.Law.TabIsEXInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (Item)
open Meaning (Follows)
open P5J (TPart TS parts4 constrQAt AtMgA CellsM)
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}

/-- **The sentence of the output head's four items at the Script's witness.** Under h : AtMgA ...,
at a served request and under ScriptTies: for p among idn, lookCalls, rider, small: "means v
(Item.constr 24 p)" holds at the pair (v.x.pub, s), the strings y and the witness Q.wit k v ds, for
every state s, all y and every list ds. The binders are those of constr_at_thread but for m and hm,
which fall. By constr_head at the parameters of h.𝔇. -/
theorem constr_head_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) {i : Cm.Idx}
    {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x) (Ti : ScriptTies Z Zp cF Q k v i x)
    (s : TS) (y : Strs) (ds : List Fmt.Drawn) {p : TPart} (hp : p ∈ parts4) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means v (Item.constr 24 p)
      (v.x.pub, s) y (Q.wit k v ds) := by
  have hZ := h.scope
  have hR := h.reads
  have hP := h.pubOne
  have Fo : Follows (P5J.At.X Zp) (Meaning.sizesOf (P5J.At.X Zp)) :=
    Meaning.follows_of_core hP (Hd.core_of_scope hZ hR hP)
  have hb : ∀ k < 25, (Meaning.sizesOf (P5J.At.X Zp) k).beta = 2 ^ 17 := fun _ _ => rfl
  have hr : ∀ k < 25, (Meaning.sizesOf (P5J.At.X Zp) k).rad = 2 ^ 20 := fun _ _ => rfl
  have S := Ti.syms ds
  show constrQAt (VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp)) h.𝔇.put
    (VerifiableInference.Desc.Sound.oneDec (fun _ _ => some (Q.cells v)) h.𝔇.H) h.𝔇.headPart
    h.𝔇.digitsPart 24 p (v.x.pub, s) y (Q.wit k v ds)
  rw [P5J.headLink_in_scope hZ hR hP]
  exact constr_head (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
    (Meaning.sizesOf (P5J.At.X Zp)) _ P5J.tokVOf
    (fun a => (Meaning.backReq (P5J.At.reqB a.1)).getD P5J.At.d₀)
    (fun _ _ => some (Q.cells v)) h.plan.hN h.plan.hG hZ hR hP Sv Fo hb hr OnBytes.Flat.putReq
    (v.x.pub, s) y (Q.wit k v ds) (fun M hM => (Option.some.inj hM) ▸ Ti.cells)
    (fun M hM => (Option.some.inj hM).symm) Ti.req S _ _ _ _ (by decide) (by decide)
    (VerifiableInference.Desc.Kinds.Head.Law.tab_of_B
      (VerifiableInference.Desc.Kinds.Head.Law.InScope.tabIsEX_in_scope hZ hR hP h.headAt))
    _ hp

/-- **The same in the form in which the honest side asks it**: Thread.Items at the one item, at a
value mm of Mid whose input meets ScriptTies, at every state s and all oracles E. The binders are
those of items_constr_at_thread but for m and hm, which fall. -/
theorem items_constr_head_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst T) X')
    {i : Cm.Idx} {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x)
    (Ti : ScriptTies Z Zp cF Q k mm.st.input i x) (s : TS) (E : Env) {p : TPart}
    (hp : p ∈ parts4) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items [Item.constr 24 p] k s
      mm E := by
  intro ds j hj
  obtain rfl := List.mem_singleton.1 hj
  exact constr_head_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm.st.input Sv Ti s _
    (mm.st.heard ++ ds) hp

/-- **The sentence of all 100 items constr m p at the Script's witness**: m < 25 and p among idn,
lookCalls, rider, small. Below 24 it is constr_at_thread; at 24 constr_head_at_thread. -/
theorem constr_all_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) {i : Cm.Idx}
    {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x) (Ti : ScriptTies Z Zp cF Q k v i x)
    (s : TS) (y : Strs) (ds : List Fmt.Drawn) {m : ℕ} {p : TPart} (hp : p ∈ parts4)
    (hm : m < 25) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means v (Item.constr m p)
      (v.x.pub, s) y (Q.wit k v ds) := by
  by_cases h24 : m < 24
  · exact constr_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k v Sv Ti s y ds hp
      (Or.inl h24)
  · obtain rfl : m = 24 := by omega
    exact constr_head_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k v Sv Ti s y ds hp

/-- The same as Thread.Items at the one item. -/
theorem items_constr_all_at_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst T) X')
    {i : Cm.Idx} {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x)
    (Ti : ScriptTies Z Zp cF Q k mm.st.input i x) (s : TS) (E : Env) {m : ℕ} {p : TPart}
    (hp : p ∈ parts4) (hm : m < 25) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items [Item.constr m p] k s
      mm E := by
  intro ds j hj
  obtain rfl := List.mem_singleton.1 hj
  exact constr_all_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm.st.input Sv Ti s _
    (mm.st.heard ++ ds) hp hm

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.constr_head_at_thread
#print axioms OnBytes.HonestTrace.items_constr_head_at_thread
#print axioms OnBytes.HonestTrace.constr_all_at_thread
#print axioms OnBytes.HonestTrace.items_constr_all_at_thread
