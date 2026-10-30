-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/HonestTrace/ConstrItemsAtStart.lean

Two conditional lemmas, and joinings: items_constr_all_at_thread
(Johnson/Goal/HonestTrace/ConstrHeadAtThread.lean) in the form of the premise hparts of
head_items_start (Johnson/Desc/ProofFile/Honest/Thread/EntersItems.lean), and the call of
head_items_start at it. Neither adds a fact to the two theorems that it calls. The type T of the
input's own trace is a letter, as in head_items_start.
This file states no goal.
It imports a module under Johnson/Goal/ directly: Johnson/Goal/HonestTrace/ConstrHeadAtThread.lean.

Main theorems:
* "constr_parts_at_start": under h : AtMgA ..., at a served request and under ScriptTies
  (Johnson/Goal/HonestTrace/ConstrAtThread.lean) at the input of mm: at every written link l and
  each of the four parts p, Thread.Items at the one item constr l p, at every state s and all
  oracles E.
* "opened_at_start_of_mark_pile": under the same, where the state bears no mark and the pile's item
  holds: Thread.Items at all that is open at border 0.

Limits. NO MEMBER OF ScriptTies IS SHOWN, HERE OR ELSEWHERE IN THE LIBRARY: so neither lemma is
shown to speak of any Script, witness or run. No member of AtMgA is shown here. Of the 103 items
that are open at the first chain's start the first lemma treats the 100 items constr; in the second
"no mark" and the pile stay premises, and the stored table's pin is head_pinW's. ScriptTies is asked
at the one input mm.st.input and at the one k. The full size alone; at the concrete earlier hash.
enters_head is not called. The limits of Johnson/Goal/HonestTrace/ConstrHeadAtThread.lean come with
it.

Not claimed: that an honest prover's witness meets any relation; anything on what a verifier
accepts; any property of the protocol. No property of a release, of a verifier or of a prover is
claimed.
-/
import Johnson.Goal.HonestTrace.ConstrHeadAtThread
import Johnson.Desc.ProofFile.Honest.Thread.EntersItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (Item Part)
open P5J (TS AtMgA CellsM)
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}

/-- **The hundred items constr, in the form of head_items_start's premise hparts.** Under
h : AtMgA ..., at a served request and under ScriptTies at the input of mm: at every written link l
and each of the four parts p, Thread.Items at the one item constr l p, at every state s and all
oracles E. It is items_constr_all_at_thread: the written links are 25, and the list is parts4. -/
theorem constr_parts_at_start (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst T) X')
    {i : Cm.Idx} {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x)
    (Ti : ScriptTies Z Zp cF Q k mm.st.input i x) (s : TS) (E : Env) :
    ∀ l sub, P5J.At.links[l]? = some sub →
      ∀ p ∈ [Part.idn, Part.lookCalls, Part.rider, Part.small],
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items [Item.constr l p] k s
          mm E := by
  intro l sub hl p hp
  have e : P5J.At.links.length = 25 := rfl
  exact items_constr_all_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm Sv Ti s E hp
    (e ▸ (List.getElem?_eq_some_iff.1 hl).1)

/-- **head_items_start at these parts.** Under the same, and where the state bears no mark and the
pile's item holds: Thread.Items at all that is open at border 0. At w₁ := R.own, mm := R.start₁ H
and the first state this is the form of enters_head's premise hItems, which stands at one E and at
the k of that lemma's premise on "ready": here both are free letters. The tie is then asked at the
input of R.start₁ H. enters_head is not called. -/
theorem opened_at_start_of_mark_pile (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts}
    {W₀ Rc Ky T X₀ X' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky T X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst T → Prop)
    (Rd : ℕ → Local W₀ Rc ProofFile.Inst T → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst T) (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst T) X')
    {i : Cm.Idx} {x : Instance ppref} (Sv : ServesAt (P5J.At.X Zp) i x)
    (Ti : ScriptTies Z Zp cF Q k mm.st.input i x) (s : TS) (E : Env)
    (hmark : s.failed = none)
    (hpile : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items [Item.pile] k s
      mm E) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Items
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened 0) k s mm E :=
  head_items_start h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hmark hpile
    (constr_parts_at_start h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ k mm Sv Ti s E)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.constr_parts_at_start
#print axioms OnBytes.HonestTrace.opened_at_start_of_mark_pile
