-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FormBehind.lean: the first field of the debt «behind» at a code switch (the kind K2):
behind a member's step the thread's form holds at the next border.

  k2_form_behind     the pair at the member's border and the member's step give the form behind it
  k2_formBehindAtS   the same in the form that the thread's column asks

The four behind a yes stand in Honest/K2/Law/: no mark (NoMarkBehind.lean), the six Bools
(HandsOfHead.lean), «held» (HeldBehind.lean), what the open public items say (PubPBehind.lean). This
file joins them: the yes off the thread's step, the reach from the pair, the front off the thread's
form, the four behind into form_behind_of_xk.

Limits. The library's head is a premise. The prover, the script and all letters of the thread are
free. It says nothing of rides or keeps, and not that the member accepts.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.HandsOfHead
import Johnson.Desc.ProofFile.Honest.K2.Law.NoMarkBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.HeldBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.PubPBehind
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FormShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Block Chain KindName Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (k2_noMark_behind k2_xk_behind_at k2_held_behind k2_pubP_behind)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The form behind a member of the kind**, from the pair in front and the member's step. -/
theorem k2_form_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2)
    {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hblk : cF.blocksInOrder[b]? = some blk)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' y.2 := by
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hb : b ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hf : Meaning.K2.FkR Zp cF m.st.input.x.pub b s :=
    thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have h₀ : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have h₁ : s'.failed = none := k2_noMark_behind h ha hk hblk hyes
  have hx := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  have hH := held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS h₁
    (k2_xk_behind_at h ha hk hblk hf hyes h₀ h₁ hx) (k2_held_behind h ha hk hblk hf hyes hx hH)
    (k2_pubP_behind h ha hk _)

/-- **The same in the form of the thread's column.** -/
theorem k2_formBehindAtS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b :=
  fun _ hblk _ _ _ _ _ _ _ _ hT _ hS =>
    k2_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ha hk hblk hT hS

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.k2_form_behind
#print axioms AtFullSide.K2.Term.k2_formBehindAtS
