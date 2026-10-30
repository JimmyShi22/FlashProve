-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K2FormBehind.lean: THE FORM BEHIND A CODE SWITCH's MEMBER, AT
THE FIRST CHAIN's LAID LETTERS: THE SECOND LAYING OF LEMMAS INTO `form_behind_of_xk`. The
kind K2 has, with no thread in them, at every place of the
kind, under the library's head alone, at the library's own terms: no mark behind a yes of the
member (`k2_noMark_behind`) · the six Bools behind from the six in front (`k2_xk_behind_at`) ·
"held" behind from the six and "held" in front (`k2_held_behind`); the last two from a state that
is reached over the members under `below`. What the open public items say beside their Bools is
ours wherever the library's test with code `saidBehindB` accepts (`K2Ties.pubP_behind`): that
test's yes at the member's number is a premise of the first lemma and is paid in the second by the
library's `P1K2.said_at`. The join is as at the head's merge (Honest/Thread/K11FormBehind.lean). No
definition. Two conditional lemmas.

  `k2_form_behind`       the pair at b · the member's step · the test's yes at b ⟹ the form at b + 1
  `k2_form_behind_all`   the same with the test's yes paid by the library's `P1K2.said_at`

Limits. The full size and the format's second hash function alone: as the library's head, which is a
premise. It says nothing of `rides` or `keeps`, and not that the member accepts. It stands over
three files of that house which are not sealed. None is one of the library's goals. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.HandsOfHead
import Johnson.Desc.ProofFile.Honest.K2.Law.NoMarkBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.HeldBehind
import Johnson.Top.H0.K2Ties.PubBehind
import Johnson.P1K2R.TableAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FORM BEHIND A MEMBER OF THE KIND K2**, from the pair in front and the member's step. -/
theorem k2_form_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    (hsaid : VerifiableInference.Desc.First.K2Ties.saidBehindB linksFull
      (flatPlacesOf linksFull true) b = true)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
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
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have h1 : s'.failed = none := ProofFile.Honest.K2.Law.k2_noMark_behind h ha hk hblk hyes
  have hx := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS h1
    (ProofFile.Honest.K2.Law.k2_xk_behind_at h ha hk hblk hf hyes h0 h1 hx)
    (ProofFile.Honest.K2.Law.k2_held_behind h ha hk hblk hf hyes hx
      (held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF))
    (VerifiableInference.Desc.First.K2Ties.pubP_behind h.𝔇 linksFull
      (flatPlacesOf linksFull true) b hsaid _)

/-- **THE SAME WITH THE TEST's YES PAID**: the library's `P1K2.said_at`: at every place of the kind
K2 of the written list the test accepts. -/
theorem k2_form_behind_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' y.2 :=
  k2_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ha hk hblk (P1K2.said_at ha hk) hT hS

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k2_form_behind
#print axioms ProofFile.Honest.FirstThread.k2_form_behind_all
