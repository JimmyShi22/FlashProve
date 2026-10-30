-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K11FormBehind.lean: THE FORM BEHIND THE HEAD's MERGE, AT THE
FIRST CHAIN's LAID LETTERS: THE FIRST USE OF THE KIND K11's FOUR LEMMAS IN
`form_behind_of_xk`. The kind K11's lemmas give, with no
thread in it: under the library's head, behind a yes of the member number 346 from a state that is
reached over the members under `below`: no mark · the six Bools · "held" · what the open public
items say, all four at 346 in front, give all four at 347 behind (their `promiseBehindStepAt`, at
the library's own terms). Here the join, which is ours: the yes off the thread's step · that reach
from the pair at `SaidOk` (`thrS_reach_below`) · the four in front off the thread's form
(`xk_of_form`, `held_of_form`, `pubP_of_form`) · the four behind into `form_behind_of_xk`. That the
letters' terms are the library's is by unfolding. No definition. One conditional lemma.

  `k11_form_behind`   the pair at 346 · the member's step ⟹ the form at 347

Limits. The full size and the format's second hash function alone: as the library's head, which is a
premise. It says nothing of `rides` or `keeps`, and not that the member accepts. It stands over
files of these authors which are not sealed. None is one of the library's goals. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.K11.Behind.AtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FORM BEHIND THE MEMBER NUMBER 346**, from the pair in front and the member's step. -/
theorem k11_form_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hblk : cF.blocksInOrder[346]? = some blk)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346 k s m
      E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form 347 k s' y.2 := by
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hb : 346 ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  obtain ⟨a, b, c, d⟩ := Johnson.Desc.First.ForkMerge.Behind.promiseBehindStepAt Z D r Zp Np cF x
    h blk m.st.input.x.pub s s' hblk hyes
    (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (Option.isNone_iff_eq_none.1 hF.1)
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (pubP_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS a b c d

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k11_form_behind
