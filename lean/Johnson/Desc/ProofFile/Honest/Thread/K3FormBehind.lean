-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K3FormBehind.lean: two lemmas. Each shows the part `Form` of
the first chain's invariant at the border after a lookup argument (kind K3), from the invariant
before it and the sub-protocol's step. There are two lookup arguments in each of the 25 segments,
one on the calls and one on the digits, at the numbers `k3K l false` and `k3K l true` of the chain's
list. No definition.

The work is done in two other places. The lemmas `step_calls_top` and `step_digits_top`
(Honest/K3/Law/Total/NoMarkBehind.lean)
speak of the verifier's states alone. They give four facts after an accepting step: no mark, the
six Boolean tests of the public book-keeping, the samples are held, and what the open public items
say. Before the step they ask that the state is reached (in the library's sense, over the wrapped
sub-protocols), and the first three of the four facts; at the digits also the fourth. So "reached"
goes in and does not come out. FormXK.lean shows that the four facts are the part `Form` of the
invariant (`form_behind_of_xk`), and with FormXKFront.lean that the invariant before the step gives
them. "Reached" comes from the invariant together with `SaidOk`, by `thrS_reach_below`
(ReachAtHead.lean). This file joins these, as K11FormBehind.lean and K2FormBehind.lean do for two
other kinds.

  1  `k3_form_behind_calls`    after the lookup argument on the calls of segment `l`
  2  `k3_form_behind_digits`   after the lookup argument on the digits of segment `l`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The step is a hypothesis: nothing here shows that the sub-protocol accepts.
  * The invariant before the step is a hypothesis, together with `SaidOk` (every word shown so far
    is below the prime). Nothing here shows that it holds in any run.
  * At the digits, the invariant before the step includes what the open item `leftOn l` says. Four
    sub-protocols of other kinds stand between a segment's two lookup arguments and have to pass
    that statement on; this file does not show that they do.
  * Only the part `Form` is shown, not the parts `rides` and `keeps`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.NoMarkBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The part `Form` of the invariant after the lookup argument on the calls of segment `l`, from the
invariant before it (`hT`) and the sub-protocol's step (`hS`). -/
theorem k3_form_behind_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.OnPublicFiles.k3K l false]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (VerifiableInference.OnPublicFiles.k3K l false) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (VerifiableInference.OnPublicFiles.k3K l false + 1) k s' y.2 := by
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hb : VerifiableInference.OnPublicFiles.k3K l false ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  obtain ⟨a, b, c, d⟩ := ProofFile.Honest.K3.Law.Total.step_calls_top h hl hblk
    m.st.input.x.pub
    (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT) hyes
    (Option.isNone_iff_eq_none.1 hF.1)
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS a b c d

/-- The part `Form` of the invariant after the lookup argument on the digits of segment `l`, from
the invariant before it (`hT`) and the sub-protocol's step (`hS`). -/
theorem k3_form_behind_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.OnPublicFiles.k3K l true]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (VerifiableInference.OnPublicFiles.k3K l true) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (VerifiableInference.OnPublicFiles.k3K l true + 1) k s' y.2 := by
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hb : VerifiableInference.OnPublicFiles.k3K l true ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  obtain ⟨a, b, c, d⟩ := ProofFile.Honest.K3.Law.Total.step_digits_top h hl hblk
    m.st.input.x.pub
    (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT) hyes
    (Option.isNone_iff_eq_none.1 hF.1)
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (held_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (pubP_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS a b c d

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k3_form_behind_calls
#print axioms ProofFile.Honest.FirstThread.k3_form_behind_digits
