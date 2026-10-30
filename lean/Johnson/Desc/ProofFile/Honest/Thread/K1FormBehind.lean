-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1FormBehind.lean: the part `Form` of the first chain's
invariant at the border after each of the 50 sub-protocols of kind K1 that stand inside a segment
after its first place: the sending of the reads and the sending of the digits, in each of the 25
segments. Their numbers in the chain's list are `K1.noL l d` (Johnson/Desc/K1/Law/LaterOne.lean),
for a segment `l` and `d` false at the reads and true at the digits. One conditional lemma, no
definition.

The work is done in other places. The lemmas for kind K1 show four facts
on the verifier's state after an accepting step, each from the same fact before the step, under the
library's hypothesis at the full size (all under Honest/K1/Law/):
  * no failure mark: `mark_later_head` (FiftyAtHead.lean)
  * the Boolean tests, stated with the library's public test `EW`: `xk_later_head`
    (PubBehindAtFifty.lean)
  * the test on the samples: `samples_later_head` (HeldAtFifty.lean)
  * what the open public items state beside their tests: `pubP_later_all` (DoorFactsAtAll.lean),
    with `paid_later_head` (FiftyAtHead.lean) for the sub-protocol's form
K9FormBehind.lean shows that the four facts in this form are the part `Form` (`form_behind_of_ew`).
This file joins them, as K9FormBehind.lean, K11FormBehind.lean, K2FormBehind.lean and
K3FormBehind.lean do for four other kinds.

What these lemmas ask of the state before the step is shown from the invariant there: that the state
is reached (`thr_reach`, ReachFacts.lean), the group and the shape in the open segment's copy of the
frame (`head_live`, HeadLive.lean), and the four facts themselves (`xk_ew_front`, `held_w_front`,
K9FormBehind.lean; `xk_of_form`, FormXK.lean; `pubP_of_form`, FormXKFront.lean).

  `k1_form_behind_later`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The step is a hypothesis: nothing here shows that the sub-protocol accepts.
  * The invariant before the step is a hypothesis. Nothing here shows that it holds in any run.
  * Only the part `Form` is shown, not the parts `rides` and `keeps`.
  * Nothing on K1's opening of the first segment or on the sending after the segments.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.HeadLive
import Johnson.Desc.ProofFile.Honest.K1.Law.PubBehindAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.DoorFactsAtAll
import Johnson.Desc.K1.Law.CallsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The part `Form` of the invariant after the sending of the reads (`d` false) or of the digits
(`d` true) of segment `l`, from the invariant before it (`hT`) and the sub-protocol's step
(`hS`). -/
theorem k1_form_behind_later (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {l : Nat} (hl : l < 25) (d : Bool) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.Desc.K1.noL l d]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (VerifiableInference.Desc.K1.noL l d) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
      (VerifiableInference.Desc.K1.noL l d + 1) k s' y.2 := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hb : VerifiableInference.Desc.K1.noL l d ≤ cF.blocksInOrder.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hblk
    exact Nat.le_of_lt hlt
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hxE := xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  refine form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (K1.mark_later_head h hl d hblk 0 hyes)
    (K1.xk_later_head h hl d hblk (mgBase : Meaning ProofFile.InstPub WtF).pub K1.hbase_mgBase
      m.st.input.x.pub 0
      (head_live h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
        (VerifiableInference.Desc.K1.place_fifty l hl d) rfl)
      (fun e1 e2 => by
        subst e1
        subst e2
        exact hR)
      hyes h0 hxE)
    (K1.samples_later_head h hl d hblk _
      (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) m.st.input.x.pub 0 hR
      (IM.xk_parts hxE).2.2.2.1 hyes
      (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF)) ?_
  obtain ⟨Bs, X₁, arrs, hu, -⟩ := K1.paid_later_head h hl d hblk
  have eL := head_links_full h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have eP := head_ps_full h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have hx0 := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  have hp0 := pubP_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  rw [eL, eP] at hx0 hp0
  rw [eL, eP]
  exact K1.pubP_later_all h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub (P5J.At.X Zp) h.𝔇.sent
    h.𝔇.d1 h.𝔇.rw13 h.𝔇.A1 h.𝔇.cr1 _
    (head_pubP_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _ m.st.input.x.pub 0 Zp Bs.G₀ l hl d
    X₁ arrs blk hu s s' hyes hx0 fun m' hm' => hp0 _ hm'

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1_form_behind_later
