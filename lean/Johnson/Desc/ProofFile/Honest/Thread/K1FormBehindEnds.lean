-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1FormBehindEnds.lean: the part `Form` of the first chain's
invariant at the border after the two sub-protocols of kind K1 that K1FormBehind.lean leaves out:
number 356, the sending of the message W after the segments, and number 2, the opening of the first
segment. At 356 the part `Form` is shown. At 2 one of its four facts stays a hypothesis. No
definition.

The lemmas for kind K1 show these facts on the verifier's state after an
accepting step, under the library's hypothesis at the full size (all under Honest/K1/Law/):
  * at 356: no failure mark and the Boolean tests (`mark_W_head`, `xk_W_head`, WAtHead.lean), and
    the test on the samples (`samples_W_head`, HeldAtW.lean)
  * at 2: no failure mark and the Boolean tests (`mark_opening_head`, `xk_opening_head`,
    OpeningAtHead.lean). The second takes two of the tests after the step as a hypothesis, which
    `head_six_at_three` (Honest/Law/NoHouse/SixAtThree.lean) shows
The fourth fact, what the open public items state beside their tests, is shown here at both borders:
no item `left m` or `leftOn m` is open at border 3 or 357, and PubPAtHead.lean reduces the fact to
these two sorts of item.

  1  `no_left_at_ends`, `no_left_can_fail`, `sets_at_ends_not_empty`   the closed test at the two
     borders, and two controls: the test rejects at some border of the same list, and the sets at
     the two borders are not empty (kernel evaluations)
  2  `head_pubP_at_ends`   the fourth fact at borders 3 and 357, at every state
  3  `k1_form_behind_W`   the part `Form` at border 357
  4  `k1_xk_at_three`   the Boolean tests at border 3, from the invariant at border 2 and the step
  5  `k1_form_behind_opening`   the part `Form` at border 3, with the test on the samples there as
     a hypothesis (`hs`)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The step is a hypothesis: nothing here shows that a sub-protocol accepts.
  * The invariant before the step is a hypothesis. Nothing here shows that it holds in any run.
  * `hs` speaks of the state after the step. It is not shown.
  * Only the part `Form` is shown, not the parts `rides` and `keeps`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.PubPAtHead
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.SixAtThree
import Johnson.Desc.ProofFile.Honest.K1.Law.OpeningAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.WAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Meaning flatPlacesOf pubSets samplesHeld)
open VerifiableInference.Desc.K1 (leftish saidSetB)
open VerifiableInference.Desc.Sound (MsgT mgBase linksFull moreAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 No `left` and no `leftOn` is open at borders 3 and 357 -/

/-- By the kernel: at borders 3 and 357 no open public item is `left m` or `leftOn m`. -/
theorem no_left_at_ends :
    ([3, 357].all fun c =>
      saidSetB moreAll linksFull (flatPlacesOf linksFull true) c fun q => !leftish q) = true := by
  decide +kernel

/-- Control, by the kernel: the same test rejects at some border of the same list. -/
theorem no_left_can_fail :
    ((List.range 359).any fun c =>
      !saidSetB moreAll linksFull (flatPlacesOf linksFull true) c fun q => !leftish q) = true := by
  decide +kernel

/-- Control, by the kernel: the open public sets at the two borders are not empty. -/
theorem sets_at_ends_not_empty :
    ([3, 357].all fun c =>
      !((pubSets moreAll linksFull (flatPlacesOf linksFull true))[c]?.getD []).isEmpty) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 2 What the open public items state, at the two borders -/

/-- At borders 3 and 357 every open public item's statement holds at every state `a`. -/
theorem head_pubP_at_ends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {c : Nat} (hc : c ∈ [3, 357]) (a : ProofFile.InstPub × TS) :
    ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP q a := by
  have hs : saidSetB moreAll linksFull (flatPlacesOf linksFull true) c (fun q => !leftish q) =
      true := List.all_eq_true.1 no_left_at_ends c hc
  have hno : ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c,
      leftish q = false := by
    intro q hq
    have e := head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    unfold P1K2.pubAt at hq
    rw [e] at hq
    have h1 : (!leftish q) = true := List.all_eq_true.1 hs q hq
    cases hh : leftish q with
    | false => rfl
    | true => rw [hh] at h1; cases h1
  refine head_pubP_of_left h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ a ?_ ?_
  · intro m hm
    exact Bool.noConfusion (show true = false from hno _ hm)
  · intro m hm
    exact Bool.noConfusion (show true = false from hno _ hm)

/-! ## 3 After the sending of W -/

/-- The part `Form` of the invariant after sub-protocol number 356, from the invariant before it
(`hT`) and the sub-protocol's step (`hS`). -/
theorem k1_form_behind_W (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[356]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 356 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (356 + 1) k s' y.2 := by
  have hF := hT.2.2.1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hb : 356 ≤ cF.blocksInOrder.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hblk
    exact Nat.le_of_lt hlt
  have hxE := xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF
  exact form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (K1.mark_W_head h hblk 0 hyes)
    (K1.xk_W_head h hblk (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub 0 hyes
      (Option.isNone_iff_eq_none.1 hF.1) hxE)
    (K1.samples_W_head h hblk _ (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      m.st.input.x.pub 0 (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
      (IM.xk_parts hxE).2.2.2.1 hyes (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF))
    (head_pubP_at_ends h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by decide) _)

/-! ## 4 and 5 After the opening of the first segment -/

/-- The Boolean tests at border 3 after sub-protocol number 2, from the invariant before it and an
accepting step. -/
theorem k1_xk_at_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[2]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 k s m E)
    (hy : Johnson.Desc.First.Walk.Tied.StepYes 0 blk s s') :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP IM.linksW IM.placesW
        m.st.input.x.pub) (2 + 1) s' = true := by
  have hF := hT.2.2.1
  have hb : 2 ≤ cF.blocksInOrder.length := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hblk
    exact Nat.le_of_lt hlt
  have hx := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
  rw [← head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    ← head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hx
  have hy' : IM.Yes 0 blk s s' := by
    obtain ⟨R, c, -, hs⟩ := hy
    exact ⟨R, c, c.length, hs⟩
  exact K1.xk_opening_head h hblk _ (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (mgBase : Meaning ProofFile.InstPub WtF).pub (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    m.st.input.x.pub 0 (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT) hy'
    (Option.isNone_iff_eq_none.1 hF.1) hx
    (head_six_at_three h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT hblk hy)

/-- The part `Form` of the invariant after sub-protocol number 2, from the invariant before it
(`hT`), the sub-protocol's step (`hS`, `hy`) and the test on the samples after it (`hs`). -/
theorem k1_form_behind_opening (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[2]? = some blk)
    {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    (hy : Johnson.Desc.First.Walk.Tied.StepYes 0 blk s s')
    (hs : samplesHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      (IM.openAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps (2 + 1))
      (m.st.input.x.pub, s') = true) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (2 + 1) k s' y.2 := by
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hx := k1_xk_at_three h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hy
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hx
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS
    (K1.mark_opening_head h hblk 0 hyes) hx hs
    (head_pubP_at_ends h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by decide) _)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.no_left_at_ends
#print axioms ProofFile.Honest.FirstThread.no_left_can_fail
#print axioms ProofFile.Honest.FirstThread.sets_at_ends_not_empty
#print axioms ProofFile.Honest.FirstThread.head_pubP_at_ends
#print axioms ProofFile.Honest.FirstThread.k1_form_behind_W
#print axioms ProofFile.Honest.FirstThread.k1_xk_at_three
#print axioms ProofFile.Honest.FirstThread.k1_form_behind_opening
