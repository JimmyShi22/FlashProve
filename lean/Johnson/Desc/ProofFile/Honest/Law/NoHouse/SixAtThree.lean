-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/SixAtThree.lean: two lemmas on the library's invariant at
border 3 of the first chain, after the sub-protocol at number 2. That sub-protocol is the first
segment's opening with the verifier's step "opened" of link 0 joined to it. The invariant's Boolean
part has six tests. Two of them, "in order" and "every public item that is open or tied holds",
form the test `P1K2.EQ`. The file contains no definition.

It joins three sources. Honest/Law/NoHouse/OpenedZeroPub.lean shows nine public items after an
accept of that sub-protocol. Honest/K1/Law/FormBehindSix.lean shows that these nine are all that
are open or tied at border 3 (`open_three`, `tied_three`), that they and "in order" give `P1K2.EQ`
there (`six_of_nine`), and that `P1K2.EQ` after the step, with the six tests before it and three
further hypotheses, gives the six tests after it (`xk_opening_six`). Honest/Thread/FormXKPub.lean
and HeadLetters.lean give "in order" and the list of further public tests at the thread's meaning.

  1  `head_six_at_three`   `P1K2.EQ` at border 3, at the state after an accept, from the thread's
     conditions at border 2
  2  `head_xk_at_three`   so the six tests at border 3, under the hypotheses of `xk_opening_six`
     that remain

Limits.
  * The lemmas hold at the full size and at the format's second hash function only. The library's condition
    on the public files (`AtMgA`) is a hypothesis.
  * `head_xk_at_three` keeps three hypotheses of `xk_opening_six` that are not shown: `hTr`
    (`RowG`), `hgroups` and `hown`; and three on how the sub-protocol is built (`hL`, `hp`, `hj`).
  * They start from the thread's conditions at a border. No run that meets these is exhibited.
  * No property of a prover or of the protocol is stated or proved.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.OpenedZeroPub
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehindSix
import Johnson.Desc.ProofFile.Honest.Thread.FormXKPub
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place Strs KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (RowG)
open Johnson.Desc.First.Walk.Tied (StepYes)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **"In order" and every public item that is open or tied at border 3 hold after an accept of the
sub-protocol at number 2**, from the thread's conditions at border 2. -/
theorem head_six_at_three {k : Coins Bk} {s t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : 2 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 k s m E)
    {e : Block TS ProofFile.Cl} (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t) :
    P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP IM.linksW IM.placesW
      m.st.input.x.pub (2 + 1) t = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hm : s.failed = none := Option.isNone_iff_eq_none.1 hT.2.2.1.1
  have R := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  exact ProofFile.Honest.K1.six_of_nine _ (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _ t
    (head_inOrder h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.2.2.1 t)
    (three_unheard h O R he hy) (three_ledger h O he hy) (three_lookIn h O he hy)
    (three_linkFresh h O he hy) (three_freeAbove h O he hy) (three_sentIs h O R hm he hy)
    (three_treesAre h O he hy) (three_index h O R he hy).1 (three_index h O R he hy).2

/-- **The six tests at border 3 after an accept of the sub-protocol at number 2**, under the
hypotheses of `xk_opening_six` that remain. -/
theorem head_xk_at_three {k : Coins Bk} {s t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : 2 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 2 k s m E)
    {e b' : Block TS ProofFile.Cl} (he : cF.blocksInOrder[2]? = some e) (hy : StepYes 0 e s t)
    (h1 : t.failed = none) (G₀ : ProofFile.Ground) (mk : List VerifiableInference.Desc.First.Pub)
    (hTr : RowG (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more IM.linksW IM.placesW 2
      (VerifiableInference.Desc.K1.layOf (VerifiableInference.Desc.K1.firstPar G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp))).shapes.size
      (VerifiableInference.Desc.K1.firstPar G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size mk)
    (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Zp, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (hj : IM.Joined Zp 0 e b' { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (hgroups : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub .noneSent
        (m.st.input.x.pub, s) = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N.groupAt 0 = s.st.groups.size)
    (hown : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.inOrder
        (m.st.input.x.pub, s) = true →
      VerifiableInference.Desc.First.bookAt
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N IM.placesW[2]? s = true →
      VerifiableInference.Desc.K1.ownSeatsB
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
        (IM.openAt IM.linksW IM.placesW (2 + 1))
        (VerifiableInference.Desc.K1.firstPar G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
        (s.check.frame.atMoment 0).length s.book.trees.size = true) :
    IM.XK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N IM.linksW IM.placesW
      (P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP IM.linksW IM.placesW
        m.st.input.x.pub) (2 + 1) t = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hm : s.failed = none := Option.isNone_iff_eq_none.1 hT.2.2.1.1
  have hx := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT.2.2.1
  rw [← head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    ← head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hx
  have hy' : IM.Yes 0 e s t := by
    obtain ⟨R, c, -, hs⟩ := hy
    exact ⟨R, c, c.length, hs⟩
  exact ProofFile.Honest.K1.xk_opening_six h.scope h.reads O _ _ _ 0 G₀ mk hTr hL hp hj s t hgroups hown
    hy' hm h1 hx (head_six_at_three h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT he hy)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_six_at_three
#print axioms ProofFile.Honest.FirstThread.head_xk_at_three
