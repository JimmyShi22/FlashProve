-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkEqReach.lean: AT "THE ONE EQUATION" THE TWO NAMED PREMISES OF
Honest/K9/XkClose.lean AND XkAtHead.lean (hg · hne) ARE PAID FROM "REACHED": under the library's head, at each l < 25,
at a state s that the first chain's own members' steps reach, from the start, at that member's border (the library's
raw `Reach 0 cF.blocksInOrder (ProofFile.startS Zp)`, at the first tree 0). No prover, no string and no thread is in this file
but in its last statement, which bears the frame's letters (H : Prover · Q : Script · test · carryX over Strs · Thr).
Statements and proofs ON THE VERIFIER's TEXT; no goal is stated.
  `group_number`   the table's number of group l is l: `(P5J.At.N Zp cF).groupAt l = l`, by unfolding (a twin of the
      library's `P5J.At.foldD_groupAt`, which says it of the fold's data)
  **`hg_of_reach`**   hg: the library's `LPFK9.HandsAt.grp_reached` at the head's own scope, files read and opening
  `idxFit_W`   the library's test `idxFitE` at the written list, by Lean's kernel: OURS: a third evaluation of one
      Bool beside the library's `idxFitE_full` and `idxFitE_links` (other spellings of the list)
  `index_of_xk`   from XK at the public test `EW` at that border: the state's number of the index masks' message is
      the table's: the public item "indexIs" is open there (the library's `idxE_at` at `idxFit_W`; kin: the library's
      `index_of_promise`, at pieces and strings)
  **`hne_of_reach`**   hne (`OwnNotIndex s`): the library's `ownNotIndex_reached` at the frame's `foldFacts_raw`
      (Honest/Thread/ReachFacts.lean: `FoldFacts` at whatever family gives the raw "reached"), with `AtMg.notIx`, no
      mark at s, and the index masks' number as a premise hIx, which `index_of_xk` pays in `xk_eq_reach` (h.𝔇.pubD.N
      is `P5J.At.N Zp cF` by unfolding: no rewrite). Kin: the
      library's `notIx_of`, the same two calls at the promise with strings
  **`xk_eq_reach`**   so: at whatever block blk stands at 14 l + nAt l + 4 + 0 in the first chain's flat list:
      "reached" at that border at (z, s) · a yes of blk's step from s to s' · no mark at s · XK at `EW` there ⊢ XK at
      `EW` at the next border at s'. z : ProofFile.InstPub here
SO AT "THE ONE EQUATION" NOTHING STAYS ON THE STATE BESIDE "REACHED" AND WHAT STANDS IN FRONT (no mark · XK).
"REACHED" IS A FIFTH BESIDE THE FOUR PREMISES IN FRONT THAT THE FRAME's PEN ALLOWS A HOUSE. ON THE LETTERS hbase
stays; hb is the block's line; the yes's ft is free, "reached" stands at the first tree 0.
  **`xk_eq_thr`**   AT THE FRAME's OWN THREAD at the library's head (`lettersHead`): where the thread stands at that
      border at s (`Thr`), z := the public part of the input's instance: the same end, "reached" paid by the frame's
      `thr_reach`: SO THERE NOTHING STAYS ON THE STATE BESIDE THE THREAD's OWN STAND, NO MARK AND XK. ON THE LETTERS as
      above: hbase at that z · hb · base · ft free; k, m, E free; the yes stays; `thr_reach`'s bound on the border is
      paid off hb
IT IMPORTS ONE FILE OF THE FRAME's (Honest/Thread/ReachFacts.lean), for `foldFacts_raw` and `thr_reach`; beneath that
file lie some thirty more of the frame's: so what the first lines say of this file is said of its text, not of its
ground.
WHAT IS NOT CLAIMED. That a state is reached. That a yes is there. XK at any state. That the thread stands anywhere.
No member: `xk_eq_thr` is called by no line, `xk_eq_reach` by it alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.XkAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.LPFK9R.GrpReached
import Johnson.Desc.First.Link.Law.FifthTieLow
import Johnson.Desc.First.Link.Law.OwnBridge
import Johnson.P5T.NotIxAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (moreAll)
open Johnson.Desc.First.Walk.Tied (Reach)
open LPFK9.HandsAt (EW)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- The table's number of group l is l. -/
theorem group_number (Zp : ProofFile.Pub) (cF : Chain S ProofFile.Cl) (l : ℕ) : (P5J.At.N Zp cF).groupAt l = l := rfl

/-- **hg, from "reached".** -/
theorem hg_of_reach (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub}
    {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 0) (z, s)) :
    ∀ a, Desc.K9.atS.get? s = some a → (P5J.At.N Zp cF).groupAt l = a.L.check.group := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact fun a ha => LPFK9.HandsAt.grp_reached h.scope h.reads O z hl (group_number Zp cF l) s a hR ha

set_option maxRecDepth 1000000 in
/-- The library's test on the tables, at the written list. -/
theorem idxFit_W : LinkJoin.idxFitE moreAll IM.linksW IM.placesW = true := by decide +kernel

/-- From XK in front: the number of the index masks' message. -/
theorem index_of_xk {l : ℕ} (hl : l < 25) {N : Numbers} {Dp : PubData} {P : Type}
    {base : First.Pub → P × S → Bool} {z : P} {s : S}
    (hx : IM.XK N IM.linksW IM.placesW (EW Dp base z) (14 * l + IM.nAt l + 4 + 0) s = true) :
    s.out.indexMasks = Dp.N.indexNo := by
  obtain ⟨p, _, h1, _, h3, h4⟩ := LPFK9.HandsAt.place_W (l := l) (i := 2) hl (by omega)
  have hmem := LinkJoin.idxE_at moreAll IM.linksW IM.placesW idxFit_W _ l p h1 h3 h4
  have he : EW Dp base z (14 * l + IM.nAt l + 2 + 2) s = true := (IM.xk_parts hx).2.2.2.2
  have h5 : pubAll Dp base .indexIs (z, s) = true := List.all_eq_true.1 he .indexIs hmem
  rw [pubAll_indexIs] at h5
  exact beq_iff_eq.1 h5

/-- **hne, from "reached", no mark and the index masks' number (hIx).** -/
theorem hne_of_reach (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub}
    {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 0) (z, s)) (h0 : s.failed = none)
    (hIx : s.out.indexMasks = (P5J.At.N Zp cF).indexNo) : LinkJoin.OwnNotIndex s := by
  obtain ⟨p, _, h1, _, h3, h4⟩ := LPFK9.HandsAt.place_W (l := l) (i := 2) hl (by omega)
  have FF := ProofFile.Honest.FirstThread.foldFacts_raw h.toAtMg
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a) (fun _ _ hr => hr)
    (P5J.laid_at_head h.toAtMg) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  rw [P5J.placesW_at] at h1
  have hn := LPFK9.HandsAt.hearN_W hl
  have h9 := LPFK9.HandsAt.nAt_le l
  refine LinkJoin.ownNotIndex_reached FF (k := 14 * l + IM.nAt l + 2 + 2) (a := (z, s)) (p := p) (m := l) hR h0 h1
    h3 ?_ hIx (h.toAtMg.notIx _ hl _)
  rw [h4, hn]
  unfold IM.nAt shiftAt
  by_cases e : l = 24
  · subst e
    decide
  · rw [if_neg e]
    omega

/-- **XK behind the yes of "the one equation", from "reached" and XK in front.** -/
theorem xk_eq_reach (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {blk : Block S ProofFile.Cl} (ft : ℕ) {s s' : S} (base : First.Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub)
    (hbase : ∀ q (s s' : S), base q (z, s') = base q (z, s))
    (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0) s = true)
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 0) (z, s)) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0 + 1) s' = true :=
  xk_eq_at h hl ft base z hbase hb hy h0 hx (hg_of_reach h hl hR) (hne_of_reach h hl hR h0 (index_of_xk hl hx))

section
open ProofFile.Honest.FirstThread
open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM)

/-- **At the frame's own thread at the library's head.** -/
theorem xk_eq_thr (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → S → Option String) (carryX : Nat → ProofFile.InstPub × S → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S → Prop)
    (Kp : Place → S → S → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl}
    (ft : ℕ) {s s' : S} {k : Coins Bk} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (base : First.Pub → ProofFile.InstPub × S → Bool)
    (hbase : ∀ q (s s' : S), base q (m.st.input.x.pub, s') = base q (m.st.input.x.pub, s))
    (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * l + IM.nAt l + 4 + 0) k s m E)
    (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base m.st.input.x.pub)
      (14 * l + IM.nAt l + 4 + 0) s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base m.st.input.x.pub)
      (14 * l + IM.nAt l + 4 + 0 + 1) s' = true :=
  xk_eq_reach h hl ft base _ hbase hb hy h0 hx
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.xk_eq_thr
#print axioms ProofFile.Honest.K9.group_number
#print axioms ProofFile.Honest.K9.hg_of_reach
#print axioms ProofFile.Honest.K9.idxFit_W
#print axioms ProofFile.Honest.K9.index_of_xk
#print axioms ProofFile.Honest.K9.hne_of_reach
#print axioms ProofFile.Honest.K9.xk_eq_reach
