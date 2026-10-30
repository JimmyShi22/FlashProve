-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/GAt356.lean: kind K13, the members' batching: hPile (THE LIBRARY's SENTENCE `PileIs`
ON THE PILE's FILLER, at the border 355: a definition: a premise's form) IS A PREMISE. UNDER THE
LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE, h (`P5J.AtMgA`), AT THE FRAME's OWN LAYING OF THE FIRST
CHAIN's THREAD (`lettersHead`): WHERE THE THREAD STANDS IN FRONT OF NUMBER 356, THE REPLY THAT THE
STATE HOLDS IS THE ONE ASKED, AND THE STATE's TABLE IS ONE ROW: THE ROW WEIGHTS THAT THE FILLING OF
W's MAIN ROW MAKES (`wG`, Johnson/Desc/ProofFile/Honest/K13/WData.lean) ARE THAT ROW's. Three
statements with their proofs; no definition; no closed fact of its own. THE EQUATION AND hPile READ
PUBLIC DATA ALONE: the verifier's state, the instance, the challenges heard: no coin, no entry of
the index, nothing of a Script. THE THREAD IN FRONT, AS IT IS TYPED, NAMES A RUN's COINS AND A
SCRIPT: of it the proof spends three clauses: how the state was made, the challenges' form, no mark.
THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main names: `claimG_congr`: the claim's row weights read of a pile its rows' weights and column
points alone. `k13_rounds355_at_head`: the first 355 sub-protocols have 48,270 rounds.
`k13_g_at_356`: **the tie.**

Why. W's entries are the claim's row weights times the matrix. The filling makes these weights of
the instance and the challenges heard; the verifier's claim has them in its state. That the two are
one is one of the links from which `WitnessHasW` (Honest/K13/ExchangeM4.lean) would follow.

How. Of the thread three clauses (Honest/Thread/Thr.lean): the verifier's own fold over the rounds
seen (`Thread.Made`); the form of the challenges heard (`Thread.Fit`: their number); that the state
bears no mark (in `Thread.Form`). The library cuts that fold at number 355 (`foldCutAt`,
Johnson/Desc/K13/Honest/FoldCut.lean): one state in front, the member's step on its own 2 + kCol
rounds. The member's decision is the kind's (`k13_memberIs_at`, Honest/K13/FromThreadAt.lean), and
where that returns, the state behind holds the row `Batt.rowOf` of the pile in front, at the
elements that these rounds sampled (`atM3_return_tied`, Johnson/Desc/K13/Honest/ReturnTied.lean).
That row's weights are `claimG` of the pile in front (`claimG_eq`, WData.lean). `PileIs` at the
state in front: the filler's rows and the pile's have the same weights and points. The counts:
`k13_wHeard_at_head`, `k13_wHeard_is_rounds` (WFillAtHead.lean of this folder).

Limits. CONDITIONAL ON h AND hPile: that h can be met is not shown here
(Honest/Thread/FirstHead.lean's head says what is had of it). `PileIs` is a sentence asked of a
filler, on the verifier's fold (Johnson/Desc/K13/Honest/PileDefs.lean); at these letters it is
shown, under h and a base, of the filler over the text of the claims with all its arms laid
(`k13_pileIs_at_head`, Honest/K13/PileIsAtHead.lean) and so of the closed term `pileAnyK3`
(`k13_pileIs_pileAnyK3`, GAt356AnyK3.lean of this folder): neither is imported here. The row weights
hold one value that was sent: the reply as heard: that is what ANY prover sent: only the premise on
the reply makes it the instance's; nothing follows from it on anything but that one value. THE LINK
SERVES `WitnessHasW`, AND W IS LINEAR IN THE WEIGHTS: this statement never stands in front of a law
over coins. The two premises behind the thread shut nothing out: under the thread at 356 the state's
table is always one row; where the thread's clause on the reply has begun it gives the premise on
the reply. Where the thread stands nowhere all holds for nothing. No filling of a prover is named:
the prover, the Script and the book are letters. The counts rest on evaluations in Lean's kernel
beneath, which no independent checker has replayed. This file's imports reach Johnson/Goal/.
`k13_g_at_356` is called by GAt356AnyK3.lean of this folder; nothing else outside this file calls
these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.WFillAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileOneAt356
import Johnson.Desc.ProofFile.Honest.K13.PileIs
import Johnson.Desc.K13.Honest.ReturnTied
import Johnson.Desc.K13.Honest.FoldCut
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks noDigest)
open VerifiableInference.Desc.K13 (battRounds)
open VerifiableInference.Desc.K13.Honest (rowReads PileIs roundsAhead roundsAhead_succ
  roundsAhead_take take_take_le foldCutAt atM3_return_tied sampledRV sampledRV_noDigest)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

/-- The claim's row weights read of a pile its rows' weights and column points alone (`rowReads`),
and their number: two piles with the same reads have the same. -/
theorem claimG_congr {p q : List TensorRow} (h : p.map rowReads = q.map rowReads) (x eps : E)
    (pt : List E) : claimG p x eps pt = claimG q x eps pt := by
  have hl : p.length = q.length := by
    have := congrArg List.length h
    rwa [List.length_map, List.length_map] at this
  have aux : ∀ (p q : List TensorRow) (ws : List E), p.map rowReads = q.map rowReads →
      ((p.zip ((ws.zip p).map fun a => mulE eps (mulE a.1 (eqEval a.2.psi pt)))).flatMap
        fun a => a.1.g.map fun t => t.scale a.2) =
      ((q.zip ((ws.zip q).map fun a => mulE eps (mulE a.1 (eqEval a.2.psi pt)))).flatMap
        fun a => a.1.g.map fun t => t.scale a.2) := by
    intro p
    induction p with
    | nil =>
      intro q ws hq
      cases q with
      | nil => rfl
      | cons b q => cases hq
    | cons a p ih =>
      intro q ws hq
      cases q with
      | nil => cases hq
      | cons b q =>
        rw [List.map_cons, List.map_cons, List.cons.injEq] at hq
        obtain ⟨h1, h2⟩ := hq
        have hg : a.g = b.g := congrArg Prod.fst h1
        have hs : a.psi = b.psi := congrArg Prod.snd h1
        cases ws with
        | nil => rfl
        | cons w ws =>
          simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons]
          rw [hg, hs, ih q ws h2]
  unfold claimG k13Maps
  rw [zipT_eq, zipT_eq, hl]
  exact aux p q _ h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD THE FIRST 355 SUB-PROTOCOLS OF THE FIRST CHAIN HAVE 48,270 ROUNDS**: 48,290 in
front of number 356, less the batching's 2 + kCol. CONDITIONAL on h. -/
theorem k13_rounds355_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    roundsTo cF.blocksInOrder 355 = 48270 := by
  obtain ⟨blk, hblk⟩ : ∃ blk, cF.blocksInOrder[355]? = some blk :=
    ⟨_, List.getElem?_eq_getElem (Nat.lt_of_succ_le (k13_len356 h))⟩
  have e1 : roundsTo cF.blocksInOrder 356 = 48290 :=
    (k13_wHeard_is_rounds h).symm.trans (k13_wHeard_at_head h)
  have e2 : roundsAhead cF.blocksInOrder 356 = roundsAhead cF.blocksInOrder 355 + blk.rounds.length :=
    roundsAhead_succ hblk
  have e3 : blk.rounds.length = 20 := by
    rw [(k13_memberIs_at h).rounds blk hblk]
    unfold battRounds
    rw [List.length_cons, List.length_cons, List.length_replicate, m3_kCol h]
  rw [roundsTo_eq_roundsAhead] at e1 ⊢
  omega

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- hPile (the library's sentence `PileIs` on the pile's filler, at the border 355) IS A PREMISE.
**THE ROW WEIGHTS THAT THE FILLING OF W's MAIN ROW MAKES ARE THE CLAIM's**: under h, from the thread
in front of number 356, the reply as asked, and the one row on the state's table. -/
theorem k13_g_at_356 {pile : PileOf ProofFile.Inst}
    (hPile : PileIs (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).bs
      (fun x => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).first
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf x)) 355
      (roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).bs 355) pile
      ProofFile.Inst.asked) :
    ∀ k s m En,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 k s m En →
      ReplyIs ProofFile.Inst.asked m.st.input.x s → ∀ row : TensorRow, s.rows = [row] →
      wG Zp.first.lin (wHeard Zp) pile m.st.input.x (m.st.heard.take (wHeard Zp)) = row.g := by
  intro k s m En hT hR row hrow
  unfold Thr at hT
  obtain ⟨-, hF, hP, -, hM, -, -⟩ := hT
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  subst hb'
  have hf' : foldBlocks 0 (cF.blocksInOrder.take 356) (ProofFile.startS Zp m.st.input.x.pub) m.seen cols =
      .ok (s, [], []) := hf
  have hfail : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hlen : m.st.heard.length = roundsTo cF.blocksInOrder 356 := drawsFit_length _ _ hF
  have n356 : roundsTo cF.blocksInOrder 356 = 48290 :=
    (k13_wHeard_is_rounds h).symm.trans (k13_wHeard_at_head h)
  have n355 : roundsAhead cF.blocksInOrder 355 = 48270 := k13_rounds355_at_head h
  obtain ⟨blk, hblk⟩ : ∃ blk, cF.blocksInOrder[355]? = some blk :=
    ⟨_, List.getElem?_eq_getElem (Nat.lt_of_succ_le (k13_len356 h))⟩
  have hblk' : (cF.blocksInOrder.take 356)[355]? = some blk := by
    rw [List.getElem?_take_of_lt (by decide)]
    exact hblk
  obtain ⟨sj, sj', c₀, n, h1, h2, h3⟩ := foldCutAt 0 (cF.blocksInOrder.take 356) 355 blk hblk' _ m.seen
    cols _ hf'
  rw [take_take_le cF.blocksInOrder (by decide : 355 ≤ 356),
    roundsAhead_take cF.blocksInOrder (by decide : 355 ≤ 356), n355] at h1
  rw [roundsAhead_take cF.blocksInOrder (by decide : 355 ≤ 356), n355] at h2
  have hnil : (cF.blocksInOrder.take 356).drop (355 + 1) = [] :=
    List.drop_eq_nil_of_le (List.length_take_le _ _)
  rw [hnil] at h3
  have es : sj' = s := by
    unfold foldBlocks at h3
    exact congrArg Prod.fst (Except.ok.inj h3)
  subst es
  obtain ⟨gs, hdec⟩ := VerifiableInference.Desc.stepOk h2
  obtain ⟨t, msg, x, hd, o, -, -, hfit, hrun, hs', hsamp⟩ :=
    atM3_return_tied ((k13_memberIs_at h).back blk hblk sj _ gs _ hdec)
  have hbl : blk.rounds.length = 20 := by
    rw [(k13_memberIs_at h).rounds blk hblk]
    unfold battRounds
    rw [List.length_cons, List.length_cons, List.length_replicate, m3_kCol h]
  have hB : (battRounds h.𝔇.P13).length = 20 := by
    rw [← (k13_memberIs_at h).rounds blk hblk]
    exact hbl
  have hsl : m.seen.length = 48290 := by
    rw [← n356, ← hlen, ← hseen, List.length_map]
  have htk : (m.seen.drop 48270).take blk.rounds.length = m.seen.drop 48270 := by
    apply List.take_of_length_le
    rw [List.length_drop, hsl, hbl]
  rw [htk] at hsamp
  rw [List.take_of_length_le (by rw [List.length_map, List.length_drop, hsl, hB]),
    sampledRV_noDigest] at hsamp
  have hown : drawnE (m.st.heard.drop 48270) = x :: hd.eps :: hd.rounds.map (·.2) := by
    rw [← hseen, ← List.map_drop]
    have e : drawnE ((m.seen.drop 48270).map (·.drawn)) =
        (sampledRV (m.seen.drop 48270)).map fun l => l.head?.getD zeroE := by
      unfold drawnE sampledRV
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun a _ => ?_
      show ((a.drawn.elems.head?.map E.ofTriple).getD zeroE) =
        ((a.drawn.elems.map E.ofTriple).head?).getD zeroE
      rw [List.head?_map]
    rw [e, hsamp, List.map_cons, List.map_cons, List.map_map]
    rfl
  have hfj : sj.failed = none := by
    rw [hs'] at hfail
    exact hfail
  have hrj : sj.out.reply = some (ProofFile.Inst.asked m.st.input.x) := by
    have q : ReplyIs ProofFile.Inst.asked m.st.input.x sj' := hR
    rw [hs'] at q
    exact q
  have hq := hPile m.st.input.x m.seen cols sj _ _ h1 hfj hrj ((m.st.heard.drop 48270).take 1)
  have hrw : row.g = (Batt.rowOf sj.out.pending o).g := by
    rw [hs'] at hrow
    have q := (List.cons.inj hrow).1
    rw [← q]
    rfl
  rw [hrw, (claimG_eq hfit hrun).1]
  have hk : Zp.first.lin.kCol = 18 := (k13_wRow_at_head h).2.2.2
  have hall : m.st.heard.take (wHeard Zp) = m.st.heard := by
    apply List.take_of_length_le
    rw [k13_wHeard_at_head h, hlen, n356]
  rw [hall]
  unfold wG wOwn wFront
  rw [k13_wHeard_at_head h, hk]
  show claimG (pile m.st.input.x (m.st.heard.take 48271))
    ((drawnE (m.st.heard.drop 48270)).getD 0 zeroE) ((drawnE (m.st.heard.drop 48270)).getD 1 zeroE)
    ((drawnE (m.st.heard.drop 48270)).drop 2) = _
  rw [hown]
  show claimG (pile m.st.input.x (m.st.heard.take 48271)) x hd.eps (hd.rounds.map (·.2)) = _
  apply claimG_congr
  have e5 : m.st.heard.take 48271 =
      (m.seen.take 48270).map (·.drawn) ++ (m.st.heard.drop 48270).take 1 := by
    rw [List.map_take, hseen]
    exact List.take_add (l := m.st.heard) (i := 48270) (j := 1)
  rw [e5]
  have e6 : roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).bs 355 = 48270 :=
    k13_rounds355_at_head h
  rw [e6] at hq
  exact hq

end AtFullSide.K13

#print axioms AtFullSide.K13.claimG_congr
#print axioms AtFullSide.K13.k13_rounds355_at_head
#print axioms AtFullSide.K13.k13_g_at_356
