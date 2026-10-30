-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/WitnessHasWAt356.lean: kind K13 (the members' batching) at number 356 of the proof
file's first chain, the member at which the prover sends the vector W. The full size and the
format's second hash function alone. Every statement is under the hypothesis h (`P5J.AtMgA`) and at
the
frame's own parameters of the first chain's thread (`lettersHead`, Honest/Thread/FirstHead.lean).
The type of the index W₀, the type of the stored randomness Rc, the prover H and the Script Q are
variables.

What it is for. `k13_wrowS_at_356` (Honest/K13/WRowAt356.lean), the share of the exchange at the
item "wrow" at 356, takes the premise `WitnessHasW` (Honest/K13/ExchangeM4.lean): where the reply
that the state in front holds is the one asked, and that state's table holds just one row: behind
the member's accepted step the word that the verifier's reader reads off the Script's witness, in
the main table of W's message, at the place of entry e below 2^kCol, is that row's weights times the
matrix of the witness's cells at column e. This file derives that premise from premises that name
the sender.

Main names.
  `k13_witnessHasW_of`: `WitnessHasW` at 356 from six premises: R, hmark, hmsg, hx, hg, hcells.
    General in the pile's filler and the ground.
  `k13_witnessHasW_at_356`: **`WitnessHasW` at 356 at the filler `pileAnyK3`**, from R, hG, hx, hwt
    and hM.
  `k13_seatedM4_at_356`: from these and hb, all eleven fields of `K13SeatedM4`
    (Honest/K13/SeatedM4.lean).
  `k13_items_at_356`: from the same, the shares at "pileOne" and "wrow", starting from the pair "the
    thread and what is said" (`ThrS`), at every Said.
  `k13_exchangeS_at_356`: from the same and the share at "pinV", the whole debt `ExchangeS` at 356.
  `k13_items_at_356_of_maker`: the two shares at a prover that the maker `onlineProverFromPublicFiles` returns, at its
    own book and ground, at every filling P.
  `k13_items_at_356_of_lots`: the same with R replaced by the premises from which the library
    derives it: two on the filling's lots (hex, ho) and two on the Script (msgs, pads).

The premises of `k13_witnessHasW_at_356`.
  R: kind K1's record `K1Seated` (Honest/K1/Seated.lean) at number 356, at K1's job for W's sending
    (`K1.wJobAt`) whose data are this kind's filling `wDataAt pileAnyK3 Zp G`. Among its twenty
    fields: the search of the prover's list at W's place finds K1's half at that job (`half`); the
    Script's messages and pads at W's seat are that job's texts (`msgs`, `pads`). R IS NOT SHOWN
    HERE.
  hG: G is the ground that the description's blank run makes at the public data Zp. At a maker's
    return it holds of the return's own ground (`k13_items_at_356_of_maker`).
  hx, hwt: at the one input w₁ the job's reader `wit` hands on the instance, and as the index's
    matrix what `weights` reads off the index. Where K1's sender and K13's half are given the same
    reader of the index, both hold by unfolding.
  hM: `MatTie` (Honest/K13/ExchangeAtM3.lean) at these parameters and `weights`. By
    `matTie_iff_at_head` (Honest/K13/MatTieAtHead.lean) it says: where w₁ is admitted (Vd w₁), the
    Script's cells at w₁ are the entries that `weights` reads off w₁'s index, at the rows of the
    plan's matrix and the columns below 2^kCol. It is the premise hM of the kind's own record at
    number 355 (`k13_seated_head`, `k13_riders_head`, Honest/K13/SeatedHead.lean), so one fact
    serves both numbers. Its parameter pl, a pile's filler, is read by neither matrix. hM IS NOT
    SHOWN HERE.

The premises of `k13_items_at_356_of_lots` in R's place are those of `K1.k1Seated_w_at_book`
(Honest/K1/Law/RecordAtBookFill.lean). hex: some lot of the filling has W's halves at `wit` and
`wDataAt pileAnyK3`. ho: every other lot has no half at W's place. msgs, pads: R's two fields on the
Script. NONE OF THE FOUR IS SHOWN HERE.

How. The word is the job's datum (`K1.word_is_data_head`, Honest/K1/Law/WordIsDataHead.lean, which
uses R and proves the two facts that it needs on the verifier's book behind the step). The datum is
`wVec` at the filling's row weights `wG` (`wPair_data`, Honest/K13/WPair.lean). At `pileAnyK3` these
weights are those of the one row on the verifier's table (`k13_g_at_356_pileAnyK3`, GAt356AnyK3.lean
of this folder). The matrix that `wVec` reads is the matrix of the Script's cells (hM, through
`matTie_iff_at_head`). That a yes of number 356 leaves no mark of failure, and that the shape's
message is the written one, hold under h (`K1.k1_w_noMark`, `K1.msg_w_head`).

Limits. Conditional on h and on the premises that each statement lists: R, hx, hwt and hM in all
from `k13_witnessHasW_at_356` on (in `k13_items_at_356_of_lots` hex, ho, msgs and pads stand in R's
place); hG where no maker's return is named; hb in all behind `k13_witnessHasW_at_356`; hV in
`k13_exchangeS_at_356`. Whether R and hM can hold together at a Script for which the thread's
invariant holds at some run in front of number 356 is not shown here. Where that invariant holds at
no run, or the member's step is never accepted, every statement here holds vacuously. `WitnessHasW`
speaks under two conditions: the reply that the state in front holds is the one asked (`ReplyIs`),
and that state's table holds just one row. In the shares both are met: the first by the thread's
clause on the reply, which has begun under hb (`head_reply`); the second by the field `claim` of
`PublicAtM4`, which holds wherever the invariant holds at 356 (`k13_public_at_356`,
Honest/K13/PileOneAt356.lean). `WitnessHasW` asks nothing of a pad's place, a row's tail, an entry
from 2^kCol on, or a mask row. `RowData.readyAt` is not asked of the filling: the job reads it
through `at_`, which tests `lays` alone, and under h every entry below 2^kCol is laid
(`k13_wLays_at_head`), so the default 0 of `K1.word_is_data_head` is not read; that the value laid
there is W's entry, though `ready` is not asked, is what hg says: the weights that the filling makes
are the verifier's row's. W IS LINEAR IN THE WEIGHTS: these statements are not to stand in front of
a law over coins. (The weights of that sentence are the claim's row weights, not the reader
`weights`; and W's entries hold values of the index's own entries.) "pinW" among the fields of
`K13SeatedM4` is, at these parameters, an item whose decoder is the constant "the Script's cells of
the input": it says nothing on what is committed. The facts beneath rest on evaluations in Lean's
kernel.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.K13.GAt356AnyK3
import Johnson.Desc.ProofFile.Honest.K13.WRowAt356
import Johnson.Desc.ProofFile.Honest.K13.WPair
import Johnson.Desc.ProofFile.Honest.K13.MatTieAtHead
import Johnson.Desc.ProofFile.Honest.K13.SeatedM4S
import Johnson.Desc.ProofFile.Honest.K1.Law.WordIsDataHead
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtBookFill
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K13.Law (cellAtNo matOfCells_low lowBits pin_at ρg wMsgFull)
open VerifiableInference.Desc.Sound (MsgT Mem)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_reply)
open ProofFile.Honest.K1 (K1Seated PlaceIn)
open ProofFile.Honest.K4.W (indexFacts_thr)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`WitnessHasW` at number 356 from six premises**, general in the pile's filler and the ground.
R: kind K1's record at W's job, whose data are `wDataAt pile Zp G`. hmark: a yes of the member
leaves no mark of failure. hmsg: the shape has W's message. hx: at the one input the job's instance
is the input's. hg: the row weights that the filling makes are those of the one row on the
verifier's table. hcells: at the one input the Script's cells are the entries of the matrix that the
job's reader gives. -/
theorem k13_witnessHasW_of {pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst} {G : ProofFile.Ground}
    {msg : Array OracleNotice} {first : ℕ} {blk₆ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'} {seats₀ : List (ℕ × ℕ)}
    {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 msg first (wDataAt pile Zp G)) own₀ .w h.𝔇.arr seats₀ ms
      rad)
    (hmark : ∀ s rs gs t, blk₆.decide s rs gs = .ok t → t.failed = none)
    (hmsg : linMessageW Zp.first.lin = some msg)
    (hx : (wit w₁).x = w₁.x)
    (hg : ∀ k s m En,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 356 k s m En →
      ReplyIs ProofFile.Inst.asked m.st.input.x s → ∀ row : TensorRow, s.rows = [row] →
      wG Zp.first.lin (wHeard Zp) (pile Zp G) m.st.input.x (m.st.heard.take (wHeard Zp)) = row.g)
    (hcells : Vd w₁ → ∀ i C, i < h.𝔇.P13.lin.matrixRows → C < 2 ^ h.𝔇.P13.lin.kCol →
      cellAtNo (Q.cells w₁) i C = Reading.gl.val (eOfF ((wit w₁).R.weights.entry i C))) :
    WitnessHasW (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 Zp h.𝔇.arr
      h.𝔇.mat13 ProofFile.Inst.asked := by
  intro blk hblk k s m En ds y cols s' hT hRp hd hS ds' row hrow e he
  obtain rfl : blk = blk₆ := Option.some.inj (hblk.symm.trans R.member)
  have hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      (fun _ _ _ => True) 356 k s m En := ⟨hT, trivial⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hin, -⟩ :=
    K1.step_at_block R (fun _ _ _ => True) hA hd hS
  obtain ⟨hw, hV⟩ : m.st.input = w₁ ∧ Vd m.st.input := by
    have hT' := hT
    unfold Thr at hT'
    exact hT'.2.2.2.2.2.2
  obtain ⟨sh, F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (k13_len356 h) (by decide)
    (pin_at (k := 356) (by decide) (by decide)) hT
  have hc : s.st.codes = Zp.first.codes := F.hc
  have hx' : (wit m.st.input).x = m.st.input.x := by
    rw [hw]
    exact hx
  have he' : e < 2 ^ Zp.first.lin.kCol := he
  obtain ⟨hl, hno⟩ := k13_wLays_at_head h pile G (wit m.st.input).x he'
  obtain ⟨hr, hj⟩ := wPair_lays_in_shape pile Zp G _ hmsg hl
  have hsh : Johnson.Prover.Send.shapeAt
      (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 msg first (wDataAt pile Zp G)).P 0 =
      Zp.first.lin.w := K1.w_shape_zero Zp.first (K1.wGp Zp) 4 msg hmsg
  have hn : 0 < (VerifiableInference.Desc.K1.parW Zp.first (K1.wGp Zp) 4 msg).sent.size := by
    rw [K1.parW_sent]
    have q := K1.w_first Zp.first.lin msg hmsg
    by_contra h0
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h0)] at q
    cases q
  have W := K1.word_is_data_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ R
    (fun _ _ _ => True) hmark hA hd hS 0 hn ds' _ _ hr hj
    (by rw [hsh]; exact (k13_wShape_at_head h).2)
    (by rw [hsh, k13_noPad_at_head h]; exact List.not_mem_nil)
    (by rw [hsh, (k13_wShape_at_head h).1]; rfl)
  have hlay : linLayW s.st.codes (VerifiableInference.Desc.K13.whereOf Zp).lin =
      linLayW Zp.first.codes Zp.first.lin := by
    rw [hc]
    rfl
  rw [hlay]
  have hidx : (linLayW Zp.first.codes Zp.first.lin).index e %
        2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits +
      2 ^ Johnson.Pack.k1 (Johnson.Prover.Send.shapeAt
        (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 msg first (wDataAt pile Zp G)).P 0) *
        ((linLayW Zp.first.codes Zp.first.lin).index e /
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits) =
      (linLayW Zp.first.codes Zp.first.lin).index e := by
    rw [hsh]
    exact Nat.mod_add_div _ _
  rw [hidx, Nat.add_zero] at W
  refine W.trans ?_
  rw [wPair_data pile Zp G msg first (wit m.st.input) _ 0 _ _, if_pos ⟨rfl, hl⟩]
  show wVec Zp.first.lin (wit m.st.input).R.weights
    (wG Zp.first.lin (wHeard Zp) (pile Zp G) (wit m.st.input).x
      (m.st.heard.take (wHeard Zp))) _ = _
  rw [hno, hx', hg k s m En hT hRp row hrow]
  unfold wVec
  rw [if_pos he', List.sum_ofFn]
  have key : ∀ (n n' : ℕ) (_ : n = n') (f : ℕ → OnBytes.Slice.GE),
      ∑ i : Fin n, f i.val = ∑ i : Fin n', f i.val := by
    intro n n' e f
    subst e
    rfl
  have hrows : OnBytes.Flat.numsFull.rows = Zp.first.lin.matrixRows := k13_rows_full h
  refine (key _ _ hrows.symm fun j => (row.g.map fun t => ρg.val (t.entry j)).sum *
    Reading.gl.val (eOfF ((wit m.st.input).R.weights.entry j e))).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : h.𝔇.mat13 ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).Q.wit k
      y.2.st.input (y.2.st.heard ++ ds')).cells i (lowBits _ e) =
      cellAtNo (Q.cells y.2.st.input) i e := matOfCells_low _ _ _ i e he
  have e2 : Reading.gl.val (eOfF ((wit m.st.input).R.weights.entry i.val e)) =
      cellAtNo (Q.cells y.2.st.input) i e := by
    rw [hin, hw, hcells (hw ▸ hV) i e (hrows ▸ i.isLt) he]
  exact congrArg (fun z => (row.g.map fun t => ρg.val (t.entry i.val)).sum * z) (e2.trans hm.symm)

variable {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst} {G : ProofFile.Ground} {first : ℕ}
  {blk₆ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- R and hM are premises that are not shown here. **`WitnessHasW` at number 356, at the filler
`pileAnyK3`.** R: kind K1's record at number 356, at W's job with the data `wDataAt pileAnyK3 Zp G`.
hG: G is the ground of the description's blank run at Zp. hx, hwt: at the one input the job's reader
hands on the instance, and as the matrix what `weights` reads off the index. hM: the kind's tie
`MatTie`: the Script's cells at the one input are the entries that `weights` reads. -/
theorem k13_witnessHasW_at_356
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h)) :
    WitnessHasW (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 Zp h.𝔇.arr
      h.𝔇.mat13 ProofFile.Inst.asked := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hC := (matTie_iff_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).1 hM
  exact k13_witnessHasW_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ R
    (K1.k1_w_noMark h.scope h.reads O R.member) (K1.msg_w_head h O) hx
    (k13_g_at_356_pileAnyK3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Bs O.made)
    fun hV i C hi hC' => by
      rw [hwt]
      exact hC hV i C hi hC'

/-- R and hM are premises that are not shown here. **All eleven fields of `K13SeatedM4` at number
356**, from the premises of `k13_witnessHasW_at_356` and hb: the thread's clause on the reply has
begun. -/
theorem k13_seatedM4_at_356 (hb : b₀ ≤ 356)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h)) :
    K13SeatedM4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 Zp cF h.𝔇.arr
      h.𝔇.mat13 ProofFile.Inst.asked :=
  seatedM4_at_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _
    (fun _ _ hr => head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb hr)
    (fun _ _ _ _ hT => k13_public_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT)
    (k13_witnessHasW_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ R hG hx hwt hM)

/-- R and hM are premises that are not shown here. **The kind's two shares of the exchange at number
356, from the pair "the thread and what is said", at every Said**: "pileOne" (which needs h alone)
and "wrow". -/
theorem k13_items_at_356 (hb : b₀ ≤ 356)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
        Item.pileOne ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
        Item.wrow :=
  ⟨k13_pileOneS_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said,
    k13_wrowS_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb
      (k13_witnessHasW_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ R hG hx hwt hM) Said⟩

/-- R, hM and hV are premises that are not shown here. **The whole debt `ExchangeS` at number 356**,
at every Said, from the same premises and hV: the share at "pinV", the one item of the member's row
that the structure `K13SeatedM4` does not give. -/
theorem k13_exchangeS_at_356 (hb : b₀ ≤ 356)
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    (hV : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
      Item.pinV) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356 :=
  k13_seated_m4_exchangeS
    (k13_seatedM4_at_356 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb R hG hx hwt hM) Said hV

end AtFullSide.K13

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT Mem)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead Letters OwnMsgs OwnPads)
open ProofFile.Honest.K1 (K1Seated PlaceIn SendJob lotNo wHalves wJobAt wGp seatAtMember msgTxt padTxt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {W₀ Rc Tr X₀ X' : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
include hA

/-- R and hM are premises that are not shown here. **The same two shares at a prover that the maker
returns**, at its own book and ground: P, the filling, is a variable, and so are the types of the
index and of the stored randomness. -/
theorem k13_items_at_356_of_maker
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst} {first : ℕ} {blk₆ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'} {seats₀ : List (ℕ × ℕ)}
    {ms : List Mem} {rad : ℕ → ℕ} (hb : b₀ ≤ 356)
    (R : K1Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp A.G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pl h.𝔇.P13
      (k13ReaderAt h))
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
        Item.pileOne ∧
      ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said 356
        Item.wrow := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  exact k13_items_at_356 h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb R
    (eG ▸ O.blank) hx hwt hM Said

/-- hex, ho, msgs, pads and hM are premises that are not shown here. **The same two shares with kind
K1's record replaced by the premises from which the library derives it.** hex: some lot of the
filling has W's halves at `wit` and `wDataAt pileAnyK3`. ho: every other lot has no half at W's
place. msgs, pads: the Script's messages and pads at W's seat are the texts of W's job. -/
theorem k13_items_at_356_of_lots
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = wHalves wit no (wDataAt pileAnyK3) A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves A.Z A.G = wHalves wit no (wDataAt pileAnyK3) A.Z A.G)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X')
    {L : Letters A.B ProofFile.Cl W₀ Rc ProofFile.Inst Tr X' ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)
    {J : SendJob (PlaceIn ProofFile.Inst) X'}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
      (wDataAt pileAnyK3 Zp A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 356)
        ((P5J.At.arr Zp) (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2)
        (L.thread.front + roundsTo L.bs 356) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2
        (fun k _ => padTxt 0 J n k))
    {weights : W₀ → Weights} {pl : PileOf ProofFile.Inst} (hb : b₀ ≤ 356)
    (hx : (wit w₁).x = w₁.x) (hwt : (wit w₁).R.weights = weights w₁.w₀)
    (hM : MatTie L weights pl h.𝔇.P13 (k13ReaderAt h))
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) :
    ExchangeAtS L.thread Said 356 Item.pileOne ∧ ExchangeAtS L.thread Said 356 Item.wrow := by
  obtain ⟨blk, R⟩ := K1.k1Seated_w_at_book h hA wit no (wDataAt pileAnyK3) hex ho Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w₁ own₀ hL hJ msgs pads
  subst hL
  subst hJ
  exact k13_items_at_356_of_maker h hA Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb R hx hwt hM Said

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_witnessHasW_of
#print axioms AtFullSide.K13.k13_witnessHasW_at_356
#print axioms AtFullSide.K13.k13_seatedM4_at_356
#print axioms AtFullSide.K13.k13_items_at_356
#print axioms AtFullSide.K13.k13_exchangeS_at_356
#print axioms AtFullSide.K13.k13_items_at_356_of_maker
#print axioms AtFullSide.K13.k13_items_at_356_of_lots
