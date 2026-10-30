-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoWeightsParts.lean: CONDITIONAL.

What is here. THE TIE ON THE WEIGHTS THAT THE PENDING ROW's ITEM ASKS (`K4WeightsTieK`,
Law/WoShareK.lean) IN ITS THREE PARTS, EACH WITH ITS OWNER, at the member of the feed-forward
layers' own rounds (sub-protocol K4). The tie has three conjuncts of three sorts. (a) The witness's
matrix has at most 2 ^ kRow rows: A PUBLIC FACT: under the library's hypothesis h on the public
files it is a theorem here (`rows_head`). (b) The matrix of the honest input's weights is 0 from row
nR on: A SENTENCE ON THE INDEX ALONE: it is named (`K4IndexZeroFrom`) and is drawn, where the thread
stands, from what the thread's parameter Vd says of the thread's own input. (c) Inside its rows the
witness's matrix, as the reader of the pile of pending rows reads it, is that matrix: A TIE ON THE
THREAD's WITNESS: it is named (`K4EntriesTieK`) and stays a hypothesis; at the library's own reader
it reads the script's cells and the input alone (Law/WoOfIndex.lean).

  `K4IndexZeroFrom`   (b), in the reader's own field. This defines a hypothesis.
  `K4EntriesTieK`   (c): the tie's third conjunct, to the letter. This defines a hypothesis.
  `weightsTieK_of`   the tie from the three.
  `wm_zero_of_index`   (b) in the tie's own form, from `K4IndexZeroFrom`.
  `rows_head`   **(a) under h.** No comparison of numbers by Lean's kernel: by the library's
     `lin_in_scope` (Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean).
  `k4_weightsTie_head`   **the hypothesis hWt of the statements on the pending row's item at the
     first chain's thread (Law/WoHead.lean and those over it), in its binder's own shape, from one
     clause on Vd and `K4EntriesTieK`.**

Limits. `K4IndexZeroFrom` AND `K4EntriesTieK` ARE HYPOTHESES: nothing shows either of any input or
thread. THE TYPE OF AN INPUT DOES NOT GIVE `K4IndexZeroFrom`: the reader of the index is a free
function of a row and a column, and at some inputs that the type allows the sentence is false: so it
is asked under Vd (hZ). h: the library's hypothesis `P5J.AtMgA`. THE FULL SIZE ALONE, and the
format's second hash function alone, in `rows_head` and `k4_weightsTie_head`. On h: the side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). h is `rows_head`'s only hypothesis; of h together with hZ and hE no example is known to
us. A LAW, NOT A PART: its imports reach modules under Johnson/Goal/ through h: no file that defines
a part of the proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoHead
import Johnson.Desc.Sound.K11Tests.PendAllNoPin
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (Reading Forest.Heard)
open OnBytes.Road (Wm)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim First.S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open VerifiableInference.Desc.K13.Law (lowBits)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_valid)

/-- **The index is 0 from row nR on.** weights: how the index is read. This defines a hypothesis;
the definition claims nothing. -/
def K4IndexZeroFrom {W₀ Rc Xi Tr : Type} (nR : ℕ) (weights : W₀ → Weights)
    (v : Local W₀ Rc Xi Tr) : Prop :=
  ∀ j, nR ≤ j → ∀ C, (weights v.w₀).entry j C = 0

/-- **Inside its rows the witness's matrix is M**, at a reader typed at any number kC of column
bits. This defines a hypothesis; the definition claims nothing. -/
def K4EntriesTieK {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk First.S Claim V W X Pb)
    {nR kC : Nat} (rw : T.P × First.S → T.Wt → PileWit nR kC) (k : Coins Bk) (y : Mid W X)
    (s' : First.S) (M : Wm Cb.Gl.E) : Prop :=
  ∀ ds' (i : Fin nR) (C : Nat), C < 2 ^ kC →
    (rw (T.seat k y s') (T.wit k y.st.input (y.st.heard ++ ds'))).mat i (lowBits kC C) = M i C

/-- **The tie from its three parts.** CONDITIONAL: on the three. -/
theorem weightsTieK_of {Bk : ProverCoinCounts} {V W X Pb : Type} {T : Thread Bk First.S Claim V W X Pb}
    {d : PubData} {nR kC : Nat} {rw : T.P × First.S → T.Wt → PileWit nR kC} {k : Coins Bk}
    {y : Mid W X} {s' : First.S} {M : Wm Cb.Gl.E} (a : nR ≤ 2 ^ d.lin.kRow)
    (b : ∀ j, nR ≤ j → ∀ C, M j C = 0) (c : K4EntriesTieK T rw k y s' M) :
    K4WeightsTieK T d rw k y s' M := by
  unfold K4WeightsTieK
  exact ⟨a, b, c⟩

/-- **The matrix of the honest input's weights is 0 from row nR on.** CONDITIONAL: on hz. -/
theorem wm_zero_of_index {W₀ Rc Xi Tr : Type} (Q : K4Pub) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat) (look : List Fmt.Drawn → Forest.Heard)
    {nR : ℕ} {v : Local W₀ Rc Xi Tr} (hz : K4IndexZeroFrom nR weights v) :
    ∀ j, nR ≤ j → ∀ C, wmOf (k4Wit Q cells weights tokens look v).w j C = 0 := by
  intro j hj C
  show Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF ((weights v.w₀).entry j C))) = 0
  rw [hz j hj C]
  show OnBytes.Slice.readE (OnBytes.ofF (OnBytes.Slice.ofF (0 : Cb.Gl.F))) = 0
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF, map_zero]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE READER's NUMBER OF ROWS IS AT MOST 2 ^ kRow, UNDER h.** CONDITIONAL: on h. THE FULL SIZE
ALONE (h). -/
theorem rows_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    OnBytes.Flat.numsFull.rows ≤ 2 ^ h.𝔇.d1.lin.kRow := by
  have e : h.𝔇.d1.lin.matrixRows = 3076096 := (LT28.K11Tests.lin_in_scope h.scope h.laid.pub).1
  show OnBytes.Flat.numsFull.rows ≤ 2 ^ OnBytes.ceilLog2 h.𝔇.d1.lin.matrixRows
  rw [e]
  exact OnBytes.Slice.le_two_pow_ceilLog2 3076096

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE TIE ON THE WEIGHTS AT EVERY ACCEPTED STEP OF THE MEMBER, FROM ONE CLAUSE ON Vd AND THE TIE
ON THE ENTRIES.** hZ: under Vd the thread's own input has an index that is 0 from the reader's
number of rows on. hE: the tie on the entries, at every accepted step. CONDITIONAL: on h, hZ and hE.
THE FULL SIZE ALONE (h). -/
theorem k4_weightsTie_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k : ℕ}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hZ : Vd w₁ → K4IndexZeroFrom OnBytes.Flat.numsFull.rows weights w₁)
    (hE : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4EntriesTieK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c y.2
        s' (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w)) :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4WeightsTieK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.d1
        h.𝔇.rw13 c y.2 s' (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w) := by
  intro blk hb c s mm E ds y cols s' hT hd hS
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨e, hV⟩ := (head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ mm.st.input).1
    hT'.2.2.2.2.2.2
  refine weightsTieK_of (rows_head h)
    (wm_zero_of_index Qp cells weights tokens (look Qp) ?_)
    (hE blk hb c s mm E ds y cols s' hT hd hS)
  rw [e]
  exact hZ (e ▸ hV)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.weightsTieK_of
#print axioms ProofFile.Honest.K4.wm_zero_of_index
#print axioms ProofFile.Honest.K4.rows_head
#print axioms ProofFile.Honest.K4.k4_weightsTie_head
