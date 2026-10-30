-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoOfIndex.lean: CONDITIONAL.

What is here. THE TWO PARTS OF THE TIE ON THE WEIGHTS THAT THE PENDING ROW's ITEM LEAVES AS
HYPOTHESES (Law/WoWeightsParts.lean: `K4IndexZeroFrom`, a sentence on the index alone, and
`K4EntriesTieK`, a tie on the thread's witness), EACH FROM THE ONE HYPOTHESIS ON THE WEIGHTS
`K4IndexIs` (Law/IndexIs.lean: the script's cells hold an index of the library's own type, and the
honest side's reader of the index answers with that index's matrix at every row and column), at the
member of the feed-forward layers' own rounds (sub-protocol K4). The first: that matrix is 0 outside
the cells' shape, and the field's embedding is one-to-one. The second, under the library's
hypothesis h: the reader of the pile of pending rows reads the witness's cells (the library's
`matOfCells`, Johnson/Desc/K13/Law/MatOfCells.lean), which are the script's, and inside the shape
these are the images of the matrix's entries. So the whole tie follows, under h, from one clause on
the thread's parameter Vd (the condition on inputs under which the thread speaks: `valid`,
Honest/Thread/FirstHead.lean).

  `zeroFrom_of_index`   `K4IndexZeroFrom` at the cells' number of rows.
  `entriesTie_of_index`   **`K4EntriesTieK` at the library's own reader**, at a state of the run
     whose input is v.
  `k4_weightsTie_index`   **the hypothesis hWt of the statements on the pending row's item at the
     first chain's thread, in its binder's own shape, from h and hI : Vd w₁ → K4IndexIs Q weights
     w₁.**

Limits. `K4IndexIs` IS A HYPOTHESIS: nothing shows it of any script and input; the type of an input
does not give it (Law/IndexIs.lean's head says what an input must be for it to hold). IT ASKS MORE
THAN THE TWO PARTS TOGETHER: that the matrix is well formed (through the library's type of an
index), and zeros from the cells' number of columns on, of which neither part speaks: so a statement
that asks hI in their place has fewer names and a stronger hypothesis. h: the library's hypothesis
`P5J.AtMgA`. THE FULL SIZE ALONE, and the format's second hash function alone, from `entriesTie_of_index`
on. On h: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hI (and ev, at `entriesTie_of_index`) no example is known to us. A
LAW, NOT A PART: its imports reach modules under Johnson/Goal/: no file that defines a part of the
proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.IndexIs
import Johnson.Desc.ProofFile.Honest.K4.Law.WoWeightsParts
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Desc.K13.Law.MatOfCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (Forest.Heard)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (lowBits matOfCells matOfCells_in)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

/-- **The index is 0 from the cells' number of rows on.** CONDITIONAL: on hI. -/
theorem zeroFrom_of_index {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {weights : W₀ → Weights} {v : Local W₀ Rc ProofFile.Inst Tr} (hI : K4IndexIs Q weights v) :
    K4IndexZeroFrom OnBytes.Flat.numsFull.rows weights v := by
  obtain ⟨i, ⟨_, h2⟩, he⟩ := hI
  intro j hj C
  have e := he j C
  rw [h2 j C fun q => absurd q.1 (Nat.not_lt.2 hj), Int.cast_zero] at e
  exact (map_eq_zero (algebraMap Cb.Gl.F Cb.Gl.E)).1 e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **INSIDE ITS ROWS THE WITNESS's MATRIX, AS THE LIBRARY's OWN READER READS IT, IS THE MATRIX OF
THE HONEST INPUT's WEIGHTS.** y: where the run stands; v: its input. CONDITIONAL: on h, ev and hI.
THE FULL SIZE ALONE (h). -/
theorem entriesTie_of_index (c : Coins Bk) {y : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} (s' : TS)
    (Qp : K4Pub) (cells : Tr → Cells) {weights : W₀ → Weights} (tokens : ProofFile.Inst → Array Nat)
    (look : List Fmt.Drawn → Forest.Heard) {v : Local W₀ Rc ProofFile.Inst Tr} (ev : y.st.input = v)
    (hI : K4IndexIs Q weights v) :
    K4EntriesTieK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.rw13 c y s'
      (wmOf (k4Wit Qp cells weights tokens look v).w) := by
  obtain ⟨i, ⟨h1, _⟩, he⟩ := hI
  intro ds' a C hC
  have hc : C < P5J.colsAt OnBytes.Flat.numsFull :=
    lt_of_lt_of_eq hC
      (show 2 ^ h.𝔇.P13.lin.kCol = P5J.colsAt OnBytes.Flat.numsFull from h.cols13)
  rw [wm_of_entries Qp cells weights tokens look v he]
  show matOfCells OnBytes.Flat.numsFull.rows h.𝔇.P13.lin.kCol (Q.cells y.st.input) a
      (lowBits h.𝔇.P13.lin.kCol C) = ((i.mat a C : ℤ) : Cb.Gl.E)
  rw [matOfCells_in _ _ _ a C hC a.isLt hc, ev]
  exact h1 ⟨a, a.isLt⟩ ⟨C, hc⟩

/-- **THE TIE ON THE WEIGHTS AT EVERY ACCEPTED STEP OF THE MEMBER, FROM ONE CLAUSE ON Vd.** hI:
under Vd the script's cells and the honest side's reader are one index's matrix, at the thread's
own input. CONDITIONAL: on h and hI. THE FULL SIZE ALONE (h). -/
theorem k4_weightsTie_index
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k : ℕ}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hI : Vd w₁ → K4IndexIs Q weights w₁) :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' →
      K4WeightsTieK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread h.𝔇.d1
        h.𝔇.rw13 c y.2 s' (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w) :=
  k4_weightsTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said
    (fun hV => zeroFrom_of_index (hI hV))
    fun _ _ c _ _ _ _ _ _ s' hT _ hS =>
      entriesTie_of_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ c s' Qp cells tokens (look Qp)
        (moved_state hS.1).1
        (indexIs_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hI hT.1)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.zeroFrom_of_index
#print axioms ProofFile.Honest.K4.entriesTie_of_index
#print axioms ProofFile.Honest.K4.k4_weightsTie_index
