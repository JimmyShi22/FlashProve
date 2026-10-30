-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/IndexIs.lean: CONDITIONAL.

What is here. ONE HYPOTHESIS ON THE WEIGHTS, FOR THE THREE TIES THAT THE LAWS ON THE FEED-FORWARD
LAYERS' OWN ROUNDS (sub-protocol K4) ASK. Three laws tie the honest side's reader of the index (the
parameter weights: how an input's index is read, by row and column) to the matrix that the script's
witness holds (Q.cells), each as far as it spends the tie: the hypothesis on the embedding in the
law on the layers' own item (there called hiW), K4WeightsTieK (Law/WoShareK.lean: the merge's own
claim, entry by entry) and K4LayersTieAt (Law/W/LayersTie.lean: the layers' matrices). K4IndexIs
says of one input v: there is an index i of the library's own type (Cm.Idx, Cm/RelBase.lean: a
well-formed digit matrix on the reference shape) such that the script's cells at v hold i (Holds,
Johnson/Flat/LedgerClaim.lean: each cell is the image of i's matrix's entry, and that matrix is 0
outside the cells' shape), and the reader's entry AT EVERY ROW AND COLUMN has the image of i's
matrix's entry. It reads no coin, no challenge, no state and no group. It is meant to be asked
once, of the thread's own input, under the thread's parameter Vd: the condition on inputs under
which the thread speaks (valid, Honest/Thread/FirstHead.lean).

  `K4IndexIs`       the hypothesis. This defines a hypothesis.
  `wm_of_entries`   its second clause, at wmOf of K4's own input structure k4Wit.
  `input_head`      where the first chain's thread stands, the run's input is the thread's own,
                    and Vd holds of it.
  `indexIs_thr`     so a clause under Vd gives the hypothesis at the run's input.

Not shown here. THAT IT HOLDS OF ANY SCRIPT AND INPUT: no example is shown here
(k4IndexIs_of_reader, Law/W/ExchangeAllItems.lean, has it at a ready input of a prover that onlineProverFromPublicFiles
returns, where the filling's trace is an index's, the reader reads that index and the Script's cells
are its matrix: five hypotheses). WHAT AN INPUT MUST BE FOR IT TO HOLD: its reader answers with the
index's own matrix, so WITH 0 OUTSIDE THE TABLE, in rows and in columns. THE TYPE OF AN INPUT DOES
NOT GIVE THAT: the reader's entry is a free function of a row and a column. WHERE weights IS THE
IDENTITY THIS IS A CONDITION ON THE PROVER's PRIVATE INPUT, which the thread can have from Vd alone.
That it gives each of the three ties is not shown in this file. THE FULL SIZE ALONE: the definition
stands at the full size's shape of the cells and at the library's reference shape of an index; of
the four names wm_of_entries alone is general in the sizes. h, in input_head and indexIs_thr: the
library's hypothesis on the public files; no example of h is shown here; the format's second hash
function alone there. A LAW, NOT A PART: its imports reach modules under Johnson/Goal/, through h
and through the type of the script's cells: no file that defines a part of the proof file's
description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (Forest.Heard)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead head_valid)

/-- **THE SCRIPT's CELLS AND THE HONEST SIDE's READER ARE ONE INDEX's MATRIX**, at the input v: the
cells hold an index i, and the reader's entry at every row a and column b, also outside the table,
has the image of i's matrix's entry. weights: how the index is read. This defines a hypothesis; the
definition claims nothing. -/
def K4IndexIs {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (weights : W₀ → Weights) (v : Local W₀ Rc ProofFile.Inst Tr) : Prop :=
  ∃ i : Cm.Idx, Holds (Q.cells v) i ∧
    ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((weights v.w₀).entry a b) = ((i.mat a b : ℤ) : Cb.Gl.E)

/-- K4IndexIs' second clause, at wmOf of K4's own input structure. W: any integer matrix.
CONDITIONAL: on he. -/
theorem wm_of_entries {W₀ Rc Xi Tr : Type} (Qp : K4Pub) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat) (look : List Fmt.Drawn → Forest.Heard)
    (v : Local W₀ Rc Xi Tr) {W : Inst.Model.Mat}
    (he : ∀ a b,
      algebraMap Cb.Gl.F Cb.Gl.E ((weights v.w₀).entry a b) = ((W a b : ℤ) : Cb.Gl.E)) :
    wmOf (k4Wit Qp cells weights tokens look v).w = fun a b => ((W a b : ℤ) : Cb.Gl.E) := by
  funext a b
  show OnBytes.Slice.readE (OnBytes.ofF (OnBytes.Slice.ofF _)) = _
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]
  exact he a b

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **Where the thread stands, the run's input is the thread's own, and Vd holds of it.**
CONDITIONAL: on hT. -/
theorem input_head {k : ℕ} {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    mm.st.input = w₁ ∧ Vd w₁ := by
  have q := (head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ mm.st.input).1
    hT.2.2.2.2.2.2
  exact ⟨q.1, q.1 ▸ q.2⟩

/-- **A clause under Vd gives the hypothesis at the run's input.** CONDITIONAL: on hI and hT. -/
theorem indexIs_thr {weights : W₀ → Weights} (hI : Vd w₁ → K4IndexIs Q weights w₁) {k : ℕ}
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4IndexIs Q weights mm.st.input := by
  obtain ⟨e, hV⟩ := input_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  rw [e]
  exact hI hV

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.wm_of_entries
#print axioms ProofFile.Honest.K4.input_head
#print axioms ProofFile.Honest.K4.indexIs_thr
