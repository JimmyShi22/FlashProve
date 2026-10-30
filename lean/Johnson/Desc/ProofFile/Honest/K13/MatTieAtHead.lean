-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/MatTieAtHead.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h (`P5J.AtMgA`: a hypothesis), AT THE FRAME's OWN LAYING OF THE FIRST CHAIN's THREAD
(`lettersHead`) AND THE LIBRARY's READER (`k13ReaderAt`): THE KIND's TIE `MatTie` (both:
ExchangeAtM3.lean of this folder) SAID OVER AGAIN IN THE LETTERS OF THOSE WHO CAN PAY IT. IT PAYS
NOTHING: an "if and only if". One statement with its proof; no definition.

Main name: `matTie_iff_at_head`.

What it says. `MatTie` at these letters holds exactly if: where the one input w₁ is admitted (Vd
w₁), the cell number (i, C) of the Script's cells of w₁ is the value of the entry (i, C) that the
half's reader of the index gives: for every row i of the plan's matrix and every column C below
2^kCol. Both sides are functions of the prover's input alone: no coin, no challenge, no state,
nothing that is sent or shown.

Whose the debt then is. Whoever lays the Script's field `cells` (Honest/Thread/First.lean) and
whoever lays the half's reader `weights` in a filling: where `cells` is laid as a term the equation
is had by unfolding or by a law: the laying's page is to say which.

How. At `lettersHead` an input is admitted exactly if it is w₁ and Vd holds of it. The reader's
matrix is the library's `matOfCells` (Johnson/Desc/K13/Law/MatOfCells.lean) at the witness's cells,
cast along the equation of the two numbers of rows (`k13_rows_full`, FromThreadAt.lean); the
witness's cells are the Script's. The half's matrix is `k13Wit` at `k13Ask` (Part.lean). Both read a
row's number and the column's bits as a number; the columns are the numbers below 2^kCol.

Limits. CONDITIONAL ON h. `MatTie` ITSELF IS SHOWN NOWHERE. ONE INPUT: w₁. A premise of
completeness's kind on data that the prover alone holds: not to stand in front of a law over coins.
`cellAtNo` is 0 outside the cells' own bounds: under h every (i, C) of the statement lies inside
them (`k13_rows_full`; the library's `P5J.AtMg.cols13`, Johnson/P5J/Cols13Paid.lean): not used here.
Of what is stored or committed nothing is said. Nothing calls this statement.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ExchangeAtM3
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K13.Law.MatOfCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K13.Law (Wit cellAtNo matOfCells matOfCells_low lowBits)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

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

/-- **`MatTie` AT THE HEAD, IN ITS PAYERS' OWN LETTERS**: at the frame's own laying of the thread,
at the library's reader: it says just this: if the one input w₁ is admitted (Vd w₁), the cell number
(i, C) of the Script's cells of w₁ is the value of the entry (i, C) that the half's reader of the
index gives: for every row i of the plan's matrix and every column C below 2^kCol. IT PAYS NOTHING.
CONDITIONAL on h. -/
theorem matTie_iff_at_head {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst} :
    MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) weights pile h.𝔇.P13
        (k13ReaderAt h) ↔
      (Vd w₁ → ∀ i C, i < h.𝔇.P13.lin.matrixRows → C < 2 ^ h.𝔇.P13.lin.kCol →
        cellAtNo (Q.cells w₁) i C = Reading.gl.val (eOfF ((weights w₁.w₀).entry i C))) := by
  have cm : ∀ {n n' k : Nat} (e : n = n') (W : Wit OnBytes.Slice.GE n k) (i : Fin n')
      (c : Fin k → Bool), (castWit e W).mat i c = W.mat ⟨i.val, e ▸ i.isLt⟩ c := by
    intro n n' k e W i c
    subst e
    rfl
  have hl : ∀ (k : Coins Bk) (s : TS) (hd : List Fmt.Drawn)
      (i : Fin h.𝔇.P13.lin.matrixRows) (c : Fin h.𝔇.P13.lin.kCol → Bool),
      (k13ReaderAt h ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf w₁.x, s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).Q.wit k w₁ hd)).mat i c =
        cellAtNo (Q.cells w₁) i.val (Nat.ofBits c) := by
    intro k s hd i c
    unfold k13ReaderAt
    rw [cm]
    rfl
  constructor
  · intro hM hV i C hi hC
    have q := congrFun (congrFun (hM default
      (ProofFile.startS Zp ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf w₁.x)) w₁ []
      ⟨rfl, hV⟩) ⟨i, hi⟩) (lowBits h.𝔇.P13.lin.kCol C)
    rw [hl] at q
    have e : Nat.ofBits (lowBits h.𝔇.P13.lin.kCol C) = C := by
      unfold lowBits
      rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hC]
    rw [e] at q
    rw [q]
    show Reading.gl.val (eOfF ((weights w₁.w₀).entry i
      (Nat.ofBits (lowBits h.𝔇.P13.lin.kCol C)))) = _
    rw [e]
  · intro hR k s w hd hv
    obtain ⟨e, hV⟩ := hv
    subst e
    funext i c
    rw [hl]
    exact hR hV i.val (Nat.ofBits c) i.isLt (Nat.ofBits_lt_two_pow c)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.matTie_iff_at_head
