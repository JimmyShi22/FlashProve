-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SymOfLaysCells.lean: CONDITIONAL: IT MOVES A DEBT,
IT PAYS NONE.

What is here. THE INNER STEP OF THE THIRD STONE OF A BRIDGE TO THE HYPOTHESIS `CellIsList`
(Law/W/CellsTieOf.lean): WHAT ANOTHER HOUSE's PREMISE's FORM «THE SCRIPT LAYS THE FILLING OFF THE
PLANES» (`LaysCells`, Honest/K5/Law/LaysCells.lean) GIVES AT ONE SYMBOL OF ONE ARRAY, SPELLED AS A
PACKING OF THE TRACE's CELLS. General in the segment l: no kind of sub-protocol, no place of a
lookup and no plan is named. One statement; its proof is a chain of calls of that house's laws:
`msg_of_laysCells_all` (Honest/K5/Law/ReaderReadsOwn.lean), `cellsVals_size`, `cellsVals_pack` and
`labelNo_arrayLabel` (Honest/K5/Law/PackedVals.lean). It is the part of `eSyms_of_laysCells`
(Honest/K5/Law/LaysCells.lean) that does not speak of an attention segment.

  `sym_of_laysCells`   **the message with the plan's number of (l, the array's own message) holds,
      at the place at which the layout's rule lays symbol (i', c) of the array "M mu", the packing
      of the trace's cells of rows 3 i', 3 i' + 1, 3 i' + 2 of column c**, read under segment l and
      the matrix's label.

Not shown here. L: THAT A SCRIPT MEETS THE FORM: shown of no script here. hrd: that the frame's
reader of the cells is the lot's: a hypothesis.
hSz: on the filling's sizes; Honest/K5/Law/SizesOffPlanes.lean says where it is met. hA, hM, hne,
ho, hp, hi', hc: on public data: the array is there under the name "M mu"; mu names the matrix μ of
segment l; μ holds no planes and has an array of its own segment; the rule lays the symbol at p;
the symbol lies inside the matrix's packed shape. h: the library's hypothesis `P5J.AtMgA` on the
public files. NOT TRIED FOR EMPTINESS: no instance of the premises together is exhibited. All
limits of the heads of the files that it imports hold here; among them: closed facts by evaluation
in Lean's kernel lie beneath; no independent checker that its writers know of has replayed them;
through its imports it stands over files under Johnson/Goal/. THE FULL SIZE ALONE, and the format's
second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one. Nothing on soundness, on completeness or on any other
property.

Kin. The house whose form `LaysCells` is stands at Honest/K5/Law/LaysCells.lean,
Honest/K5/Law/ReaderReadsOwn.lean and Honest/K5/Law/PackedVals.lean;
this statement's proof is a chain of calls of its laws.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReaderReadsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName arrayLabel)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (LaysCells offPlanes planesAtRef msg_of_laysCells_all cellsVals_size
  cellsVals_pack labelNo_arrayLabel)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- CONDITIONAL: on every hypothesis named; the head says of each what it is. **WHAT THE FORM GIVES
AT ONE SYMBOL, AS A PACKING OF THE TRACE's CELLS.** -/
theorem sym_of_laysCells {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ} {l : ℕ}
    (L : LaysCells h Q S Vd N rd seat heard l) {cells : Tr → Cells}
    (hrd : ∀ v, (rd v).cells = cells v.trace) {mu : ℕ} (hmu : mu < 26)
    {A : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l (arrayLabel mu) = some A)
    {σ : Seg} {μ : MatName} (hM : Sz.ref.matAt l mu = some (σ, μ))
    (hne : μ ≠ .b ∧ μ ≠ .bA ∧ μ ≠ .bH) (ho : (Sz.ref.arrayNo σ μ).isSome = true) {i' c : ℕ}
    {p : ℕ × ℕ} (hp : VerifiableInference.Desc.laidAt A i' c = some p)
    (hi' : i' < Alg.symRows (Sz.ref.shape σ μ).1) (hc : c < (Sz.ref.shape σ μ).2)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) {hd : List Fmt.Drawn}
    (hN : N ≤ hd.length) :
    Q.msg (P5J.At.num Zp l A.message) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l A.message))) false
        p.1 p.2 =
      Alg.pack (2 ^ 20) (fun r : Fin (Sz.ref.shape σ μ).1 =>
        algebraMap Cb.Gl.F Cb.Gl.E ((cells v.trace).cell l μ.label r.val c)) i' := by
  obtain ⟨As, -, hf⟩ := Option.bind_eq_some_iff.1 hA
  have hname : A.name = arrayLabel mu := by simpa using List.find?_some hf
  have hn : labelNo A.name = some mu := by
    rw [hname]
    exact labelNo_arrayLabel hmu
  have hO : offPlanes l A.name = true := by
    simp only [offPlanes, hn, hM, Option.all_some]
    exact decide_eq_true hne
  have hz : (cellsVals Sz.ref).size l A.name =
      some (Alg.symRows (Sz.ref.shape σ μ).1, (Sz.ref.shape σ μ).2) := by
    rw [cellsVals_size Sz.ref hn hM ho]
    simp only [Sz.packedShape, Sz.shapeNo, hM]
  rw [msg_of_laysCells_all hSz L hA hO hn hM hp hz hi' hc k hv hN [],
    cellsVals_pack Sz.ref (rd v) [] hn hM hc i', hrd v]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.sym_of_laysCells
