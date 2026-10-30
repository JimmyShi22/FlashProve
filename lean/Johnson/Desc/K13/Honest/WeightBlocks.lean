-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/WeightBlocks.lean: kind K13, the members' batching: OF WHAT FORM THE WEIGHTS
OF A ROW ON THE TABLE ARE, IN FRONT OF THE BATCHING AND BEHIND IT. Where the verifier's
`pendingRowO` returns a row, that row's weights are the list of vectors that the library's
`stretchBlocks` (OnBytes/Iop/Lin.lean) returns, at a stretch of rows that ends at or below the
matrix's rows; where each row of a pile has weights of that form, each weight of the one row that
the batching hands on is a vector of some such stretch times an element. Which stretch is not
said: the statement does not tie it to the pile. Three statements with their proofs; no definition.
The library's text is called, not written anew. It stands over the library alone. GENERAL IN THE
SIZE; no hypothesis on public files.

TWO SENTENCES ON A LIST g OF WEIGHTS, AT A SHAPE Sh, WRITTEN OUT WHEREVER THEY STAND.
  (plain)   there are firstRow and values with firstRow + values.size ≤ Sh.matrixRows and
            g = stretchBlocks Sh.kRow firstRow values (2 * Sh.kRow + 2) firstRow
  (scaled)  each w in g is t.scale x for an element x and a vector t of some
            stretchBlocks Sh.kRow firstRow values fuel start with
            firstRow + values.size ≤ Sh.matrixRows
Main names:
  `pendingRowO_blocks`: **the row that the verifier's `pendingRowO`
    (Johnson/Desc/First/Pend/Row.lean) returns has (plain).** Two calls of the library:
    `pendingRowO_iff` and `weightsOnRows_iff` (Johnson/Desc/First/Pend/RowMeans.lean): the bound is
    the first test of `weightsOnRows` itself.
  `battRow_blocks`: **where each row of a pile has (plain), the row that the batching hands on
    (`Batt.rowOf`, OnBytes/Iop/Batt.lean) has (scaled).** `batt_blocks`: so where `K13.batt`
    answers.
Who calls them: WeightBlocksAtFlat.lean (Johnson/Desc/ProofFile/Honest/K13/): the first and the
third; the third calls the second.
Nearest kin in the library: `rowOf_weights` and `batt_weights`
(Johnson/Desc/K13/Law/WeightsKept.lean) and `rowOf_ok` (Johnson/Desc/Key/KeyBattRow.lean): the same
road for the test `Tensor.ok`; the two proofs here follow theirs step for step.
`stretchBlocks_skel` (OnBytes/Flat/PendingSizes.lean): the vectors' pairs and written-out variables
do not hang on the values.

What it is for. A later sub-protocol asks that each of these weights can be cut below the matrix's
rows; whether it can hangs on the vectors' pairs and written-out variables, which `stretchBlocks`
lays and `Tensor.scale` leaves.

Limits. Sh is a letter: nothing here ties it to the shape at which a sub-protocol is made. That each
row of a pile comes from `pendingRowO` is a premise of the second and the third, in the form
"(plain) at each row". (scaled) is not shown to pass a second batching.

What is not claimed. That `pendingRowO` or `K13.batt` returns anywhere. Anything on the values, the
column point, the mask form or the target. That a weight can be cut. It is none of the library's
goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Desc.K13.Law.Law
import OnBytes.Chain.Lists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff weightsOnRows_iff)

/-- **The weights of the row that `pendingRowO` returns are the vectors of one stretch that ends at
or below the matrix's rows.** -/
theorem pendingRowO_blocks {lay : WsLay} {im : ℕ} {o : WsForkOut} {n : ℕ} {Sh : LinShape}
    {os os' : Array OnBytes.Oracle} {r : TensorRow}
    (h : pendingRowO lay im o n Sh os = .ok (r, os')) :
    ∃ (firstRow : ℕ) (values : Array E), firstRow + values.size ≤ Sh.matrixRows ∧
      r.g = stretchBlocks Sh.kRow firstRow values (2 * Sh.kRow + 2) firstRow := by
  obtain ⟨_, _, _, _, first, last, _, _, _, _, _, Gamma, _, g, hg, _, _, _, _, _, rfl, _⟩ :=
    (pendingRowO_iff lay im o n Sh os os' r).1 h
  obtain ⟨⟨h1, -, -, -⟩, rfl⟩ := (weightsOnRows_iff Sh first _ g).1 hg
  exact ⟨first, _, h1, rfl⟩

/-- **Where the weights of each row of a list are the vectors of one stretch that ends at or below
the matrix's rows (the head's (plain)), each weight of the row that the batching hands on
(`Batt.rowOf`) is `t.scale x` for an element x and a vector t of some
`stretchBlocks Sh.kRow firstRow values fuel start` with firstRow + values.size ≤ Sh.matrixRows (the
head's (scaled)).** The conclusion does not say that t is one of the list's own vectors. -/
theorem battRow_blocks (Sh : LinShape) (rows : List TensorRow) (o : Psc.Out)
    (h : ∀ r ∈ rows, ∃ (firstRow : ℕ) (values : Array E),
      firstRow + values.size ≤ Sh.matrixRows ∧
        r.g = stretchBlocks Sh.kRow firstRow values (2 * Sh.kRow + 2) firstRow) :
    ∀ w ∈ (Batt.rowOf rows o).g, ∃ (firstRow : ℕ) (values : Array E) (fuel start : ℕ) (x : E),
      firstRow + values.size ≤ Sh.matrixRows ∧
        ∃ t ∈ stretchBlocks Sh.kRow firstRow values fuel start, w = t.scale x := by
  intro w hw
  have hw' : w ∈ (zipT rows o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2 := hw
  rw [zipT_eq] at hw'
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hw'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
  obtain ⟨f, v, hle, hg⟩ := h p.1 (List.of_mem_zip hp).1
  rw [hg] at hu
  exact ⟨f, v, _, _, p.2, hle, u, hu, rfl⟩

/-- **Where K13's batching (`batt`) answers and each row of its pile has (plain), each weight of the
row that it returns is of the form (scaled):** a vector of some `stretchBlocks` at a stretch that
ends at or below the matrix's rows, times an element. The conclusion does not tie that vector to the
pile. -/
theorem batt_blocks (Sh : LinShape) {owed : Johnson.Desc.First.ForkGround.RowsOwed} {k n : ℕ}
    {pile : List TensorRow} {ledger : ℕ} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}
    (h : batt owed k n pile ledger d rs = .ok out)
    (hp : ∀ r ∈ pile, ∃ (firstRow : ℕ) (values : Array E),
      firstRow + values.size ≤ Sh.matrixRows ∧
        r.g = stretchBlocks Sh.kRow firstRow values (2 * Sh.kRow + 2) firstRow) :
    ∀ w ∈ out.1.g, ∃ (firstRow : ℕ) (values : Array E) (fuel start : ℕ) (x : E),
      firstRow + values.size ≤ Sh.matrixRows ∧
        ∃ t ∈ stretchBlocks Sh.kRow firstRow values fuel start, w = t.scale x := by
  obtain ⟨_, _, _, _, _, o, _, _, _, _, _, _, _, _, _, rfl⟩ := Law.batt_ok h
  exact battRow_blocks Sh pile o hp

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.pendingRowO_blocks
#print axioms VerifiableInference.Desc.K13.Honest.battRow_blocks
#print axioms VerifiableInference.Desc.K13.Honest.batt_blocks
