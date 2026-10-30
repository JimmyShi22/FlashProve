-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/WeightsKept.lean: KIND K13's BLOCKS KEEP THE TEST ON THE WEIGHTS
(`First.weightsB`, Johnson/Desc/First/Pend/WeightsB.lean: every weight vector of every row on the
table passes `Tensor.ok`). Statements and proofs; no definition. THIN: cut out of
Johnson/Desc/Last/ShapeWeights.lean, so that kind K13's files' top can call these
without the last chain's tables: not a sign of a statement or a proof has turned; the names stay in
the namespace `VerifiableInference.Desc.Last`.

Main names (namespace `VerifiableInference.Desc.Last`).
  `rowOf_weights`: the row that the batching hands on (`Batt.rowOf`) has the pile's vectors, each
    times a scalar: it passes if the pile does (by `scale_ok`). `batt_weights`: so where
    `K13.batt` answers (by `K13.Law.batt_ok`).
  **`weights_atM3`**: K13's joined block (the front, the batching, the quiet part): a yes; the test
    in front: the test behind (by `atM3_ok`). `weights_oneRowB`, `weights_rowsB`: the block for a
    pile of one row, and the block behind W's commitment: the test behind is the test in front (by
    `oneRowB_ok`, `rowsB_rows`).

Every "there is": none.
Limits. The laws speak of K13's blocks at the lens `atS`: that the seat's blocks are these under
their wrappers is not said here. W's commitment itself is another kind's block. The test is true for
nothing where no row lies. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Pend.RowOk
import Johnson.Desc.First.Pend.WeightsB
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K13.Law.OneRow
import OnBytes.Chain.Lists

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.First.Pend (scale_ok)
open VerifiableInference.Desc.First (weightsB weightsB_same)

/-- **The batching's row keeps it**: the row that is handed on has the pile's vectors, each times a
scalar. -/
theorem rowOf_weights (rows : List TensorRow) (o : Psc.Out)
    (h : ∀ r ∈ rows, ∀ t ∈ r.g, t.ok = true) : ∀ t ∈ (Batt.rowOf rows o).g, t.ok = true := by
  intro t ht
  have ht' : t ∈ (zipT rows o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2 := ht
  rw [zipT_eq] at ht'
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 ht'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hq
  rw [scale_ok]
  exact h p.1 (List.of_mem_zip hp).1 u hu

/-- **Where K13's batching answers**, the row that it returns passes, if the pile does. -/
theorem batt_weights {owed : Johnson.Desc.First.ForkGround.RowsOwed} {k n : ℕ}
    {pile : List TensorRow} {ledger : ℕ} {d : K13.St} {rs : List Fmt.RoundView} {out : TensorRow × K13.St}
    (h : K13.batt owed k n pile ledger d rs = .ok out)
    (hp : ∀ r ∈ pile, ∀ t ∈ r.g, t.ok = true) : ∀ t ∈ out.1.g, t.ok = true := by
  obtain ⟨_, _, _, _, _, o, _, _, _, _, _, _, _, _, _, rfl⟩ := K13.Law.batt_ok h
  exact rowOf_weights pile o hp

variable {Cl : Type}

/-- **K13's joined block (the front, the batching, the quiet part) keeps it.** -/
theorem weights_atM3 {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K13.atM3 (Cl := Cl) P).decide s rs gs = .ok s')
    (hw : weightsB s = true) : weightsB s' = true := by
  obtain ⟨out, hb, e, e'⟩ := K13.Law.atM3_ok h
  unfold weightsB at hw ⊢
  rw [e] at hw
  rw [e']
  simp only [List.all_eq_true] at hw
  simp only [List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true]
  exact batt_weights hb hw

/-- **The block for a pile of one row keeps it.** -/
theorem weights_oneRowB {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.oneRowB (Cl := Cl) K13.atS P).decide s rs gs = .ok s') :
    weightsB s' = weightsB s :=
  weightsB_same (K13.Law.oneRowB_ok h).1

/-- **The block behind W's commitment (the own group, the joinings, the row (Eval)) keeps it.** -/
theorem weights_rowsB {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Cl) K13.atS P).decide s rs gs = .ok s') :
    weightsB s' = weightsB s :=
  weightsB_same (K13.Law.rowsB_rows h)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.rowOf_weights
#print axioms VerifiableInference.Desc.Last.batt_weights
#print axioms VerifiableInference.Desc.Last.weights_atM3
#print axioms VerifiableInference.Desc.Last.weights_oneRowB
#print axioms VerifiableInference.Desc.Last.weights_rowsB
