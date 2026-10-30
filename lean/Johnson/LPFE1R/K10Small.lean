-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K10Small.lean: TWO SMALL PREMISES OF THE CLOSING KIND K10's LAW AT THE
CLOSED CONSTANT's LETTERS. Closed facts by Lean's kernel, and theorems. A law file; no running text
imports it.
  `rowsQW_small`      BY THE KERNEL: each of the 25 written numbers of rows is at most 2 ^ 57.
  `hn57_at`           THE FIELD hn57 OF WHAT IS LEFT OF K10's LAW (K10Heavy,
                    Johnson/Desc/First/Close/Law/K10Heavy.lean: n ≤ 2 ^ 57, at n := Q.rows): in
                    scope, laid: Q.rows ≤ 2 ^ 57. From rows_q_at (RowsQAt.lean beside this file).
  `segOpenB d`, `seg_open_full`, `seg_shut_behind`   BY THE KERNEL: at K10's border of link l a
                    class of rows of segment l is open, at all 25 links; THE CONTROL: one border on,
                    behind K10, at no link.
  `hm_at`             l ∈ rowSegs (P5J.oAt (ixK10 l)), l < 25: the closed premise hm of the first
                    tie's call at the row asks.

Limits. hn57_at: RowsQAt.lean's. The full size alone. So hn57_at spends "the value is laid" also for
the entry test cutRow (Johnson/Desc/Laid/ProofAsks.lean); hm_at spends neither that test nor
madeRow. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.RowsQAt
import Johnson.P5J.K10Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S rowSegs)
open VerifiableInference.Desc.First.Close (Par kind)
open LPFK10 (ixK10)
open ProofFile (Cl)

theorem rowsQW_small : (rowsQW.all fun n => decide (n ≤ 2 ^ 57)) = true := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- **The field hn57.** -/
theorem hn57_at (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    {b : Block S Cl} (hb : cF.blocksInOrder[ixK10 l]? = some b) {Q : Par}
    (hr : b.rounds = (kind (Cl := Unit) Q).rounds) : Q.rows ≤ 2 ^ 57 := by
  rw [rows_q_at hW L hl hb hr]
  have hlen : l < rowsQW.length := by
    have : rowsQW.length = 25 := by decide
    omega
  rw [List.getD_eq_getElem _ _ hlen]
  exact of_decide_eq_true (List.all_eq_true.1 rowsQW_small _ (List.getElem_mem hlen))

/-- A class of rows of segment l is open d borders behind K10's border of link l. -/
def segOpenB (d l : ℕ) : Bool := (rowSegs (P5J.oAt (ixK10 l + d))).contains l

set_option maxRecDepth 1000000 in
theorem seg_open_full : (List.range 25).all (segOpenB 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: behind K10, at no link. -/
theorem seg_shut_behind : (List.range 25).any (segOpenB 1) = false := by decide +kernel

/-- **The premise hm.** -/
theorem hm_at {l : ℕ} (hl : l < 25) : l ∈ rowSegs (P5J.oAt (ixK10 l)) :=
  List.contains_iff_mem.1 (List.all_eq_true.1 seg_open_full l (List.mem_range.2 hl))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsQW_small
#print axioms VerifiableInference.Desc.LinkJoin.hn57_at
#print axioms VerifiableInference.Desc.LinkJoin.seg_open_full
#print axioms VerifiableInference.Desc.LinkJoin.seg_shut_behind
#print axioms VerifiableInference.Desc.LinkJoin.hm_at
