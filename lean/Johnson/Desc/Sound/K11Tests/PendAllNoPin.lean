-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean: THE CLOSED TEST pendAllB SAYS YES AT ALL PUBLIC FILES
IN THE GOALS' SCOPE, WITH NO ENTRY PIN: pendAll_in_scope
(Johnson/Desc/Sound/K11Tests/PendAllInScope.lean) without its premise hy. Statements and proofs. One
closed fact is by Lean's kernel.

WHY hy CAN GO. By reading: of the first entry pin that file's proof spends one number:
the rows of the shape of the test on the committed table (kRow is ceilLog2 of them,
OnBytes/Iop/Lin.lean). THE MAKER OF THE BUILT SEGMENTS TESTS THAT NUMBER ITSELF: tableHeld, a step
of buildLinksH (OnBytes/Model/StagesLinks.lean), refuses unless the shape's rows and column bits
are the layout's.

  table_of_build   where buildLinksH returns, tableHeld has accepted
  table_of_pub     SO, WHEREVER THE ROAD RETURNS THE PUBLIC PART Z: Z.first.lin's rows and column
                   bits are those of Z.p.X.layers.wsLay: NO SCOPE, NO PIN, NO NUMBER
  light_reads_rows · lightAll_reads_rows   the light test reads of the shape its rows alone
  rows_full        the written layout's rows are the written shape's, 3076096; its column bits 18:
                   by the kernel
  rows_full_not    a negative twin: they are not these less one
  lay_in_scope     in scope the layout has these numbers, at every o : ProofFile.SecondHashFunctionArgument
  pendAll_in_scope_bare   MAIN
  lin_in_scope     in scope the shape has 3076096 rows and 18 column bits

table_of_build is the walk of Fo.built_cut (OnBytes/Tie/Pv/Lookup/Ends/FoBuiltCut.lean: of the maker
of the program `verify-on-bytes`), stopped at the seventh step; buildLinksH_cut
(Johnson/Road/K4/Rec/BuiltTests.lean) is the same walk and keeps three other tests.

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on a
verifier's state. Nothing on soundness.

-/
import Johnson.Desc.Sound.K11Tests.PendAllInScope
import Johnson.Desc.ProofFile.Law.HeadNs
import OnBytes.Tie.Pv.Lookup.Ends.FoBuiltCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes OnBytes.Model OnBytes.Model.Stages
open OnBytes.Params (recordLines)
open Lk6.AtPlan Johnson.G
open VerifiableInference.PlanWritten
open VerifiableInference.Desc.First (FillP1.d1At)
open VerifiableInference.Desc.First.MergeLaw (pendAllB hlay_at)
open OnBytes.Params (exc_bind)
open Fo (tableHeld_cut)

/-! ## 1 The maker's own test -/

/-- Where the maker of the built segments returns, its test on the table's shape has accepted. -/
theorem table_of_build {links : Array LinkH} {NGr : ℕ} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links NGr p4 wsLay p = .ok B) :
    Stages.tableHeld wsLay p = .ok () := by
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h7, _⟩ := exc_bind h
  exact h7

/-- **Wherever the road returns the public part: the shape's rows and column bits are the
layout's.** -/
theorem table_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.first.lin.matrixRows = Z.p.X.layers.wsLay.m0 ∧ Z.first.lin.kCol = Z.p.X.layers.wsLay.lk := by
  have hb : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    (ProofFile.Law.planned_chains (ProofFile.Law.pub_planned h)).2.2
  unfold ProofFile.Plain.builtOf at hb
  obtain ⟨ls, _, hb⟩ := OnBytes.TieK.ok_of_bind hb
  exact tableHeld_cut (table_of_build hb)

/-! ## 2 The light test reads the shape's rows alone -/

theorem light_reads_rows (lay : WsLay) (uis : List ℕ) (n : ℕ) {S S' : Params.LinShape}
    (e : S.matrixRows = S'.matrixRows) :
    OnBytes.Road.K4.Pend.pendB lay uis n S = OnBytes.Road.K4.Pend.pendB lay uis n S' := by
  have k : S.kRow = S'.kRow := by
    unfold Params.LinShape.kRow
    rw [e]
  unfold OnBytes.Road.K4.Pend.pendB
  rw [e, k]

theorem lightAll_reads_rows (lay : WsLay) {S S' : Params.LinShape}
    (e : S.matrixRows = S'.matrixRows) : lightAllB lay S = lightAllB lay S' := by
  unfold lightAllB
  congr 1
  funext ui
  exact light_reads_rows lay [ui] 1 e

/-! ## 3 In scope, with no pin -/

/-- The written layout's rows are the written shape's. By the kernel. -/
theorem rows_full :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok l => decide (l.m0 = proofSizedFull.batch.shape.matrixRows ∧ l.m0 = 3076096 ∧ l.lk = 18)
      | .error _ => false) = true := by decide +kernel

/-- A negative twin. By the kernel. -/
theorem rows_full_not :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok l => decide (l.m0 = proofSizedFull.batch.shape.matrixRows - 1)
      | .error _ => true) = false := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- The layout's numbers, at every o : ProofFile.SecondHashFunctionArgument. -/
theorem lay_in_scope (hS : VerifierAndGoals.InScope P = true)
    (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z) :
    Z.p.X.layers.wsLay.m0 = proofSizedFull.batch.shape.matrixRows ∧
      Z.p.X.layers.wsLay.m0 = 3076096 ∧ Z.p.X.layers.wsLay.lk = 18 := by
  have hf := rows_full
  rw [wsLay_in_scope_O hS (ProofFile.Law.pub_public h)] at hf
  exact of_decide_eq_true hf

/-- **In scope the shape has 3076096 rows and 18 column bits: no pin.** -/
theorem lin_in_scope (hS : VerifierAndGoals.InScope P = true)
    (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z) :
    Z.first.lin.matrixRows = 3076096 ∧ Z.first.lin.kCol = 18 :=
  ⟨(table_of_pub h).1.trans (lay_in_scope hS h).2.1,
    (table_of_pub h).2.trans (lay_in_scope hS h).2.2⟩

/-- **THE CLOSED TEST SAYS YES IN SCOPE: NO ENTRY PIN.** -/
theorem pendAll_in_scope_bare {mk : ProofFile.LinksBy} (hS : VerifierAndGoals.InScope P = true)
    (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G₀) :
    pendAllB (K11.parOf Z G₀).lay (FillP1.d1At Z).lin = true := by
  have hf := lightAll_full
  rw [wsLay_in_scope_O hS (ProofFile.Law.pub_public h)] at hf
  rw [← hlay_at hG, pendAll_eq_light]
  show lightAllB Z.p.X.layers.wsLay Z.first.lin = true
  rw [lightAll_reads_rows _ ((table_of_pub h).1.trans (lay_in_scope hS h).1)]
  exact hf

end

end LT28.K11Tests

#print axioms LT28.K11Tests.table_of_build
#print axioms LT28.K11Tests.table_of_pub
#print axioms LT28.K11Tests.light_reads_rows
#print axioms LT28.K11Tests.lightAll_reads_rows
#print axioms LT28.K11Tests.rows_full
#print axioms LT28.K11Tests.rows_full_not
#print axioms LT28.K11Tests.lay_in_scope
#print axioms LT28.K11Tests.lin_in_scope
#print axioms LT28.K11Tests.pendAll_in_scope_bare
