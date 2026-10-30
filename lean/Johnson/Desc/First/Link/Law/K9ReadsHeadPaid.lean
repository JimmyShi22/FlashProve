--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K9ReadsHeadPaid.lean: AT THE OUTPUT HEAD's SEGMENT THE NUMBER OF READS
THAT THE TEST `rowsFitB` COUNTS (`readsB` at `headPairs`, Johnson/Desc/First/Link/K9RowsAsk.lean:
another house's) IS THE NUMBER OF READS OF THE HEAD's OWN PLAN (`Head.readsH`,
OnBytes/Model/HeadPlan.lean), AT ALL PUBLIC FILES IN THE GOALS' SCOPE. Definitions, and statements
with their proofs. PREMISES: the scope and publicOf's return ALONE: no pin, no head of a table, no
opening. WHAT IT IS FOR. The test asks: claims + (firstB + readsB * stepF) ≤ the declared round's
rows. The plan's rows are claims + equationsF (readsH ..) (the landed `planH2_rows`,
OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean). So of the test's clause at segment 24 this is the third
"the reads are at most the plan's". HOW. Both texts are taken off the numbers that they read, by
rfl: `headPairsN` (over a fellow pen's `headTabsN`,
Johnson/Desc/First/Link/Law/K9PosHeadPaid.lean) with `headPairsN_is`; `readsHN` with `readsHN_is`.
The numbers are closed in scope by landed laws: the matrices and their number (another house's
`plan_in_scope`, Johnson/Desc/Kinds/Law/HeadPlanWritten.lean); NHf, la, T, lmbH, lt
(`hS_in_scope`, Johnson/Goal/Meaning/HeadShapeScope.lean); the layout's three numbers of rows
(`numH_of_layout`, Johnson/Road/HeadPlace.lean); the stream's rows (`border_in_scope`,
Johnson/Goal/Meaning/HeadAtFullIs.lean). **`readsHead_written`**: BY LEAN's KERNEL: the tables can
  be laid, and the two counts are one number (93: by matrix 2, 2, 2, 2, 32, 48, 3, 2). LOOKED AT
  WITH THE EVALUATOR FIRST, UNDER A FORECAST LAID IN THE OPEN. `readsHead_bites`: it can fail:
  with blocks of half the rows the test's count EXCEEDS the plan's; with one matrix fewer counted
  the two part; where no table can be laid nothing is returned. **`reads_head_eq`**: the equation.
  `reads_head`: "at most": the direction that the join spends.
What is not claimed. The test's clause at segment 24: it wants "the declared round's rows are the
plan's" too. Anything at the other 24 segments. That publicOf returns at any files in scope.
Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Link.K9RowsAsk
import Johnson.Desc.First.Link.Law.K9PosHeadPaid
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Goal.Meaning.HeadAtFullIs
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope border_in_scope)

/-- `headPairs`, of the five values that it reads. -/
def headPairsN (N la T lmb : ℕ) (mats : Array TMat) : Option (List (ℕ × ℕ)) :=
  (headTabsN N la T lmb mats).map fun t => t.funs.toList.map fun Fn => (Fn.mat, Fn.len)

theorem headPairsN_is (h : Head.Shape) (hp : Head.HPlanH2) :
    headPairs h hp = headPairsN h.NHf h.la h.T h.lmbH hp.tl.mats := rfl

/-- `Head.readsH`, of the seven numbers that it reads. -/
def readsHN (N la lt m mD mR mxb : ℕ) : ℕ :=
  2 * N * (m / 2 ^ la) + 2 * (mD / 2 ^ lt) + 6 * (mR / 2 ^ lt) + 3 + 2 * (mxb / 2 ^ la)

theorem readsHN_is (h : Head.Shape) (L : Head.HL) (b : Head.Border) :
    Head.readsH h L b = readsHN h.NHf h.la h.lt L.m L.mD L.mR b.mxb := rfl

/-- **The kernel's fact at the written values**: the tables can be laid, and the two counts are one
number. -/
theorem readsHead_written :
    (match headPairsN 4 16 1024 15 matsW with
      | some ps => decide (readsB 8 matsW ps = readsHN 4 16 10 65536 16384 8192 65536)
      | none => false) = true := by decide +kernel

/-- It can fail: blocks of half the rows: more reads than the plan's; one matrix fewer is counted:
fewer; and where no table can be laid. -/
theorem readsHead_bites :
    (match headPairsN 4 15 1024 15 matsW with
      | some ps => decide (readsB 8 matsW ps ≤ readsHN 4 16 10 65536 16384 8192 65536)
      | none => true) = false ∧
    (match headPairsN 4 16 1024 15 matsW with
      | some ps => decide (readsB 7 matsW ps = readsHN 4 16 10 65536 16384 8192 65536)
      | none => true) = false ∧
    headPairsN 4 16 1024 15 #[] = none := by decide +kernel

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **At the output head's segment the reads that the test counts are the plan's reads.** -/
theorem reads_head_eq (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) :
    ∃ ps, headPairs X.hS X.H = some ps ∧
      readsB X.H.tl.NM X.H.tl.mats ps = Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y) := by
  have PW := plan_in_scope hS hR hpub
  have eS := _root_.Meaning.HeadS.hS_in_scope hS hR hpub
  have eN : X.hS.NHf = 4 := by rw [eS]; rfl
  have eA : X.hS.la = 16 := by rw [eS]; rfl
  have eT : X.hS.T = 1024 := by rw [eS]; rfl
  have eB : X.hS.lmbH = 15 := by rw [eS]; rfl
  have eL : X.hS.lt = 10 := by rw [eS]; rfl
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have Bc := (OnBytes.Road.Hd.eleven_of_core hpub C (OnBytes.Road.Hd.npOf X.hS)).1
  have Nm := OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head
  have hb : Verify.borderOf X.layers.y = Kinds.Head.Law.Cond.bFull := border_in_scope hS hR hpub
  have hf := readsHead_written
  rw [headPairsN_is, readsHN_is, eN, eA, eT, eB, eL, PW.mats, PW.nm, Nm.m, Nm.mD, Nm.mR, hb]
  cases e : headPairsN 4 16 1024 15 matsW with
  | none =>
    rw [e] at hf
    cases hf
  | some ps =>
    rw [e] at hf
    exact ⟨ps, rfl, of_decide_eq_true hf⟩

/-- So they are at most the plan's: the direction that the join spends. -/
theorem reads_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) :
    ∃ ps, headPairs X.hS X.H = some ps ∧
      readsB X.H.tl.NM X.H.tl.mats ps ≤ Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y) := by
  obtain ⟨ps, h1, h2⟩ := reads_head_eq hS hR hpub
  exact ⟨ps, h1, Nat.le_of_eq h2⟩

end

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.reads_head_eq
#print axioms VerifiableInference.Desc.K9Asks.reads_head
#print axioms VerifiableInference.Desc.K9Asks.readsHead_written
#print axioms VerifiableInference.Desc.K9Asks.readsHead_bites
#print axioms VerifiableInference.Desc.K9Asks.headPairsN_is
#print axioms VerifiableInference.Desc.K9Asks.readsHN_is
