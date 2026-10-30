-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Tables.lean: the places and the weight vectors of an attention segment's tables, as
a plain function on the four records of OnBytes/Model's verifier.

The routines are the lines of OnBytes/Model/AttentionTables.lean that their docstrings name, in a plain
state monad (the tables placed so far; a refusal) in the place of that verifier's monad over a
context. Its pure helpers are called by name.
Three reads give a default in silence, as in the lines that they follow (two in `tok`; the lookup's
weight vectors behind the test on its planes).
It refuses at seven places: five tests on public numbers, two on values (the lookup's point and the
units' inner points share coordinates).
Not asked here: that a sent word is below the prime (the general fold's).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Model.AttentionTables

set_option autoImplicit false

namespace VerifiableInference.Desc.First.Att.Tab
open OnBytes OnBytes.Attention

/-- The tables placed so far; a refusal. -/
abbrev T : Type → Type := StateT Placed Option

/-- A test; the name is dropped. -/
def mustAs (_name : String) (b : Bool) : Option Unit := if b then some () else none

/-- After OnBytes/Model/AttentionTables.lean:62-65. -/
def T.getAs {α : Type} (_name : String) (x : Option α) : T α :=
  match x with
  | some a => pure a
  | none => failure

/-- After OnBytes/Model/AttentionTables.lean:70-71. -/
def T.weights (_len : Nat) (f : Unit → Array E) : T (Array E) :=
  pure (f ())

/-- After OnBytes/Model/AttentionTables.lean:74-74. -/
def T.placed : T Placed := fun t => pure (t, t)

/-- After OnBytes/Model/AttentionTables.lean:87-92. -/
def add (mats : Array Model.TMat) (mat len : Nat) (phi : Array E) (elems : Nat) : T Nat :=
  fun t => do
    mustAs "internal-a-table-length" (fits mats mat len elems)
    let table : Model.HFun := { mat := mat, len := len, phi := phi, tree := 2, start := t.next }
    pure (t.next, { next := t.next + elems, tabLen := (t.next, elems) :: t.tabLen,
                    funs := t.funs.push table })

/-- After OnBytes/Model/AttentionTables.lean:97-98. -/
def T.total (start : Nat) : T Unit := fun t =>
  pure ((), { t with tabLen := (start, t.next - start) :: t.tabLen })

/-- After OnBytes/Model/AttentionTables.lean:104-110. -/
def addAs (S : Shape) (mats : Array Model.TMat) (phi : Unit → Array E) : T Nat := do
  let phi ← T.weights (2 ^ S.cf.lmS) phi
  let start := (← T.placed).next
  (List.range S.cf.NAs).forM fun q =>
    discard (add mats q (2 ^ S.cf.lmS) phi (S.kAs / S.cf.NAs))
  T.total start
  pure start

/-- After OnBytes/Model/AttentionTables.lean:141-145. -/
def lng (S : Shape) (zc : Array E) (ptk : Unit → Array E) : T (Array E) := do
  let tokens ← T.weights S.T ptk
  mustAs "plan-tensor-layout" (tokens.size == S.T && 2 ^ S.cf.la == 2 ^ S.ls * S.T)
  let c ← T.getAs "plan-tensor-layout" (Model.cutLast zc S.ls).toOption
  T.weights (2 ^ S.cf.la) fun _ => Model.blockRows (Model.eqTab c.2) tokens

/-- After OnBytes/Model/AttentionTables.lean:205-206. -/
def addRow (S : Shape) (mats : Array Model.TMat) (psi : Unit → Array E) : T Nat := do
  add mats S.cf.NAs S.T (← T.weights S.T psi) S.fillH

/-- After OnBytes/Model/AttentionTables.lean:210-213. -/
def addLong (S : Shape) (mats : Array Model.TMat) (mat : Nat) (zc : Array E)
    (ptk : Unit → Array E) (elems : Nat) : T Nat := do
  let phi ← lng S zc ptk
  add mats mat (2 ^ S.cf.la) phi elems

/-- After OnBytes/Model/AttentionTables.lean:218-272. -/
def placeAll (S : Shape) (mats : Array Model.TMat) (nW : Nat) (g : Model.Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    T Tables := do
  let cf := S.cf
  let gSo := S.fillO * S.T / 2 ^ cf.la
  let gSq := S.fillQ * S.T / 2 ^ cf.la
  let mb := 2 ^ cf.lmb
  let iAO := cf.NAs + 1
  let iBA := cf.NAs + 2
  let iQA := cf.NAs + 3
  let ptM := pointM S d
  let ptD := pointD S d
  let riE := d.scE.r.extract cf.lgk (cf.lgk + cf.lt)
  mustAs "internal-a-merged-point" (mergedPlanes cf.lmS g.zx planes)
  let tA ← addAs S mats fun _ => lastN g.zx cf.lmS
  let tVM ← addAs S mats fun _ => lastN ptM cf.lmS
  let tVD ← addAs S mats fun _ => lastN ptD cf.lmS
  let tM ← scores.mapM fun k => addRow S mats fun _ => tok S k.wI k.zi
  let hW ← addRow S mats fun _ => Model.eqTab d.ziW
  let hX ← addRow S mats fun _ => Model.eqTab d.ziX
  let hE ← addRow S mats fun _ => Model.eqTab riE
  let hT ← addRow S mats fun _ => Model.eqTab x.ti
  let hPi ← addRow S mats fun _ => Model.eqTab (x.pi S)
  let hR2 ← addRow S mats fun _ => Model.eqTab (x.ri2 S)
  mustAs "internal-a-merged-point" (mergedTokens S g.zx d)
  let tO ← addLong S mats iAO d.zcW (fun _ => Model.eqTab d.ziW) gSo
  let tQK ← scores.mapM fun k => do
    let rcK := lastCoords k.sc.r cf.ldh
    let tQ ← addLong S mats iQA rcK (fun _ => tok S (scoreTiles S k).1 k.zi) gSq
    let tK ← addLong S mats iQA rcK (fun _ => tok S (scoreTiles S k).2 k.zj) gSq
    pure (tQ, tK)
  let qO ← addLong S mats iQA d.zcW (fun _ => Model.eqTab riE) gSq
  let qVM ← addLong S mats iQA d.zcW (fun _ => tok S d.wJv (lastCoords d.vpm.r cf.lB)) gSq
  let qVD ← addLong S mats iQA d.zcW
    (fun _ => tok S (Model.eqTab (d.vpd.r.extract cf.lgk (cf.lgk + S.lnT)))
      (lastCoords d.vpd.r cf.lB)) gSq
  let qF ← addLong S mats iQA (x.rc S) (fun _ => Model.eqTab (x.ri S)) gSq
  let qKx ← addLong S mats iQA (x.rc S) (fun _ => Model.eqTab (x.pj S)) gSq
  -- phiB returns nothing exactly when planeCols refuses. That is tested here, on public numbers, so
  -- getD never takes its default.
  mustAs "forest-planes" (Model.Forest.planeCols g.shape cf.lmb).toBool
  let phiB0 ← T.weights mb fun _ => (Model.Forest.phiB g cf.lmb 0).getD #[]
  let tBit0 ← add mats iBA mb phiB0 S.kbA
  let phiB1 ← T.weights mb fun _ => (Model.Forest.phiB g cf.lmb 1).getD #[]
  let tBit1 ← add mats iBA mb phiB1 S.kbA
  let tPin ← add mats iBA mb (← T.weights mb fun _ => Model.Forest.phiP cf.lmb) S.kbA
  let t ← T.placed
  mustAs "internal-af-W-length" (t.next == nW)
  let score : Array ScoreTables := (tM.zip tQK).map fun y => ⟨y.1, y.2.1, y.2.2⟩
  pure {
    ptM := ptM, ptD := ptD, tA := tA, tVM := tVM, tVD := tVD, score := score,
    hW := hW, hX := hX, hE := hE, hT := hT, hPi := hPi, hR2 := hR2, tO := tO,
    qO := qO, qVM := qVM, qVD := qVD, qF := qF, qKx := qKx,
    tBit0 := tBit0, tBit1 := tBit1, tPin := tPin,
    tabLen := t.tabLen, funs := t.funs }

/-- After OnBytes/Model/AttentionTables.lean:277-280. -/
def tables (S : Shape) (mats : Array Model.TMat) (nW : Nat) (g : Model.Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    Option Tables := do
  pure (← placeAll S mats nW g planes scores d x {}).1

end VerifiableInference.Desc.First.Att.Tab
