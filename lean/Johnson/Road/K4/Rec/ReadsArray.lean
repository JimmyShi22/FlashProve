-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/ReadsArray.lean: THE PUBLIC TEST ON THE ARRAY OF READS AT A STATE OF THE
VERIFIER IN A LAYERS' LINK (`readsArrayB`, Johnson/Road/K4/ReadsArrayAt.lean) EXCHANGED FOR A TEST
WITH CODE ON THE PLAN's LETTERS, UNDER `RecIs` (Johnson/Road/K4/Rec/Whole.lean). One definition, one
lemma on lists, one statement with its proof. GLUE.

  `readsArrayP hp shape layout arrs m T`: the test on the plan: `readsArrayB`'s four clauses with
    the state's own copies exchanged for the plan's: `readsThereP`, `oneRowP`, the clause on hp
    alone as it stands, and "virtual row 0 of the array begins at column 0 and holds so many
    weights" off the plan's list of looks T.
  `row_look`: virtual row j of array i, off the looks.
  **`readsArray_plan`**: under `RecIs A R n m`, at a state s in the layers' link b whose part is A:
    `readsArrayB hp s` IS `readsArrayP` at R's letters.

OBJECT: none of its own. USER: none yet; meant: whoever pays `readsArrayB`. LETTERS: hp, s, b, A, R,
n, m.

Limits. `RecIs` IS A PREMISE HERE. `readsArrayP` HAS RUN NOWHERE. K04_law, the law of K4's block
itself, IS NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Road.K4.ReadsArrayAt
import Johnson.Road.K4.Rec.InT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Road.K4.InT (oneRowB readsThereB)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.FillSent (TreeLook treeLook)
open VerifiableInference.Desc.First.RecordPlan (oneRowP readsThereP look_at)
open VerifiableInference.Desc.K9 (segAt?)

/-- **The test on the plan.** -/
def readsArrayP (hp : HPlan2) (shape : Params.ReqShape) (layout : Params.ReqLayout)
    (arrs : Array (ℕ × String)) (m : ℕ) (T : List TreeLook) : Bool :=
  match hp.tl.ix.U.getD 2 none with
  | some iU3 =>
    readsThereP shape layout arrs m iU3 (hp.nU.getD 2 0) && (oneRowP T iU3 &&
      (decide (hp.nU.getD 2 0 ≤ ((hp.Fp.trees[iU3]?).map (·.K)).getD 0) &&
        (match (T[iU3]?).bind (·.2.2[0]?) with
          | some r => r.1 == 0 && decide (hp.nU.getD 2 0 ≤ r.2)
          | none => false)))
  | none => false

/-- Virtual row j of array i, off the looks. -/
theorem row_look {trees : Array HTree} {T : List TreeLook} (h : trees.toList.map treeLook = T)
    (i j : ℕ) : (T[i]?).bind (·.2.2[j]?) =
      ((trees[i]?).bind (·.rows[j]?)).map fun r => (r.L0, r.L.size) := by
  rw [look_at h i]
  cases trees[i]? with
  | none => rfl
  | some X =>
    show (X.rows.toList.map fun r => (r.L0, r.L.size))[j]? = (X.rows[j]?).map _
    rw [List.getElem?_map, Array.getElem?_toList]

/-- **Under `RecIs`: the test at the state is the test on the plan.** -/
theorem readsArray_plan {A : Part9} {R : RecPlan} {n m : ℕ} (h : RecIs A R n m) (hp : HPlan2)
    {s : S} {b : LayOwn} (hs : s.here = .lay b) (hA : segAt? s = some A) :
    readsArrayB hp s = readsArrayP hp R.shape R.layout (R.arrs m) m (R.d.trees m) := by
  obtain ⟨A₀, h₀, eF, -⟩ := OnBytes.Desc.First.K4.InT.segAt_lay hs
  obtain rfl : A = A₀ := Option.some.inj (hA.symm.trans h₀)
  have hT : b.F.trees.toList.map treeLook = R.d.trees m := eF ▸ h.trees
  unfold readsArrayB readsArrayP
  cases hp.tl.ix.U.getD 2 none with
  | none => rfl
  | some iU3 =>
    rw [hs, hA]
    show (readsThereB A iU3 (hp.nU.getD 2 0) && (oneRowB b.F iU3 &&
      (decide (hp.nU.getD 2 0 ≤ ((hp.Fp.trees[iU3]?).map (·.K)).getD 0) &&
        (match (b.F.trees[iU3]?).bind (·.rows[0]?) with
          | some r => r.L0 == 0 && decide (hp.nU.getD 2 0 ≤ r.L.size)
          | none => false)))) = _
    rw [reads_plan h iU3 (hp.nU.getD 2 0), ← eF, oneRow_plan h iU3, eF]
    show (_ && (_ && (_ && _))) = (_ && (_ && (_ &&
      (match ((R.d.trees m)[iU3]?).bind (·.2.2[0]?) with
          | some r => r.1 == 0 && decide (hp.nU.getD 2 0 ≤ r.2)
          | none => false))))
    rw [row_look hT iU3 0]
    cases (b.F.trees[iU3]?).bind (·.rows[0]?) <;> rfl

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.readsArray_plan
