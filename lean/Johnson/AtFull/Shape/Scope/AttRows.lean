-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttRows.lean: THE MAKERS OF THE RUNS' INPUT READ NOTHING OF THE CALLS' SHIFTS AND TABLES:
leftP, pointsOf, ptsFrom, tablesP; inAt_flat: the input at the flat geometry. The rows: AttRowsB.lean.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.AttRuns
import Johnson.AtFull.Shape.Scope.AttChain
import Johnson.Desc.K5.Honest.Law.RunsJoin
import Johnson.Desc.First.Att.Row.K5DryNoPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo parCOf ParC Heard)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP PadIn)
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll Heard5Sh LedSh ClaimSh affSh)
open H2K5.Honest (partsOf inBlank keysBlank tabsGC tabsG heard5Blank ledBlank ShIn JSh k5FirstG
  k5SecondG k5KeysG k5JoinG bareSh formsSh)
open K5Law (OptRel)

/-! ## 1 The makers of the runs' input -/

theorem leftP_strip (g : Geo) (zk : Array (Array E)) (h : Heard) (F : Fork) :
    P.leftP (stripG g) zk h F = P.leftP g zk h F := by
  unfold P.leftP
  simp only [scores_strip, single_strip]
  rfl

theorem zip_map_inv {U V T : Type} (l : List U) (r : Array V) (φ : U → U) (F : U × V → T)
    (hF : ∀ u s, F (φ u, s) = F (u, s)) :
    ((l.map φ).toArray.zip r).map F = (l.toArray.zip r).map F := by
  apply Array.toList_inj.1
  simp only [Array.toList_map, Array.toList_zip, List.zip_map_left, List.map_map]
  apply List.map_congr_left
  intro x _
  obtain ⟨u, s⟩ := x
  exact hF u s

theorem pointsOf_strip (g : Geo) (zk : Array (Array E)) (h : Heard) (L : P.Left) :
    P.pointsOf (stripG g) zk h L = P.pointsOf g zk h L := by
  unfold P.pointsOf
  dsimp only
  rw [units_strip, scores_strip, single_strip, single_strip, single_strip,
    zip_map_inv _ _ (fun u => (u.1, stripCG u.2.1, u.2.2)) _ (fun u s => rfl)]
  simp only [List.size_toArray, List.length_map]
  rfl

theorem ptsFrom_strip (g : Geo) (zk : Array (Array E)) (h : Heard) (F : Fork) :
    P.ptsFrom (stripG g) zk h F = P.ptsFrom g zk h F := by
  unfold P.ptsFrom
  rw [leftP_strip]
  simp only [pointsOf_strip]

theorem tablesP_strip (g : Geo) (mats : Array (Nat × Nat)) (nW : Nat) (lk : P.LookIn) (p : P.Pts) :
    P.tablesP (stripG g) mats nW lk p = P.tablesP g mats nW lk p := rfl

theorem parCOf_strip (A : Attention.Plan) :
    parCOf (stripPlan A) = { parCOf A with geo := stripG (parCOf A).geo } := by
  have e : (parCOf (stripPlan A)).geo = stripG (parCOf A).geo := geo_strip A.S
  show _ = _
  rw [← e]
  rfl

/-- The runs' input at the flat geometry. -/
theorem inAt_flat (c : ParC) (gl : Forest.Heard) (h : Heard) (U : Fork) :
    K5Law.inAt { c with geo := stripG c.geo } gl h U =
      (K5Law.inAt c gl h U).map fun x => (flatIn x.1, x.2) := by
  unfold K5Law.inAt
  dsimp only
  rw [ptsFrom_strip]
  cases P.ptsFrom c.geo gl.zk h U with
  | none => rfl
  | some p =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [tablesP_strip, show (stripG c.geo).lmb = c.geo.lmb from rfl]
    cases P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb gl) p with
    | none => rfl
    | some t =>
      cases U.trees[c.iU3]? <;> rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.ptsFrom_strip
#print axioms Johnson.AtFull.Shape.Scope.inAt_flat
