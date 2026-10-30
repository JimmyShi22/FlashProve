-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesShape.lean: THE SMALLNESS TEST: THE VERIFIER's TEST ON THE PLANES'
SHAPES (`planesShapeHeld`, OnBytes/Model/Tail.lean: sizes of the bits' array, of its three virtual
rows' weights and of the lookup's two points on the bits) SAYS YES BEHIND THE ADDING, FROM SIZES AT
THE LEDGER BEHIND THE RUNS, TWO PUBLIC NUMBERS AND THE TWO POINTS' SIZES. The adding turns no size
(`Added8.core`: everything but the values of the weights stays; Johnson/Desc/K8/Honest/Added8.lean);
the routine that lays the row weights turns no look and no column weight, and what it lays on the
bits' array has 32 entries a row (the library's `K9L.coef_looks`, `Fo.coef_bz`, `Fo.eqTab_size`).
What a yes of the test means is the library's (`planesShapeHeld_iff`, `planesShapeHeld_eq`). None of
the library's goals.

  `look_at`   where two ledgers' arrays have the same looks, so has each array
  `lsize_of_frame`   the number of a virtual row's column weights is read off the arrays' frame
  `BitsAt tl Y`   at the ledger Y the bits' array has 3 virtual rows, 32 rows and the plan's number
                   of columns, and each of the three rows has a weight a column
  `BitsPub tl g`   two public numbers (two calls; one bit for the call) · each of the lookup's two
                   points on the bits has 5 + kT + cK coordinates
  **`Added8.planesShape`**   what a yes of the batching block opens (Added8) · BitsAt tl Y · BitsPub
                   tl g · no matrix's array of symbols is the bits' array ⊢ tl'.planesShapeHeld
                   (coefBody tl' g G) g = true
Limits. AN IMPLICATION: `Added8`, `BitsAt`, `BitsPub` and the last premise ARE PAID BY NOBODY HERE.
`BitsAt` speaks of the ledger behind the runs, not of the ledger in front of the batching: that the
draw fills each row with a weight a column is not said here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.PlaneEqs
import Johnson.Desc.First.Batch.Law.K8Tests
import OnBytes.Tie.Pv.Lookup.Ends.FoSlEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law

/-- Where two ledgers' arrays have the same looks, so has each array. -/
theorem look_at {A B : Array HTree} (h : A.map LinkJoin.look = B.map LinkJoin.look) (t : Nat) :
    LinkJoin.look (A.getD t {}) = LinkJoin.look (B.getD t {}) := by
  have h1 := congrArg (fun X => (X[t]?).getD (LinkJoin.look {})) h
  simp only [Array.getElem?_map] at h1
  simp only [Array.getD_eq_getD_getElem?]
  cases hA : A[t]? <;> cases hB : B[t]? <;> simp only [hA, hB, Option.map_some, Option.map_none,
    Option.getD_some, Option.getD_none] at h1 ⊢ <;> exact h1

/-- The number of a virtual row's column weights, off the arrays' frame. -/
theorem lsize_of_frame (A : Array HTree) (t r : Nat) :
    ((A.getD t {}).rows.getD r {}).L.size =
      ((((treesFrame A).getD t (HTree.frame {})).2).getD r (HRow.frame {})).2 := by
  simp only [treesFrame, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? with
  | none => simp [HTree.frame, HRow.frame]
  | some X =>
    simp only [Option.map_some, Option.getD_some, HTree.frame, Array.getElem?_map]
    cases X.rows[r]? <;> rfl

/-- The sizes of the bits' array at a ledger. -/
structure BitsAt (tl : HTailF2) (Y : Fork) : Prop where
  rows : (Y.trees.getD tl.ix.BZ {}).rows.size = 3
  R : (Y.trees.getD tl.ix.BZ {}).R = 32
  K : (Y.trees.getD tl.ix.BZ {}).K = tl.bzColumns
  full : ∀ r, r < 3 → ((Y.trees.getD tl.ix.BZ {}).rows.getD r {}).L.size = tl.bzColumns

/-- Public numbers, and the sizes of the lookup's two points on the bits. -/
structure BitsPub (tl : HTailF2) (g : Forest.Heard) : Prop where
  NC : tl.f9.NC = 2
  cK : tl.f9.cK = 1
  zb0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK)
  zb1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK)

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE TEST ON THE PLANES' SHAPES SAYS YES BEHIND THE ADDING.** -/
theorem Added8.planesShape (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (B : BitsAt tl Y) (P : BitsPub tl g)
    (hm : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ) :
    tl'.planesShapeHeld (coefBody tl' g G) g = true := by
  have hfr := A.core.2.2.1
  have eI : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eF9 : tl'.f9 = tl.f9 :=
    eq_same (·.f9) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eBz : tl'.bzColumns = tl.bzColumns :=
    eq_same (·.bzColumns) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hm' : ∀ mu < tl'.NM, tl'.gtTree.getD mu 0 ≠ tl'.ix.BZ :=
    (eq_same (fun t : HTailF2 => ∀ mu < t.NM, t.gtTree.getD mu 0 ≠ t.ix.BZ) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr hm
  have lk : LinkJoin.look ((coefBody tl' g G).trees.getD tl.ix.BZ {}) =
      LinkJoin.look (Y.trees.getD tl.ix.BZ {}) :=
    (look_at (K9L.coef_looks tl' g G) _).trans (look_at (LinkJoin.looks_of_frame _ _ hfr) _)
  have lR : ((coefBody tl' g G).trees.getD tl.ix.BZ {}).R = 32 :=
    (congrArg (·.2.1) lk).trans B.R
  have lK : ((coefBody tl' g G).trees.getD tl.ix.BZ {}).K = tl.bzColumns :=
    (congrArg (·.2.2.1) lk).trans B.K
  have lr : ((coefBody tl' g G).trees.getD tl.ix.BZ {}).rows.size = 3 :=
    (congrArg (·.2.2.2) lk).trans B.rows
  have rG : (G.trees.getD tl'.ix.BZ {}).rows.size = 3 := by
    rw [eI]
    exact (congrArg (·.2.2.2) (look_at (LinkJoin.looks_of_frame _ _ hfr) tl.ix.BZ)).trans B.rows
  obtain ⟨c0, c1, c2⟩ := Fo.coef_bz tl' g G (hasRow_of_rows rG (by omega))
    (hasRow_of_rows rG (by omega)) (hasRow_of_rows rG (by omega)) hm'
  rw [← coefBody_all, eI] at c0 c1 c2
  have lL : ∀ r, r < 3 →
      (((coefBody tl' g G).trees.getD tl.ix.BZ {}).rows.getD r {}).L.size = tl.bzColumns := by
    intro r hr
    have e1 : (((coefBody tl' g G).trees.getD tl.ix.BZ {}).rows.getD r {}).L =
        weightsOf G tl.ix.BZ r := weights_coefBody tl' g G _ _
    rw [e1]
    show ((G.trees.getD tl.ix.BZ {}).rows.getD r {}).L.size = _
    rw [lsize_of_frame, hfr, ← lsize_of_frame]
    exact B.full r hr
  have s0 : (eqTab (g.zb0.extract 0 5)).size = 32 := by
    rw [Fo.eqTab_size, Array.size_extract, P.zb0]
    have e5 : min 5 (5 + (tl.f9.kT + tl.f9.cK)) - 0 = 5 := by omega
    rw [e5]
    rfl
  have s1 : (eqTab (g.zb1.extract 0 5)).size = 32 := by
    rw [Fo.eqTab_size, Array.size_extract, P.zb1]
    have e5 : min 5 (5 + (tl.f9.kT + tl.f9.cK)) - 0 = 5 := by omega
    rw [e5]
    rfl
  have h := (planesShapeHeld_iff tl' (coefBody tl' g G) g).2 (by
    dsimp only
    rw [eI, eF9, eBz, lK]
    refine ⟨lr, lR, rfl, P.NC, P.cK, rfl, fun r hr => ⟨?_, lL r hr⟩, P.zb0, P.zb1⟩
    have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr3 with rfl | rfl | rfl
    · exact (congrArg Array.size c0).trans s0
    · exact (congrArg Array.size c1).trans s1
    · exact (congrArg Array.size c2).trans Array.size_replicate)
  rw [planesShapeHeld_eq] at h
  exact h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.look_at
#print axioms VerifiableInference.Desc.First.K8.Honest.lsize_of_frame
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.planesShape
