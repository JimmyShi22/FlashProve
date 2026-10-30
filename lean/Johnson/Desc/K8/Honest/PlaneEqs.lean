-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlaneEqs.lean: THE SMALLNESS TEST: THE VERIFIER's TEST ON THE PLANES' WEIGHTS
(`planesWeightsHeld`, OnBytes/Model/Tail.lean: the row weights and the column weights of the three
virtual rows of the bits' array are those of a second computation) SAYS YES BEHIND THE ADDING, WHERE
NO PLAIN CLAIM BUT ITS OWN BEARS ON EACH ROW. The column weights' values are
Johnson/Desc/K8/Honest/PlanesWeight.lean's; the row weights are what the routine that lays them
writes (the library's `Fo.coef_bz`, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean); the second computation
walks a running product, which is the plain product (`eqAt_plain`,
Johnson/Desc/K8/Honest/EqRunPlain.lean), whose value is the table's (`eqPlainF_val`, `eqTab_pt`,
Johnson/Desc/K8/Honest/EqFactor.lean); all are words below the prime, so equal values are equal
words. What a yes of the test means, and of the test on the planes' shapes, is the library's
(`planesWeightsHeld_iff`, `planesShapeHeld_iff`, Johnson/Desc/First/TailClaims/AgainMeans.lean;
`planesWeightsHeld_eq`, `planesShapeHeld_eq`, Johnson/Desc/First/TailClaims/AgainAgrees.lean). None
of the library's goals.

  `eqPlainF_ok`   the plain product is a word below the prime
  **`eqTab_plain`**   i < 2 ^ z.size ⊢ (eqTab z).getD i zeroE = eqPlainF z i, AS WORDS: what the
                   library tests at one point of three coordinates by a guard
                   (OnBytes/Model/TestTail.lean)
  `hasRow_of_rows`   an array that has n virtual rows in a ledger is there, with each row below n
  **`Added8.planeEqs`**   what a yes of the batching block opens (Added8) · n₀ = fr.length ·
                   tl.heard = some g · the verifier's test on the planes' shapes says yes behind the
                   adding (`planesShapeHeld`) · the three rows begin at column 0 in the ledger in
                   front · OffAt at the three rows · the form of the lookup's last sumcheck names no
                   entry of the bits' array · PlaneOff at each row and column ⊢ tl'.joinObj9 = some
                   fr.length ∧ tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true
Limits. AN IMPLICATION, UNDER EIGHT PREMISES, NONE PAID HERE: `Added8` IS MADE BY ANOTHER FILE UNDER
ITS OWN PREMISES; `PlaneOff` HANGS ON OTHER KINDS' CLAIMS, AND ON THE KIND's OWN FOUR; "n₀ =
fr.length" IS A REAL PREMISE: the second computation goes by the number that the run was handed, the
adding by the claim's place in the list; the test on the shapes is another clause of the same test
of the verifier's.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.PlanesWeight
import Johnson.Desc.K8.Honest.PlanesFront
import Johnson.Desc.K8.Honest.EqFactor
import Johnson.Desc.K8.Honest.SecondNz
import Johnson.Desc.K8.Honest.AgainVals
import Johnson.Desc.First.TailClaims.AgainAgrees
import Johnson.Desc.First.TailClaims.CoefficientsAll
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The plain product is a word below the prime. -/
theorem eqPlainF_ok (z : Array E) (idx : Nat) : OnBytes.okE (eqPlainF z idx) = true := by
  rw [eqPlainF_pre]
  cases z.size with
  | zero => exact Part.MaskedSum.okE_one
  | succ n => exact Part.MaskedSum.okE_mul _ _

/-- **An entry of the table of equality weights is the plain product, as words.** -/
theorem eqTab_plain (z : Array E) (i : Nat) (hi : i < 2 ^ z.size) :
    (eqTab z).getD i zeroE = eqPlainF z i :=
  ProdV.gl_inj _ _ (eqTab_ok z i) (eqPlainF_ok z i) (by rw [eqTab_pt z i hi, eqPlainF_val])

/-- An array that has n virtual rows in a ledger is there, with each row below n. -/
theorem hasRow_of_rows {F : Fork} {t n e : Nat} (h : (F.trees.getD t {}).rows.size = n)
    (he : e < n) : Fo.HasRow F t e := by
  refine ⟨?_, by omega⟩
  by_contra hc
  have e0 : F.trees.getD t {} = {} := by simp [Array.getD, hc]
  rw [e0] at h
  have h0 : ({} : HTree).rows.size = 0 := by simp
  omega

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE TEST ON THE PLANES' WEIGHTS SAYS YES BEHIND THE ADDING.** -/
theorem Added8.planeEqs (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (hn : n₀ = fr.length) (hg : tl.heard = some g)
    (hSh : tl'.planesShapeHeld (coefBody tl' g G) g = true)
    (hz : ∀ e, e ≤ 2 → ((Y.trees.getD tl.ix.BZ {}).rows.getD e {}).L0 = 0)
    (hO : ∀ e, e ≤ 2 → OffAt tl tl.ix.BZ e)
    (hfree : ∀ y ∈ (g.leaves.rowForm oneE {}).ents.toList, y.tree ≠ tl.ix.BZ)
    (hP : ∀ e, e ≤ 2 → ∀ x, x < tl.bzColumns → PlaneOff fr k8 bk tl e x) :
    tl'.joinObj9 = some fr.length ∧
      tl'.planesWeightsHeld (coefBody tl' g G) g fr.length = true := by
  obtain ⟨cθ, -, -, cok⟩ := A.core
  have bθ : (coefBody tl' g G).theta = Y.theta :=
    (congrArg (·.2.1) (K9L.core_coefBody tl' g G)).trans cθ
  have eI : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  obtain ⟨g', hg', hjo, hbit⟩ := eq_join_bits A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  have eF9 : tl'.f9 = tl.f9 :=
    eq_same (·.f9) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eBz : tl'.bzColumns = tl.bzColumns :=
    eq_same (·.bzColumns) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hSh' := (planesShapeHeld_iff tl' (coefBody tl' g' G) g').1 (by
    rw [planesShapeHeld_eq]
    exact hSh)
  dsimp only at hSh'
  obtain ⟨r3, -, kB, -, -, -, -, z0, z1⟩ := hSh'
  have hS : g'.zb0.size = 5 + (tl.f9.kT + tl.f9.cK) ∧
      g'.zb1.size = 5 + (tl.f9.kT + tl.f9.cK) := by
    rw [← eF9]
    exact ⟨z0, z1⟩
  have hm' : ∀ mu < tl'.NM, tl'.gtTree.getD mu 0 ≠ tl'.ix.BZ :=
    (eq_same (fun t : HTailF2 => ∀ mu < t.NM, t.gtTree.getD mu 0 ≠ t.ix.BZ) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr
      fun mu hmu e => (hO 0 (by omega)).2.2.1 mu hmu ⟨e, rfl⟩
  have rG : (G.trees.getD tl'.ix.BZ {}).rows.size = 3 :=
    ((Fo.frame_all tl' g' G).2 tl'.ix.BZ).2.symm.trans r3
  obtain ⟨c0, c1, c2⟩ := Fo.coef_bz tl' g' G (hasRow_of_rows rG (by omega))
    (hasRow_of_rows rG (by omega)) (hasRow_of_rows rG (by omega)) hm'
  rw [← coefBody_all, eI] at c0 c1 c2
  have eK : ((coefBody tl' g' G).trees.getD tl.ix.BZ {}).K = tl.bzColumns := by
    rw [← eI, kB, eBz]
  have eL : ∀ e, (((coefBody tl' g' G).trees.getD tl.ix.BZ {}).rows.getD e {}).L =
      weightsOf G tl.ix.BZ e := fun e => weights_coefBody tl' g' G _ _
  have s0 : (g'.zb0.extract 0 5).size = 5 := by
    rw [Array.size_extract, hS.1]
    omega
  have s1 : (g'.zb1.extract 0 5).size = 5 := by
    rw [Array.size_extract, hS.2]
    omega
  have x0 : g'.zb0.extract 5 g'.zb0.size = g'.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK) := by
    rw [hS.1, Nat.add_assoc]
  have x1 : g'.zb1.extract 5 g'.zb1.size = g'.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK) := by
    rw [hS.2, Nat.add_assoc]
  have w0 : (g'.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size = tl.f9.kT + tl.f9.cK := by
    rw [Array.size_extract, hS.1]
    omega
  have w1 : (g'.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size = tl.f9.kT + tl.f9.cK := by
    rw [Array.size_extract, hS.2]
    omega
  have h := (planesWeightsHeld_iff tl' (coefBody tl' g' G) g' fr.length).2 (by
    dsimp only
    rw [eI, eK, bθ, hbit]
    refine ⟨fun x hx => ?_, fun e he => ?_, fun x hx => ?_⟩
    · have c2' : (((coefBody tl' g' G).trees.getD tl.ix.BZ {}).rows.getD 2 {}).coef =
          Array.replicate 32 oneE := c2
      rw [c2'] at hx
      exact (Array.mem_replicate.1 hx).2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · refine ⟨fun r hr => ?_, fun x hx => ?_⟩
        · have c0' : (((coefBody tl' g' G).trees.getD tl.ix.BZ {}).rows.getD 0 {}).coef =
              eqTab (g'.zb0.extract 0 5) := c0
          rw [c0']
          exact eqTab_plain _ r (by rw [s0]; exact hr)
        · rw [eL 0, eqAt_plain, Nat.zero_add]
          show _ = mulE (mulE _ (mulE g'.leaves.eps g'.leavesA))
            (eqPlainF (g'.zb0.extract 5 g'.zb0.size) x)
          rw [x0, ← eqTab_plain _ x (by rw [w0]; exact hx)]
          refine word_of_val cok (Part.MaskedSum.okE_mul _ _) ?_
          rw [A.weight_plane0 hg x hx (hz 0 (by omega)) (hO 0 (by omega)) hfree
            (hP 0 (by omega) x hx)]
          simp only [Reading.gl.mul, kappa_val]
          ring
      · refine ⟨fun r hr => ?_, fun x hx => ?_⟩
        · have c1' : (((coefBody tl' g' G).trees.getD tl.ix.BZ {}).rows.getD 1 {}).coef =
              eqTab (g'.zb1.extract 0 5) := c1
          rw [c1']
          exact eqTab_plain _ r (by rw [s1]; exact hr)
        · rw [eL 1, eqAt_plain, Nat.zero_add]
          show _ = mulE (mulE _ (subE zeroE oneE)) (eqPlainF (g'.zb1.extract 5 g'.zb1.size) x)
          rw [x1, ← eqTab_plain _ x (by rw [w1]; exact hx)]
          refine word_of_val cok (Part.MaskedSum.okE_mul _ _) ?_
          rw [A.weight_plane1 hg x hx (hz 1 (by omega)) (hO 1 (by omega))
            (hP 1 (by omega) x hx)]
          simp only [Reading.gl.mul, kappa_val]
          ring
    · rw [eL 2]
      refine word_of_val cok (okE_scaleNat _ _) ?_
      have ep : (Fo.pinW tl).getD x zeroE = ofNat (2 ^ (x % 32)) := by
        unfold Fo.pinW
        exact getD_map_range _ _ _ _ hx
      rw [A.weight_plane2 hg x hx (hz 2 (by omega)) (hO 2 (by omega)) (hP 2 (by omega) x hx),
        ep, Fo.scaleNat_val Reading.gl, Fo.ofNat_val Reading.gl, kappa_val, Reading.gl.one]
      ring)
  rw [planesWeightsHeld_eq] at h
  exact ⟨hjo.trans (congrArg some hn), h⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqPlainF_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTab_plain
#print axioms VerifiableInference.Desc.First.K8.Honest.hasRow_of_rows
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.planeEqs
