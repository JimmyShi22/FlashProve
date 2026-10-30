-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/ColSumLayers.lean: IN THE GOALS' SCOPE THE COLUMNS OF THE NINE MATRICES OF EVERY
LAYERS' PLAN ADD UP TO 24086: THE PREMISE sL OF `trits_of_sums` (TritsOfSums.lean) IS PAID.
Statements and proofs; closed facts by Lean's kernel.

  `look_kT`: **the layers' lookup's greatest table has 2 ^ 16 rows: X.y.fo.kT = 16.** kT is the
    greatest k of the lookup's calls (`Cb.Fo.shape_more`, OnBytes/Tie/Pv/Lookup/Port/FoShape.lean);
    the eight calls' k are 8 (the fourth) and 16 (`Meaning.P34.hL_in_scope`,
    Johnson/Goal/Meaning/TabsScope.lean).
  `kbm_in_scope`: **the planes' matrix has 256 columns**: the number of calls times 2 ^ (kT + 5 -
    lmb) (`layout_kbm`); eight calls (`look_eight`); lmb at the written shape hKF.
  `colSum_layers`: **MAIN: colSum hp.tl = 24086 at every plan hp of X.G.** The plan's pairs (rows,
    columns) are `sizesTab X.y` (`tails_of_public`, `tails_pairs`); the parts, the columns of af,
    ad, ar, qa and of the stream's two are closed at hKF.
  `trits_of_sumA`: trits_of_sums with sL paid.
Limits. **sA (the attention plans' sum is 10248) is the one premise left at which `trits_of_sumA`
could be idle: shown of nothing here.** Its end is TritsOfSums.lean's own text, not K8.lean's ht:
see TritsOfSums.lean. The numerals are sizes of plans: functions of the parameter and layout files.
No soundness statement.

-/
import Johnson.LPFK9R.TritsOfSums
import Johnson.Goal.Meaning.LookScope
import Johnson.Goal.Meaning.TabsScope
import Johnson.Goal.Meaning.Pub34All
import Johnson.Road.FormsKeysTab
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model OnBytes.Road
open Meaning.P34

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **The greatest table of the layers' lookup.** -/
theorem look_kT (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : Verify.publicOf P.pol P.KL lay = .ok X) : X.y.fo.kT = 16 := by
  obtain ⟨-, -, ⟨s0, pub, hs0, efo⟩, -⟩ := pub34_all hS hR hX gl_numerals
  obtain ⟨ec, eN, -, ek, -⟩ := Cb.Fo.shape_more hs0
  have e8 : X.y.fo.NC = 8 := look_eight hS hR hX
  have hk : X.y.fo.kT = X.y.fo.calls.foldl (fun m c => max m c.k) 0 := by
    rw [efo]
    show s0.kT = s0.calls.foldl (fun m c => max m c.k) 0
    rw [ek, ec]
  have hsz : X.y.fo.calls.size = 8 := by
    rw [efo] at e8 ⊢
    show s0.calls.size = 8
    rw [ec, ← eN]
    exact e8
  rw [hk]
  apply Nat.le_antisymm
  · refine Cb.Fo.foldl_max_le _ 16 fun c hc => ?_
    obtain ⟨c0, h1, -, h3⟩ := hL_in_scope hS hR hX ⟨c, by omega⟩
    have e : X.y.fo.calls[c] = c0 := by
      have := Array.getElem?_eq_getElem hc
      rw [this] at h1
      exact Option.some.inj h1
    rw [e, h3]
    split <;> omega
  · obtain ⟨c0, h1, -, h3⟩ := hL_in_scope hS hR hX (0 : Fin 8)
    have hc : 0 < X.y.fo.calls.size := by omega
    have e : X.y.fo.calls[0] = c0 := by
      have := Array.getElem?_eq_getElem hc
      have h1' : X.y.fo.calls[0]? = some c0 := h1
      rw [this] at h1'
      exact Option.some.inj h1'
    have := Cb.Fo.le_foldl_max X.y.fo.calls 0 hc
    rw [e, h3] at this
    simpa using this

/-- **The planes' matrix has 256 columns.** -/
theorem kbm_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : Verify.publicOf P.pol P.KL lay = .ok X) : X.y.kbm = 256 := by
  have B := Hd.public_of_core hX (Hd.core_of_scope hS hR hX)
  have hh := (shape_of_public hX).trans (shape_in_scope hS hR hX)
  rw [_root_.Fo.PlaneMatG.layout_kbm B.lay]
  unfold _root_.Fo.planeCols
  rw [look_eight hS hR hX, look_kT hS hR hX, hh]
  rfl

/-- **THE LAYERS' SUM.** -/
theorem colSum_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : Verify.publicOf P.pol P.KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) : colSum hp.tl = 24086 := by
  have B := Hd.public_of_core hX (Hd.core_of_scope hS hR hX)
  have L2 := laid2_of_layout B.lay
  have hh := (shape_of_public hX).trans (shape_in_scope hS hR hX)
  have ey : X.layers.y = X.y := (pub_more (more_of_public hX).2.2.2.1).1
  have hlt : g < X.y.NGr := by
    rw [← ey]
    exact _root_.Fo.PlaneMatG.public_G_lt hX hg
  have hm : (hp.tl.mats.map fun M => (M.m, M.k)) = (sizesTab X.y).toArray := by
    rw [(tails_of_public hX hg).1]
    exact tails_pairs X.y hlt
  have hk : hp.tl.mats.toList.map (·.k) = (sizesTab X.y).map (·.2) := by
    have := congrArg (fun a => a.toList.map (·.2)) hm
    simpa [List.map_map, Function.comp_def] using this
  have hs : (sizesTab X.y).map (·.2) = [5990, 5990, 5990, 3200, 324, 256, 1536, 400, 400] := by
    unfold sizesTab
    rw [kbm_in_scope hS hR hX, L2.parts, L2.kcol, L2.kxb, hh]
    show (List.replicate ((((sizesOf hKF).map (·.2.2.2.2)).toArray).getD 0 0)
        (X.y.mrow.getD 0 0, (((sizesOf hKF).map (·.2.2.1)).toArray).getD 0 0) ++
      List.replicate ((((sizesOf hKF).map (·.2.2.2.2)).toArray).getD 1 0)
        (X.y.mrow.getD 1 0, (((sizesOf hKF).map (·.2.2.1)).toArray).getD 1 0) ++
      [(X.y.mrow.getD 2 0, (((sizesOf hKF).map (·.2.2.1)).toArray).getD 2 0), (2 ^ hKF.lmb, 256),
        (X.y.mrow.getD 3 0, (((sizesOf hKF).map (·.2.2.1)).toArray).getD 3 0),
        (X.y.mxb, roundUp (hKF.xl * hKF.d) (2 ^ hKF.lmx / 2 ^ hKF.lt) /
          (2 ^ hKF.lmx / 2 ^ hKF.lt)),
        (X.y.mxb, roundUp (hKF.xl * hKF.d) (2 ^ hKF.lmx / 2 ^ hKF.lt) /
          (2 ^ hKF.lmx / 2 ^ hKF.lt))]).map (·.2) = _
    have p0 : (((sizesOf hKF).map (·.2.2.2.2)).toArray).getD 0 0 = 3 := by decide +kernel
    have p1 : (((sizesOf hKF).map (·.2.2.2.2)).toArray).getD 1 0 = 1 := by decide +kernel
    have k0 : (((sizesOf hKF).map (·.2.2.1)).toArray).getD 0 0 = 5990 := by decide +kernel
    have k1 : (((sizesOf hKF).map (·.2.2.1)).toArray).getD 1 0 = 3200 := by decide +kernel
    have k2 : (((sizesOf hKF).map (·.2.2.1)).toArray).getD 2 0 = 324 := by decide +kernel
    have k3 : (((sizesOf hKF).map (·.2.2.1)).toArray).getD 3 0 = 1536 := by decide +kernel
    have kx : roundUp (hKF.xl * hKF.d) (2 ^ hKF.lmx / 2 ^ hKF.lt) /
        (2 ^ hKF.lmx / 2 ^ hKF.lt) = 400 := by decide +kernel
    rw [p0, p1, k0, k1, k2, k3, kx]
    rfl
  unfold colSum
  rw [hk, hs]
  rfl

/-- trits_of_sums with sL paid. -/
theorem trits_of_sumA {ly : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (sA : ∀ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a → colSum a.seam.tl = 10248) :
    (G.built.toList.all fun X => tritsOf X == tritsW X.kind) = true :=
  trits_of_sums hS hR hZ hG (fun _ _ hg => colSum_layers hS hR
    ((VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some ly)).symm.trans
      (ProofFile.Law.pub_public hZ)) hg) sA

end LPFK9

#print axioms LPFK9.look_kT
#print axioms LPFK9.kbm_in_scope
#print axioms LPFK9.colSum_layers
#print axioms LPFK9.trits_of_sumA
