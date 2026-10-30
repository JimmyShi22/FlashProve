-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LeftPoint.lean: the kind "lookup" (K3): BEHIND A YES THE KEY POINT HAS ALL ITS
COORDINATES: the list zx ++ zy of the record of end values, off which the row out's fourth item
reads its places (keyPt, Johnson/Top/H/K3RowOutRider.lean), has dT + rK = v' + 1 members; AND THE
LEAVES' AND THE BITS' POINTS HAVE kT + cK + 5 MACHINE WORDS EACH (zb0_size_of_heardIs,
zb1_size_of_heardIs, K3Left.zb_size): wherever the heard record stands for some rounds.

Why. keyPt reads place t of zx ++ zy, and 0 beyond the list's end, in silence. What stands behind a
yes (K3Left, Johnson/Top/H/K3LeftStatement.lean) has the two sizes as machine words, and HeardIs
reads the lists off these.

Limits. A tie: no error term. It says nothing on which places a rider's selection reads.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement
import OnBytes.Tie.Pv.Lookup.Ends.FoBitsPayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- **Behind a yes the key point has dT + rK = v' + 1 coordinates.** -/
theorem K3Left.point_len {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : Forest.Shape}
    {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : Rounds K} (L : K3Left ρ h lm F F' g rs)
    (hok : FoNums.ok h = true) :
    ((endsOf h lm F.next rs).zx ++ (endsOf h lm F.next rs).zy).length = FoNums.v' h + 1 := by
  have e1 : (endsOf h lm F.next rs).zx.length = h.dT := by
    rw [← L.heardIs.zx, ← L.zx]
    simp [rdA]
  have e2 : (endsOf h lm F.next rs).zy.length = h.rK := by
    rw [← L.heardIs.zy, ← L.zy]
    simp [rdA]
  have e3 : h.v = h.dT + h.rK := rfl
  rw [List.length_append, e1, e2, ← Cb.Fo.ok_v hok, e3]

/-- **Where the heard record stands for some rounds, the leaves' point has kT + cK + 5 machine
words**: so the planes' weights, which are cut out of it, have their full length. -/
theorem zb0_size_of_heardIs {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : FoNums.Sh}
    {lm first : ℕ} {F' : Fork} {g : Forest.Heard} {rs : Rounds K}
    (hI : HeardIs ρ g F' (endsOf h lm first rs)) : g.zb0.size = h.kT + h.cK + 5 := by
  have e : (rdA ρ g.zb0).length = 5 + (h.kT + h.cK) := by
    rw [hI.zb0]
    exact ends_zb0_len h lm first rs
  simp only [rdA, List.length_map, Array.length_toList] at e
  omega

/-- And so has the bits' point. -/
theorem zb1_size_of_heardIs {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : FoNums.Sh}
    {lm first : ℕ} {F' : Fork} {g : Forest.Heard} {rs : Rounds K}
    (hI : HeardIs ρ g F' (endsOf h lm first rs)) : g.zb1.size = h.kT + h.cK + 5 := by
  have e : (rdA ρ g.zb1).length = 5 + (h.kT + h.cK) := by
    rw [hI.zb1]
    exact ends_zb1_len h lm first rs
  simp only [rdA, List.length_map, Array.length_toList] at e
  omega

/-- Behind a yes. -/
theorem K3Left.zb_size {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : Forest.Shape}
    {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : Rounds K} (L : K3Left ρ h lm F F' g rs) :
    g.zb0.size = h.kT + h.cK + 5 ∧ g.zb1.size = h.kT + h.cK + 5 :=
  ⟨zb0_size_of_heardIs L.heardIs, zb1_size_of_heardIs L.heardIs⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.K3Left.point_len
#print axioms VerifiableInference.OnPublicFiles.K3Left.zb_size
