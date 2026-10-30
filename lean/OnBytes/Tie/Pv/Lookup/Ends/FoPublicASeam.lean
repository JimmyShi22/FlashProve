-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicASeam.lean.
The attention plans of a record that Verify.publicOf returns: the two equations from which a plan's
seam comes, every argument written.

In Fo.PubA.public_A_seam (OnBytes/Tie/Pv/Lookup/Ends/FoPublicAPlFor.lean) the seam from which
Attention.Seam.plan runs stands under "there is" with no equation of its own. Here it has one.

States:
  public_A_seam_at: at a member a of X.A there are seams seam0 and s1 with: Attention.Seam.shape, at
    the record's settings and at Attention.matrices of a's shape, returns seam0; Attention.Seam.plan
    at seam0 returns s1; a's seam is s1 but for the field plFor of the record of its smallness test.
    Both are values of equations at written arguments (Fo.BatRows.planA_rows0).
Under: Verify.publicOf's equation and the membership; nothing else.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAPlFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **The seam's own two equations, at a0; a's seam is that seam but for plFor.** -/
theorem public_A_seam_at (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ (seam0 s1 : Attention.Seam),
      Attention.Seam.shape X.P.settings (Attention.matrices a.S (Attention.inOf X.P.settings
          X.layers.y (Pub.midQ X.layers.y g) g)) X.P.settings.tau
        (Attention.inOf X.P.settings X.layers.y (Pub.midQ X.layers.y g) g).col0Q (Attention.inOf
            X.P.settings X.layers.y (Pub.midQ X.layers.y g) g).ktO (Attention.inOf X.P.settings
            X.layers.y (Pub.midQ X.layers.y g) g).aO = .ok seam0 ∧
      seam0.plan a.nW (X.P.settings.hb - X.P.settings.pow) X.P.settings.hb = .ok s1 ∧
      a.seam = { s1 with tl := { s1.tl with plFor := a.seam.tl.plFor } } := by
  obtain ⟨a0, hp, ha⟩ := public_A_plFor h g a hg
  obtain ⟨seam0, h0, h1, _⟩ := BatRows.planA_rows0 _ _ _ a0 hp
  have eW : a.nW = a0.nW := by rw [ha]
  have eS : a.S = a0.S := by rw [ha]
  refine ⟨seam0, a0.seam, ?_, ?_, ?_⟩
  · rw [eS]
    exact h0
  · rw [eW]
    exact h1
  · conv_lhs => rw [ha]


end

end Fo.PubA
