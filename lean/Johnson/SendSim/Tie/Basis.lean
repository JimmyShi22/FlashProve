-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Basis.lean: an element of the extension field GE is the sum of its three
coordinates in the base field GF, each multiplied by the library's power of θ (1, θ, θ²), and the
three coordinates are unique.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model"; Johnson/SendSim/At/Sim.lean, "Terms". Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for the library's two fields, by algebra.
  against         The definition: for a triple a of elements of GF, the sum over t < 3 of a t, cast
                  into GE, times readE (thetaE t). thetaE t (OnBytes/Field/Ext.lean) is the
                  executable field's power t of θ, and readE reads it as an element of GE.
  against_eq      against a is the element of GE with the coordinates a 0, a 1, a 2.
  against_coords  Each element of GE is against of its own three coordinates.
  against_inj     Two triples with the same sum are equal.
  against_add     against is additive in the triple.

How it fits. The instance of the general model (Johnson/SendSim/At/Bridge.lean) reads everything
over GF. Its map put builds a coin of GE from three coins of GF by against, and
Johnson/SendSim/Tie/Coord.lean has the inverse direction. That serves rowsExact and rowsFresh.
against_eq rests on readE_theta (OnBytes/Slice/RecordOK.lean) and on the lemmas on coordinates of
Code/Field.lean. against_coords and against_inj are used by no file of Johnson/SendSim/; they say
that the three powers are a basis.
-/
import OnBytes.Slice.RecordOK

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes OnBytes.Slice

/-- The sum of three elements of GF, each cast into GE and multiplied by the library's power of θ: a
0 * 1 + a 1 * θ + a 2 * θ². -/
noncomputable def against (a : Fin 3 → GF) : GE :=
  ∑ t : Fin 3, algebraMap GF GE (a t) * readE (thetaE t.val)

/-- against a is the element of GE with the coordinates a 0, a 1, a 2. -/
theorem against_eq (a : Fin 3 → GF) : against a = ⟨a 0, a 1, a 2⟩ := by
  unfold against
  rw [Fin.sum_univ_three]
  simp only [readE_theta]
  ext <;> simp

/-- Each element of GE is against of its own three coordinates. -/
theorem against_coords (d : GE) : against ![d.c0, d.c1, d.c2] = d := by
  rw [against_eq]
  rfl

/-- Two triples with the same sum against are equal. -/
theorem against_inj : Function.Injective against := by
  intro a b h
  rw [against_eq, against_eq] at h
  have h0 := congrArg Code.Cubic.c0 h
  have h1 := congrArg Code.Cubic.c1 h
  have h2 := congrArg Code.Cubic.c2 h
  funext t
  fin_cases t
  · exact h0
  · exact h1
  · exact h2

/-- against is additive in the triple. -/
theorem against_add (a b : Fin 3 → GF) : against (a + b) = against a + against b := by
  rw [against_eq, against_eq, against_eq]
  rfl

end OnBytes.SendSim

#print axioms OnBytes.SendSim.against_eq
#print axioms OnBytes.SendSim.against_coords
#print axioms OnBytes.SendSim.against_inj
#print axioms OnBytes.SendSim.against_add
