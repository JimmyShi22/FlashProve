-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/RopeAny.lean: CONDITIONAL.

What is here. The library's hypothesis on the rotary tables, `RopeFits`
(Johnson/Road/FormsKeysQK.lean), does not read the end point of the claims' environment: where it
holds at an environment it holds at the same environment with any other end point. So each of the
library's public structures `Pub34` (Johnson/Road/Rows/LayerEnds34.lean) gives, by its own field R,
the fit at every end point: Pub34At.lean's `pub34At` lays it into the structure that it moves to
another end point.

  `ropeFits_rt`   the fit at another end point
  `rope_of_pub`   **the fit at every end point, from a public structure alone**

Limits. NOTHING NEW IS SHOWN: the two fields are handed on. That a structure X exists is not shown.

No property is claimed.
-/
import Johnson.Road.Rows.LayerEnds34

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (RopeFits)
open OnBytes.Road.Rows (Pub34)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim)

variable {K : Type} [Field K]

/-- **The fit at another end point.** CONDITIONAL: on h. -/
theorem ropeFits_rt {ρ : Reading K} {c : ClaimEnv} {D : Dim} {tb : Tables} {L0 lam : ℕ}
    (h : RopeFits ρ c D tb L0 lam) (rt : Array E) :
    RopeFits ρ { c with rt := rt } D tb L0 lam :=
  ⟨h.cos, h.sin⟩

/-- **THE ROTARY TABLES FIT AT EVERY END POINT, FROM A PUBLIC STRUCTURE ALONE.** -/
theorem rope_of_pub (X : Pub34 K) :
    ∀ (rt : Array E) (lam : ℕ), lam < X.c.v.y.Lam →
      RopeFits X.ρ { X.c with rt := rt } X.D X.tb (X.c.v.g * X.c.v.y.Lam) lam :=
  fun rt lam h => ropeFits_rt (X.R lam h) rt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ropeFits_rt
#print axioms ProofFile.Honest.K4.rope_of_pub
