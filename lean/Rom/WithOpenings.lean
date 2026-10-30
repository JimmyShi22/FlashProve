-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/WithOpenings.lean: index binding of a scheme with openings in place of proofs (`withOpenings`,
ZKCP/WithOpenings.lean) passes from a family of oracles to one oracle and to the syntax of
ZKCP/Defs.lean, with the same bound.

First the definitions of ZKCP/WithOpenings.lean for schemes over a family of oracles
(ZKCP/Gen.lean): `Gen.Arg.commitAt`, `Gen.Arg.withOpenings`, `Gen.Extractor.withOpenings`.

`binding_withOpenings_oneOf`: if `G.withOpenings` has index binding over the family, with an
extractor that reads one-block entries only (`LocalTo`, Rom/Family.lean), then
`(SpecialAny.oneOf (schemeOverOneHashFunction m G)).withOpenings` has it over the one oracle.
The steps are those for every scheme: `binding_overOne` (Rom/ExitBind.lean) and
`SpecialAny.bindingWith_of_gen` (ZKCP/SpecialAny.lean). What is shown here is that the two ways give
the same verifier (`withOpenings_V_oneOf`): to bring G to one oracle and then put openings in place
of proofs, or the other way round. Index binding reads the verifier alone (ZKCP/SameV.lean).
Queries over the one oracle are counted in bit strings.
-/
import Rom.ExitBind
import Rom.WithCoins
import ZKCP.WithOpenings
import ZKCP.SameV
import ZKCP.SpecialKeyTag
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

variable {S : Rom.OSpec} {I X W IVK ISK Pf : Type}

/-- `Arg.commitAt` for a scheme over a family of oracles. -/
def Arg.commitAt (G : Arg S I X W IVK ISK Pf) (i : I) (coins : ℕ) : Rom.OComp S IVK :=
  ((G.C i).withCoins coins).bind fun keys => .pure keys.1

open Classical in
/-- `Arg.withOpenings` for a scheme over a family of oracles. -/
def Arg.withOpenings (G : Arg S I X W IVK ISK Pf) :
    Arg S I (I × ℕ) Unit IVK ISK Unit where
  C := G.C
  P := fun _ b => .pure ⟨b.map fun _ => (), by simp⟩
  V := fun key x _ => (G.commitAt x.1 x.2).bind fun key' => .pure (decide (key' = key))

/-- `Extractor.withOpenings` for a scheme over a family of oracles. -/
def Extractor.withOpenings (E : Extractor S I X W IVK Pf) : Extractor S I (I × ℕ) Unit IVK Unit
    where
  Ei := E.Ei
  Ew := fun _ _ _ _ _ => ()

end ZKCP.Gen

namespace Rom

open ZKCP

variable {S : OSpec} {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- The extractor for openings reads what the index part of E reads. -/
theorem LocalTo.withOpenings {E : Gen.Extractor S I X W IVK Pf} {m : OracleCoding S lam} (h : LocalTo E m) :
    LocalTo E.withOpenings m :=
  ⟨h.1, fun _ _ _ _ _ => rfl⟩

/-- Openings in place of proofs, before or after the step to one oracle: the same verifier. -/
theorem withOpenings_V_oneOf (m : OracleCoding S lam) (G : Gen.Arg S I X W IVK ISK Pf) :
    (SpecialAny.oneOf (schemeOverOneHashFunction m G.withOpenings)).V
      = (SpecialAny.oneOf (schemeOverOneHashFunction m G)).withOpenings.V := by
  classical
  funext key x π
  show ofRom (((((G.C x.1).withCoins x.2).bind fun keys => OComp.pure keys.1).bind
      fun key' => OComp.pure (decide (key' = key))).overOne m)
    = (((ofRom ((G.C x.1).overOne m)).withCoins x.2).mapO Prod.fst).mapO
      fun key' => decide (key' = key)
  rw [overOne_bind, overOne_bind, SpecialAny.ofRom_bind, SpecialAny.ofRom_bind, withCoins_ofRom,
    withCoins_overOne]
  rfl

/-- Index binding of the scheme with openings in place of proofs passes to one oracle and to the
syntax of ZKCP/Defs.lean, with the same bound, if the extractor reads one-block entries only
(`hE`). -/
theorem binding_withOpenings_oneOf (m : OracleCoding S lam) (G : Gen.Arg S I X W IVK ISK Pf)
    (E : Gen.Extractor S I X W IVK Pf) (hE : LocalTo E.withOpenings m) (β : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.HasIndexBindingWith (Special.toPair (openingRelation I)) G.withOpenings E.withOpenings
        β) :
    HasIndexBindingWith (openingRelation I) (SpecialAny.oneOf (schemeOverOneHashFunction m G)).withOpenings
      (Special.extOf (extractorOverOneHashFunction m E)).withOpenings β := by
  have h1 := binding_overOne m _ G.withOpenings E.withOpenings hE β h
  have h2 : HasIndexBindingWith (openingRelation I) (SpecialAny.oneOf (schemeOverOneHashFunction m G.withOpenings))
      (Special.extOf (extractorOverOneHashFunction m E.withOpenings)) β :=
    SpecialAny.bindingWith_of_gen (openingRelation I) (SpecialAny.agrees_oneOf _) _ β
      (by rwa [Special.extTo_extOf])
  exact (SameV.hasIndexBindingWith_iff (withOpenings_V_oneOf m G) (openingRelation I) _ β).1 h2

end Rom
