-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/OneAny.lean: AN ENCODING OF THE TYPED ORACLES' POINTS INTO ONE HASH FUNCTION
EXISTS AT THE CARRIER of an object with records, also at the passed object; so binding_one's
quantifier «for m with one-block leaf and node answers» (One.lean) does not run over the empty set.
By the library's implAny | exists_impl (CompileK/ImplExists.lean: a code by choice, in unary: no
proposal for a program) and countable_pts, ctbSh_pull | grind, ctbS_pull | grind
(CompileK/ImplCountable.lean), used as they stand.
Under: instances, records, the alphabet, positions, symbols and plain parts are countable (CtbSh,
CtbS); nonces countable.

-/
import Johnson.RecCompile.One
import Johnson.RecCompile.Pass
import CompileK.ImplCountable

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type}

theorem exists_impl_carrier (lam K : ℕ) (L : HolographicProtocol I X) [Countable X] [Countable L.Rec]
    (hSg : Countable L.Symbol) (hT : CtbSh L.offline.shape) (hL : CtbSh L.link.shape)
    (hB : CtbS L.onlineBatch.loc.shape L.onlineBatch.ann) :
    ∃ m : OracleCoding (spec lam K L.carrierC) lam, m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 := by
  obtain ⟨h1, h2⟩ := countable_pts I L.XC lam K L.carrierC inferInstance hSg hT hL hB
  haveI := h1
  haveI := h2
  exact ⟨implAny lam K L.carrierC, exists_impl I L.XC lam K L.carrierC⟩

theorem exists_impl_passed (lam K : ℕ) (Nn : Type) [Inhabited Nn] [Countable Nn] (L : HolographicProtocol I X)
    [Countable X] [Countable L.Rec] (hSg : Countable L.Symbol) (hT : CtbSh L.offline.shape)
    (hL : CtbSh L.link.shape) (hB : CtbS L.onlineBatch.loc.shape L.onlineBatch.ann)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape) :
    ∃ m : OracleCoding (spec lam K ((L.pull σT σL σB).grind Nn gT gL gB).carrierC) lam,
      m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 :=
  haveI : Countable ((L.pull σT σL σB).grind Nn gT gL gB).Rec := inferInstanceAs (Countable L.Rec)
  exists_impl_carrier lam K ((L.pull σT σL σB).grind Nn gT gL gB) hSg
    (ctbSh_grind Nn _ (ctbSh_pull _ hT)) (ctbSh_grind Nn _ (ctbSh_pull _ hL))
    (ctbS_grind Nn _ (ctbS_pull _ hB))

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.exists_impl_passed
