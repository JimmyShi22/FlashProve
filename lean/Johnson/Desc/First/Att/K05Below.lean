-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Below.lean: the written counts of K05_whole_any and of the laws built on
it (bearErr ds _ (A.ch.eps Ex)) are
shares of at most 2^-k of their rounds' challenges, from a yes of one Boolean test on public
numbers.

Main names:
  `errList_one`: the library's two lists of a block's errors (Att/K05Bears.lean, Cb/G6/Cut.lean)
    are one.
  `K05_below`: kap = 4; the plan's record is recOf P rows; the written rounds' entries are the
    kind's ROUNDS; k5Held k (zOf p.own) on
    the written rounds' own entries and kinds says yes: then Err.Below (bearErr ds _ (A.ch.eps Ex))
      (2⁻¹ ^ k).

How: K05_rounds (the chain's errors are errOf over the kind's entries), eZ_eq, held_of_check,
bear_below.
Limits: the test is evaluated in no file of this tree. That a file's written rounds have given kinds
is not shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb OnBytes OnBytes.Model Cb.Pv.Att Inst.Model OnBytes.Maker
open OnBytes.Tie.Pv.Att (recOf ownAt_fits)
open scoped ENNReal

/-- The library has the list of a block's errors twice (Att/K05Bears.lean · Cb/G6/Cut.lean):
they are one. -/
theorem errList_one : ∀ {s : Shape} (ε : Err s), Cb.errList ε = TWhole.errList ε
  | [], _ => rfl
  | _ :: _, (e, ε) => congrArg (e :: ·) (errList_one ε)

theorem K05_below {M X : Type} (P : OwnPar Cb.Gl.E M X) (hk4 : P.kap = 4) (rows : ℕ) (p : Par) (hrec : p.own = recOf P rows)
    (Ex : ExtSpec) (k : ℕ) (ds : List RDT) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hc : k5Held k (zOf p.own) (ds.map fun d => (d.entry, d.kind)) = true) :
    Err.Below (bearErr ds _ ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps Ex)) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  have hfit := ownAt_fits P (theMeans Cb.Gl.E _ _ _) hk4 rows
  rw [← hrec] at hfit
  have ez := eZ_eq P (theMeans Cb.Gl.E _ _ _) hk4 rows
  rw [← hrec] at ez
  refine bear_below ds _ _ (held_of_check _ Ex k ds ?_ (by rw [ez]; exact hc))
  rw [he, errList_one]
  exact (K05_rounds _ p hfit Ex).2.1

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_below
