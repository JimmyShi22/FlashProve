-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Switch/Recut.lean: the rounds of an interactive oracle reduction are split and merged by a
plan, and what is kept: point queries, locality, round-by-round knowledge soundness.

Why. A chain that is composed of blocks has a round for each prover message of each block. The
programs close a round only where the verifier draws: a prover message behind which nothing is drawn
stands in the message of the next round that is closed. So two blocks in a row may have three
rounds, (words . seeds) (answers . one value) (nothing . positions), where the programs have two,
(words . seeds) (answers . positions). The library merges such rounds for interactive oracle proofs
(`XPlan`, `InteractiveOracleProof.recut`, Iop/Recut.lean; the two cases: Iop/Join.lean), and later once more on the
compiler's interface (CompileK/KnowJoin.lean). Here the same plans are applied to a reduction
(`IOR`, Ior/Ior.lean), so that a block with the programs' rounds can be written as a value of the
library's blocks. Nothing on rounds is proved anew: each law below is the library's law on
transcripts (Iop/RecutProofs.lean) read at a reduction. Definitions and proofs.

Main names:
  `IOR.recut R P`: the reduction on the new list of rounds `P.shape`. The verifier and the new
    implicit instance are R's on the transcript read back (`Tr.old P`); the sets of positions are
    R's, carried along `OPos.oldEquiv P`.
  `recut_know`, `recut_knowInto`: round-by-round knowledge soundness is kept, for every plan,
    between the same relations, with the extractor on the transcript read back and the errors
    `Err.recut P`: 0 for a first part that is split off, e1 * |C2| + |C1| * e2 for a merged round.
  `recut_onOut`: the clause on outputs is kept. `recut_isLocal`: locality is kept, under `P.OK`.
  `recut_point`: every oracle part is a string, if it was so before and the plan's parts have their
    data (`P.Kits`: for a plan without a split there is nothing to give).
  `recut_out`, `recut_imp`: the verifier and the new implicit instance in closed form.
Limits: `recut_know` asks no condition on the plan, but without `P.OK` the new reduction is another
protocol than R: at a merge by (J1) the old transcript is read at the one value u that the plan
names, whatever values the old challenge has, and the merged round's error e1 * |C2| + |C1| * e2 may
pass the number |C2| of values of the new challenge, so that the statement says nothing. Nothing on
an honest prover, completeness or hiding (for proofs the library has these: Iop/RecutProofs.lean).
Which rounds of a chain are to be merged is not said here. As in Iop/Join.lean: two oracles of a
merged message stay two oracles.
-/
import Iop.RecutProofs
import Iop.RecutData
import Ior.KnowColl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop.IOR
open Prob

variable {Xi Xo : Type} {Ei Eo : ExtSpec}

/-- The reduction R on the list of rounds that the plan P makes. -/
def recut (R : IOR Xi Ei Xo Eo) (P : XPlan R.shape) : IOR Xi Ei Xo Eo where
  shape := P.shape
  blinded p := R.blinded (OPos.oldEquiv P p)
  extReads ρ := R.extReads (Rho.old P ρ)
  reads ρ := (R.reads (Rho.old P ρ)).map (OPos.oldEquiv P).symm.toEmbedding
  out x y τ := R.out x y (Tr.old P τ)
  imp y τ := R.imp y (Tr.old P τ)
  srcE ρ q := R.srcE (Rho.old P ρ) q
  srcO ρ q := (R.srcO (Rho.old P ρ) q).map (OPos.oldEquiv P).symm.toEmbedding
  tie ρ p := R.tie (Rho.old P ρ) (OPos.oldEquiv P p)

variable (R : IOR Xi Ei Xo Eo) (P : XPlan R.shape)

theorem recut_out (x : Xi) (y : Ei.Str) (τ : Tr P.shape) :
    (R.recut P).out x y τ = R.out x y (Tr.old P τ) := rfl

theorem recut_imp (y : Ei.Str) (τ : Tr P.shape) : (R.recut P).imp y τ = R.imp y (Tr.old P τ) := rfl

/-- Round-by-round knowledge soundness is kept, for every plan. -/
theorem recut_know {WA WB : Type} (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → WA → Prop)
    (RB : Xo × Eo.Str → WB → Prop) (ext : Xi × Ei.Str → Tr R.shape → WB → WA) (ε : Err R.shape)
    (h : R.red.Know on RA RB ext ε) :
    (R.recut P).red.Know on RA RB (fun a τ w => ext a (Tr.old P τ) w) (Err.recut P ε) :=
  fun a ha => Doomed.recutS P ε _ (h a ha)

/-- The same into the next joint's condition. -/
theorem recut_knowInto {WA WB : Type} (on : Xi × Ei.Str → Prop) (on' : Xo × Eo.Str → Prop)
    (RA : Xi × Ei.Str → WA → Prop) (RB : Xo × Eo.Str → WB → Prop)
    (ext : Xi × Ei.Str → Tr R.shape → WB → WA) (ε : Err R.shape)
    (h : R.red.KnowInto on on' RA RB ext ε) :
    (R.recut P).red.KnowInto on on' RA RB (fun a τ w => ext a (Tr.old P τ) w) (Err.recut P ε) :=
  recut_know R P on RA _ ext ε h

/-- The clause on outputs is kept, for every plan. -/
theorem recut_onOut (on : Xi × Ei.Str → Prop) (on' : Xo × Eo.Str → Prop)
    (h : ∀ a τ b, on a → R.red.out a τ = some b → on' b) :
    ∀ a τ b, on a → (R.recut P).red.out a τ = some b → on' b :=
  fun a τ b ha hb => h a (Tr.old P τ) b ha hb

/-- Locality is kept, under the plan's conditions. -/
theorem recut_isLocal (h : R.IsLocal) (hP : P.OK) : (R.recut P).IsLocal where
  out := by
    intro x y y' τ τ' hρ hpl hext hrd
    refine h.out x y y' (Tr.old P τ) (Tr.old P τ') ?_ ?_ ?_ ?_
    · rw [Tr.rho_old, Tr.rho_old]
      exact congrArg (Rho.old P) hρ
    · rw [Tr.plains_old, Tr.plains_old]
      exact congrArg (Plains.old P) hpl
    · intro p hp
      rw [Tr.rho_old] at hp
      exact hext p hp
    · intro p hp
      rw [Tr.rho_old] at hp
      obtain ⟨p', rfl⟩ := (OPos.oldEquiv P).surjective p
      rw [Tr.read_old P hP, Tr.read_old P hP]
      refine congrArg (OSym.old P p') (hrd p' ?_)
      show p' ∈ (R.reads (Rho.old P τ.rho)).map (OPos.oldEquiv P).symm.toEmbedding
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact hp
  imp := by
    intro y y' τ τ' q hρ hpl hext hrd
    refine h.imp y y' (Tr.old P τ) (Tr.old P τ') q ?_ ?_ ?_ ?_
    · rw [Tr.rho_old, Tr.rho_old]
      exact congrArg (Rho.old P) hρ
    · rw [Tr.plains_old, Tr.plains_old]
      exact congrArg (Plains.old P) hpl
    · intro p hp
      rw [Tr.rho_old] at hp
      exact hext p hp
    · intro p hp
      rw [Tr.rho_old] at hp
      obtain ⟨p', rfl⟩ := (OPos.oldEquiv P).surjective p
      rw [Tr.read_old P hP, Tr.read_old P hP]
      refine congrArg (OSym.old P p') (hrd p' ?_)
      show p' ∈ (R.srcO (Rho.old P τ.rho) q).map (OPos.oldEquiv P).symm.toEmbedding
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact hp

/-- Every oracle part is a string, as before. -/
theorem recut_point (K : P.Kits) (h : Nonempty R.shape.IsPoint) :
    Nonempty (R.recut P).shape.IsPoint :=
  h.elim fun p => ⟨p.recutK P K⟩

end Iop.IOR

#print axioms Iop.IOR.recut_know
#print axioms Iop.IOR.recut_knowInto
#print axioms Iop.IOR.recut_onOut
#print axioms Iop.IOR.recut_isLocal
#print axioms Iop.IOR.recut_point
