-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Rider.lean: the rule for further oracles that a block only hands on: round-by-round knowledge
soundness alone is kept, at the same errors; and two facts on a round whose oracle is a string of
columns that holds a further oracle.

An oracle that was sent for a later block (a rider) stands in the implicit part of the statements
between, as a second component of which the joints ask nothing (`IOR.Rels.keepE`, Ior/Frame.lean);
a block between runs as `R.keepE F` (same file). The library proves its whole bundle for that frame
(Ior/KnowCollRulesFrame.lean); here are the two clauses that knowledge soundness needs, alone.
Main names:
  `know_keepE`: `Reduction.Know` of R between A and B gives it of `R.keepE F` between `A.keepE F`
    and `B.keepE F`, with R's extractor on the first component and R's errors.
  `onOut_keepE`: the clause on outputs likewise.
  The rounds are R's by definition; locality: `IOR.IsLocal.keepE` (Ior/FrameProofs.lean).
  `doomed_col`: "the prover has lost" behind a round of columns (`ColLay`, Cb/Ent/ColRound.lean).
  `colPoint`: a round of columns over finitely many leaves is a string.
A rider here is an oracle without a sample; Cb/Ld/LdGroupNewRide.lean uses the word for sampled
oracle messages of a next part.
A round of columns here (`ColLay`, Cb/Ent/ColRound.lean) is not a packing (`PackAt`,
Iop/PackAt.lean): a packing gathers the positions of one round's own oracle into columns and keeps
soundness, locality and point oracles without a premise; a round of columns also holds the symbols
of an oracle that a later round would send, which a packing cannot, and locality and point oracles
of a reduction over it are shown block by block.
Limits: nothing on an honest prover. Nothing is said of the oracle that is handed on.

-/
import Ior.FrameProofs
import Cb.Ent.ColRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv
open Iop Prob IOR

variable {K Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} (F : ExtSpec) (R : IOR Xi Ei Xo Eo)
  (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)

theorem know_keepE (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape)
    (h : R.red.Know A.on A.relR B.relR ext ε) :
    (R.keepE F).red.Know (A.keepE F).on (A.keepE F).relR (B.keepE F).relR
      (fun a τ w => ext (a.1, a.2.1) τ w) ε := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h (a.1, a.2.1) ha)
  intro τ hτ b w hb hw
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  exact hτ (b.1, b.2.1) w (red_out_eq_some.2 ⟨h1, congrArg Prod.fst h2⟩) hw

theorem onOut_keepE (h : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b) :
    ∀ a τ b, (A.keepE F).on a → (R.keepE F).red.out a τ = some b → (B.keepE F).on b := by
  intro a τ b ha hb
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  exact h (a.1, a.2.1) τ (b.1, b.2.1) ha (red_out_eq_some.2 ⟨h1, congrArg Prod.fst h2⟩)

/-- "The prover has lost" behind a round of columns: the bound for every first message of the round
r holds for the message cut out of the columns. -/
theorem doomed_col {r : Round} {W : Type} (L : ColLay r W) (pt : r.IsPoint) (s : Shape) (e : ℕ)
    (ε : Err s) (bad : Tr (r :: s) → Prop) (h : Doomed (r :: s) (e, ε) bad) :
    Doomed (L.round :: s) (e, ε) (fun τ => bad (L.up pt τ)) :=
  fun m => h (L.main pt m.1, m.2)

/-- A round of columns over finitely many leaves is a string. -/
def colPoint {r : Round} {W : Type} (L : ColLay r W) [Fintype L.Pt] [DecidableEq L.Pt] :
    L.round.IsPoint where
  finPos := inferInstanceAs (Fintype L.Pt)
  decPos := inferInstanceAs (DecidableEq L.Pt)
  ofSyms := fun f => f
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := L.join r.dOrc L.dW

#print axioms know_keepE
#print axioms onOut_keepE
#print axioms doomed_col

end Cb.Pv
