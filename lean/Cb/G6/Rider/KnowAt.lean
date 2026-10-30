-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/KnowAt.lean: the rule for a second zero test, and the lemma that carries a clause past a
block, at `KnowAt` (Cb/G6/Cut.lean): the four clauses of `GoodAt` that speak of the verifier alone.

Statements with their proofs. No protocol occurs here. The forms at `GoodAt` (Cb/G6/Rider/Both.lean,
Carrier.lean, Carry.lean) take an honest prover in their type. A block whose soundness is stated as
`KnowAt` has none. Each statement here is the clause `know` of the form at `GoodAt`; the clauses
`point`, `isLocal` and `onOut` are the premise's.

Main names:
  `knowAt_both`: a block with `KnowAt` that is sound, for each fixed tuple of messages, from a
    second set of input statements to a second set of output statements has `KnowAt` between the two
    joints with the second claim, with the same extractor and the larger count in each round.
  `knowAt_cubes`: the second claim is a family of arrays that are 0 on their cubes; behind the block
    their multilinear extensions are 0 at chosen coordinates of a point that the output statement
    holds. Asked: `Carries` (Cb/G6/Rider/Carrier.lean) at the block's own counts. No count changes.
  `knowAt_carry`: a clause on the tuple of messages and a kept part of the state goes past any block
    that hands the kept part on (`IOR.Passes`), at the block's own counts.
  `knowAt_hollow_own`, `knowAt_hollow_out`: the empty uses.

Limits: the joints A and B are free letters. Wherever the input joint's own relaxed relation `relR`
or the output joint's `relR` gives the source, the statement with the second claim follows from the
block's own `KnowAt` alone and says nothing (`knowAt_hollow_own`, `knowAt_hollow_out`). A use should
prove the two sentences that stand at `hollow_own` (Cb/G6/Rider/Both.lean). Nothing on an honest
prover, completeness or zero knowledge.

Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Cut
import Cb.G6.Rider.Carrier

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks TWhole

section KnowAt
variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The rule at `KnowAt`: the larger count in each round. Warning: A and B are free
(`knowAt_hollow_own`, `knowAt_hollow_out`). -/
theorem knowAt_both {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : KnowAt R A B ext ε) (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (ε' : Err R.shape) (hs : ∀ m, R.red.Sound (fun a => ¬ A.on a ∨ SA m a) (SB m) ε') :
    KnowAt R (withRider A SA) (withRider B SB) ext (Err.max ε ε') :=
  ⟨h.point, h.isLocal, h.onOut, fun m => know_both (h.know m) (hs m)⟩

/-- A clause C that reads the tuple of messages and a kept part of the state, of a fixed type Z,
goes past any block that hands the kept part on, at the block's own counts. Mind: it is not to be
used, for a rider's own source, on the block that draws the rider's coordinates. -/
theorem knowAt_carry {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : KnowAt R A B ext ε) {Z : Type} (rI : Xi → Z) (rO : Xo → Z) (hp : R.Passes rI rO)
    (C : M → Z → Prop) :
    KnowAt R (withRider A fun m a => C m (rI a.1)) (withRider B fun m b => C m (rO b.1)) ext ε :=
  ⟨h.point, h.isLocal, h.onOut, fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw => ⟨hτ b w hb hw.1, by
      have h2 : C m (rO b.1) := hw.2
      rw [hp a.1 a.2 τ b.1 (red_out hb)] at h2
      exact h2⟩) (h.know m a ha)⟩

/-- An empty use, by the input. If the input joint's own `relR` gives the source at the statements
with `on`, the statement with the second claim holds at the block's own counts, whatever the target
says. -/
theorem knowAt_hollow_own {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : KnowAt R A B ext ε) (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hA : ∀ a w, A.on a → A.relR a w → SA w.1 a) :
    KnowAt R (withRider A SA) (withRider B SB) ext ε :=
  ⟨h.point, h.isLocal, h.onOut, fun m a ha =>
    Doomed.mono _ _ (fun _ hτ b w hb hw => ⟨hτ b w hb hw.1, hA a _ ha (hτ b w hb hw.1)⟩)
      (h.know m a ha)⟩

/-- An empty use, by the output. If the output joint's `relR` gives the source, the statement with
the second claim holds at the block's own counts, whatever the target says. A relation that rides
along and comes out as it went in falls under this. -/
theorem knowAt_hollow_out {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : KnowAt R A B ext ε) (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hB : ∀ m a τ b wp, R.red.out a τ = some b → B.relR b (m, wp) → SA m a) :
    KnowAt R (withRider A SA) (withRider B SB) ext ε :=
  ⟨h.point, h.isLocal, h.onOut, fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw => ⟨hτ b w hb hw.1, hB m a τ b w hb hw.1⟩) (h.know m a ha)⟩

variable {E : Type} [Field E] [Fintype E]

/-- The rule for arrays on cubes at `KnowAt`, at the block's own counts: for any block whose output
statement holds coordinates that are single challenges (`Carries`). The arrays are read off the
input statement (fi) and off the output statement (fo), which must agree wherever the verifier
outputs (hf). Cube and choice of coordinates are per member. Warning: A and B are free
(`knowAt_hollow_own`, `knowAt_hollow_out`). -/
theorem knowAt_cubes {ι : Type} {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : KnowAt R A B xt ε) {β : Binds ℕ E R.shape} {T : ℕ → Prop} {r : Xo → ℕ → E}
    (C : Carries R β ε T r) (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelOK T g sel)
    (fi : ι → M → Xi × Ei.Str → ℕ → E) (fo : ι → M → Xo × Eo.Str → ℕ → E)
    (hf : ∀ i m a τ b, R.red.out a τ = some b → ∀ X < 2 ^ g i, fo i m b X = fi i m a X) :
    KnowAt R (withRider A fun m a => ∀ i, ∀ X < 2 ^ g i, fi i m a X = 0)
      (withRider B fun m b => ∀ i, Blocks.ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0) xt
      ε := by
  have G := knowAt_both h (fun m a => ∀ i, ∀ X < 2 ^ g i, fi i m a X = 0)
    (fun m b => ∀ i, Blocks.ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0) (β.err fun _ => 1)
    fun m => (sound_rider R.red β C.inj (d := fun _ => 1)
      (G := fun i a (z : ℕ → E) => Blocks.ext (g i) (fi i m a) fun t => z (sel i t))
      (fun i a => degLE_ext_comp (g i) (fi i m a) (sel i) (hsel i).1) (fun _ _ => 0)
      (fun a τ b hb hS i => by
        have h1 := hS i
        rw [ext_congr (hf i m a τ b hb), ext_congr_point (fun t ht =>
          (C.rd a.1 a.2 τ b.1 (fun _ => 0) (red_out hb) (sel i t) ((hsel i).2 t ht)).symm)
            (fi i m a)] at h1
        exact h1)).conseq
      (fun a hv => Or.inr fun i =>
        vanishes_ext (hsel i).1 (fun t ht => C.mem _ ((hsel i).2 t ht)) (hv i)) (fun _ => id)
  rwa [Blocks.Err.max_eq_left_of_le C.le] at G

end KnowAt

end Cb.Rider

#print axioms Cb.Rider.knowAt_both
#print axioms Cb.Rider.knowAt_carry
#print axioms Cb.Rider.knowAt_hollow_own
#print axioms Cb.Rider.knowAt_hollow_out
#print axioms Cb.Rider.knowAt_cubes
