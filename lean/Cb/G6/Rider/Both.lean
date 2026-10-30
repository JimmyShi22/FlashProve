-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Both.lean: two relations on one reduction; a second zero test on challenges that a block
draws anyway.

Definitions, statements and proofs. No protocol of its own: no term of a reduction is added or
changed.

What it is for. A condition of the form "an array is 0 at every vertex of a cube" can be tested at a
point whose coordinates are challenges of a sumcheck or of a lookup that runs anyway, with no round,
no message and no challenge of its own. This folder proves that such a second test may be added to a
block's input and output relations while the block stays the same term, with the same honest prover
and extractor; in each round the count is the larger of the block's own and the test's.

The words. The second claim is called the rider (as in Blocks/StageBoth.lean; not the further oracle
message of Cb/Ld/LdGroupNewRideFresh.lean). Its source is the claim before the block ("every array
of a family is 0 on its cube"); its target is the claim behind the block ("the multilinear extension
of every array is 0 at the chosen coordinates of the drawn point").

The rule. `know_both`: a reduction that is knowledge sound for one pair of relations and sound for a
second pair, on statements, is knowledge sound for both pairs together, with the same extractor and
the larger count in each round. The library has the like for soundness on statements
(`Reduction.Sound.both`, Iop/Compose.lean; Blocks/StageBoth.lean; Blocks/LookupRider.lean); new here
is the rule at `Know` and at the bundle `GoodAt` (Cb/Ld/LdSigLift.lean). `goodAt_both`,
`goodAt_both_le`, `goodAt_both_twice`: the rule at `GoodAt`, for each fixed tuple of messages.
`sound_rider`, `goodAt_rider`, `goodAt_cube`: the second pair is a zero test on chosen challenges;
its soundness is the library's `doomed_rider`.

What the second claim may read: the tuple of messages and the statement. It cannot read the further
witness, a message of the block, or a message that is sent later: by type. For a claim that reads
the further witness, or what the extractor makes, the rule is false: `further_not_know`,
`know_not_both` (Cb/G6/Rider/PscTest.lean).

An empty use. A and B are free letters in every statement here. Wherever the input joint's own
relaxed relation `relR` (any part of it: a relation that rides along, or the block's own claim) or
the output's `relR` gives the source, the statement with the rider follows from the block's own
theorem alone and says nothing: `hollow_own`, `hollow_own_on`, `hollow_out`. Two more empty forms:
`hollow_relOnly`, `hollow_in_relOnly`. A use of the rule should therefore prove the two sentences
that stand at `hollow_own`.

Limits. By `Binds` a round binds at most one coordinate, so the rules of this file do not reach a
verifier's message that is a whole point; for such a round see `point_rider`, `point_rider_both`
(Cb/G6/Rider/ShortN.lean), with the count g |E|^(g - 1). A rider whose coordinates are drawn partly
in one block and partly in the next is had on the composed term (`Binds.app`). The counts are
numbers of challenge values in a round, as everywhere in `Doomed`.

Of the fields of `GoodAt` only `acc` and `know` are proved anew; the others are the premise's, term
for term.

No definition of this file is computed by a verifier.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigLift
import Blocks.StageBoth
import Iop.State

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks
open scoped ENNReal

/-! ## 1. Two relations on one reduction, at knowledge soundness -/

section Know
variable {A B WA WB : Type}

/-- Two relations on one reduction, at knowledge soundness. If a reduction is knowledge sound from
RA to RB with counts ε, and sound from a set SA of input statements to a set SB of output statements
with counts ε' (asked at the statements with `on` alone), then it is knowledge sound from (RA and
SA) to (RB and SB), with the same extractor and, in each round, the larger of the two counts. The
reason: whether SA holds is decided by the input statement, before the first challenge, so for each
statement only one of the two cases is followed. -/
theorem know_both {K : Reduction A B} {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε ε' : Err K.shape} {SA : A → Prop} {SB : B → Prop}
    (h : K.Know on RA RB ext ε) (h' : K.Sound (fun a => ¬ on a ∨ SA a) SB ε') :
    K.Know on (fun a w => RA a w ∧ SA a) (fun b w => RB b w ∧ SB b) ext (Err.max ε ε') := by
  intro a ha
  by_cases hS : SA a
  · exact Doomed.max_left _ ε'
      (Doomed.mono _ _ (fun τ hτ b w hb hw => ⟨hτ b w hb hw.1, hS⟩) (h a ha))
  · exact Doomed.max_right _ ε
      (Doomed.mono _ _ (fun τ hτ b w hb hw => absurd hw.2 (hτ b hb))
        (h' a fun hn => hn.elim (fun x => x ha) hS))

end Know

/-! ## 2. The same at GoodAt -/

section GoodAt
variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- A joint with a second claim S. The claim reads the tuple of messages `w.1` and the statement; it
is added to the honest relation `rel` and to the relaxed relation `relR`; `on` and `core` stay. -/
@[reducible] def withRider {X W : Type} {E : ExtSpec} (A : IOR.Rels K X E (M × W))
    (S : M → X × E.Str → Prop) : IOR.Rels K X E (M × W) :=
  ⟨fun x y w => A.rel x y w ∧ S w.1 (x, y), fun a w => A.relR a w ∧ S w.1 a, A.on, A.core⟩

/-- The numbers of a block with the larger count in each round. The field `err` alone changes. -/
@[reducible] def numsMax {R : IOR Xi Ei Xo Eo} (P : IOR.Nums K R) (ε' : Err R.shape) : IOR.Nums K
    R :=
  ⟨Err.max P.err ε', P.pBad, P.pHid, P.bud, P.cov⟩

/-- The rule at `GoodAt`. For each fixed tuple m let the reduction be sound from SA m to SB m with
counts ε' (hs), and let every output statement of an input statement with SA m have SB m, on every
transcript (hf: the second claim adds no message and no check). Then the same reduction, honest
prover and extractor are `GoodAt` between the two joints with the second claim, with the larger
count in each round. Only the fields `acc` and `know` are proved anew; the other fields are the
premise's. Warning: A and B are free. SA is called the source, SB the target. Wherever the input
joint's `relR` without the rider (a relation that rides along, or the block's own claim) or the
output joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`; the
test of a use stands at `hollow_own`). -/
theorem goodAt_both {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop) (ε' : Err R.shape)
    (hs : ∀ m, R.red.Sound (fun a => ¬ A.on a ∨ SA m a) (SB m) ε')
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b) :
    GoodAt R H (withRider A SA) (withRider B SB) ext (numsMax P ε') where
  point := h.point
  isLocal := h.isLocal
  acc := fun x y w c ρ hR hρ => by
    obtain ⟨h1, h2⟩ := h.acc x y w c ρ hR.1 hρ
    refine ⟨h1, h2, ?_⟩
    have ho : R.red.out (x, y) ((H.strat w x c).run ρ).1 =
        some (((H.strat w x c).run ρ).2.1, R.imp y ((H.strat w x c).run ρ).1) := by
      show (R.out x y ((H.strat w x c).run ρ).1).map _ = _
      rw [h1]
      rfl
    rw [h.same w x c ρ]
    exact hf w.1 (x, y) _ _ hR.2 ho
  onOut := h.onOut
  keeps := h.keeps
  prBad := h.prBad
  cover := h.cover
  prCov := h.prCov
  same := h.same
  know := fun m => know_both (h.know m) (hs m)

/-- Second claims that say the same may be exchanged. -/
theorem goodAt_congr_rider {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R}
    {SA SA' : M → Xi × Ei.Str → Prop} {SB SB' : M → Xo × Eo.Str → Prop}
    (hA : ∀ m a, SA m a ↔ SA' m a) (hB : ∀ m b, SB m b ↔ SB' m b)
    (h : GoodAt R H (withRider A SA) (withRider B SB) ext P) :
    GoodAt R H (withRider A SA') (withRider B SB') ext P := by
  have e1 : SA = SA' := funext fun m => funext fun a => propext (hA m a)
  have e2 : SB = SB' := funext fun m => funext fun b => propext (hB m b)
  subst e1
  subst e2
  exact h

/-- If the second list lies below the block's own, round by round, the numbers do not change. -/
theorem numsMax_eq {R : IOR Xi Ei Xo Eo} (P : IOR.Nums K R) {ε' : Err R.shape}
    (h : Err.le ε' P.err) : numsMax P ε' = P := by
  show (⟨Err.max P.err ε', P.pBad, P.pHid, P.bud, P.cov⟩ : IOR.Nums K R) = P
  rw [Blocks.Err.max_eq_left_of_le h]

/-- The rule with no number changed: the second list of counts lies below the block's own, round by
round. Warning: A and B are free. SA is called the source, SB the target. Wherever the input joint's
`relR` without the rider (a relation that rides along, or the block's own claim) or the output
joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`; the test of
a use stands at `hollow_own`). -/
theorem goodAt_both_le {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop) (ε' : Err R.shape)
    (hε : Err.le ε' P.err) (hs : ∀ m, R.red.Sound (fun a => ¬ A.on a ∨ SA m a) (SB m) ε')
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b) :
    GoodAt R H (withRider A SA) (withRider B SB) ext P := by
  have h' := goodAt_both h SA SB ε' hs hf
  rwa [numsMax_eq P hε] at h'

/-- Consequence at `GoodAt`, with the reduction kept as a term: the like of the library's
`goodB_conseq` (Ior/Masked.lean), with the numbers unchanged. (The library's `goodAt_postMap` and
`goodAt_preMap`, Cb/Ld/LdSigStep.lean, change R into `R.post` and `R.pre`.) Mind that `rel` and
`relR` are treated apart: no clause of `GoodAt` compares them. What a statement with a second claim
says on soundness lies in the input's `relR`: the hypothesis hrA allows the source to be dropped
from it, and the statement is then empty (`hollow_in_relOnly`). -/
theorem goodAt_conseq {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A A' : IOR.Rels K Xi Ei (M × Wi)} {B B' : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (hA : ∀ x y w, A'.rel x y w → A.rel x y w) (hB : ∀ x y w, B.rel x y w → B'.rel x y w)
    (hoA : ∀ a, A'.on a → A.on a) (hoB : ∀ b, B.on b → B'.on b)
    (hrA : ∀ a w, A'.on a → A.relR a w → A'.relR a w) (hrB : ∀ b w, B'.relR b w → B.relR b w)
    (hcA : ∀ w, A'.core w = A.core w) (hcB : ∀ w, B'.core w = B.core w) :
    GoodAt R H A' B' ext P where
  point := g.point
  isLocal := g.isLocal
  acc := fun x y w c ρ hR hρ =>
    ⟨(g.acc x y w c ρ (hA x y w hR) hρ).1, hB _ _ _ (g.acc x y w c ρ (hA x y w hR) hρ).2⟩
  onOut := fun a τ b ha hb => hoB b (g.onOut a τ b (hoA a ha) hb)
  keeps := fun w x c ρ => by rw [hcA, hcB]; exact g.keeps w x c ρ
  prBad := g.prBad
  cover := fun w x => by rw [hcA]; exact g.cover w x
  prCov := g.prCov
  same := g.same
  know := fun m => (g.know m).conseq hoA (fun a wp ha h => hrA a (m, wp) ha h)
    fun b wp h => hrB b (m, wp) h

/-- Larger counts. The field `err` alone changes. -/
theorem goodAt_mono_err {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (ε : Err R.shape) (h : Err.le P.err ε) :
    GoodAt R H A B ext ⟨ε, P.pBad, P.pHid, P.bud, P.cov⟩ where
  point := g.point
  isLocal := g.isLocal
  acc := g.acc
  onOut := g.onOut
  keeps := g.keeps
  prBad := g.prBad
  cover := g.cover
  prCov := g.prCov
  same := g.same
  know := fun m => (g.know m).mono_err h

/-- The rule applied to its own result: two second claims on one block; the counts stay maxima.
Warning: A and B are free. SA and SA' are the sources, SB and SB' the targets. Wherever the input
joint's `relR` without the rider (a relation that rides along, or the block's own claim) or the
output joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`; the
test of a use stands at `hollow_own`). -/
theorem goodAt_both_twice {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (SA SA' : M → Xi × Ei.Str → Prop) (SB SB' : M → Xo × Eo.Str → Prop) (e e' : Err R.shape)
    (hs : ∀ m, R.red.Sound (fun a => ¬ A.on a ∨ SA m a) (SB m) e)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b)
    (hs' : ∀ m, R.red.Sound (fun a => ¬ A.on a ∨ SA' m a) (SB' m) e')
    (hf' : ∀ m a τ b, SA' m a → R.red.out a τ = some b → SB' m b) :
    GoodAt R H (withRider (withRider A SA) SA') (withRider (withRider B SB) SB') ext
      (numsMax (numsMax P e) e') :=
  goodAt_both (goodAt_both h SA SB e hs hf) SA' SB' e' hs' hf'

end GoodAt

/-! ## 3. A zero test on chosen challenges -/

section Rider
variable {κ E : Type} [Field E] [Fintype E] [DecidableEq κ]

/-- Soundness of a zero test on chosen challenges. G i is a family of polynomials fixed by the input
statement, of degree at most d k in variable k; b says which round's challenge is which variable. If
some member does not vanish in the bound variables, then it stays non-zero at the drawn point,
except for at most d k values of the challenge in the round that binds k. One list of counts serves
the whole family: a statement outside the source names one member that fails, before the first
challenge. By the library's `doomed_rider` (Blocks/StageBoth.lean). -/
theorem sound_rider {A B ι : Type} (K : Reduction A B) (b : Binds κ E K.shape) (hb : b.Inj)
    {d : κ → ℕ} {G : ι → A → (κ → E) → E} (hG : ∀ i a, Alg.DegLE d (G i a)) (z₀ : A → κ → E)
    {SB : B → Prop}
    (hout : ∀ a τ o, K.out a τ = some o → SB o → ∀ i, G i a (b.pt τ.rho (z₀ a)) = 0) :
    K.Sound (fun a => ∀ i, Vanishes (G i a) (z₀ a) b.vars) SB (b.err d) := by
  intro a ha
  obtain ⟨i, hi⟩ := not_forall.mp ha
  exact Doomed.mono _ _ (fun τ hτ o ho hS => hτ (hout a τ o ho hS i))
    (doomed_rider (hG i a) b hb (z₀ a) hi)

variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The rule for a zero test on chosen challenges: any block that is `GoodAt` stays so, as the same
term, with "every G i vanishes in the bound variables" added before and a clause SB added behind,
where hiff says that SB means: every G i is 0 at the point of the chosen challenges. z₀ holds the
coordinates that are bound elsewhere. Warning: A and B are free. Wherever the input joint's `relR`
without the rider (a relation that rides along, or the block's own claim) or the output joint's
`relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`; the test of a use
stands at `hollow_own`). -/
theorem goodAt_rider {ι : Type} {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (b : Binds κ E R.shape) (hb : b.Inj) {d : κ → ℕ} (G : ι → M → Xi × Ei.Str → (κ → E) → E)
    (hG : ∀ i m a, Alg.DegLE d (G i m a)) (z₀ : M → Xi × Ei.Str → κ → E)
    (SB : M → Xo × Eo.Str → Prop)
    (hiff : ∀ m a τ o, R.red.out a τ = some o →
      (SB m o ↔ ∀ i, G i m a (b.pt τ.rho (z₀ m a)) = 0)) :
    GoodAt R H (withRider A fun m a => ∀ i, Vanishes (G i m a) (z₀ m a) b.vars) (withRider B SB) ext
      (numsMax P (b.err d)) :=
  goodAt_both h (fun m a => ∀ i, Vanishes (G i m a) (z₀ m a) b.vars) SB (b.err d)
    (fun m => (sound_rider R.red b hb (G := fun i a => G i m a) (fun i a => hG i m a) (z₀ m)
      (fun a τ o ho hS => (hiff m a τ o ho).1 hS)).conseq (fun _ => Or.inr) (fun _ => id))
    (fun m a τ o hv ho => (hiff m a τ o ho).2 fun i => hv i _ fun _ hj => b.pt_of_notMem _ _ hj)

/-- The same for multilinear extensions of arrays on a cube, on any block whose output statement
holds the point. The block's own `GoodAt` is used as a black box; what is asked beside it is where
the challenges stand in the output statement. Warning: A and B are free. Wherever the input joint's
`relR` without the rider (a relation that rides along, or the block's own claim) or the output
joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`; the test of
a use stands at `hollow_own`). -/
theorem goodAt_cube {ι : Type} {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (b : Binds κ E R.shape) (hb : b.Inj) (g : ℕ) (σ : ℕ → κ)
    (hσ : ∀ t < g, ∀ t' < g, σ t = σ t' → t = t') (hT : ∀ t < g, σ t ∈ b.vars)
    (fi : ι → M → Xi × Ei.Str → ℕ → E) (fo : ι → M → Xo × Eo.Str → ℕ → E)
    (pt : Xo × Eo.Str → ℕ → E)
    (hf : ∀ i m a τ o, R.red.out a τ = some o → ∀ X < 2 ^ g, fo i m o X = fi i m a X)
    (hp : ∀ a τ o, R.red.out a τ = some o → ∀ t < g, pt o t = b.pt τ.rho (fun _ => 0) (σ t)) :
    GoodAt R H (withRider A fun m a => ∀ i, ∀ X < 2 ^ g, fi i m a X = 0)
      (withRider B fun m o => ∀ i, Blocks.ext g (fo i m o) (pt o) = 0) ext
      (numsMax P (b.err fun _ => 1)) := by
  refine goodAt_congr_rider (fun m a => ?_) (fun _ _ => Iff.rfl)
    (goodAt_rider h b hb (fun i m a z => Blocks.ext g (fi i m a) fun t => z (σ t))
      (fun i m a => degLE_ext_comp g (fi i m a) σ hσ) (fun _ _ _ => 0)
      (fun m o => ∀ i, Blocks.ext g (fo i m o) (pt o) = 0) fun m a τ o ho => ?_)
  · exact forall_congr' fun i =>
      ⟨fun hv => vanishes_ext hσ hT hv, fun hz => vanishes_ext_of_zero σ _ _ hz⟩
  · refine forall_congr' fun i => ?_
    rw [ext_congr (hf i m a τ o ho), ext_congr_point (hp a τ o ho)]

end Rider

/-! ## 4. Empty forms and empty uses -/

section Hollow

/-- A second claim in `rel` alone. Used only to name an empty form. -/
def riderRelOnly {K M X W : Type} {Ex : ExtSpec} (A : IOR.Rels K X Ex (M × W))
    (S : M → X × Ex.Str → Prop) : IOR.Rels K X Ex (M × W) :=
  ⟨fun x y w => A.rel x y w ∧ S w.1 (x, y), A.relR, A.on, A.core⟩

/-- An empty form. With the second claim in `rel` alone the rule holds of every `GoodAt` and every
pair with hf, at the block's own numbers, with no soundness of the second claim: it says nothing on
soundness. `withRider` puts the claim into `relR` too. -/
theorem hollow_relOnly {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest (M × Wi) (M × Wo)} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b) :
    GoodAt R H (riderRelOnly A SA) (riderRelOnly B SB) ext P where
  point := g.point
  isLocal := g.isLocal
  acc := fun x y w c ρ hR hρ => by
    obtain ⟨h1, h2⟩ := g.acc x y w c ρ hR.1 hρ
    refine ⟨h1, h2, ?_⟩
    rw [g.same w x c ρ]
    refine hf w.1 (x, y) ((H.strat w x c).run ρ).1 _ hR.2 ?_
    show (R.out x y ((H.strat w x c).run ρ).1).map _ = _
    rw [h1]
    rfl
  onOut := g.onOut
  keeps := g.keeps
  prBad := g.prBad
  cover := g.cover
  prCov := g.prCov
  same := g.same
  know := g.know

/-- A clause that B's honest relation already gives can be added to B for nothing. -/
theorem hollow_add {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}
    {R : IOR Xi Ei Xo Eo} {H : R.Honest (M × Wi) (M × Wo)}
    {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (h : GoodAt R H A B ext P)
    (SB : M → Xo × Eo.Str → Prop) (hB : ∀ x y w, B.rel x y w → SB w.1 (x, y)) :
    GoodAt R H A (withRider B SB) ext P where
  point := h.point
  isLocal := h.isLocal
  acc := fun x y w c ρ hR hρ =>
    ⟨(h.acc x y w c ρ hR hρ).1, (h.acc x y w c ρ hR hρ).2, hB _ _ _ (h.acc x y w c ρ hR hρ).2⟩
  onOut := h.onOut
  keeps := h.keeps
  prBad := h.prBad
  cover := h.cover
  prCov := h.prCov
  same := h.same
  know := fun m => (h.know m).conseq (fun _ => id) (fun _ _ _ => id) (fun _ _ hw => hw.1)

/-- An empty form. The source in `rel` alone, the target in `rel` and `relR`: the output joint is
the rule's own, so a look at the output joint shows nothing wrong; yet the statement holds of every
`GoodAt` and every pair with hf, at the block's own numbers. `goodAt_conseq` makes it out of the
rule's conclusion in one step (at the rule's numbers). -/
theorem hollow_in_relOnly {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest (M × Wi) (M × Wo)} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b) :
    GoodAt R H (riderRelOnly A SA) (withRider B SB) ext P :=
  goodAt_conseq (hollow_relOnly g SA SB hf) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ h => h)
    (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h.1) (fun _ => rfl) (fun _ => rfl)

/-- An empty use, by the input. If the input joint's own `relR` gives the source (any part of it: a
relation that rides along, or the block's own claim), the statement with the second claim holds at
the block's own numbers with no soundness of the second claim. So a use of the rule should prove two
sentences. (i) There are a statement a with `A.on a` and a witness (m, wp) with `A.relR a (m, wp)`
and not `SA m a`. (ii) For the same a and m there are a transcript τ, an output b with `R.red.out a
τ = some b`, and a wp' with `B.relR b (m, wp')` and `SB m b`. Sentence (i) refutes the premise of
`hollow_own_on`; (i) and (ii) together refute that of `hollow_out`. Sentence (ii) alone is not
enough: it can hold in an empty use, where it shows the block's own bad challenge. [An argument in
words; no theorem here.] -/
theorem hollow_own {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest (M × Wi) (M × Wo)} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b)
    (hA : ∀ a w, A.relR a w → SA w.1 a) :
    GoodAt R H (withRider A SA) (withRider B SB) ext P :=
  goodAt_conseq (hollow_in_relOnly g SA SB hf) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ h => h)
    (fun _ h => h) (fun a w _ h => ⟨h, hA a w h⟩) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl)

/-- The premise of `hollow_own` is needed only at the statements with `on`. -/
theorem hollow_own_on {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest (M × Wi) (M × Wo)} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b)
    (hA : ∀ a w, A.on a → A.relR a w → SA w.1 a) :
    GoodAt R H (withRider A SA) (withRider B SB) ext P :=
  goodAt_conseq (hollow_in_relOnly g SA SB hf) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ h => h)
    (fun _ h => h) (fun a w ho h => ⟨h, hA a w ho h⟩) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl)

/-- An empty use, by the output. If the output joint's `relR` gives the source, the statement with
the second claim holds at the block's own numbers with no soundness of the second claim. A relation
that rides along and comes out as it went in falls under this and under `hollow_own`. -/
theorem hollow_out {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest (M × Wi) (M × Wo)} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : IOR.Nums K R} (g : GoodAt R H A B ext P)
    (SA : M → Xi × Ei.Str → Prop) (SB : M → Xo × Eo.Str → Prop)
    (hf : ∀ m a τ b, SA m a → R.red.out a τ = some b → SB m b)
    (hB : ∀ m a τ b wp, R.red.out a τ = some b → B.relR b (m, wp) → SA m a) :
    GoodAt R H (withRider A SA) (withRider B SB) ext P :=
  { (hollow_in_relOnly g SA SB hf) with
    acc := (hollow_in_relOnly g SA SB hf).acc
    know := fun m a ha =>
      Doomed.mono _ _ (fun τ hτ b w hb hw => ⟨hτ b w hb hw.1, hB m a τ b w hb hw.1⟩)
          (g.know m a ha) }

end Hollow

end Cb.Rider

#print axioms Cb.Rider.know_both
#print axioms Cb.Rider.goodAt_both
#print axioms Cb.Rider.goodAt_both_le
#print axioms Cb.Rider.goodAt_both_twice
#print axioms Cb.Rider.goodAt_congr_rider
#print axioms Cb.Rider.goodAt_conseq
#print axioms Cb.Rider.goodAt_mono_err
#print axioms Cb.Rider.sound_rider
#print axioms Cb.Rider.goodAt_rider
#print axioms Cb.Rider.goodAt_cube
#print axioms Cb.Rider.hollow_relOnly
#print axioms Cb.Rider.hollow_add
#print axioms Cb.Rider.hollow_in_relOnly
#print axioms Cb.Rider.hollow_own
#print axioms Cb.Rider.hollow_own_on
#print axioms Cb.Rider.hollow_out
