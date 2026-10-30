-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/UsesK.lean: the rule for arrays on cubes for a block whose output statement holds a
point and a kept state; three shapes of rider at `KnowAt`, for any block that has the rule.

Definitions, statements and proofs. No protocol of its own.

Main names:
  `SelIn n g sel`: for each member of a family a choice of different coordinates among 0, .., n.
  `RidesAt R A B xt ε n sI sO pt`: a proposition on a reduction R with joints A, B, extractor xt and
    counts ε: for every family of arrays that read a kept state and the tuple of messages, each
    member on its own cube at its own choice of coordinates of the point pt that the output
    statement holds, R has `KnowAt` from (A and "every array is 0 on its cube") to (B and "every
    extension is 0 at the chosen coordinates"), with xt and ε.
  `ridesAt_of_carries`: a block with the bundle `Carries` (Cb/G6/Rider/Carrier.lean) whose reader is
    pt read backwards, that hands the kept state on and has `KnowAt` between A and B, has the rule.
    A, B and xt are any: the rule applies to its own result.
  `know_cubes`, `know_of_carries`: the same with round-by-round knowledge soundness alone as premise
    and conclusion.
  `oneHot_of`: for each member of a family, nE maps sum to 1 at every vertex; the pick is an
    interval off, .., off + lt - 1.
  `two_lines_of`: two conditions at the vertices that a public indicator marks; the same kind of
    pick.
  `denom_of`: on a cube (block | head | position), a denominator equals a row sum over tiles, at the
    blocks below NP; the pick `selAtt` (Cb/G6/Rider/Picks.lean) is no interval and names coordinate
    0 of the point where iota < nb.
  `knowAt_congr_rider`: two joints with riders that say the same.

The three shapes are statements of form. Every map (sl; cost, l3, l4; den, wtM, wtD, rowOf) is a
free letter: any function of state and tuple. None of the three has an inhabitant or a test against
emptiness of its own in this file.

Limits: A and B are free in every statement. Wherever A's relaxed relation or B's gives the source,
the statement follows from the block's own `KnowAt` alone and says nothing (`knowAt_hollow_own`,
`knowAt_hollow_out`, Cb/G6/Rider/KnowAt.lean). Nothing on whether a later stage takes a target up;
nothing on an honest prover.

Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Rider.KnowAt
import Cb.G6.Rider.Picks

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks TWhole Finset

variable {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- Two joints with riders that say the same. -/
theorem knowAt_congr_rider {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    {SA SA' : M → Xi × Ei.Str → Prop} {SB SB' : M → Xo × Eo.Str → Prop}
    (hA : ∀ m a, SA m a ↔ SA' m a) (hB : ∀ m b, SB m b ↔ SB' m b)
    (h : KnowAt R (withRider A SA) (withRider B SB) xt ε) :
    KnowAt R (withRider A SA') (withRider B SB') xt ε := by
  obtain rfl : SA = SA' := funext fun m => funext fun a => propext (hA m a)
  obtain rfl : SB = SB' := funext fun m => funext fun b => propext (hB m b)
  exact h

/-- The choices: for each member different coordinates, each at most n. -/
def SelIn {ι : Type} (n : ℕ) (g : ι → ℕ) (sel : ι → ℕ → ℕ) : Prop :=
  ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧ ∀ t < g i, sel i t ≤ n

variable {E : Type} [Field E] {St : Type}

/-- The block has the rule for arrays on cubes: any family, cube and choice per member, the choices
among the coordinates 0, .., n of the point pt in the output statement; the arrays read the state sI
of the input statement, which the output statement holds as sO. -/
def RidesAt (R : IOR Xi Ei Xo Eo) (A : IOR.Rels K Xi Ei (M × Wi)) (B : IOR.Rels K Xo Eo (M × Wo))
    (xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (n : ℕ) (sI : Xi → St)
    (sO : Xo → St) (pt : Xo → ℕ → E) : Prop :=
  ∀ (ι : Type) (g : ι → ℕ) (sel : ι → ℕ → ℕ), SelIn n g sel → ∀ f : ι → St → M → ℕ → E,
    KnowAt R (withRider A fun m a => OnCubes g f (sI a.1) m)
      (withRider B fun m b => AtCoords g sel f (sO b.1) (pt b.1) m) xt ε

section Uses
variable {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
  {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape} {n : ℕ} {sI : Xi → St}
  {sO : Xo → St} {pt : Xo → ℕ → E}

/-- "The entries sum to 1 at every vertex", for each member lm of a family, all at one point, in
linear form. Source: for each lm and each X < 2^lt the nE values sl lm st m k X sum to 1. Target:
for each lm the nE multilinear extensions, at the coordinates off, .., off + lt - 1 of the point,
sum to 1. The cube is full: the source speaks of every X < 2^lt. With nE = 0 the source is false
wherever the family is inhabited; an empty family makes source and target true. Warning: A and B are
free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem oneHot_of (h : RidesAt R A B xt ε n sI sO pt) {Lm : Type} (lt nE off : ℕ)
    (hoff : off + lt ≤ n + 1) (sl : Lm → St → M → Fin nE → ℕ → E) :
    KnowAt R
      (withRider A fun m a => ∀ lm, ∀ X < 2 ^ lt, ∑ k, sl lm (sI a.1) m k X = 1)
      (withRider B fun m b =>
        ∀ lm, ∑ k, ext lt (sl lm (sO b.1) m k) (fun t => pt b.1 (off + t)) = 1) xt ε := by
  have h1 := h Lm (fun _ => lt) (fun _ t => off + t)
    (fun _ => ⟨fun t _ t' _ e => Nat.add_left_cancel e, fun t ht => by
      show off + t ≤ n
      have : t < lt := ht
      omega⟩)
    (fun lm st m X => ∑ k, sl lm st m k X - 1)
  refine knowAt_congr_rider (fun m a => ?_) (fun m b => ?_) h1
  · exact forall_congr' fun lm => forall₂_congr fun X _ => sub_eq_zero
  · refine forall_congr' fun lm => ?_
    show ext lt (fun X => ∑ k, sl lm (sO b.1) m k X - 1) (fun t => pt b.1 (off + t)) = 0 ↔ _
    rw [ext_sub lt (fun X => ∑ k, sl lm (sO b.1) m k X) (fun _ => 1), ext_sum Finset.univ,
      ext_const]
    exact sub_eq_zero

/-- Two conditions tested at one point, with a public indicator inside the arrays. cost st X says
whether vertex X counts; it reads the state alone. l3 and l4 are the two conditions' defects, any
maps of state and tuple. Source: at each X < 2^lt that counts, both defects are 0. Target: the
extensions of the two arrays "defect where X counts, else 0" are 0 at the coordinates off, .., off +
lt - 1 of the point. The indicator is part of the arrays: without it the source would also speak of
the vertices that do not count. If no vertex counts, both arrays are 0 everywhere and the rider says
nothing (two_lines_none). Warning: A and B are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem two_lines_of (h : RidesAt R A B xt ε n sI sO pt) (lt off : ℕ) (hoff : off + lt ≤ n + 1)
    (cost : St → ℕ → Bool) (l3 l4 : St → M → ℕ → E) :
    KnowAt R
      (withRider A fun m a =>
        ∀ X < 2 ^ lt, cost (sI a.1) X = true → l3 (sI a.1) m X = 0 ∧ l4 (sI a.1) m X = 0)
      (withRider B fun m b =>
        ext lt (fun X => if cost (sO b.1) X = true then l3 (sO b.1) m X else 0)
            (fun t => pt b.1 (off + t)) = 0 ∧
          ext lt (fun X => if cost (sO b.1) X = true then l4 (sO b.1) m X else 0)
            (fun t => pt b.1 (off + t)) = 0) xt ε := by
  have h1 := h Bool (fun _ => lt) (fun _ t => off + t)
    (fun _ => ⟨fun t _ t' _ e => Nat.add_left_cancel e, fun t ht => by
      show off + t ≤ n
      have : t < lt := ht
      omega⟩)
    (fun i st m X => if cost st X = true then (if i = true then l4 st m X else l3 st m X) else 0)
  refine knowAt_congr_rider (fun m a => ?_) (fun m b => ?_) h1
  · constructor
    · intro hh X hX hc
      have h3 := hh false X hX
      have h4 := hh true X hX
      simp only [hc, if_true] at h3 h4
      exact ⟨by simpa using h3, h4⟩
    · intro hh i X hX
      show (if cost (sI a.1) X = true then
        (if i = true then l4 (sI a.1) m X else l3 (sI a.1) m X) else 0) = 0
      by_cases hc : cost (sI a.1) X = true
      · rw [if_pos hc]
        cases i
        · simpa using (hh X hX hc).1
        · simpa using (hh X hX hc).2
      · rw [if_neg hc]
  · constructor
    · intro hh
      have h3 := hh false
      have h4 := hh true
      exact ⟨by simpa using h3, by simpa using h4⟩
    · intro hh i
      cases i
      · simpa using hh.1
      · simpa using hh.2

/-- "The denominator is the row sum at every block, head and position." Source: at every block P <
NP, every g < 2^lgk, every i < 2^lt: den = rowSumA. Target, in linear form: the extension of the
(cut) denominators equals the extension of the (cut) row sums, both at the coordinates selAtt of the
point. Fixed: the cube of dimension nb + lgk + lt, sel := selAtt dT rK iota nb, the indicator. Free,
under the stated arithmetic: the sizes; rowOf; the maps den, wtM, wtD, any readings of state and
tuple. Warning: A and B are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem denom_of (h : RidesAt R A B xt ε n sI sO pt)
    (dT rK iota nb lgk lt ldh nS nT B' NP : ℕ) (hv : n + 1 = dT + rK) (h1 : iota ≤ rK)
    (hb : nb + 1 + lgk + lt + ldh = dT + iota) (hN : NP ≤ 2 ^ nb)
    (rowOf : ℕ → ℕ → ℕ) (den : St → M → ℕ → ℕ → ℕ → E)
    (wtM : St → M → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E) (wtD : St → M → ℕ → ℕ → ℕ → ℕ → ℕ → E) :
    KnowAt R
      (withRider A fun m a =>
        ∀ P < NP, ∀ g < 2 ^ lgk, ∀ i < 2 ^ lt,
          den (sI a.1) m P g i = rowSumA nS nT B' rowOf wtM wtD (sI a.1) m P g i)
      (withRider B fun m b =>
        ext (nb + lgk + lt) (onPieces lgk lt NP (den (sO b.1) m))
            (fun t => pt b.1 (selAtt dT rK iota nb t)) =
          ext (nb + lgk + lt) (onPieces lgk lt NP (rowSumA nS nT B' rowOf wtM wtD (sO b.1) m))
            (fun t => pt b.1 (selAtt dT rK iota nb t))) xt ε := by
  obtain ⟨hs, hl⟩ := selAtt_ok (dT := dT) (rK := rK) (iota := iota) (nb := nb) (lgk := lgk)
      (lt := lt) (ldh := ldh) h1 hb
  have h2 := h Unit (fun _ => nb + lgk + lt) (fun _ => selAtt dT rK iota nb)
    (fun _ => ⟨hs, fun t ht => by
      show selAtt dT rK iota nb t ≤ n
      have := hl t ht
      omega⟩)
    (fun _ st m => onPieces lgk lt NP fun P g i =>
      den st m P g i - rowSumA nS nT B' rowOf wtM wtD st m P g i)
  have hsub : ∀ (st : St) (m : M) (X : ℕ),
      onPieces lgk lt NP (fun P g i => den st m P g i - rowSumA nS nT B' rowOf wtM wtD st m P g i)
          X =
        onPieces lgk lt NP (den st m) X -
          onPieces lgk lt NP (rowSumA nS nT B' rowOf wtM wtD st m) X := by
    intro st m X
    unfold onPieces
    split
    · rfl
    · rw [sub_zero]
  refine knowAt_congr_rider (fun m a => ?_) (fun m b => ?_) h2
  · show (∀ _ : Unit, ∀ X < 2 ^ (nb + lgk + lt), onPieces lgk lt NP _ X = 0) ↔ _
    rw [forall_const, onPieces_zero hN]
    exact forall₂_congr fun P _ => forall₂_congr fun g _ => forall₂_congr fun i _ => sub_eq_zero
  · show (∀ _ : Unit, ext (nb + lgk + lt) (onPieces lgk lt NP _) _ = 0) ↔ _
    rw [forall_const, ext_congr (fun X _ => hsub (sO b.1) m X), ext_sub]
    exact sub_eq_zero

end Uses

/-! ## The rule at the clause know alone; the rule from the bundle -/

section Know
variable [Fintype E]

/-- The rule for arrays on cubes at the clause know alone: knowAt_cubes (Cb/G6/Rider/KnowAt.lean)
without the three clauses on the verifier, for a statement whose premise is round-by-round knowledge
soundness and nothing else. Warning: A and B are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem know_cubes {ι : Type} {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wi)}
    {B : IOR.Rels K Xo Eo (M × Wo)} {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : ∀ m, R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (xt m)
      ε)
    {β : Binds ℕ E R.shape} {T : ℕ → Prop} {r : Xo → ℕ → E} (C : Carries R β ε T r) (g : ι → ℕ)
    (sel : ι → ℕ → ℕ) (hsel : SelOK T g sel) (fi : ι → M → Xi × Ei.Str → ℕ → E)
    (fo : ι → M → Xo × Eo.Str → ℕ → E)
    (hf : ∀ i m a τ b, R.red.out a τ = some b → ∀ X < 2 ^ g i, fo i m b X = fi i m a X) (m : M) :
    R.red.Know A.on (fun a wp => A.relR a (m, wp) ∧ ∀ i, ∀ X < 2 ^ g i, fi i m a X = 0)
      (fun b wp => B.relR b (m, wp) ∧ ∀ i, ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0)
      (xt m) ε := by
  have G := know_both (h m) (SA := fun a => ∀ i, ∀ X < 2 ^ g i, fi i m a X = 0)
    (SB := fun b => ∀ i, ext (g i) (fo i m b) (fun t => r b.1 (sel i t)) = 0)
    (ε' := β.err fun _ => 1)
    ((sound_rider R.red β C.inj (d := fun _ => 1)
      (G := fun i a (z : ℕ → E) => ext (g i) (fi i m a) fun t => z (sel i t))
      (fun i a => degLE_ext_comp (g i) (fi i m a) (sel i) (hsel i).1) (fun _ _ => 0)
      (fun a τ b hb hS i => by
        have h1 := hS i
        rw [ext_congr (hf i m a τ b hb), ext_congr_point (fun t ht =>
          (C.rd a.1 a.2 τ b.1 (fun _ => 0) (red_out hb) (sel i t) ((hsel i).2 t ht)).symm)
            (fi i m a)] at h1
        exact h1)).conseq
      (fun a hv => Or.inr fun i =>
        vanishes_ext (hsel i).1 (fun t ht => C.mem _ ((hsel i).2 t ht)) (hv i)) (fun _ => id))
  rwa [Blocks.Err.max_eq_left_of_le C.le] at G

/-- A choice of coordinates among 0, .., n, counted from n down. -/
theorem selIn_rev {ι : Type} {n : ℕ} {g : ι → ℕ} {sel : ι → ℕ → ℕ} (hsel : SelIn n g sel) :
    SelOK (fun k => k ≤ n) g fun i t => n - sel i t :=
  fun i => ⟨fun t ht t' ht' e => (hsel i).1 t ht t' ht' (by
      have h1 := (hsel i).2 t ht
      have h2 := (hsel i).2 t' ht'
      have e' : n - sel i t = n - sel i t' := e
      omega), fun _ _ => Nat.sub_le _ _⟩

omit [Fintype E] in
theorem atCoords_rev {ι : Type} {n : ℕ} {g : ι → ℕ} {sel : ι → ℕ → ℕ} (hsel : SelIn n g sel)
    (f : ι → St → M → ℕ → E) (st : St) (pt : ℕ → E) (m : M) :
    AtCoords g sel f st pt m ↔
      ∀ i, ext (g i) (f i st m) (fun t => pt (n - (n - sel i t))) = 0 :=
  forall_congr' fun i => Eq.congr_left (ext_congr_point (g := g i) (z := fun t => pt (sel i t))
    (z' := fun t => pt (n - (n - sel i t)))
    (fun t ht => by
      show pt (sel i t) = pt (n - (n - sel i t))
      rw [Nat.sub_sub_self ((hsel i).2 t ht)]) (f i st m))

section Carried
variable {R : IOR Xi Ei Xo Eo} {β : Binds ℕ E R.shape} {ε : Err R.shape} {n : ℕ}
  {pt : Xo → ℕ → E} {sI : Xi → St} {sO : Xo → St}

/-- A block has the rule if its output statement holds a point pt of n + 1 coordinates each of which
is a single challenge (the bundle, its reader pt read backwards, at the block's own counts) and a
state that it hands on, and it has KnowAt between A and B. A, B and xt are any, so the rule applies
to its own result: two families of different shape ride on one block. Warning: A and B are free
(knowAt_hollow_own, knowAt_hollow_out). -/
theorem ridesAt_of_carries (C : Carries R β ε (fun k => k ≤ n) fun b k => pt b (n - k))
    (hp : R.Passes sI sO) {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} (h : KnowAt R A B xt ε) :
    RidesAt R A B xt ε n sI sO pt := fun _ g sel hsel f =>
  knowAt_congr_rider (fun _ _ => Iff.rfl)
    (fun m b => (atCoords_rev hsel f (sO b.1) (pt b.1) m).symm)
    (knowAt_cubes h C g (fun i t => n - sel i t) (selIn_rev hsel) (fun i m a => f i (sI a.1) m)
      (fun i m b => f i (sO b.1) m) fun i m a τ b hb X _ => by
        show f i (sO b.1) m X = f i (sI a.1) m X
        rw [hp _ _ _ _ (red_out hb)])

/-- The same with round-by-round knowledge soundness alone as premise and conclusion. -/
theorem know_of_carries (C : Carries R β ε (fun k => k ≤ n) fun b k => pt b (n - k))
    (hp : R.Passes sI sO) {A : IOR.Rels K Xi Ei (M × Wi)} {B : IOR.Rels K Xo Eo (M × Wo)}
    {xt : M → Xi × Ei.Str → Tr R.shape → Wo → Wi}
    (h : ∀ m, R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (xt m)
      ε)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelIn n g sel) (f : ι → St → M → ℕ → E)
    (m : M) :
    R.red.Know A.on (fun a wp => A.relR a (m, wp) ∧ OnCubes g f (sI a.1) m)
      (fun b wp => B.relR b (m, wp) ∧ AtCoords g sel f (sO b.1) (pt b.1) m) (xt m) ε :=
  (know_cubes h C g (fun i t => n - sel i t) (selIn_rev hsel) (fun i m a => f i (sI a.1) m)
    (fun i m b => f i (sO b.1) m) (fun i m a τ b hb X _ => by
      show f i (sO b.1) m X = f i (sI a.1) m X
      rw [hp _ _ _ _ (red_out hb)]) m).conseq (fun _ ha => ha) (fun _ _ _ hw => hw)
    (fun b _ hw => ⟨hw.1, (atCoords_rev hsel f (sO b.1) (pt b.1) m).1 hw.2⟩)

end Carried

end Know

end Cb.Rider

#print axioms Cb.Rider.knowAt_congr_rider
#print axioms Cb.Rider.oneHot_of
#print axioms Cb.Rider.two_lines_of
#print axioms Cb.Rider.denom_of
#print axioms Cb.Rider.know_cubes
#print axioms Cb.Rider.ridesAt_of_carries
#print axioms Cb.Rider.know_of_carries
