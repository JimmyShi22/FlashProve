-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Walk.lean: the honest side of the kind "lookup" (K3): AT ANY
NUMBER OF PARTS OF KEYS: tools for walking the verifier's hearing along a course's rounds. General
in the face. Theorems.

  `varsAt_same`      two structures of points that agree in what a stage's job reads give the
                     stage's variables alike
  `varsAt_prefixP`   a stage's variables read the challenges in front of the stage alone
  `call_eqP`         CONDITIONAL ON `Fit`: a stage's call as it stands in the run is its shape with
                     the verifier's own variables at the run's points
  `all_eq`, `elem_at`, `draws_at`, `chals_at`   what the run's points read at the stage with a given
                     number in the row is read off the course's rounds from that stage on
  `off_levels`       rounds in front of a tree's level, counted from the tree's first level
  `hpt_of`           the points in front of a tree's levels, as the run of levels makes them: the
                     premise on points of `run_walk` (Honest/K3/Law/Walk.lean), from the text of
                     the run's points

No closed form of the number of rounds in front of a stage is used.

Limits. CONDITIONAL ON `Fit` and on `Cut` where they stand. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Index
import Johnson.Desc.ProofFile.Honest.K3.Parts.Numbered
import Johnson.Desc.ProofFile.Honest.K3.Law.LookHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.K3.Law

variable {W : Type}

/-! ## A stage's variables and call -/

theorem varsAt_same (f : LFace) (s : Stage) (p q : Pts) (h : SameForP f s p q) :
    varsAt f s p = varsAt f s q := by
  cases s with
  | key i m =>
    have h' : p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.keyPt i m = q.keyPt i m := h
    simp only [varsAt, h'.2.2]
  | tab l =>
    have h' : p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.tabPt l = q.tabPt l := h
    simp only [varsAt, h'.2.2]
  | leaves =>
    have h' : p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.tabPt f.d = q.tabPt f.d := h
    simp only [varsAt, h'.2.2]
  | bits =>
    have h' : p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.zeroPt = q.zeroPt := h
    simp only [varsAt, h'.2.2]
  | shift => rfl
  | alpha => rfl
  | tie j => rfl
  | split i => rfl
  | join => rfl
  | keyLine i m => rfl
  | tabLine l => rfl
  | zero => rfl

/-- **A stage's variables read the challenges in front of the stage alone.** -/
theorem varsAt_prefixP (f : LFace) (front ds : List Fmt.Drawn) (s : Stage) (hs : s ∈ stages f) :
    varsAt f s (ptsOf f front.length (front ++ ds.take (firstRound f s))) =
      varsAt f s (ptsOf f front.length (front ++ ds)) :=
  varsAt_same f s _ _ (same_cut f front ds s hs)

/-- **CONDITIONAL ON `Fit`: the stage's call as it stands in the run** is its shape with the
verifier's own variables at the run's points. -/
theorem call_eqP (R : Course W) (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call}
    (hk : s.call R.f = some k) : R.call s = { k with vs := varsAt R.f s R.pts } := by
  have hsh : shapeAt R.a s = k := by
    unfold shapeAt
    rw [hk]
    rfl
  show ({ (shapeAt R.a s) with
    vs := withPoints (shapeAt R.a s).vs
      (pointsAt R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds.take (firstRound R.f s)))) } : Call) =
    { k with vs := varsAt R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds)) }
  rw [hsh, withPoints_varsAt R.f s k _ _ hk hs hF.ok, ← hF.base,
    varsAt_prefixP R.f R.t.heard R.ds s hs]

/-! ## What the points read, off the rounds -/

section Read
variable {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x)

include C in
theorem all_eq : R.t.heard ++ R.ds = allOf R.t.heard x [] := by
  rw [← C.drawn]
  simp [allOf]

include hF C in
/-- The first element of a stage's first round. -/
theorem elem_at {n : Nat} {s : Stage} {r : Fmt.RoundView} {rest : List Fmt.RoundView}
    (hn : (stages R.f)[n]? = some s) (a : x.drop (off R.f n) = r :: rest) :
    elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base s) = e1 r := by
  unfold roundAt
  rw [all_eq C, ← hF.base, off_at hn, elemAt_all _ _ _ _ (drop_cons a).2.1]
  exact one_of_drop a

include hF C in
/-- All elements of a stage's first round. -/
theorem draws_at {n k : Nat} {s : Stage} {r : Fmt.RoundView} {rest : List Fmt.RoundView}
    (hn : (stages R.f)[n]? = some s) (a : x.drop (off R.f n) = r :: rest)
    (hk : r.drawn.elems.length = k) :
    drawsAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base s) k = r.drawn.elems.map E.ofTriple := by
  have hm := many_of_drop a
  unfold roundAt
  rw [all_eq C, ← hF.base, off_at hn,
    drawsAt_all _ _ _ _ _ (drop_cons a).2.1 (by rw [hm]; simpa using hk), hm]

include hF C in
/-- The challenges of a stage's variables. -/
theorem chals_at {n k : Nat} {s : Stage} (hn : (stages R.f)[n]? = some s)
    (hk : off R.f n + 1 + k ≤ x.length) :
    varChals R.f R.a.base (R.t.heard ++ R.ds) s k = seg x (off R.f n + 1) k := by
  rw [all_eq C, ← hF.base]
  exact varChals_all R.f _ _ x s _ k (off_at hn) hk

end Read

/-! ## A tree's levels -/

/-- Rounds in front of a tree's level, counted from the tree's first level. -/
theorem off_levels (f : LFace) (m0 : Nat) (sg ln : Nat → Stage) (i0 N : Nat)
    (hsg : ∀ l, l < N → (stages f)[i0 + 2 * l]? = some (sg l))
    (hln : ∀ l, l < N → (stages f)[i0 + 2 * l + 1]? = some (ln l))
    (hrounds : ∀ l, l < N → (sg l).rounds f = m0 + l + 3)
    (hr1 : ∀ l, l < N → (ln l).rounds f = 1) :
    ∀ l, l ≤ N → off f (i0 + 2 * l) = off f i0 + K m0 l
  | 0, _ => rfl
  | l + 1, h => by
    have hl : l < N := by omega
    have ih := off_levels f m0 sg ln i0 N hsg hln hrounds hr1 l (by omega)
    rw [show i0 + 2 * (l + 1) = i0 + 2 * l + 1 + 1 by omega, off_succ (hln l hl),
      off_succ (hsg l hl), ih, hrounds l hl, hr1 l hl]
    show _ = off f i0 + (K m0 l + (m0 + l + 4))
    omega

/-- **The points in front of a tree's levels, as the run of levels makes them.** pt: the points, by
level; hptS: the text of the run's points behind a level. -/
theorem hpt_of {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x) (m0 : Nat)
    (orders : Nat → List Nat) (sg ln : Nat → Stage) (i0 : Nat) (pt : Nat → Array E) (N : Nat)
    (hsg : ∀ l, l < N → (stages R.f)[i0 + 2 * l]? = some (sg l))
    (hln : ∀ l, l < N → (stages R.f)[i0 + 2 * l + 1]? = some (ln l))
    (hrounds : ∀ l, l < N → (sg l).rounds R.f = m0 + l + 3)
    (hr1 : ∀ l, l < N → (ln l).rounds R.f = 1)
    (hptS : ∀ l, l < N → pt (l + 1) = behind (m0 + l) (orders (m0 + l))
      (varChals R.f R.a.base (R.t.heard ++ R.ds) (sg l) (m0 + l))
      (elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (ln l)))) :
    ∀ l, l ≤ N → pt l = lastPt m0 orders (pt 0) (x.drop (off R.f i0)) 0 l
  | 0, _ => rfl
  | l + 1, h => by
    have hl : l < N := by omega
    have o1 := off_levels R.f m0 sg ln i0 N hsg hln hrounds hr1 l (by omega)
    have o2 : off R.f (i0 + 2 * l + 1) = off R.f i0 + K m0 l + (m0 + l + 3) := by
      rw [off_succ (hsg l hl), o1, hrounds l hl]
    have o3 : off R.f (i0 + 2 * l + 1 + 1) = off R.f (i0 + 2 * l + 1) + 1 := by
      rw [off_succ (hln l hl), hr1 l hl]
    have hle := off_le R.f (i0 + 2 * l + 1 + 1)
    rw [← C.len] at hle
    have hlt : off R.f (i0 + 2 * l + 1) < x.length := by omega
    rw [hptS l hl, chals_at hF C (hsg l hl) (by omega), lastPt_drop]
    have e2 : elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (ln l)) =
        one x (off R.f (i0 + 2 * l + 1)) := by
      unfold roundAt
      rw [all_eq C, ← hF.base, off_at (hln l hl), elemAt_all _ _ _ _ hlt]
    rw [e2, o1, o2]
    rfl

#print axioms ProofFile.Honest.K3.Parts.varsAt_same
#print axioms ProofFile.Honest.K3.Parts.varsAt_prefixP
#print axioms ProofFile.Honest.K3.Parts.call_eqP
#print axioms ProofFile.Honest.K3.Parts.all_eq
#print axioms ProofFile.Honest.K3.Parts.elem_at
#print axioms ProofFile.Honest.K3.Parts.draws_at
#print axioms ProofFile.Honest.K3.Parts.chals_at
#print axioms ProofFile.Honest.K3.Parts.off_levels
#print axioms ProofFile.Honest.K3.Parts.hpt_of

end ProofFile.Honest.K3.Parts
