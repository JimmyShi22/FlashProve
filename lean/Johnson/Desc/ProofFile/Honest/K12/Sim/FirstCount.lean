-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstCount.lean: a count. What the first member of a proximity
test shows (`firstMember`, Sim/Row.lean), where the first fold's fresh table has come earlier, holds
2 k + 1 scalars and no list of columns; so does what its simulator yields (`firstSim`,
Sim/Sims.lean). k: the first stage's number of fold rounds.

  `scalars`, `columns`   how many items in the clear a list of shown rounds holds; for how many
                 roots it lists columns
  `sum_const`, `count_laidAs`   2 k + 1 values, laid as a fold's rounds show them (`laidAs`,
                 Sim/FoldLaw.lean), are 2 k + 1 scalars and no list of columns
  `first_count`  what the member shows, played alone, at every side, state of the run, random values
                 and positions, at challenges of the declared form
  `sim_count`    what the simulator yields, at all its arguments

By what. `shows_first` (Sim/ShowsFirst.lean), `first_text` and `tells_first` (Sim/ExactFirst.lean).

Limits. A count of items. It says nothing on the items' values or on how they are distributed. What
is asked is `FirstPub` (Sim/ExactFirst.lean), all of it public, and that the challenges have the
declared form. All limits of Sim/ExactFirst.lean stand. Nothing on completeness, soundness or
hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE)
open H2K.JointK (laidOf)
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type}

/-- How many items in the clear a list of shown rounds holds. -/
def scalars (l : List Shown) : ℕ := (l.map fun x => x.vals.length).sum

/-- For how many roots a list of shown rounds lists columns. -/
def columns (l : List Shown) : ℕ := (l.map fun x => x.cols.length).sum

theorem sum_const (k c : ℕ) : ((List.range k).map fun _ => c).sum = k * c := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Nat.succ_mul]
    simp

theorem count_laidAs (k : ℕ) (x : ℕ → GE) :
    scalars (laidAs k x) = 2 * k + 1 ∧ columns (laidAs k x) = 0 := by
  unfold scalars columns laidAs
  rw [List.map_cons, List.map_cons, List.map_map, List.map_cons, List.map_cons, List.map_map]
  constructor
  · show 0 + (1 + ((List.range k).map fun _ => 2).sum) = 2 * k + 1
    rw [sum_const]
    omega
  · show 0 + (0 + ((List.range k).map fun _ => 0).sum) = 0
    rw [sum_const]
    omega

/-- **What the first member shows: 2 k + 1 scalars and no list of columns.** -/
theorem first_count (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (hfr : J.fresh.isNone = false) (T : FirstPub J Js) (m : ProofFile.Honest.Mid W X)
    (ds : List Fmt.Drawn) (hfit : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true)
    (asks : List (List (List ℕ))) (c : (firstMember J Js : Member V W X Pb).part.Coins) :
    ∃ l, σ.shows φ (firstMember J Js) c m ds asks = some l ∧ scalars l = 2 * J.s₀.k + 1 ∧
      columns l = 0 := by
  obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
    have hform := T.form
    unfold formPubB at hform
    cases hs : J.p.nums.stages with
    | nil => rw [hs] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs] at hform; cases hform
      | cons b r => exact ⟨a, b, r, rfl⟩
  have FP := formPub_of_B J.p s next rest hst T.form
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have h0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  have hlen : ds.length = firstLen J.p.nums.stages := by
    have h := drawsFit_length _ _ hfit
    rw [h, List.length_map]
    show ((laidOf J.p).take _).length = _
    rw [List.length_take]
    exact Nat.min_eq_left T.enough
  rw [shows_first φ σ J Js s next rest m (byNo ds) ds
    ⟨hst, T.enough, FP.sorts, T.tables, hlen, fun n h => (List.getD_eq_getElem _ _ h).symm⟩ c asks,
    first_text J hfr s next rest hst hk, h0, hk]
  exact ⟨_, rfl, count_laidAs _ _⟩

/-- **What the simulator yields: as many.** -/
theorem sim_count (Js : SimJob Pb) (ho : Js.own = false) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : Js.p.nums.stages = s :: next :: rest) (pb : Pb)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (c : Cs (firstSim Js).takes) :
    ∃ l, (firstSim Js).tell pb front ds asks c = some l ∧ scalars l = 2 * s.k + 1 ∧
      columns l = 0 := by
  obtain ⟨p, own, r₀, op⟩ := Js
  simp only at ho hst
  subst ho
  rw [tells_first p r₀ op s next rest hst pb front ds asks c]
  exact ⟨_, rfl, count_laidAs _ _⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.scalars
#print axioms ProofFile.Honest.K12.Light.columns
#print axioms ProofFile.Honest.K12.Light.sum_const
#print axioms ProofFile.Honest.K12.Light.count_laidAs
#print axioms ProofFile.Honest.K12.Light.first_count
#print axioms ProofFile.Honest.K12.Light.sim_count
