-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/PscEnds.lean: the masked sumcheck's law over the plain record
(OnBytes/Desc/First/P1/PscSound.lean, PscSoundK.lean) at two kinds of summand whose end terms are
shown UNDER MASKS THAT MAY DEPEND ON THE CHALLENGES. Statements and proofs.

Why. OnBytes/Desc/First/P1/PscProducts.lean serves end values each of which is one table's extension
plus beta times ONE mask entry. Two sumchecks of a layers' sub-proof are otherwise. In the batched
sumcheck each of the two end terms is a combination of several shown values UNDER PUBLIC
COEFFICIENTS AT THE RUN's OWN CHALLENGES: so its mask is that combination of mask entries, a
function of the challenges. In the second token sumcheck one factor of each product is not shown at
all: the summand is affine in the further variable, and its value at the end point is no element
that the verifier computes.

  `cutY`: a function of the challenges in front and of the further challenge, as a function of the
    whole list; `cutY_snoc`.
  `two_ends_sound`: FIXED FIRST: the variables' weights ws (two-point, at least three coefficients);
    two tables A, B over them; two functions ma, mb of the challenges; the hiding coefficients; T,
    Cv. A record as in `psc_sound` over ws and the further variable (read at 0, three coefficients),
    whose row at the end term S0 is 0, where S0 reads as (A's extension + beta * ma) * (B's
    extension + beta * mb) at the challenges, and no bad element was drawn: then Cv is the sum over
    the cube, under the weights, of A * B.
  `affine_end_sound`: the further variable with TWO coefficients; FIXED FIRST: a summand s of the
    challenges with its sum sigma (`IsSum`), a function m of the challenges. The row is made WITHOUT
    the summand, a form u; kt is a value with kt * eps = -(u's value). If kt = s + beta * m at the
    challenges and no bad element was drawn, Cv = sigma.

ma, mb, m STAND BEFORE THE BAD SETS: they may read the challenges that are handed to them and what
is fixed first (mask entries, public numbers), nothing else of the run. Limits: those of
PscSound.lean. That S0 | kt is as asked is the caller's: from the ledger's world (shown = hidden +
beta * mask) and the truth of the hidden end values: further claims. hY: that the further variable's
weight passes its two tests is a premise.
-/
import OnBytes.Desc.First.P1.SumSnoc
import OnBytes.Desc.First.P1.PscSoundK
import OnBytes.Desc.First.P1.PscProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-- A function of the challenges in front and of the last one, as a function of the whole list. -/
def cutY (f : List K → K → K) (l : List K) : K := f l.dropLast (l.getLastD 0)

theorem cutY_snoc (f : List K → K → K) (rs : List K) (y : K) : cutY f (rs ++ [y]) = f rs y := by
  unfold cutY
  rw [List.dropLast_concat, List.getLastD_concat]

theorem held_snoc {ws : List OnBytes.Psc.Weight} {w : OnBytes.Psc.Weight}
    (hw : ∀ v ∈ ws, Held v) (hY : Held w) : ∀ v ∈ ws ++ [w], Held v := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact hw v h
  · rw [List.mem_singleton] at h
    rw [h]
    exact hY

/-- **Two end terms, each under a mask that may depend on the challenges.** -/
theorem two_ends_sound (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w)
    (xs : List (K × K)) (h3 : Twos 3 (ws.map (wtOf ρ)) xs) (A B : List Bool → K)
    (ma mb : List K → K) (hcoef : ℕ → K) (T Cv : K)
    (hY : Held (OnBytes.Psc.Weight.atZero 3)) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((ws ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd) (y : Rnd) (S0 : E),
        ms.map (·.1) = ws → y.1 = OnBytes.Psc.Weight.atZero 3 →
        (∀ x ∈ ms ++ [y], x.2.1.length + 1 = x.1.d) →
        p.vars.toList = ws ++ [OnBytes.Psc.Weight.atZero 3] →
        p.r.toList = (ms ++ [y]).map (·.2.2) →
        p.claim = claimAfter (ms ++ [y]) (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (ws ++ [OnBytes.Psc.Weight.atZero 3]) →
          W.slot (p.first + i) = hcoef i) →
        (p.rowForm S0 {}).value ρ W = 0 →
        ρ.val S0 =
          (mle ws.length A (ms.map fun x => ρ.val x.2.2) +
              ρ.val y.2.2 * ma (ms.map fun x => ρ.val x.2.2)) *
            (mle ws.length B (ms.map fun x => ρ.val x.2.2) +
              ρ.val y.2.2 * mb (ms.map fun x => ρ.val x.2.2)) →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps))
          (movesP ρ (ms ++ [y]) (addE mu (mulE p.eps p.target)))) →
        Cv = tot xs fun b => A b * B b := by
  have hmul := isSum_mul (ws.map (wtOf ρ)) xs A B h3
  rw [List.length_map] at hmul
  have hS := isSum_Y_mul (wtOf ρ (OnBytes.Psc.Weight.atZero 3)) (two_atZero ρ 3 (by omega))
    (le_refl 3) (ws.map (wtOf ρ)) (mle ws.length A) (mle ws.length B) ma mb _ hmul
    (cutY fun rs y => (mle ws.length A rs + y * ma rs) * (mle ws.length B rs + y * mb rs))
    (fun rs y => cutY_snoc _ rs y)
  have hmap : ws.map (wtOf ρ) ++ [wtOf ρ (OnBytes.Psc.Weight.atZero 3)] =
      (ws ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ) := by simp
  rw [hmap] at hS
  obtain ⟨badE, bad, hE, hB, hrun⟩ := psc_sound ρ _ (held_snoc hw hY) hcoef _ _ hS T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms y S0 hms hy hlens hvars hr hclaim hT hC hslots hzero hS0 hne hnb
  refine hrun W p mu (ms ++ [y]) S0 {} (by rw [List.map_append, hms]; simp [hy]) hlens hvars
    hr hclaim hT hC hslots hzero ?_ hne hnb
  rw [Aff.value_empty, add_zero, hS0, List.map_append, List.map_singleton, cutY_snoc]

/-- **A summand that is affine in the further variable, its end term a value in the field.** -/
theorem affine_end_sound (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w)
    (s m : List K → K) (sigma : K) (hs : IsSum (ws.map (wtOf ρ)) s sigma) (hcoef : ℕ → K)
    (T Cv : K) (hY : Held (OnBytes.Psc.Weight.atZero 2)) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((ws ++ [OnBytes.Psc.Weight.atZero 2]).map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd) (y : Rnd) (kt : K),
        ms.map (·.1) = ws → y.1 = OnBytes.Psc.Weight.atZero 2 →
        (∀ x ∈ ms ++ [y], x.2.1.length + 1 = x.1.d) →
        p.vars.toList = ws ++ [OnBytes.Psc.Weight.atZero 2] →
        p.r.toList = (ms ++ [y]).map (·.2.2) →
        p.claim = claimAfter (ms ++ [y]) (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (ws ++ [OnBytes.Psc.Weight.atZero 2]) →
          W.slot (p.first + i) = hcoef i) →
        kt * ρ.val p.eps = -(p.rowForm zeroE {}).value ρ W →
        kt = s (ms.map fun x => ρ.val x.2.2) + ρ.val y.2.2 * m (ms.map fun x => ρ.val x.2.2) →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps))
          (movesP ρ (ms ++ [y]) (addE mu (mulE p.eps p.target)))) →
        Cv = sigma := by
  have hS := isSum_Y_lin (wtOf ρ (OnBytes.Psc.Weight.atZero 2)) (two_atZero ρ 2 (by omega))
    (le_refl 2) (ws.map (wtOf ρ)) s m sigma hs (cutY fun rs y => s rs + y * m rs)
    (fun rs y => cutY_snoc _ rs y)
  have hmap : ws.map (wtOf ρ) ++ [wtOf ρ (OnBytes.Psc.Weight.atZero 2)] =
      (ws ++ [OnBytes.Psc.Weight.atZero 2]).map (wtOf ρ) := by simp
  rw [hmap] at hS
  obtain ⟨badE, bad, hE, hB, hrun⟩ := psc_sound_neg ρ _ (held_snoc hw hY) hcoef _ _ hS T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms y kt hms hy hlens hvars hr hclaim hT hC hslots hkt hk hne hnb
  refine hrun W p mu (ms ++ [y]) kt (by rw [List.map_append, hms]; simp [hy]) hlens hvars
    hr hclaim hT hC hslots hkt ?_ hne hnb
  rw [hk, List.map_append, List.map_singleton, cutY_snoc]

end OnBytes.Desc.First.P1
