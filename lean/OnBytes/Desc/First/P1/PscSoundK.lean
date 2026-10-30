-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/PscSoundK.lean: the masked sumcheck's law over the plain record
(OnBytes/Desc/First/P1/PscSound.lean), WITH THE END TERM AS A VALUE IN THE FIELD. Statements and
proofs.

Why. `psc_sound` takes the summand's value at the challenges as the reading of an element S0 that
the verifier has computed, plus the value of a form that it keeps. One sumcheck of a layers'
sub-proof cannot do so: its summand at the end point holds products with weights, which is no form
in the reads. There the verifier makes the row WITHOUT the summand (S0 = 0, nothing kept), a form u,
and goes on with -u / eps in the summand's place.

  `rowForm_split`: the row with an end term is the row without, plus eps times the end term's value.
  `psc_sound_K`: THE LAW, with the premise: u's value + eps * S (the challenges) = 0, where u is the
    row without the summand. All other letters and premises are `psc_sound`'s.
  `psc_sound_neg`: the same for the value that the verifier goes on with: if kt is a value with
    kt * eps = -(u's value), and kt = S (the challenges), the claimed form's value is the sum. (That
    eps reads as not 0 is not needed here.)

Limits: those of PscSound.lean. THAT kt IS THE SUMMAND AT THE CHALLENGES IS A PREMISE: further
claims must give it.
-/
import OnBytes.Desc.First.P1.PscSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-- The row with an end term is the row without, plus eps times the end term's value. -/
theorem rowForm_split (W : World K) (p : Psc) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ W =
      (p.rowForm zeroE {}).value ρ W + ρ.val p.eps * (ρ.val S0 + kept.value ρ W) := by
  rw [Psc.rowForm_value ρ W p S0 kept, Psc.rowForm_value ρ W p zeroE {}, ρ.zero,
    Aff.value_empty]
  ring

/-- **THE LAW, the end term a value in the field.** -/
theorem psc_sound_K (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w) (hcoef : ℕ → K)
    (S : List K → K) (sigma : K) (hS : IsSum (ws.map (wtOf ρ)) S sigma) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card < dAt (ws.map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd),
        ms.map (·.1) = ws → (∀ m ∈ ms, m.2.1.length + 1 = m.1.d) →
        p.vars.toList = ws → p.r.toList = ms.map (·.2.2) →
        p.claim = claimAfter ms (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries ws → W.slot (p.first + i) = hcoef i) →
        (p.rowForm zeroE {}).value ρ W + ρ.val p.eps * S (ms.map fun m => ρ.val m.2.2) = 0 →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps)) (movesP ρ ms (addE mu (mulE p.eps p.target)))) →
        Cv = sigma := by
  classical
  have hpsi := psiOk_of_held ρ ws hw
  obtain ⟨muT, hU⟩ := isSum_hid (ws.map (wtOf ρ)) hcoef hpsi (by
    intro v hv
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hv
    have := (hw w hwm).spec.1
    show 1 ≤ w.d
    omega)
  choose badE bad hE hB hrun using fun mu =>
    masked (ws.map (wtOf ρ)) (hid (ws.map (wtOf ρ)) hcoef) S (psiProd (ws.map (wtOf ρ))) muT
      sigma hU hS (isSum_psiProd _ hpsi) mu T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms hms hlen hvars hr hclaim hT hC hslots hzero hne hnb
  have hok : OkRnds ms := fun m hm =>
    ⟨hw m.1 (by rw [← hms]; exact List.mem_map_of_mem hm), hlen m hm⟩
  have hch := chainP ρ ms (addE mu (mulE p.eps p.target)) hok
  have hmap : (ms.map fun m => wtOf ρ m.1) = ws.map (wtOf ρ) := by
    rw [← hms, List.map_map]
    rfl
  rw [hmap, ρ.add, ρ.mul, hT] at hch
  have hmv := movesP_chal ρ ms (addE mu (mulE p.eps p.target))
  have hzipl : p.vars.toList.zip p.r.toList = ms.map fun m => (m.1, m.2.2) := by
    rw [hvars, hr, ← hms]
    exact zip_maps _ _ ms
  obtain ⟨hu1, hu2⟩ := hidingWalk_val ρ (p.vars.toList.zip p.r.toList) hcoef
  have hz1 : (p.vars.toList.zip p.r.toList).map (fun x => wtOf ρ x.1) = ws.map (wtOf ρ) := by
    rw [hzipl, List.map_map, ← hmap]
    rfl
  have hz2 : (p.vars.toList.zip p.r.toList).map (fun x => ρ.val x.2) =
      ms.map fun m => ρ.val m.2.2 := by
    rw [hzipl, List.map_map]
    rfl
  rw [hz1, hz2] at hu1 hu2
  have hwalk : p.walk = OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList) := by
    rw [Psc.walk, zipT_eq]
  have hv0 := Psc.rowForm_value ρ W p zeroE {}
  rw [hT, hC, sumFrom_dotFrom, hwalk, hu2, ρ.zero, Aff.value_empty] at hv0
  have hdot : dotFrom ρ (fun i => W.slot (p.first + i))
      (OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList)).1 =
      dotFrom ρ hcoef (OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by
      have hle := hidingWalk_length_le (p.vars.toList.zip p.r.toList)
      have hf1 : (p.vars.toList.zip p.r.toList).map (·.1) = ws := by
        rw [hzipl, List.map_map, ← hms]
        rfl
      rw [hf1] at hle
      omega)
  rw [hdot, hu1] at hv0
  refine hrun (ρ.val mu) (ρ.val p.eps) _ _ hch ?_ hne (by convert hnb)
  rw [hmv, ← hclaim]
  linear_combination hv0 - hzero

/-- **The same for the value that the verifier goes on with in the summand's place.** -/
theorem psc_sound_neg (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w) (hcoef : ℕ → K)
    (S : List K → K) (sigma : K) (hS : IsSum (ws.map (wtOf ρ)) S sigma) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card < dAt (ws.map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd) (kt : K),
        ms.map (·.1) = ws → (∀ m ∈ ms, m.2.1.length + 1 = m.1.d) →
        p.vars.toList = ws → p.r.toList = ms.map (·.2.2) →
        p.claim = claimAfter ms (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries ws → W.slot (p.first + i) = hcoef i) →
        kt * ρ.val p.eps = -(p.rowForm zeroE {}).value ρ W →
        kt = S (ms.map fun m => ρ.val m.2.2) →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps)) (movesP ρ ms (addE mu (mulE p.eps p.target)))) →
        Cv = sigma := by
  obtain ⟨badE, bad, hE, hB, hrun⟩ := psc_sound_K ρ ws hw hcoef S sigma hS T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms kt hms hlen hvars hr hclaim hT hC hslots hkt hS' hne hnb
  refine hrun W p mu ms hms hlen hvars hr hclaim hT hC hslots ?_ hne hnb
  rw [← hS']
  linear_combination hkt

end OnBytes.Desc.First.P1
