-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumTruth.lean: the masked sumcheck's soundness law over the part's own text
(Johnson/Desc/Part/MaskedSumSound.lean's `sound` and `sound_hear`), WITH ITS BAD SETS EMPTY AT THE
TRUTH. Statements and proofs.

  `sound_true`, `sound_hear_true`: the letters of `sound` | `sound_hear`, fixed first, unturned.
    There are muT, the sets badE and bad, and tq (for each mu, eps and challenges in front: the true
    round polynomial), with: muT is the sum of the hiding polynomial; the two sizes and the law, to
    the letter; AND: if Cv = sigma, no eps is bad; a round's set is empty at the true round
    polynomial; and, if Cv = sigma, for all challenges of the right number the run of the true round
    polynomials goes from muT + eps * T to the value, at the challenges, of the hiding polynomial +
    eps * S + eps * (T - Cv) * the product of the psi.

The proofs are those of `sound` and `sound_hear`, over `masked_true`
(OnBytes/Desc/First/P1/SumTruth.lean) in the place of `masked`. The new conjuncts speak of
polynomials over K. NOTHING HERE JOINS SUCH A RUN TO ROUNDS OF THE PROGRAM's ELEMENTS.
-/
import Johnson.Desc.Part.MaskedSumSound
import OnBytes.Desc.First.P1.SumTruth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-- **The law, its bad sets empty at the truth.** -/
theorem sound_true (vs : List Var) (hv : ∀ v ∈ vs, 2 ≤ v.d) (hcoef : ℕ → K) (S : List K → K)
    (sigma : K) (hS : IsSum (vs.map (Var.wt ρ)) S sigma) (T Cv : K) :
    ∃ (muT : K) (badE : K → Finset K) (tq : K → K → List K → K[X])
      (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      IsSum (vs.map (Var.wt ρ)) (hid (vs.map (Var.wt ρ)) hcoef) muT ∧
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card < dAt (vs.map (Var.wt ρ)) pre.length) ∧
      (∀ (W : World K) (h : Heard) (mu : E) (l : List (List E × E)) (S0 : E) (kept : Aff)
        (F G : Fork) (f : Aff),
        h.vars = vs → Lens vs l → h.r = l.map (·.2) →
        h.claim = after vs l (addE mu (mulE h.eps h.target)) →
        ρ.val h.target = T → h.start.value ρ W = Cv →
        (∀ i, i < ownSlots vs → W.slot (h.first + i) = hcoef i) →
        row h S0 kept F = some (f, G) → f.value ρ W = 0 →
        S (l.map fun x => ρ.val x.2) = ρ.val S0 + kept.value ρ W →
        ρ.val h.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val h.eps))
          (movesOf ρ vs l (addE mu (mulE h.eps h.target)))) →
        Cv = sigma) ∧
      (Cv = sigma → ∀ mu, badE mu = ∅) ∧
      (∀ mu eps pre, bad mu eps pre (tq mu eps (pre.map (·.2))) = ∅) ∧
      (Cv = sigma → ∀ (mu eps : K) (rs : List K), rs.length = (vs.map (Var.wt ρ)).length →
        Chain (vs.map (Var.wt ρ)) (honest (tq mu eps) [] rs) (muT + eps * T)
          (hid (vs.map (Var.wt ρ)) hcoef rs + eps * S rs +
            eps * (T - Cv) * psiProd (vs.map (Var.wt ρ)) rs)) := by
  classical
  have hpsi := psiOk_wt ρ vs hv
  obtain ⟨muT, hU⟩ := isSum_hid (vs.map (Var.wt ρ)) hcoef hpsi (by
    intro w hw
    obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hw
    rw [Var.wt_d]
    have := hv v hvm
    omega)
  choose badE tq bad hE hB hrun hEt hBt hCh using fun mu =>
    masked_true (vs.map (Var.wt ρ)) (hid (vs.map (Var.wt ρ)) hcoef) S
      (psiProd (vs.map (Var.wt ρ))) muT sigma hU hS (isSum_psiProd _ hpsi) mu T Cv
  refine ⟨muT, badE, tq, bad, hU, hE, hB, ?_, fun h mu => hEt mu h, hBt,
    fun h mu => hCh mu h⟩
  intro W h mu l S0 kept F G f hvars hlens hr hclaim hT hC hslots hrow hzero hend hne hnb
  have hch := chain_after ρ vs l (addE mu (mulE h.eps h.target)) hlens
  rw [ρ.add, ρ.mul, hT] at hch
  have hmv := movesOf_chal ρ vs l (addE mu (mulE h.eps h.target)) hlens
  have hfst : (h.vars.zip h.r).map (·.1) = vs := by
    rw [hvars, hr]
    have gen : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
        (vs.zip (l.map (·.2))).map (·.1) = vs := by
      intro vs
      induction vs with
      | nil => intro l _; rfl
      | cons v vs ih =>
        intro l hl
        cases l with
        | nil => exact hl.elim
        | cons x l =>
          simp only [List.map_cons, List.zip_cons_cons]
          rw [ih l hl.2.2]
    exact gen vs l hlens
  have hzip : (h.vars.zip h.r).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ) ∧
      (h.vars.zip h.r).map (fun x => ρ.val x.2) = l.map fun x => ρ.val x.2 := by
    rw [hvars, hr]
    have gen : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
        (vs.zip (l.map (·.2))).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ) ∧
          (vs.zip (l.map (·.2))).map (fun x => ρ.val x.2) = l.map fun x => ρ.val x.2 := by
      intro vs
      induction vs with
      | nil =>
        intro l hl
        cases l with
        | nil => exact ⟨rfl, rfl⟩
        | cons _ _ => exact hl.elim
      | cons v vs ih =>
        intro l hl
        cases l with
        | nil => exact hl.elim
        | cons x l =>
          obtain ⟨a, b⟩ := ih l hl.2.2
          constructor
          · simp only [List.map_cons, List.zip_cons_cons]
            rw [a]
          · simp only [List.map_cons, List.zip_cons_cons]
            rw [b]
    exact gen vs l hlens
  obtain ⟨hu1, hu2⟩ := hidingAt_val ρ (h.vars.zip h.r) hcoef
  rw [hzip.1, hzip.2] at hu1 hu2
  have hv0 := row_value ρ W hrow
  rw [hzero, hT, hC, hu2] at hv0
  have hdot : dotFrom ρ (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 =
      dotFrom ρ hcoef (hidingAt (h.vars.zip h.r)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by
      have := hidingAt_length_le (h.vars.zip h.r)
      rw [hfst] at this
      omega)
  rw [hdot, hu1] at hv0
  refine hrun (ρ.val mu) (ρ.val h.eps) _ _ hch ?_ hne (by convert hnb)
  rw [hmv, ← hclaim, hend]
  linear_combination hv0

/-- **The same from the hearing's own return.** -/
theorem sound_hear_true (lead : Nat) (vs : List Var) (e : Ends)
    (hk : shapeOk ⟨lead, vs, some e⟩ = true) (hcoef : ℕ → K) (S : List K → K) (sigma : K)
    (hS : IsSum ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) S sigma) (T Cv : K) :
    ∃ (muT : K) (badE : K → Finset K) (tq : K → K → List K → K[X])
      (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      IsSum ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ))
        (hid ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) hcoef) muT ∧
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) pre.length) ∧
      (∀ (W : World K) (C : Aff) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (S0 : E)
        (kept : Aff) (F' G' : Fork) (f : Aff),
        hear C ⟨lead, vs, some e⟩ F rs = some (h, G) → readAll ⟨lead, vs, some e⟩ rs = some R →
        ρ.val h.target = T → C.value ρ W = Cv →
        (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (h.first + i) = hcoef i) →
        row h S0 kept F' = some (f, G') → f.value ρ W = 0 →
        S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds
            (addE R.mu (mulE R.eps h.target)))) →
        Cv = sigma) ∧
      (Cv = sigma → ∀ mu, badE mu = ∅) ∧
      (∀ mu eps pre, bad mu eps pre (tq mu eps (pre.map (·.2))) = ∅) ∧
      (Cv = sigma → ∀ (mu eps : K) (rs : List K),
        rs.length = ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)).length →
        Chain ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) (honest (tq mu eps) [] rs)
          (muT + eps * T)
          (hid ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) hcoef rs + eps * S rs +
            eps * (T - Cv) * psiProd ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) rs)) := by
  obtain ⟨muT, badE, tq, bad, hU, hE, hB, hrun, hEt, hBt, hCh⟩ :=
    sound_true ρ (⟨lead, vs, some e⟩ : Call).all (two_le_all hk) hcoef S sigma hS T Cv
  refine ⟨muT, badE, tq, bad, hU, hE, hB, ?_, hEt, hBt, hCh⟩
  intro W C F G rs h R S0 kept F' G' f hh hR hT hC hslots hrow hzero hend hne hnb
  obtain ⟨_, T', R', _, hR', hrec, _⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  subst hRR
  obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := readAll_spec hR
  have hl : Lens (⟨lead, vs, some e⟩ : Call).all R'.rounds := lens_of_read hvr (two_le_all hk)
  have e1 : h.vars = (⟨lead, vs, some e⟩ : Call).all := by rw [hrec]
  have e2 : h.r = R'.rounds.map (·.2) := by rw [hrec]
  have e3 : h.eps = R'.eps := by rw [hrec]
  have e4 : h.start = C := by rw [hrec]
  have e5 : h.claim = after (⟨lead, vs, some e⟩ : Call).all R'.rounds
      (addE R'.mu (mulE h.eps h.target)) := by rw [hrec]
  refine hrun W h R'.mu R'.rounds S0 kept F' G' f e1 hl e2 e5 hT (by rw [e4]; exact hC) hslots hrow
    hzero ?_ (by rw [e3]; exact hne) (by rw [e3]; exact hnb)
  rw [← hend, e2, List.map_map]
  rfl

end VerifiableInference.Desc.Part.MaskedSum
