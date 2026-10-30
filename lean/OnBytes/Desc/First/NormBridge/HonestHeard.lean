--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/NormBridge/HonestHeard.lean: the masked sumcheck is complete at a true claim, at
equality weights and a sum of products, in the letters of OnBytes/Desc/First/NormBridge/EqSum.lean.
Statement and proof, over OnBytes/Desc/First/NormBridge/HonestRounds.lean and masked_true
(OnBytes/Desc/First/P1/SumTruth.lean: the honest run of polynomials). Plain records alone.

Main names:
  honest_heard: fixed: a reading with a lift (onto); the point zs; the tables A; the end values'
    masks m; the terms ts; the hiding coefficients hcoef; a target T; a start form C; a first slot;
    Cv, which is the true sum; and any sets badE, bad that never fill the field. Then there is a
    sumcheck as heard (Heard1) with: the Shape; the given start form, target and first slot; its end
    term the summand on what an honest prover shows (each table's extension at the challenges plus
    beta times its mask); eps not in badE; no challenge bad; and its row worth 0 in every world that
    gives C the value Cv and the hiding slots the hiding coefficients.
  free_of_card: in a field with more than n elements a set of at most n elements leaves one free.
  honest_clean: the same against EqSum.lean's own bad sets pscBadE, pscBad: so Heard1.Clean can be
    met together with psc_law's other premises, in a field of more than two elements.

Limits. That every honest run is clean is not shown: the draws are chosen here, round by round. So
honest_heard does not join with a tape, whose draws are given: for that stands
OnBytes/Desc/First/NormBridge/HonestAt.lean.
Not claimed: anything on soundness or hiding; that the prover's program sends what is written here.

-/
import OnBytes.Desc.First.NormBridge.HonestRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset Polynomial
open OnBytes OnBytes.Model
open Blocks (ext ofList)
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

theorem held_all (zs : List E) : ∀ w ∈ eqWs zs ++ [wY], Held w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact held_eqWs zs w h
  · rw [List.mem_singleton] at h
    rw [h]
    exact held_eq zeroE

theorem fixed_all (zs : List E) : ∀ w ∈ eqWs zs ++ [wY], w.fixed = 0 := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h
    rfl
  · rw [List.mem_singleton] at h
    rw [h]
    rfl

theorem map_lift (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (rs : List K) :
    (rs.map lift).map ρ.val = rs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id rs]
  exact List.map_congr_left fun x _ => hlift x

/-- **Complete at a true claim.** -/
theorem honest_heard (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (zs : List E)
    (A : ℕ → ℕ → K) (m : ℕ → K) (ts : List (Term K)) (hcoef : ℕ → K) (T : E) (C : Aff) (first : ℕ)
    (Cv : K)
    (hCv : Cv = ext zs.length (fun X => sumTerms ts fun i => A i X) (ofList (zs.map ρ.val)))
    (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K)
    (hE : ∀ mu, ∃ x, x ∉ badE mu) (hB : ∀ mu eps pre g, ∃ x, x ∉ bad mu eps pre g) :
    ∃ h : Heard1, h.Shape zs ∧ h.p.start = C ∧ h.p.target = T ∧ h.p.first = first ∧
      ρ.val h.S0 =
        sumTerms ts (fun i => ext zs.length (A i) (ofList (h.r ρ)) + h.beta ρ * m i) ∧
      ρ.val h.p.eps ∉ badE (ρ.val h.mu) ∧
      (haveI := Classical.decEq K
       NoBad (bad (ρ.val h.mu) (ρ.val h.p.eps))
        (movesP ρ (h.ms ++ [h.y]) (addE h.mu (mulE h.p.eps h.p.target)))) ∧
      ∀ W : World K, C.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (eqWs zs ++ [wY]) → W.slot (first + i) = hcoef i) →
        (h.p.rowForm h.S0 {}).value ρ W = 0 := by
  haveI : DecidableEq K := Classical.decEq K
  have hlen : (eqWs zs).length = zs.length := List.length_map _
  have htw : Twos 3 ((eqWs zs ++ [wY]).map (wtOf ρ)) (wts (zs.map ρ.val) ++ [(1, 0)]) := by
    rw [List.map_append]
    exact twos_append _ _ _ _ (twos_eqWs ρ zs) (two_atZero ρ 3 (by omega)) (le_refl 3)
  have hS := isSum_terms _ _ htw
    (fun i => ext1 (eqWs zs).length (fun b => A i (numFrom 0 b)) (m i)) ts
  have hl1 : ((eqWs zs ++ [wY]).map (wtOf ρ)).length = (eqWs zs).length + 1 := by simp
  rw [hl1] at hS
  have hxl : (wts (zs.map ρ.val)).length = (eqWs zs).length := by simp [wts, eqWs]
  have hsig : tot (wts (zs.map ρ.val) ++ [(1, 0)]) (fun b => sumTerms ts fun i =>
      ext1 (eqWs zs).length (fun b => A i (numFrom 0 b)) (m i) b) = Cv := by
    rw [← hxl, tot_ext1_terms, hCv]
    have e := tot_ext (ofList (zs.map ρ.val)) zs.length fun X => sumTerms ts fun i => A i X
    have hl : (zs.map ρ.val).length = zs.length := List.length_map _
    rw [← hl, coords_ofList, hl] at e
    exact e
  have hpsi := psiOk_of_held ρ (eqWs zs ++ [wY]) (held_all zs)
  obtain ⟨muT, hU⟩ := isSum_hid ((eqWs zs ++ [wY]).map (wtOf ρ)) hcoef hpsi (by
    intro v hv
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hv
    have := (held_all zs w hwm).spec.1
    show 1 ≤ w.d
    omega)
  obtain ⟨_, tq, _, _, _, _, _, _, hhon⟩ := masked_true ((eqWs zs ++ [wY]).map (wtOf ρ))
    (hid ((eqWs zs ++ [wY]).map (wtOf ρ)) hcoef) _ (psiProd ((eqWs zs ++ [wY]).map (wtOf ρ))) muT _
    hU hS (isSum_psiProd _ hpsi) muT (ρ.val T) Cv
  obtain ⟨epsK, heps⟩ := hE muT
  obtain ⟨rs, hrl, hnb⟩ := exists_noBad (tq epsK) (bad muT epsK) (hB muT epsK)
    ((eqWs zs).length + 1)
  have hch := hhon hsig.symm epsK rs (by rw [hrl, hl1])
  have hc0 : ρ.val (addE (lift muT) (mulE (lift epsK) T)) = muT + epsK * ρ.val T := by
    rw [ρ.add, ρ.mul, hlift, hlift]
  obtain ⟨msE, a1, a2, a3, a4, a5⟩ := lift_run ρ lift hlift (eqWs zs ++ [wY]) (held_all zs)
    (fixed_all zs) (honest (tq epsK) [] rs) (rs.map lift)
    (addE (lift muT) (mulE (lift epsK) T)) _ (by rw [hc0]; exact hch)
    (by rw [honest_chal, map_lift ρ lift hlift])
  obtain ⟨ms, b, rfl, hms, hb⟩ := List.map_eq_append_iff.mp a1
  obtain ⟨y, rfl, hy⟩ : ∃ y, b = [y] ∧ y.1 = wY := by
    cases b with
    | nil => simp at hb
    | cons y b' =>
      cases b' with
      | nil => exact ⟨y, rfl, by simpa using hb⟩
      | cons _ _ => simp at hb
  -- the challenges, read
  have hrs : (ms ++ [y]).map (fun x => ρ.val x.2.2) = rs := by
    have e : (ms ++ [y]).map (fun x => ρ.val x.2.2) = ((ms ++ [y]).map (·.2.2)).map ρ.val := by
      rw [List.map_map]
      rfl
    rw [e, a2, map_lift ρ lift hlift]
  have hml : (ms.map fun x => ρ.val x.2.2).length = zs.length := by
    rw [List.length_map, ← hlen, ← hms, List.length_map]
  -- the summand at the challenges is the summand on what is shown
  have hSr : (sumTerms ts fun i => mle ((eqWs zs).length + 1)
        (ext1 (eqWs zs).length (fun b => A i (numFrom 0 b)) (m i)) rs) =
      sumTerms ts fun i =>
        ext zs.length (A i) (ofList (ms.map fun x => ρ.val x.2.2)) + ρ.val y.2.2 * m i := by
    congr 1
    funext i
    rw [← hrs, List.map_append]
    show mle ((eqWs zs).length + 1) _ ((ms.map fun x => ρ.val x.2.2) ++ [ρ.val y.2.2]) = _
    rw [mle_ext1 (eqWs zs).length _ (m i) _ _ (by rw [hml, hlen]), hlen]
    have e := mle_ext (ofList (ms.map fun x => ρ.val x.2.2)) zs.length (A i)
    rw [← hml, coords_ofList, hml] at e
    rw [e]
  refine ⟨{ p := { start := C, target := T, eps := lift epsK,
                   claim := claimAfter (ms ++ [y]) (addE (lift muT) (mulE (lift epsK) T)),
                   first := first, vars := (eqWs zs ++ [wY]).toArray,
                   r := ((ms ++ [y]).map (·.2.2)).toArray }
            mu := lift muT, ms := ms, y := y
            S0 := lift (sumTerms ts fun i =>
              ext zs.length (A i) (ofList (ms.map fun x => ρ.val x.2.2)) + ρ.val y.2.2 * m i) },
    ⟨hms, hy, a3, by simp, by simp, rfl⟩, rfl, rfl, rfl, hlift _, ?_, ?_, ?_⟩
  · show ρ.val (lift epsK) ∉ badE (ρ.val (lift muT))
    rw [hlift, hlift]
    exact heps
  · show NoBad (bad (ρ.val (lift muT)) (ρ.val (lift epsK)))
      (movesP ρ (ms ++ [y]) (addE (lift muT) (mulE (lift epsK) T)))
    rw [hlift, hlift, a4]
    exact hnb
  · intro W hCW hslots
    refine honest_row ρ (eqWs zs ++ [wY]) hcoef W _ (ms ++ [y]) _ a1 (by simp) (by simp) hslots ?_
    show ρ.val (claimAfter (ms ++ [y]) (addE (lift muT) (mulE (lift epsK) T))) =
      hid ((eqWs zs ++ [wY]).map (wtOf ρ)) hcoef ((ms ++ [y]).map fun x => ρ.val x.2.2) +
        ρ.val (lift epsK) * ρ.val (lift (sumTerms ts fun i =>
          ext zs.length (A i) (ofList (ms.map fun x => ρ.val x.2.2)) + ρ.val y.2.2 * m i)) +
        ρ.val (lift epsK) * (ρ.val T - C.value ρ W) *
          psiProd ((eqWs zs ++ [wY]).map (wtOf ρ)) ((ms ++ [y]).map fun x => ρ.val x.2.2)
    rw [a5, hrs, hlift, hlift, hCW, hSr]

omit [Field K] in
/-- In a field with more than n elements a set of at most n elements leaves one free. -/
theorem free_of_card [Fintype K] {n : ℕ} (hK : n < Fintype.card K) (s : Finset K)
    (hs : s.card ≤ n) : ∃ x, x ∉ s := by
  by_contra hall
  push Not at hall
  have : s = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [this, Finset.card_univ] at hs
  omega

/-- **Clean can be met, together with psc_law's other premises.** -/
theorem honest_clean [Fintype K] (hK : 2 < Fintype.card K) (lift : K → E)
    (hlift : ∀ k, ρ.val (lift k) = k) (zs : List E) (A : ℕ → ℕ → K) (m : ℕ → K)
    (ts : List (Term K)) (hcoef : ℕ → K) (T : E) (C : Aff) (first : ℕ) (Cv : K)
    (hCv : Cv = ext zs.length (fun X => sumTerms ts fun i => A i X) (ofList (zs.map ρ.val))) :
    ∃ h : Heard1, h.Shape zs ∧ h.p.start = C ∧ h.p.target = T ∧ h.p.first = first ∧
      ρ.val h.S0 =
        sumTerms ts (fun i => ext zs.length (A i) (ofList (h.r ρ)) + h.beta ρ * m i) ∧
      h.Clean ρ zs A m ts hcoef (ρ.val T) Cv ∧
      ∀ W : World K, C.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (eqWs zs ++ [wY]) → W.slot (first + i) = hcoef i) →
        (h.p.rowForm h.S0 {}).value ρ W = 0 := by
  obtain ⟨h, h1, h2, h3, h4, h5, h6, h7, h8⟩ := honest_heard ρ lift hlift zs A m ts hcoef T C first
    Cv hCv (pscBadE ρ zs A m ts hcoef (ρ.val T) Cv) (pscBad ρ zs A m ts hcoef (ρ.val T) Cv)
    (fun mu => free_of_card (by omega) _ (le_trans (pscBadE_card ρ zs A m ts hcoef _ _ mu)
      (by omega : 1 ≤ 2)))
    (fun mu eps pre g => free_of_card hK _ (pscBad_card ρ zs A m ts hcoef _ _ mu eps pre g))
  exact ⟨h, h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩

end D6.Bridge

#print axioms D6.Bridge.honest_heard
#print axioms D6.Bridge.honest_clean
