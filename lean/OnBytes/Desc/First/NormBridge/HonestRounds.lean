--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/NormBridge/HonestRounds.lean: the masked sumcheck's honest rounds over the plain
record: from an honest run of polynomials over K (OnBytes/Desc/First/P1/SumTruth.lean: "honest",
masked_true) to rounds of elements of the program's field, a record Model.Psc and a row that is
worth 0. Definitions, statements and proofs. Plain records alone; no routine in a context.

It wants a reading that is onto: a map lift : K -> E with rho (lift k) = k stands as a premise. It
speaks of weights whose constant coefficient is the one that is not sent (fixed = 0): the equality
weights and the value at 0.

Main names:
  sentFrom: what an honest prover sends for a round's polynomial q: the coefficients from X on,
    lifted.
  poly_complete: "complete" gives back q from them, if q's sum is the running claim.
  lift_run: a run of polynomials (Chain) from the reading of c0 is the movesP of rounds of elements,
    at any given challenges; the running claim behind them reads as the run's last claim.
  exists_noBad: against sets of bad challenges that never fill the field there are challenges at
    which the honest run draws no bad one: chosen round by round.
  honest_row: a record whose claim reads as the masked summand at the challenges has a row worth 0.
They are put together in OnBytes/Desc/First/NormBridge/HonestHeard.lean.

Limits. The plain sum (fixed = 1) is not covered. That every honest run is clean is not shown: for
that the bad sets must be those of OnBytes/Desc/First/P1/, with their clause "empty at the truth",
carried up through products_sound.
Not claimed: anything on soundness or hiding; that the prover's program sends what is written here.

-/
import OnBytes.Desc.First.P1.SumTruth
import OnBytes.Desc.First.NormBridge.EqSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset Polynomial
open OnBytes OnBytes.Model
open Blocks (ext ofList)
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## One round -/

/-- n coefficients of q from number s on, lifted. -/
def sentFrom (lift : K → E) (q : K[X]) : ℕ → ℕ → List E
  | _, 0 => []
  | s, n + 1 => lift (q.coeff s) :: sentFrom lift q (s + 1) n

theorem sentFrom_length (lift : K → E) (q : K[X]) : ∀ (n s : ℕ), (sentFrom lift q s n).length = n
  | 0, _ => rfl
  | n + 1, s => by
    show (sentFrom lift q (s + 1) n).length + 1 = n + 1
    rw [sentFrom_length lift q n]

theorem sentFrom_getD (lift : K → E) (q : K[X]) : ∀ (n s i : ℕ),
    (sentFrom lift q s n).getD i zeroE = if i < n then lift (q.coeff (s + i)) else zeroE
  | 0, s, i => by simp [sentFrom]
  | n + 1, s, 0 => by simp [sentFrom]
  | n + 1, s, i + 1 => by
    rw [sentFrom, List.getD_cons_succ, sentFrom_getD lift q n (s + 1) i]
    have e : s + 1 + i = s + (i + 1) := by omega
    rw [e]
    by_cases h : i < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem complete_fixed0 (w : OnBytes.Psc.Weight) (h0 : w.fixed = 0) (sent : List E) (c : E) :
    w.complete sent c =
      mulE (subE c (OnBytes.Psc.dot w.moment (zeroE :: sent))) w.fixedInv :: sent := by
  unfold OnBytes.Psc.Weight.complete
  rw [h0]
  rfl

/-- **"complete" gives back the true polynomial.** -/
theorem poly_complete (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (w : OnBytes.Psc.Weight)
    (hw : Held w) (h0 : w.fixed = 0) (q : K[X]) (hq : q.natDegree < w.d) (c : E)
    (hsum : (wtOf ρ w).sum q = ρ.val c) :
    polyOf ρ (w.complete (sentFrom lift q 1 (w.d - 1)) c) = q := by
  obtain ⟨h2, hm, _, _, hinv, _⟩ := hw.spec
  have hlen := sentFrom_length lift q (w.d - 1) 1
  have hs1 : (wtOf ρ w).sum (polyOf ρ (w.complete (sentFrom lift q 1 (w.d - 1)) c)) = ρ.val c := by
    rw [sum_poly ρ w hm]
    exact Model.complete_sum ρ w _ c (by omega) hinv
  have hc : ∀ i, (polyOf ρ (w.complete (sentFrom lift q 1 (w.d - 1)) c)).coeff (i + 1) =
      q.coeff (i + 1) := by
    intro i
    rw [polyOf_coeff, complete_fixed0 w h0, List.getD_cons_succ, sentFrom_getD]
    by_cases hi : i < w.d - 1
    · rw [if_pos hi, hlift, Nat.add_comm]
    · rw [if_neg hi, ρ.zero]
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hmom : (wtOf ρ w).mom 0 ≠ 0 := by
    intro hz
    have h1 : ρ.val (w.moment.getD w.fixed zeroE) * ρ.val w.fixedInv = 1 := by
      rw [← ρ.mul, hinv, ρ.one]
    rw [h0] at h1
    have hz' : ρ.val (w.moment.getD 0 zeroE) = 0 := hz
    rw [hz', zero_mul] at h1
    exact zero_ne_one h1
  have h00 : (polyOf ρ (w.complete (sentFrom lift q 1 (w.d - 1)) c)).coeff 0 = q.coeff 0 := by
    have e := hs1.trans hsum.symm
    unfold Wt.sum at e
    obtain ⟨n, hn⟩ : ∃ n, (wtOf ρ w).d = n + 1 := ⟨w.d - 1, by
      show w.d = w.d - 1 + 1
      omega⟩
    rw [hn, sum_range_succ', sum_range_succ'] at e
    have e2 : ∑ i ∈ range n, (wtOf ρ w).mom (i + 1) *
          (polyOf ρ (w.complete (sentFrom lift q 1 (w.d - 1)) c)).coeff (i + 1) =
        ∑ i ∈ range n, (wtOf ρ w).mom (i + 1) * q.coeff (i + 1) :=
      sum_congr rfl fun i _ => by rw [hc i]
    rw [e2] at e
    exact mul_left_cancel₀ hmom (add_left_cancel e)
  ext i
  cases i with
  | zero => exact h00
  | succ i => exact hc i

/-! ## A run -/

/-- **From polynomials to elements.** -/
theorem lift_run (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) :
    ∀ (ws : List OnBytes.Psc.Weight), (∀ w ∈ ws, Held w) → (∀ w ∈ ws, w.fixed = 0) →
    ∀ (ms : List (K[X] × K)) (rsE : List E) (c0 : E) (cf : K),
    Chain (ws.map (wtOf ρ)) ms (ρ.val c0) cf → ms.map (·.2) = rsE.map ρ.val →
    ∃ msE : List Rnd, msE.map (·.1) = ws ∧ msE.map (·.2.2) = rsE ∧
      (∀ m ∈ msE, m.2.1.length + 1 = m.1.d) ∧ movesP ρ msE c0 = ms ∧
      ρ.val (claimAfter msE c0) = cf := by
  intro ws
  induction ws with
  | nil =>
    intro _ _ ms rsE c0 cf hc hr
    cases ms with
    | nil =>
      cases rsE with
      | nil => exact ⟨[], rfl, rfl, by simp, rfl, hc⟩
      | cons r rs => simp at hr
    | cons m ms => exact absurd hc (by simp [OnBytes.Desc.First.P1.Chain])
  | cons w ws ih =>
    intro hw h0 ms rsE c0 cf hc hr
    cases ms with
    | nil => exact absurd hc (by simp [OnBytes.Desc.First.P1.Chain])
    | cons m ms =>
      cases rsE with
      | nil => simp at hr
      | cons r rs =>
        rw [List.map_cons] at hc
        obtain ⟨hg, hsum, hrest⟩ := hc
        simp only [List.map_cons, List.cons.injEq] at hr
        obtain ⟨hr1, hr2⟩ := hr
        have hww := hw w (by simp)
        have hp := poly_complete ρ lift hlift w hww (h0 w (by simp)) m.1 hg c0 hsum
        have hc1 : ρ.val (OnBytes.Psc.polyAt (w.complete (sentFrom lift m.1 1 (w.d - 1)) c0) r) =
            m.1.eval m.2 := by
          rw [hr1]
          conv_rhs => rw [← hp]
          exact (polyOf_eval ρ r _).symm
        obtain ⟨msE, a1, a2, a3, a4, a5⟩ := ih (fun v hv => hw v (by simp [hv]))
          (fun v hv => h0 v (by simp [hv])) ms rs
          (OnBytes.Psc.polyAt (w.complete (sentFrom lift m.1 1 (w.d - 1)) c0) r) cf
          (by rw [hc1]; exact hrest) hr2
        refine ⟨(w, sentFrom lift m.1 1 (w.d - 1), r) :: msE, by rw [List.map_cons, a1],
          by rw [List.map_cons, a2], ?_, ?_, a5⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · show (sentFrom lift m.1 1 (w.d - 1)).length + 1 = w.d
            rw [sentFrom_length]
            have := hww.spec.1
            omega
          · exact a3 x hx
        · show (polyOf ρ (w.complete (sentFrom lift m.1 1 (w.d - 1)) c0), ρ.val r) ::
              movesP ρ msE (OnBytes.Psc.polyAt (w.complete (sentFrom lift m.1 1 (w.d - 1)) c0) r) =
            m :: ms
          rw [hp, a4, ← hr1]

/-! ## Challenges that are not bad, chosen round by round -/

theorem exists_noBad_from [DecidableEq K] (tq : List K → K[X])
    (bad : List (K[X] × K) → K[X] → Finset K) (hfree : ∀ pre g, ∃ x, x ∉ bad pre g) :
    ∀ (n : ℕ) (pre : List K) (front : List (K[X] × K)), ∃ rs : List K, rs.length = n ∧
      ∀ i m, (honest tq pre rs)[i]? = some m →
        m.2 ∉ bad (front ++ (honest tq pre rs).take i) m.1
  | 0, _, _ => ⟨[], rfl, fun i m h => by simp [honest] at h⟩
  | n + 1, pre, front => by
    obtain ⟨r, hr⟩ := hfree front (tq pre)
    obtain ⟨rs, hl, hrs⟩ := exists_noBad_from tq bad hfree n (pre ++ [r]) (front ++ [(tq pre, r)])
    refine ⟨r :: rs, by rw [List.length_cons, hl], fun i m h => ?_⟩
    rw [honest_cons] at h ⊢
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      rw [← Option.some.inj h, List.take_zero, List.append_nil]
      exact hr
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have := hrs i m h
      rw [List.append_assoc] at this
      exact this

theorem exists_noBad [DecidableEq K] (tq : List K → K[X])
    (bad : List (K[X] × K) → K[X] → Finset K) (hfree : ∀ pre g, ∃ x, x ∉ bad pre g) (n : ℕ) :
    ∃ rs : List K, rs.length = n ∧ NoBad bad (honest tq [] rs) := by
  obtain ⟨rs, hl, h⟩ := exists_noBad_from tq bad hfree n [] []
  exact ⟨rs, hl, fun i m hi => by
    have := h i m hi
    rwa [List.nil_append] at this⟩

/-! ## The row -/

/-- A record whose claim reads as the masked summand at the challenges has a row worth 0. -/
theorem honest_row (ws : List OnBytes.Psc.Weight) (hcoef : ℕ → K) (W : World K) (p : Psc)
    (ms : List Rnd) (S0 : E) (hms : ms.map (·.1) = ws) (hvars : p.vars.toList = ws)
    (hr : p.r.toList = ms.map (·.2.2))
    (hslots : ∀ i, i < OnBytes.Psc.hidingEntries ws → W.slot (p.first + i) = hcoef i)
    (hclaim : ρ.val p.claim =
      hid (ws.map (wtOf ρ)) hcoef (ms.map fun m => ρ.val m.2.2) + ρ.val p.eps * ρ.val S0 +
        ρ.val p.eps * (ρ.val p.target - p.start.value ρ W) *
          psiProd (ws.map (wtOf ρ)) (ms.map fun m => ρ.val m.2.2)) :
    (p.rowForm S0 {}).value ρ W = 0 := by
  have hmap : (ms.map fun m => wtOf ρ m.1) = ws.map (wtOf ρ) := by
    rw [← hms, List.map_map]
    rfl
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
  have hv0 := Psc.rowForm_value ρ W p S0 {}
  rw [sumFrom_dotFrom, hwalk, hu2, hdot, hu1, Aff.value_empty, hclaim] at hv0
  rw [hv0]
  ring

end D6.Bridge

#print axioms D6.Bridge.poly_complete
#print axioms D6.Bridge.lift_run
#print axioms D6.Bridge.exists_noBad
#print axioms D6.Bridge.honest_row
