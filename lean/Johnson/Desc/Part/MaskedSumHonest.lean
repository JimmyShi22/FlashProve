-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumHonest.lean: THE PART "THE MASKED SUMCHECK": FROM A RUN OF POLYNOMIALS
OVER K TO ROUNDS OF THE PROGRAM's ELEMENTS THAT THE PART's OWN READER TAKES. Definitions, statements
and proofs, in the part's letters (Part/MaskedSum4.lean: Var, complete, readAll, leadScalars;
Part/MaskedSumSound.lean: movesOf, polyOf, Lens; OnBytes/Desc/First/P1/SumCore.lean: Chain).
WHAT IT DOES NOT SHOW. THAT THE HEARING RETURNS ON THESE ROUNDS: hear also asks the start form's
public part and room in the ledger: not here. That the row is worth 0. That the prover's program
sends these elements. Nothing on soundness, on probabilities or on hiding.
IT WANTS A READING THAT IS ONTO: a map lift : K -> E with rho (lift k) = k is a premise.
WHAT IT IS.
  sentFrom, sentOf   what an honest prover sends for a round's polynomial q: all coefficients but
                     the one that the text derives (summed plainly: the linear one; summed at a
                     point: the constant one), lifted.
  poly_eq_of         two polynomials with one sum that agree in all coefficients but one, whose
                     moment is not 0, are one.
  poly_complete      "complete" gives back q from sentOf, if q's sum is the running claim. BOTH
                     KINDS OF VARIABLE.
  lift_run           a run of polynomials (Chain) from the reading of c0 is the movesOf of rounds of
                     elements, at any given challenges; the claim behind them reads as the run's
                     last claim; every scalar sent is a lift.
  rvOf               a round as the view shows it, of scalars and drawn elements.
  varRounds_of, readAll_of, leadScalars_of   THE READER RETURNS on such rounds: the converse of
                     Part/MaskedSumShape.lean's readAll_spec.
  honest_read        all together, for a call with ends: for any lead, mu, eps, target, challenges
                     and end values, and any run from mu + eps T: there are rounds t that readAll
                     takes, with just these letters, whose movesOf IS the run.
  honest_read_tq     the same at the run "honest tq" (OnBytes/Desc/First/P1/SumTruth.lean): each
                     round's completed polynomial is tq of the challenges in front of it.
sentFrom, poly_complete and lift_run FOLLOW CLOSELY OnBytes/Desc/First/NormBridge/HonestRounds.lean,
which has them over verify-on-bytes's plain record
(OnBytes.Psc.Weight, movesP), for weights whose constant coefficient is derived. New here: this
part's own text; the plain sum; the rounds as the view shows them; that the reader returns.

-/
import Johnson.Desc.Part.MaskedSumTruth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
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

theorem sentFrom_lift (lift : K → E) (q : K[X]) : ∀ (n s : ℕ) (x : E),
    x ∈ sentFrom lift q s n → ∃ k, x = lift k
  | 0, _, _, h => by simp [sentFrom] at h
  | n + 1, s, x, h => by
    rcases List.mem_cons.mp h with h | h
    · exact ⟨_, h⟩
    · exact sentFrom_lift lift q n (s + 1) x h

/-- What an honest prover sends for the polynomial q in the variable v. -/
def sentOf (lift : K → E) : Var → K[X] → List E
  | .plain d, q => lift (q.coeff 0) :: sentFrom lift q 2 (d - 2)
  | .point _ d, q => sentFrom lift q 1 (d - 1)

theorem sentOf_length (lift : K → E) (v : Var) (q : K[X]) (h2 : 2 ≤ v.d) :
    (sentOf lift v q).length + 1 = v.d := by
  cases v with
  | plain d =>
    have h : 2 ≤ d := h2
    show (sentFrom lift q 2 (d - 2)).length + 1 + 1 = d
    rw [sentFrom_length]
    omega
  | point z d =>
    have h : 2 ≤ d := h2
    show (sentFrom lift q 1 (d - 1)).length + 1 = d
    rw [sentFrom_length]
    omega

theorem sentOf_lift (lift : K → E) (v : Var) (q : K[X]) (x : E) (h : x ∈ sentOf lift v q) :
    ∃ k, x = lift k := by
  cases v with
  | plain d =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨_, h⟩
    · exact sentFrom_lift lift q _ _ x h
  | point z d => exact sentFrom_lift lift q _ _ x h

/-- Two polynomials with one sum that agree in all coefficients but one, whose moment is not 0. -/
theorem poly_eq_of (w : Wt K) (j0 : ℕ) (hj : j0 < w.d) (hm : w.mom j0 ≠ 0) (p q : K[X])
    (hs : w.sum p = w.sum q) (hc : ∀ i, i ≠ j0 → p.coeff i = q.coeff i) : p = q := by
  have h0 : ∑ i ∈ Finset.range w.d, w.mom i * (p.coeff i - q.coeff i) = 0 := by
    have e : ∀ i ∈ Finset.range w.d, w.mom i * (p.coeff i - q.coeff i) =
        w.mom i * p.coeff i - w.mom i * q.coeff i := fun i _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hs
  rw [Finset.sum_eq_single j0 (fun i _ hi => by rw [hc i hi, sub_self, mul_zero])
    (fun h => absurd (Finset.mem_range.mpr hj) h)] at h0
  have h1 : p.coeff j0 = q.coeff j0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hm)
  ext i
  by_cases hi : i = j0
  · rw [hi]
    exact h1
  · exact hc i hi

/-- **"complete" gives back the true polynomial.** -/
theorem poly_complete (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (v : Var) (h2 : 2 ≤ v.d)
    (q : K[X]) (hq : q.natDegree < v.d) (c : E) (hsum : (v.wt ρ).sum q = ρ.val c) :
    polyOf ρ (complete v (sentOf lift v q) c) = q := by
  have hs := (complete_sum ρ v (sentOf lift v q) c (sentOf_length lift v q h2) h2).trans hsum.symm
  cases v with
  | plain d =>
    have hd : 2 ≤ d := h2
    have hqd : q.natDegree < d := hq
    refine poly_eq_of (Var.wt ρ (.plain d)) 1 (by show 1 < d; omega)
      (by show (if (1 : ℕ) = 0 then (2 : K) else 1) ≠ 0; simp) _ q hs fun i hi => ?_
    rw [polyOf_coeff]
    show ρ.val ((lift (q.coeff 0) :: _ :: sentFrom lift q 2 (d - 2)).getD i zeroE) = _
    match i, hi with
    | 0, _ => exact hlift _
    | i + 2, _ =>
      rw [List.getD_cons_succ, List.getD_cons_succ, sentFrom_getD]
      by_cases h : i < d - 2
      · rw [if_pos h, hlift, Nat.add_comm]
      · rw [if_neg h, ρ.zero]
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  | point z d =>
    have hd : 2 ≤ d := h2
    have hqd : q.natDegree < d := hq
    refine poly_eq_of (Var.wt ρ (.point z d)) 0 (by show 0 < d; omega)
      (by show (if (0 : ℕ) = 0 then (1 : K) else ρ.val z) ≠ 0; simp) _ q hs fun i hi => ?_
    rw [polyOf_coeff]
    show ρ.val ((_ :: sentFrom lift q 1 (d - 1)).getD i zeroE) = _
    match i, hi with
    | i + 1, _ =>
      rw [List.getD_cons_succ, sentFrom_getD]
      by_cases h : i < d - 1
      · rw [if_pos h, hlift, Nat.add_comm]
      · rw [if_neg h, ρ.zero]
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ## A run -/

/-- **From polynomials to elements.** -/
theorem lift_run (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) :
    ∀ (vs : List Var), (∀ v ∈ vs, 2 ≤ v.d) →
    ∀ (ms : List (K[X] × K)) (rsE : List E) (c0 : E) (cf : K),
    Chain (vs.map (Var.wt ρ)) ms (ρ.val c0) cf → ms.map (·.2) = rsE.map ρ.val →
    ∃ l : List (List E × E), Lens vs l ∧ l.map (·.2) = rsE ∧ movesOf ρ vs l c0 = ms ∧
      ρ.val (after vs l c0) = cf ∧ ∀ x ∈ l, ∀ s ∈ x.1, ∃ k, s = lift k := by
  intro vs
  induction vs with
  | nil =>
    intro _ ms rsE c0 cf hc hr
    cases ms with
    | nil =>
      cases rsE with
      | nil => exact ⟨[], trivial, rfl, rfl, hc, by simp⟩
      | cons r rs => simp at hr
    | cons m ms => exact absurd hc (by simp [OnBytes.Desc.First.P1.Chain])
  | cons v vs ih =>
    intro hv ms rsE c0 cf hc hr
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
        have h2 : 2 ≤ v.d := hv v (by simp)
        have hg' : m.1.natDegree < v.d := by
          rw [← Var.wt_d ρ v]
          exact hg
        have hp := poly_complete ρ lift hlift v h2 m.1 hg' c0 hsum
        have hc1 : ρ.val (valueAt (complete v (sentOf lift v m.1) c0) r) = m.1.eval m.2 := by
          rw [hr1]
          conv_rhs => rw [← hp]
          exact (polyOf_eval ρ r _).symm
        obtain ⟨l, a1, a2, a3, a4, a5⟩ := ih (fun u hu => hv u (by simp [hu])) ms rs
          (valueAt (complete v (sentOf lift v m.1) c0) r) cf (by rw [hc1]; exact hrest) hr2
        refine ⟨(sentOf lift v m.1, r) :: l, ⟨sentOf_length lift v m.1 h2, h2, a1⟩,
          by rw [List.map_cons, a2], ?_, a4, ?_⟩
        · show (polyOf ρ (complete v (sentOf lift v m.1) c0), ρ.val r) ::
              movesOf ρ vs l (valueAt (complete v (sentOf lift v m.1) c0) r) = m :: ms
          rw [hp, a3, ← hr1]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact fun s hs => sentOf_lift lift v m.1 s hs
          · exact a5 x hx

end VerifiableInference.Desc.Part.MaskedSum

end

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model

/-! ## Rounds as the view shows them; the reader returns -/

/-- A round of scalars and drawn elements. -/
def rvOf (sent drawn : List E) : Fmt.RoundView :=
  { vals := sent.map fun s => .e s.triple, drawn := ⟨drawn.map (·.triple), [], [], none⟩ }

theorem scalars_of : ∀ sent : List E, scalars (sent.map fun s => Fmt.ItemValue.e s.triple) = some sent
  | [] => rfl
  | s :: l => by
    show (scalars (l.map fun s => Fmt.ItemValue.e s.triple)).map (E.ofTriple s.triple :: ·) = _
    rw [scalars_of l, E.ofTriple_triple]
    rfl

theorem drawn_of (drawn : List E) : (drawn.map (·.triple)).map E.ofTriple = drawn := by
  rw [List.map_map]
  have e : (E.ofTriple ∘ fun x : E => x.triple) = id := funext fun x => E.ofTriple_triple x
  rw [e, List.map_id]

theorem roundOf_of (sent drawn : List E) :
    roundOf sent.length drawn.length (rvOf sent drawn) = some (sent, drawn) := by
  unfold roundOf rvOf
  simp only [scalars_of, Option.bind_some, List.length_map, beq_self_eq_true, Bool.and_self,
    if_true, drawn_of]

/-- The variables' rounds. -/
def roundsRV (l : List (List E × E)) : List Fmt.RoundView := l.map fun x => rvOf x.1 [x.2]

theorem varRounds_of : ∀ (vs : List Var) (l : List (List E × E)) (rest : List Fmt.RoundView),
    Lens vs l → varRounds vs (roundsRV l ++ rest) = some (l, rest)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | v :: vs, x :: l, rest, ⟨hl, _, hr⟩ => by
    have e : v.d - 1 = x.1.length := by omega
    show (match roundOf (v.d - 1) 1 (rvOf x.1 [x.2]), varRounds vs (roundsRV l ++ rest) with
      | some (s, [g]), some (l, rest) => some ((s, g) :: l, rest)
      | _, _ => none) = _
    rw [e, show (1 : Nat) = [x.2].length from rfl, roundOf_of, varRounds_of vs l rest hr]

/-- The sumcheck's rounds, whole, for a call with ends. -/
def roundsOfRun (front : List E) (mu eps : E) (l : List (List E × E)) (values : List E) :
    List Fmt.RoundView :=
  rvOf (front ++ [mu]) [eps] :: (roundsRV l ++ [rvOf values []])

theorem firstRound_of (k : Call) (front : List E) (hf : front.length = k.lead) (mu eps : E) :
    firstRound k (rvOf (front ++ [mu]) [eps]) = some (front, [mu], [eps]) := by
  unfold firstRound
  have e : k.lead + 1 = (front ++ [mu]).length := by
    rw [List.length_append, hf]
    rfl
  rw [e, show (1 : Nat) = [eps].length from rfl, roundOf_of]
  simp [← hf]

/-- **THE READER RETURNS.** -/
theorem readAll_of (lead : Nat) (vs : List Var) (e : Ends) (front : List E)
    (hf : front.length = lead) (mu eps : E) (l : List (List E × E))
    (hl : Lens (⟨lead, vs, some e⟩ : Call).all l) (values : List E) (hv : values.length = e.n) :
    readAll ⟨lead, vs, some e⟩ (roundsOfRun front mu eps l values) =
      some ⟨mu, eps, l, values⟩ := by
  unfold readAll roundsOfRun
  simp only
  rw [firstRound_of ⟨lead, vs, some e⟩ front hf, varRounds_of _ l _ hl]
  simp only
  rw [← hv, show (0 : Nat) = ([] : List E).length from rfl, roundOf_of]
  rfl

theorem leadScalars_of (k : Call) (front : List E) (hf : front.length = k.lead) (mu eps : E)
    (l : List (List E × E)) (values : List E) :
    leadScalars k (roundsOfRun front mu eps l values) = some front := by
  unfold leadScalars roundsOfRun
  simp only [List.head?_cons, Option.bind_some]
  rw [firstRound_of k front hf]
  rfl

theorem roundsOfRun_length (front : List E) (mu eps : E) (l : List (List E × E))
    (values : List E) : (roundsOfRun front mu eps l values).length = l.length + 2 := by
  unfold roundsOfRun roundsRV
  simp

/-- Whatever holds of all the letters holds of every scalar and every drawn element of the
rounds. -/
theorem roundsOfRun_all (P : E → Prop) (front : List E) (mu eps : E) (l : List (List E × E))
    (values : List E) (hf : ∀ x ∈ front, P x) (hmu : P mu) (heps : P eps)
    (hl : ∀ x ∈ l, (∀ s ∈ x.1, P s) ∧ P x.2) (hv : ∀ x ∈ values, P x) :
    ∀ r ∈ roundsOfRun front mu eps l values,
      (∀ x, Fmt.ItemValue.e x ∈ r.vals → P (E.ofTriple x)) ∧
      ∀ x, x ∈ r.drawn.elems → P (E.ofTriple x) := by
  have one : ∀ sent drawn : List E, (∀ s ∈ sent, P s) → (∀ s ∈ drawn, P s) →
      (∀ x, Fmt.ItemValue.e x ∈ (rvOf sent drawn).vals → P (E.ofTriple x)) ∧
      ∀ x, x ∈ (rvOf sent drawn).drawn.elems → P (E.ofTriple x) := by
    intro sent drawn h1 h2
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨s, hs, e⟩ := List.mem_map.mp hx
      have e' : s.triple = x := by injection e
      rw [← e', E.ofTriple_triple]
      exact h1 s hs
    · obtain ⟨s, hs, e⟩ := List.mem_map.mp hx
      rw [← e, E.ofTriple_triple]
      exact h2 s hs
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · refine one _ _ (fun s hs => ?_) (fun s hs => ?_)
    · rcases List.mem_append.mp hs with h | h
      · exact hf s h
      · rw [List.mem_singleton.mp h]
        exact hmu
    · rw [List.mem_singleton.mp hs]
      exact heps
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      refine one _ _ (hl x hx).1 fun s hs => ?_
      rw [List.mem_singleton.mp hs]
      exact (hl x hx).2
    · rw [List.mem_singleton.mp hr]
      exact one _ _ hv (by simp)

end VerifiableInference.Desc.Part.MaskedSum

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## All together -/

/-- **FOR ANY RUN OF POLYNOMIALS FROM mu + eps T THERE ARE ROUNDS THAT THE READER TAKES AND WHOSE
movesOf IS THE RUN.** P: any property of elements that all the given letters and all lifts have
(for a caller that wants canonical writings). -/
theorem honest_read (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (lead : Nat) (vs : List Var)
    (e : Ends) (hk : shapeOk ⟨lead, vs, some e⟩ = true) (front : List E)
    (hf : front.length = lead) (mu eps T : E) (rsE values : List E) (hv : values.length = e.n)
    (ms : List (K[X] × K)) (cf : K)
    (hc : Chain ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) ms
      (ρ.val (addE mu (mulE eps T))) cf)
    (hr : ms.map (·.2) = rsE.map ρ.val) :
    ∃ l : List (List E × E),
      readAll ⟨lead, vs, some e⟩ (roundsOfRun front mu eps l values) = some ⟨mu, eps, l, values⟩ ∧
      leadScalars ⟨lead, vs, some e⟩ (roundsOfRun front mu eps l values) = some front ∧
      l.map (·.2) = rsE ∧
      movesOf ρ (⟨lead, vs, some e⟩ : Call).all l (addE mu (mulE eps T)) = ms ∧
      ρ.val (after (⟨lead, vs, some e⟩ : Call).all l (addE mu (mulE eps T))) = cf ∧
      (roundsOfRun front mu eps l values).length = vs.length + 3 ∧
      ∀ P : E → Prop, (∀ k, P (lift k)) → (∀ x ∈ front, P x) → P mu → P eps → (∀ x ∈ rsE, P x) →
        (∀ x ∈ values, P x) → ∀ r ∈ roundsOfRun front mu eps l values,
          (∀ x, Fmt.ItemValue.e x ∈ r.vals → P (E.ofTriple x)) ∧
          ∀ x, x ∈ r.drawn.elems → P (E.ofTriple x) := by
  obtain ⟨l, a1, a2, a3, a4, a5⟩ :=
    lift_run ρ lift hlift _ (two_le_all hk) ms rsE (addE mu (mulE eps T)) cf hc hr
  refine ⟨l, readAll_of lead vs e front hf mu eps l a1 values hv,
    leadScalars_of ⟨lead, vs, some e⟩ front hf mu eps l values, a2, a3, a4, ?_, ?_⟩
  · rw [roundsOfRun_length]
    have h1 : l.length = rsE.length := by rw [← a2, List.length_map]
    have h2 : ms.length = rsE.length := by
      have := congrArg List.length hr
      simpa using this
    have h3 : (movesOf ρ (⟨lead, vs, some e⟩ : Call).all l (addE mu (mulE eps T))).map (·.2) =
        l.map fun x => ρ.val x.2 := movesOf_chal ρ _ l _ a1
    have h4 : ∀ (us : List Var) (m : List (List E × E)), Lens us m → m.length = us.length := by
      intro us
      induction us with
      | nil =>
        intro m hm
        cases m with
        | nil => rfl
        | cons _ _ => exact hm.elim
      | cons u us ih =>
        intro m hm
        cases m with
        | nil => exact hm.elim
        | cons x m => simp [ih m hm.2.2]
    have h5 := h4 _ l a1
    have h6 : (⟨lead, vs, some e⟩ : Call).all.length = vs.length + 1 := by
      show (vs ++ [Var.point zeroE (e.dY + 1)]).length = _
      simp
    omega
  · intro P hP hPf hPm hPe hPr hPv
    refine roundsOfRun_all P front mu eps l values hPf hPm hPe
      (fun x hx => ⟨fun s hs => ?_, ?_⟩) hPv
    · obtain ⟨k, rfl⟩ := a5 x hx s hs
      exact hP k
    · exact hPr x.2 (by rw [← a2]; exact List.mem_map_of_mem hx)

/-- **The same at the honest run of tq**: each round's completed polynomial is tq of the challenges
in front of it. -/
theorem honest_read_tq (lift : K → E) (hlift : ∀ k, ρ.val (lift k) = k) (lead : Nat)
    (vs : List Var) (e : Ends) (hk : shapeOk ⟨lead, vs, some e⟩ = true) (front : List E)
    (hf : front.length = lead) (mu eps T : E) (rsE values : List E) (hv : values.length = e.n)
    (tq : List K → K[X]) (cf : K)
    (hc : Chain ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) (honest tq [] (rsE.map ρ.val))
      (ρ.val (addE mu (mulE eps T))) cf) :
    ∃ l : List (List E × E),
      readAll ⟨lead, vs, some e⟩ (roundsOfRun front mu eps l values) = some ⟨mu, eps, l, values⟩ ∧
      leadScalars ⟨lead, vs, some e⟩ (roundsOfRun front mu eps l values) = some front ∧
      l.map (·.2) = rsE ∧
      (∀ i m, (movesOf ρ (⟨lead, vs, some e⟩ : Call).all l (addE mu (mulE eps T)))[i]? = some m →
        m.1 = tq (((movesOf ρ (⟨lead, vs, some e⟩ : Call).all l
          (addE mu (mulE eps T))).take i).map (·.2))) ∧
      ρ.val (after (⟨lead, vs, some e⟩ : Call).all l (addE mu (mulE eps T))) = cf ∧
      (roundsOfRun front mu eps l values).length = vs.length + 3 ∧
      ∀ P : E → Prop, (∀ k, P (lift k)) → (∀ x ∈ front, P x) → P mu → P eps → (∀ x ∈ rsE, P x) →
        (∀ x ∈ values, P x) → ∀ r ∈ roundsOfRun front mu eps l values,
          (∀ x, Fmt.ItemValue.e x ∈ r.vals → P (E.ofTriple x)) ∧
          ∀ x, x ∈ r.drawn.elems → P (E.ofTriple x) := by
  obtain ⟨l, b1, b2, b3, b4, b5, b6, b7⟩ := honest_read ρ lift hlift lead vs e hk front hf mu eps T
    rsE values hv _ cf hc (honest_chal tq _ [])
  refine ⟨l, b1, b2, b3, fun i m hm => ?_, b5, b6, b7⟩
  rw [b4] at hm ⊢
  have := honest_poly tq _ [] i m hm
  rwa [List.nil_append] at this

end VerifiableInference.Desc.Part.MaskedSum

end
