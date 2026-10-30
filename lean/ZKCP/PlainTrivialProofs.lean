-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PlainTrivialProofs.lean: the proof of ZKCP/PlainTrivial.lean's statement `bf_main`: under the
hypotheses of its statement, the brute-force scheme meets the definition.

In standard terms: proofs in the random-oracle model, with the oracle sampled on demand. The scheme
`bfArg`, with `bfExt` and `bfSim`, and the statement are in ZKCP/PlainTrivial.lean; the statement
concludes `ZKCP.IsZKCPArgWith` (ZKCP/Defs.lean), which implies `ZKCP.IsZKCPArg`
(`IsZKCPArgWith.toIsZKCPArg`, ZKCP/Basic.lean). V~ is the adversary's verifier (`AdvVerifier`,
ZKCP/Defs.lean).
Theorems `bf_complete`, `bf_binding`, `bf_private`, `bf_main`, and the lemmas that they use. Nothing
is assumed beyond the hypotheses of the statements, in the random-oracle model, on Lean's three
axioms. The tools are ZKCP/Lemmas.lean's (an oracle sampled whole is an oracle sampled on demand:
`PrFrom`, `lazyRun`), ZKCP/Basic.lean's, ZKCP/Sanity.lean's and ZKCP/HashToy.lean's; `bfClose`,
`bfSim_consistent`, `bfHit_sum` follow that toy's `closed_le`, `hashSim_consistent`, `sum_hit_le`,
for K strings in the place of one and a simulator that never programs.

Main names:
  `bf_main`: see its statement in ZKCP/PlainTrivial.lean.

How the proof goes (n := |I| (M + 1), u := 2^-λ, as in ZKCP/PlainTrivial.lean; `bfAcc lam K M I`,
defined there, is n u^K):
  One chance rules completeness and binding (`bfBad`, `bfBad_le`): from a table c of answers
    already given: the chance that some pair of which a string is not in c has the key's K answers
    is at most (pairs partly in c) · u + n u^K (a string belongs to one pair: `bfPts_disj`; answers
    outside c are uniform and independent: ZKCP/Lemmas.lean: `U_cylinder`).
  Off that event V's search and the extractor's search find the same pair (`bfAgree`): a pair has
    the key's answers exactly if all its strings stand in the key maker's trace with these answers.
    V's verdict is a function of (f, ivk, x) (`bfV_run`): so the prover's queries do not enter, and
    ε has no tP (ε: the error of `bf_binding`; tP: its second argument, the bound on the prover's
    queries).
  `bf_binding`: the key maker's run with its trace, sampled on demand (`bfTraced`); at most tC
    pairs are partly in its table (`bfPart_le`).
  `bf_complete`: the honest key maker's table holds the honest pair's K strings and nothing else
    (`bfAsk_lazy`): no pair is partly in it.
  `bf_private`: the real and the simulated world are one until V~ asks a string of the honest pair
    (`bfClose`); a string names one salt, so t queries meet at most t of the M + 1 salts
    (`bfHit_sum`).

Notation: `bfArg`: the brute-force scheme (ZKCP/PlainTrivial.lean), a scheme with empty proofs,
whose verifier searches all pairs (index, salt) for the key; a pair: (index, salt), an element of
`I × Fin (M + 1)` (`bfPts`, ZKCP/PlainTrivial.lean); `K`: ℕ, the number of strings of a pair
(`bfPts`, ZKCP/PlainTrivial.lean); `M`: ℕ, there are M + 1 salts (ZKCP/PlainTrivial.lean).

Limits: what the head of ZKCP/PlainTrivial.lean lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import ZKCP.PlainTrivial
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace TopC
open ZKCP MeasureTheory
open scoped ENNReal

/-! ## The coding is one to one -/

theorem bfRep_inj {a b : ℕ} {l l' : List Bool}
    (h : List.replicate a true ++ false :: l = List.replicate b true ++ false :: l') :
    a = b ∧ l = l' := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact ⟨rfl, by simpa using h⟩
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨e, e'⟩ := ih h
      exact ⟨by rw [e], e'⟩

theorem bfPt_inj {k a σ k' a' σ' : ℕ} (h : bfPt k a σ = bfPt k' a' σ') :
    k = k' ∧ a = a' ∧ σ = σ' := by
  obtain ⟨e1, h1⟩ := bfRep_inj h
  obtain ⟨e2, h2⟩ := bfRep_inj h1
  have e3 := congrArg List.length h2
  simp only [List.length_replicate] at e3
  exact ⟨e1, e2, e3⟩

section
variable {lam : ℕ} (K M : ℕ) {I : Type} [Fintype I]

theorem bfPts_length (p : I × Fin (M + 1)) : (bfPts K M p).length = K := by simp [bfPts]

theorem bfPts_nodup (p : I × Fin (M + 1)) : (bfPts K M p).Nodup :=
  List.Nodup.map (fun _ _ h => (bfPt_inj h).1) List.nodup_range

/-- a string belongs to one pair at most -/
theorem bfPts_disj {p p' : I × Fin (M + 1)} {q : Str}
    (h : q ∈ bfPts K M p) (h' : q ∈ bfPts K M p') : p = p' := by
  simp only [bfPts, List.mem_map, List.mem_range] at h h'
  obtain ⟨k, _, e⟩ := h
  obtain ⟨k', _, e'⟩ := h'
  obtain ⟨_, e2, e3⟩ := bfPt_inj (e.trans e'.symm)
  exact Prod.ext ((Fintype.equivFin I).injective (Fin.ext e2)) (Fin.ext e3)

theorem bfPts_ne_nil (hK : 0 < K) (p : I × Fin (M + 1)) : bfPts K M p ≠ [] := fun h => by
  have := bfPts_length K M p
  rw [h] at this
  simp at this
  omega

theorem bfAll_mem (p : I × Fin (M + 1)) : p ∈ bfAll (I := I) M := by simp [bfAll]

end

/-! ## What the parties compute at a fixed oracle -/

section
variable {lam : ℕ}

theorem bfAsk_run (f : Oracle lam) (qs : List Str) :
    (bfAsk lam qs).run f = PMF.pure (qs.map f) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [bfAsk, OComp.run, run_bind, ih, PMF.pure_bind, List.map_cons]

variable (K M : ℕ) {I : Type} [Fintype I]

open Classical in
theorem bfSearch_run (f : Oracle lam) (ivk : List (Digest lam)) (ps : List (I × Fin (M + 1))) :
    (bfSearch lam K M ivk ps).run f =
      PMF.pure (ps.find? fun p => decide ((bfPts K M p).map f = ivk)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [bfSearch, run_bind, bfAsk_run, PMF.pure_bind, List.find?_cons]
    by_cases h : (bfPts K M p).map f = ivk
    · simp [h, OComp.run]
    · simp [h, ih]

end

/-! ## The one chance that matters: a pair of which something was not asked has the key's answers -/

section
variable {lam : ℕ} (K M : ℕ) {I : Type} [Fintype I]

/-- the oracles at which some pair with a string outside the table c has the answers ivk -/
def bfBad (c : Cache lam) (ivk : List (Digest lam)) : Set (Oracle lam) :=
  {f | ∃ p : I × Fin (M + 1), (bfPts K M p).map (over c f) = ivk ∧ ∃ q ∈ bfPts K M p, c q = none}

theorem bfU_le_one : (((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹) ≤ 1 :=
  ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)

open Classical in
/-- the pairs of which something stands in the table and something does not -/
def bfPart (c : Cache lam) : Finset (I × Fin (M + 1)) :=
  Finset.univ.filter fun p => (∃ q ∈ bfPts K M p, c q ≠ none) ∧ ∃ q ∈ bfPts K M p, c q = none

open Classical in
theorem bfBad_one (c : Cache lam) (ivk : List (Digest lam)) (p : I × Fin (M + 1)) :
    U lam {f | (bfPts K M p).map (over c f) = ivk ∧ ∃ q ∈ bfPts K M p, c q = none} ≤
      if p ∈ bfPart K M c then (((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹) else (((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹) ^ K := by
  by_cases hne : {f : Oracle lam | (bfPts K M p).map (over c f) = ivk ∧
    ∃ q ∈ bfPts K M p, c q = none}.Nonempty
  · obtain ⟨f₀, h₀, q₀, hq₀, hc₀⟩ := hne
    have hsub : {f : Oracle lam | (bfPts K M p).map (over c f) = ivk ∧
          ∃ q ∈ bfPts K M p, c q = none} ⊆
        {f | ∀ q ∈ (bfPts K M p).toFinset.filter (fun q => c q = none), f q = f₀ q} := by
      rintro f ⟨hf, _⟩ q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      have := List.map_inj_left.1 (hf.trans h₀.symm) q (List.mem_toFinset.1 hq1)
      simpa [over, hq2] using this
    refine le_trans (measure_mono hsub) ?_
    rw [U_cylinder]
    split
    · refine le_trans
        (pow_le_pow_right_of_le_one'
          bfU_le_one (Finset.card_pos.2 ⟨q₀, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hq₀, hc₀⟩⟩))
        ?_
      rw [pow_one]
    · rename_i hp
      have hall : ∀ q ∈ bfPts K M p, c q = none := fun q hq => by
        by_contra hn
        exact hp (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨q, hq, hn⟩, ⟨q₀, hq₀, hc₀⟩⟩)
      rw [Finset.filter_true_of_mem (fun q hq => hall q (List.mem_toFinset.1 hq)),
        List.toFinset_card_of_nodup (bfPts_nodup K M p), bfPts_length]
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
    exact zero_le _

open Classical in
theorem bfBad_le (c : Cache lam) (ivk : List (Digest lam)) :
    U lam (bfBad (I := I) K M c ivk) ≤
      ((bfPart (I := I) K M c).card : ℝ≥0∞) * ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ + bfAcc lam K M I := by
  have e : bfBad (I := I) K M c ivk =
      ⋃ p ∈ (Finset.univ : Finset (I × Fin (M + 1))),
        {f | (bfPts K M p).map (over c f) = ivk ∧ ∃ q ∈ bfPts K M p, c q = none} := by
    ext f
    simp [bfBad]
  rw [e]
  refine le_trans (measure_biUnion_finset_le _ _)
    (le_trans (Finset.sum_le_sum fun p _ => bfBad_one K M c ivk p) ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  refine add_le_add (le_of_eq ?_) ?_
  · have e2 : (Finset.univ.filter fun p : I × Fin (M + 1) => p ∈ bfPart K M c) = bfPart K M c := by
      ext p
      simp
    rw [e2]
  · unfold bfAcc
    gcongr
    exact le_trans (Finset.card_le_univ _) le_rfl

end

/-! ## A run with its trace, sampled on demand: the table at the end is the table at the start and the trace -/

section
variable {lam : ℕ} {α : Type}

theorem bfLazy_le (c : Cache lam) (q : Str) (F : Digest lam × Cache lam → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ r c₁, Ext c [(q, r)] c₁ → F (r, c₁) ≤ B) :
    expect (lazyAnswer c q) F ≤ B := by
  unfold lazyAnswer
  cases hq : c q with
  | none =>
    simp only [expect_map]
    refine expect_le_of_le _ fun r => h r _ fun q' r' => ?_
    by_cases e : q' = q
    · subst e
      simp [Function.update_self, hq, eq_comm]
    · simp [e]
  | some r =>
    simp only [expect_pure]
    refine h r c fun q' r' => ⟨Or.inl, ?_⟩
    rintro (h1 | h1)
    · exact h1
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      rw [h1.1, h1.2]
      exact hq

theorem bfExt_cons {c c₁ c₂ : Cache lam} {q : Str} {r : Digest lam} {tr : Trace lam}
    (h1 : Ext c [(q, r)] c₁) (h2 : Ext c₁ tr c₂) :
    Ext c ((q, r) :: tr) c₂ := fun q' r' => by
  rw [h2 q' r', h1 q' r']
  simp only [List.mem_cons]
  tauto

theorem bfTraced (B : ℝ≥0∞) (m : OComp lam α) :
    ∀ (t : ℕ) (c : Cache lam) (F : α × Trace lam → Cache lam → ℝ≥0∞), m.QueryBound t →
      (∀ a tr c', Ext c tr c' → tr.length ≤ t → F (a, tr) c' ≤ B) →
      expect (m.withTrace.lazyRun c) (fun o => F o.1 o.2) ≤ B := by
  induction m with
  | pure a =>
    intro t c F _ hB
    simp only [OComp.withTrace, OComp.lazyRun, expect_pure]
    exact hB a [] c (fun q r => by simp) (Nat.zero_le _)
  | sample n k ih =>
    intro t c F hb hB
    simp only [OComp.withTrace, OComp.lazyRun, expect_bind]
    exact expect_le_of_le _ fun r => ih r t c F (hb r) hB
  | query q k ih =>
    intro t c F hb hB
    cases t with
    | zero => exact absurd hb (by simp [OComp.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      simp only [OComp.withTrace, OComp.lazyRun, OComp.lazyRun_bind, expect_bind, expect_pure]
      exact bfLazy_le c q _ B fun r c₁ h1 =>
          ih r t c₁ (fun o c' => F (o.1, (q, r) :: o.2) c') (hb' r) fun a tr c' h2 hl =>
        hB a ((q, r) :: tr) c' (bfExt_cons h1 h2) (by simp only [List.length_cons]; omega)

end

/-! ## Off the bad set V's search and the extractor's search find the same pair -/

section
variable {lam : ℕ} (K M : ℕ) {I X W PP : Type} [Fintype I]

theorem bfAgree {c : Cache lam} {tr : Trace lam} (hE : Ext (fun _ => none) tr c)
    {ivk : List (Digest lam)} {f : Oracle lam}
    (hf : f ∉ bfBad (I := I) K M c ivk) (p : I × Fin (M + 1)) :
    (bfPts K M p).map (over c f) = ivk ↔
    List.Forall₂ (fun q d => (q, d) ∈ tr) (bfPts K M p) ivk := by
  constructor
  · intro h
    have hall : ∀ q ∈ bfPts K M p, c q ≠ none := fun q hq hn => hf ⟨p, h, q, hq, hn⟩
    rw [← h, List.forall₂_map_right_iff, List.forall₂_same]
    intro q hq
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (hall q hq)
    have : over c f q = r := by simp [over, hr]
    rw [this]
    exact ((hE q r).1 hr).resolve_left (by simp)
  · intro h
    have h2 : List.Forall₂ (fun q d => over c f q = d) (bfPts K M p) ivk := h.imp fun q d hqd => by
      have := (hE q d).2 (Or.inr hqd)
      simp [over, this]
    have h3 : List.Forall₂ (fun a b => a = b) ((bfPts K M p).map (over c f)) ivk :=
      List.forall₂_map_left_iff.2 h2
    exact List.forall₂_eq_eq_eq ▸ h3

open Classical in
theorem bfV_run (R : IndexedRelation I X W PP) (g : Oracle lam) (ivk : List (Digest lam)) (x : X) :
    ((bfArg lam K M R).V ivk x ()).run g =
      PMF.pure (((bfAll M).find? fun p : I × Fin (M + 1) => decide ((bfPts K M p).map g = ivk)).elim
          false fun p => decide (∃ w, R.rel p.1 x w)) := by
  simp only [bfArg, run_bind, bfSearch_run, PMF.pure_bind, OComp.run]

end

/-! ## Index binding -/

section
variable {lam : ℕ} (K M : ℕ) {I X W PP : Type} [Fintype I]

open Classical in
theorem bfPart_le {c : Cache lam} {tr : Trace lam} (hE : Ext (fun _ => none) tr c) :
    (bfPart (I := I) K M c).card ≤ tr.length := by
  refine le_trans
    (Finset.card_le_card_of_injOn (t := (tr.map Prod.fst).toFinset)
      (fun p => if h : ∃ q ∈ bfPts K M p, c q ≠ none then h.choose else []) ?_ ?_)
    (le_trans (List.toFinset_card_le _) (by simp))
  · intro p hp
    have h : ∃ q ∈ bfPts K M p, c q ≠ none := (Finset.mem_filter.1 hp).2.1
    simp only [dif_pos h]
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h.choose_spec.2
    have := ((hE _ r).1 hr).resolve_left (by simp)
    exact Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_map.2 ⟨_, this, rfl⟩))
  · intro p hp p' hp' e
    have h : ∃ q ∈ bfPts K M p, c q ≠ none := (Finset.mem_filter.1 hp).2.1
    have h' : ∃ q ∈ bfPts K M p', c q ≠ none := (Finset.mem_filter.1 hp').2.1
    simp only [dif_pos h, dif_pos h'] at e
    exact bfPts_disj K M h.choose_spec.1 (e ▸ h'.choose_spec.1)

/-- from a table c: a computation that ends badly only at oracles of the bad set ends badly with at
most that set's chance -/
theorem bfFrom_le {β : Type} (c : Cache lam) (m : OComp lam β) (E : Set β) (S : Set (Oracle lam))
    (h : ∀ f, f ∉ S → prob (m.run (over c f)) E = 0) : PrFrom c m E ≤ U lam S := by
  classical
  unfold PrFrom
  refine le_trans (lintegral_mono fun f => ?_) (lintegral_indicator_one_le S)
  by_cases hf : f ∈ S
  · simp only [Set.indicator_of_mem hf, Pi.one_apply]
    exact prob_le_one _ _
  · rw [h f hf]
    exact zero_le _

open Classical in
theorem bf_binding (R : IndexedRelation I X W PP) (w0 : W) :
    HasIndexBindingWith R (bfArg lam K M R) (bfExt lam K M R w0)
      (fun tC _ => (tC : ℝ≥0∞) * ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ + bfAcc lam K M I) := by
  intro tC tP St Ct Pt hC _
  have hexp : bindingExp (bfArg lam K M R) (bfExt lam K M R w0) Ct Pt = Ct.withTrace.bind fun o1 =>
      (Pt o1.1.2).withTrace.bind fun o2 => ((bfArg lam K M R).V o1.1.1 o2.1.1 o2.1.2).bind fun b =>
        .pure (⟨b, bfEi lam K M o1.1.1 o1.2,
            o2.1.1,
            (bfExt lam K M R w0).Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ : BindingOutcome I X W) := rfl
  rw [Pr_eq_PrFrom, hexp, PrFrom_bind]
  refine bfTraced _ Ct tC (fun _ => none)
    (fun o c' =>
      PrFrom c' ((Pt o.1.2).withTrace.bind fun o2 =>
          ((bfArg lam K M R).V o.1.1 o2.1.1 o2.1.2).bind fun b =>
            .pure (⟨b, bfEi lam K M o.1.1 o.2, o2.1.1,
                (bfExt lam K M R w0).Ew o.1.1 o.2 o2.1.1 o2.1.2 o2.2⟩ : BindingOutcome I X W))
        (bindingBad R))
    hC ?_
  rintro ⟨ivk, st⟩ tr c' hE hl
  refine le_trans (bfFrom_le c' _ _ (bfBad (I := I) K M c' ivk) fun f hf => ?_)
    (le_trans (bfBad_le K M c' ivk) ?_)
  · simp only [run_bind, prob_bind]
    refine (expect_congr _ fun o2 => ?_).trans (expect_zero _)
    obtain ⟨⟨x, π⟩, trP⟩ := o2
    cases π
    have hfind : ((bfAll M).find? fun p : I × Fin (M + 1) =>
          decide ((bfPts K M p).map (over c' f) = ivk)) =
        (bfAll M).find? fun p : I × Fin (M + 1) =>
          decide (List.Forall₂ (fun q d => (q, d) ∈ tr) (bfPts K M p) ivk) := by
      congr 1
      funext p
      exact decide_eq_decide.2 (bfAgree K M hE hf p)
    simp only [bfV_run, expect_pure, OComp.run, prob_pure]
    rw [if_neg]
    rintro ⟨hacc, hbad⟩
    simp only [hfind] at hacc
    cases hp : (bfAll M).find? fun p : I × Fin (M + 1) =>
        decide (List.Forall₂ (fun q d => (q, d) ∈ tr) (bfPts K M p) ivk) with
    | none => simp [hp] at hacc
    | some p =>
      simp only [hp, Option.elim_some, decide_eq_true_eq] at hacc
      have hi : bfEi lam K M ivk tr = some p.1 := by simp [bfEi, hp]
      have hw : ∃ w, R.rel' (bfEi lam K M ivk tr) x w := by rw [hi]; exact hacc
      rcases hbad with hb | hb
      · exact hb (by simp only [hi]; exact hacc)
      · refine hb ?_
        simp only [bfExt, dif_pos hw]
        exact hw.choose_spec
  · exact add_le_add (mul_le_mul_left (Nat.cast_le.2 (le_trans (bfPart_le K M hE) hl)) _) le_rfl

end

/-! ## Completeness -/

section
variable {lam : ℕ}

theorem bfExt_off {c c₁ : Cache lam} {q : Str} {r : Digest lam} (h : Ext c [(q, r)] c₁)
    {q' : Str} (hq : q' ≠ q) : c₁ q' = c q' :=
  Option.ext fun r' => by
    show c₁ q' = some r' ↔ c q' = some r'
    rw [h q' r']
    simp [hq]

theorem bfAsk_lazy (B : ℝ≥0∞) :
    ∀ (qs : List Str) (c : Cache lam) (F : List (Digest lam) × Cache lam → ℝ≥0∞), qs.Nodup →
      (∀ ds c', (∀ q, q ∉ qs → c' q = c q) → qs.map c' = ds.map some → F (ds, c') ≤ B) →
      expect ((bfAsk lam qs).lazyRun c) F ≤ B := by
  intro qs
  induction qs with
  | nil =>
    intro c F _ h
    simp only [bfAsk, OComp.lazyRun, expect_pure]
    exact h [] c (fun _ _ => rfl) rfl
  | cons q qs ih =>
    intro c F hnd h
    simp only [bfAsk, OComp.lazyRun, OComp.lazyRun_bind, expect_bind, expect_pure]
    refine bfLazy_le c q _ B fun r c₁ h1 =>
      ih c₁ (fun o' => F (r :: o'.1, o'.2)) (List.nodup_cons.1 hnd).2
        fun ds c' hoff hmap => h (r :: ds) c' ?_ ?_
    · intro q' hq'
      rw [List.mem_cons, not_or] at hq'
      rw [hoff q' hq'.2, bfExt_off h1 hq'.1]
    · have e : c' q = some r := by
        rw [hoff q (List.nodup_cons.1 hnd).1]
        exact (h1 q r).2 (Or.inr (by simp))
      simp only [List.map_cons, e, hmap]

theorem bfOver_map (c : Cache lam) (f : Oracle lam) :
    ∀ (l : List Str) (ds : List (Digest lam)), l.map c = ds.map some → l.map (over c f) = ds := by
  intro l
  induction l with
  | nil =>
    intro ds h
    cases ds with
    | nil => rfl
    | cons d ds => simp at h
  | cons q l ih =>
    intro ds h
    cases ds with
    | nil => simp at h
    | cons d ds =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, ih ds h.2, over, h.1, Option.getD_some]

variable (K M : ℕ) {I X W PP : Type} [Fintype I]

open Classical in
theorem bf_complete (hK : 0 < K) (R : IndexedRelation I X W PP) :
    HasCompletenessError R (bfArg lam K M R) (bfAcc lam K M I) := by
  intro i x w hR
  have hexp : completenessExp (bfArg lam K M R) i x w =
      .sample M fun σ =>
        (bfAsk lam (bfPts K M (i, σ))).bind fun ds => (bfArg lam K M R).V ds x () := by
    simp only [completenessExp, sessionExp, bfArg, bind_eq, OComp.bind, bind_assoc']
  rw [Pr_eq_PrFrom, hexp, PrFrom_sample]
  refine expect_le_of_le _ fun σ => ?_
  rw [PrFrom_bind]
  refine bfAsk_lazy _ _ _ _ (bfPts_nodup K M (i, σ)) fun ds c' hoff hmap => ?_
  have hin : ∀ (p : I × Fin (M + 1)) q,
      q ∈ bfPts K M p → c' q ≠ none → p = (i, σ) := fun p q hq hc => by
    by_contra hne
    exact hc (hoff q fun hq' => hne (bfPts_disj K M hq hq'))
  have hfull : ∀ q ∈ bfPts K M (i, σ), c' q ≠ none := fun q hq hn => by
    have : c' q ∈ (bfPts K M (i, σ)).map c' := List.mem_map.2 ⟨q, hq, rfl⟩
    rw [hmap, hn] at this
    simp at this
  refine le_trans (bfFrom_le c' _ _ (bfBad (I := I) K M c' ds) fun f hf => ?_)
    (le_trans (bfBad_le K M c' ds) ?_)
  · rw [bfV_run, prob_pure, if_neg]
    have hm : (bfPts K M (i, σ)).map (over c' f) = ds := bfOver_map c' f _ _ hmap
    cases hp : (bfAll M).find? fun p : I × Fin (M + 1) =>
        decide ((bfPts K M p).map (over c' f) = ds) with
    | none =>
      have := List.find?_eq_none.1 hp (i, σ) (bfAll_mem M _)
      simp [hm] at this
    | some p =>
      have hmp : (bfPts K M p).map (over c' f) = ds := by simpa using List.find?_some hp
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (bfPts_ne_nil K M hK p)
      have hpe : p = (i, σ) := hin p q hq fun hn => hf ⟨p, hmp, q, hq, hn⟩
      subst hpe
      have : ∃ w, R.rel i x w := ⟨w, hR⟩
      simp [this]
  · have he : bfPart (I := I) K M c' = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨⟨q, hq, hc⟩, q', hq', hn⟩ := (Finset.mem_filter.1 hp).2
      have hpe := hin p q hq hc
      subst hpe
      exact hfull q' hq' hn
    rw [he]
    simp

end

/-! ## Index privacy: the two worlds are one until the verifier asks a string of the honest pair -/

section
variable {lam : ℕ} {X W PP : Type}

open Classical in
/-- the chance, with answers sampled on demand from the table c, that V~ ever asks a string with the
property H -/
def bfHit (H : Str → Prop) (Z : ViewEnv lam (List (Digest lam)) X W Unit) :
    AdvVerifier lam X Unit → ℕ → View lam (List (Digest lam)) X Unit → Cache lam → ℝ≥0∞
  | .halt, _, _, _ => 0
  | .query q k, n, v, c =>
    if H q then 1
    else
      expect (lazyAnswer c q) fun out =>
        bfHit H Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2
  | .sample _ k, n, v, c =>
    expect (PMF.uniformOfFintype _) fun r =>
      bfHit H Z (k r) n { v with coins := v.coins ++ [r.val] } c
  | .request _, 0, _, _ => 0
  | .request k, n + 1, v, c =>
      match Z v with
      | none => 0
      | some (x, _) => bfHit H Z (k x ()) n { v with sessions := v.sessions ++ [(x, ())] } c

variable (K M : ℕ) {I : Type} [Fintype I]

theorem bfClose (R : IndexedRelation I X W PP) (H : Str → Prop)
    (Z : ViewEnv lam (List (Digest lam)) X W Unit)
    (E : Set (View lam (List (Digest lam)) X Unit)) (Vt : AdvVerifier lam X Unit) :
    ∀ (n : ℕ) (v : View lam (List (Digest lam)) X Unit) (c c' : Cache lam),
      (∀ q, ¬ H q → c' q = c q) →
      (PrFrom c' (realLoop (bfArg lam K M R) Z () Vt n v) E ≤
        prob (idealLoop (bfSim (PP := PP) lam K) Z Vt n v c) E + bfHit H Z Vt n v c) ∧
      (prob (idealLoop (bfSim (PP := PP) lam K) Z Vt n v c) E ≤
        PrFrom c' (realLoop (bfArg lam K M R) Z () Vt n v) E + bfHit H Z Vt n v c) := by
  induction Vt with
  | halt =>
    intro n v c c' _
    simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure, bfHit, add_zero]
    exact ⟨le_rfl, le_rfl⟩
  | query q k ih =>
    intro n v c c' hc
    by_cases hq : H q
    · simp only [bfHit, if_pos hq]
      exact ⟨le_trans (PrFrom_le_one _ _ _) le_add_self, le_trans (prob_le_one _ _) le_add_self⟩
    · have e : c' q = c q := hc q hq
      simp only [bfHit, if_neg hq, realLoop, idealLoop, prob_bind, bfSim]
      cases hcq : c q with
      | some r =>
        rw [PrFrom_query_hit (e.trans hcq)]
        simp only [lazyAnswer, hcq, expect_pure]
        exact ih r n _ c c' hc
      | none =>
        rw [PrFrom_query_miss (e.trans hcq)]
        simp only [lazyAnswer, hcq, expect_map]
        have hu : ∀ r : Digest lam, ∀ q', ¬ H q' →
            Function.update c' q (some r) q' = Function.update c q (some r) q' := fun r q' hq' => by
          by_cases e' : q' = q
          · subst e'
            simp
          · rw [Function.update_of_ne e', Function.update_of_ne e']
            exact hc q' hq'
        exact ⟨expect_le_add _ fun r => (ih r n _ _ _ (hu r)).1,
          expect_le_add _ fun r => (ih r n _ _ _ (hu r)).2⟩
  | sample m k ih =>
    intro n v c c' hc
    simp only [bfHit, realLoop, idealLoop, PrFrom_sample, prob_bind]
    exact ⟨expect_le_add _ fun r => (ih r n _ _ _ hc).1,
      expect_le_add _ fun r => (ih r n _ _ _ hc).2⟩
  | request k ih =>
    intro n v c c' hc
    cases n with
    | zero =>
      simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure, bfHit, add_zero]
      exact ⟨le_rfl, le_rfl⟩
    | succ n =>
      simp only [realLoop, idealLoop, bfHit]
      cases hz : Z v with
      | none =>
        simp only [pure_eq, PrFrom_pure, prob_pure, add_zero]
        exact ⟨le_rfl, le_rfl⟩
      | some xw =>
        obtain ⟨x, w⟩ := xw
        simp only [bfArg, OComp.bind, prob_bind, bfSim, expect_pure]
        exact ih x () n _ c c' hc

theorem bfSim_consistent (Z : ViewEnv lam (List (Digest lam)) X W Unit)
    (Vt : AdvVerifier lam X Unit) :
    ∀ (n : ℕ) (v : View lam (List (Digest lam)) X Unit) (c : Cache lam), TraceIn v.trace c →
      prob (idealLoop (bfSim (PP := PP) lam K) Z Vt n v c) {v | ¬ v.trace.Consistent} = 0 := by
  induction Vt with
  | halt => intro n v c h; simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
  | query q k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind, bfSim]
    exact expect_lazyAnswer_eq_zero c q _ fun r c' hc hq => ih r n _ c' ((h.mono hc).snoc hq)
  | sample m k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind]
    have : ∀ r, prob
          (idealLoop (bfSim (PP := PP) lam K) Z (k r) n { v with coins := v.coins ++ [r.val] } c)
          {v | ¬ v.trace.Consistent} = 0 :=
      fun r => ih r n _ c h
    simp only [this, expect_zero]
  | request k ih =>
    intro n v c h
    cases n with
    | zero => simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
    | succ n =>
      simp only [idealLoop]
      cases Z v with
      | none => exact prob_pure_inconsistent_eq_zero h
      | some xw =>
        simp only [prob_bind, bfSim, expect_pure]
        exact ih _ _ n _ _ h

open Classical in
/-- a verifier with t queries meets at most t of the M + 1 salts: the chances `bfHit` of asking a
string of the pair (i, σ), summed over the salts σ, are at most t -/
theorem bfHit_sum (i : I) (Z : ViewEnv lam (List (Digest lam)) X W Unit)
    (Vt : AdvVerifier lam X Unit) :
    ∀ (t n : ℕ) (v : View lam (List (Digest lam)) X Unit) (c : Cache lam), Vt.QueryBound t →
      ∑ σ : Fin (M + 1), bfHit (fun q => q ∈ bfPts K M (i, σ)) Z Vt n v c ≤ t := by
  induction Vt with
  | halt => intro t n v c _; simp [bfHit]
  | query q k ih =>
    intro t n v c hb
    cases t with
    | zero => exact absurd hb (by simp [AdvVerifier.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      have h1 : ∀ σ : Fin (M + 1), bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (.query q k) n v c ≤
          (if q ∈ bfPts K M (i, σ) then 1 else 0) +
            expect (lazyAnswer c q) fun out =>
              bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (k out.1) n
                  { v with trace := v.trace ++ [(q, out.1)] } out.2 := by
        intro σ
        by_cases e : q ∈ bfPts K M (i, σ)
        · simp only [bfHit, if_pos e]; exact le_self_add
        · simp only [bfHit, if_neg e, zero_add]; exact le_rfl
      have h2 : ∑ σ : Fin (M + 1), (if q ∈ bfPts K M (i, σ) then (1 : ℝ≥0∞) else 0) ≤ 1 := by
        by_cases ex : ∃ σ₀ : Fin (M + 1), q ∈ bfPts K M (i, σ₀)
        · obtain ⟨σ₀, hσ₀⟩ := ex
          rw [Finset.sum_eq_single σ₀]
          · simp [hσ₀]
          · intro σ _ hne
            rw [if_neg]
            intro e
            exact hne (congrArg Prod.snd (bfPts_disj K M e hσ₀))
          · intro h; exact absurd (Finset.mem_univ _) h
        · have ex' : ∀ σ₀ : Fin (M + 1), q ∉ bfPts K M (i, σ₀) := fun σ₀ e => ex ⟨σ₀, e⟩
          simp [ex']
      calc
        ∑ σ : Fin (M + 1), bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (.query q k) n v c ≤
            ∑ σ : Fin (M + 1), ((if q ∈ bfPts K M (i, σ) then 1 else 0) +
              expect (lazyAnswer c q) fun out =>
                bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (k out.1) n
                    { v with trace := v.trace ++ [(q, out.1)] } out.2) :=
            Finset.sum_le_sum fun σ _ => h1 σ
        _ = (∑ σ : Fin (M + 1), (if q ∈ bfPts K M (i, σ) then (1 : ℝ≥0∞) else 0)) +
              expect (lazyAnswer c q) fun out =>
                ∑ σ : Fin (M + 1), bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (k out.1) n
                    { v with trace := v.trace ++ [(q, out.1)] } out.2 := by
            rw [Finset.sum_add_distrib, expect_finset_sum]
        _ ≤ 1 + t := add_le_add h2 (expect_le_of_le _ fun out => ih _ _ _ _ _ (hb' _))
        _ = ((t + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  | sample m k ih =>
    intro t n v c hb
    have hb' : ∀ r, (k r).QueryBound t := hb
    simp only [bfHit]
    rw [← expect_finset_sum]
    exact expect_le_of_le _ fun r => ih _ _ _ _ _ (hb' r)
  | request k ih =>
    intro t n v c hb
    have hb' : ∀ x π, (k x π).QueryBound t := hb
    cases n with
    | zero => simp [bfHit]
    | succ n =>
      simp only [bfHit]
      cases hz : Z v with
      | none => simp
      | some xw => exact ih _ _ _ _ _ _ (hb' _ _)

end

/-! ## The honest key: K fresh answers -/

section
variable {lam : ℕ}

/-- the table c with the answers ds written at the strings qs -/
def bfProg (c : Cache lam) : List Str → List (Digest lam) → Cache lam
  | q :: qs, d :: ds => bfProg (Function.update c q (some d)) qs ds
  | _, _ => c

theorem bfProg_off :
    ∀ (qs : List Str) (ds : List (Digest lam)) (c : Cache lam) (q : Str),
      q ∉ qs → bfProg c qs ds q = c q := by
  intro qs
  induction qs with
  | nil => intro ds c q _; simp [bfProg]
  | cons q₀ qs ih =>
    intro ds c q hq
    rw [List.mem_cons, not_or] at hq
    cases ds with
    | nil => simp [bfProg]
    | cons d ds =>
      simp only [bfProg]
      rw [ih ds _ q hq.2, Function.update_of_ne hq.1]

theorem bfAsk_fresh {β : Type} (E : Set β) :
    ∀ (qs : List Str) (c : Cache lam) (g : List (Digest lam) → OComp lam β), qs.Nodup →
      (∀ q ∈ qs, c q = none) →
      PrFrom c ((bfAsk lam qs).bind g) E =
        expect (bfDraw lam qs.length) fun ds => PrFrom (bfProg c qs ds) (g ds) E := by
  intro qs
  induction qs with
  | nil =>
    intro c g _ _
    simp only [bfAsk, OComp.bind, List.length_nil, bfDraw, expect_pure, bfProg]
  | cons q qs ih =>
    intro c g hnd hc
    simp only [bfAsk, OComp.bind, bind_assoc', List.length_cons, bfDraw, expect_bind, expect_map]
    rw [PrFrom_query_miss (hc q (by simp))]
    refine expect_congr _ fun r => ?_
    have hfr : ∀ q' ∈ qs, Function.update c q (some r) q' = none := fun q' hq' => by
      have hne : q' ≠ q := fun e => (List.nodup_cons.1 hnd).1 (by rw [← e]; exact hq')
      rw [Function.update_of_ne hne]
      exact hc q' (List.mem_cons_of_mem _ hq')
    rw [ih (Function.update c q (some r)) (fun rs => g (r :: rs)) (List.nodup_cons.1 hnd).2 hfr]
    rfl

variable (K M : ℕ) {I X W PP : Type} [Fintype I]

theorem bf_private (R : IndexedRelation I X W PP) :
    HasStrongIndexPrivacyWith R (bfArg lam K M R) (bfSim lam K)
      (fun tV _ => (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞)) := by
  intro i Z _ tV Vt N hV
  have hbound : (expect (PMF.uniformOfFintype (Fin (M + 1))) fun σ =>
        expect (bfDraw lam K) fun ds =>
          bfHit (fun q => q ∈ bfPts K M (i, σ)) Z (Vt ds) N ⟨ds, [], [], []⟩ fun _ => none) ≤
      (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞) := by
    rw [expect_comm]
    refine expect_le_of_le _ fun ds => ?_
    rw [expect_uniform, ← Finset.mul_sum, Fintype.card_fin, ENNReal.div_eq_inv_mul]
    gcongr
    exact bfHit_sum K M i Z (Vt ds) tV N _ _ (hV ds)
  have hreal : ∀ E, Pr (realExp (bfArg lam K M R) Vt Z i N) (fun _ => E) =
      expect (PMF.uniformOfFintype (Fin (M + 1))) fun σ => expect (bfDraw lam K) fun ds =>
        PrFrom (bfProg (fun _ => none) (bfPts K M (i, σ)) ds)
            (realLoop (bfArg lam K M R) Z () (Vt ds) N ⟨ds, [], [], []⟩) E := by
    intro E
    have hexp : realExp (bfArg lam K M R) Vt Z i N = .sample M fun σ => (bfAsk lam (bfPts K M (i, σ))).bind fun ds =>
        realLoop (bfArg lam K M R) Z () (Vt ds) N ⟨ds, [], [], []⟩ := by
      simp only [realExp, bfArg, bind_eq, OComp.bind, bind_assoc']
    rw [Pr_eq_PrFrom, hexp, PrFrom_sample]
    refine expect_congr _ fun σ => ?_
    rw [bfAsk_fresh E _ _ _ (bfPts_nodup K M (i, σ)) (fun _ _ => rfl), bfPts_length]
  have hideal : ∀ E, prob (idealExp R (bfSim lam K) Vt Z i N) E =
      expect (PMF.uniformOfFintype (Fin (M + 1))) fun _ => expect (bfDraw lam K) fun ds =>
        prob (idealLoop (bfSim (PP := PP) lam K) Z (Vt ds) N ⟨ds, [], [], []⟩ fun _ => none) E := by
    intro E
    rw [expect_const]
    simp only [idealExp, bfSim, prob_bind, expect_map]
  have hcl := fun (E : Set (View lam (List (Digest lam)) X Unit)) (σ : Fin (M + 1)) (ds : List (Digest lam)) =>
    bfClose K M R (fun q => q ∈ bfPts K M (i, σ)) Z E (Vt ds) N ⟨ds, [], [], []⟩ (fun _ => none)
      (bfProg (fun _ => none) (bfPts K M (i, σ)) ds) (fun q hq => bfProg_off _ _ _ q hq)
  constructor
  · refine SD_le_of_forall (fun E => ?_) (fun E => ?_)
    · rw [hreal, hideal]
      refine le_trans ?_ (add_le_add le_rfl hbound)
      refine le_trans (expect_mono _ fun σ => expect_le_add _ fun ds => (hcl E σ ds).1) ?_
      rw [expect_add]
    · rw [hreal, hideal]
      refine le_trans ?_ (add_le_add le_rfl hbound)
      refine le_trans (expect_mono _ fun σ => expect_le_add _ fun ds => (hcl E σ ds).2) ?_
      rw [expect_add]
  · rw [hideal]
    have : ∀ ds : List (Digest lam),
        prob (idealLoop (bfSim (PP := PP) lam K) Z (Vt ds) N ⟨ds, [], [], []⟩ fun _ => none)
            {v | ¬ v.trace.Consistent} = 0 :=
      fun ds => bfSim_consistent K Z (Vt ds) N _ _ (TraceIn.nil _)
    simp only [this, expect_zero]

end

theorem bf_main : Spec.bf_main := fun _ K M _ _ _ _ _ R w0 hK =>
  ⟨bf_complete K M hK R, bf_binding K M R w0, bf_private K M R⟩

end TopC
