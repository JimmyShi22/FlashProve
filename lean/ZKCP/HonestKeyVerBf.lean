-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/HonestKeyVerBf.lean: the brute-force scheme (ZKCP/PlainTrivial.lean: empty proofs; V tries all
pairs of an index and a salt) held against sentences that one may add to the definition, for every
relation: it has the honest-key sentence for every prover, with no budget;
"from an honest key the extractor gives back the index" with error 0; binding for many pairs with no
factor; its V draws no coin; and its hiding is void at its own verifier's number of queries,
whatever the simulator.

Theorems with their proofs, stated outright. Each clause of the title holds under the hypotheses of
its theorem. Nothing assumed beyond the hypotheses of the statements, in the random-oracle model, on
Lean's three axioms. A guard beside ZKCP/PlainTrivial.lean, ZKCP/PlainTrivialProofs.lean.
A scheme is a triple of oracle algorithms: an index committer C, which makes a verifier's key ivk
and a prover's key isk from an index, a prover P and a verifier V (`Arg`, ZKCP/Defs.lean). "The
definition" is `IsZKCPArg` of that file. In the brute-force scheme `bfArg` a key has K blocks; n is
the number of pairs of an index and a salt, u is 2^-λ, and n u^K is `bfAcc`
(ZKCP/PlainTrivial.lean); M + 1 is the number of salts.

Main names (all but the first row ask 0 < K):
  `bfV_qb`, `bfV_dnc`: this V asks at most (number of pairs) · K queries on every path; it draws no
    coin.
  **bf_void** if the scheme meets the definition (the form of the work that this protocol builds on:
  lean/CREDITS.md, "Further work") with ANY α', ε, ζ,
    and the index matters: 1 ≤ α' + n u^K + 2 ζ(n K, 0)
  `bf_W`: Pr [ V accepts x' ∧ x' is not in the language of i1 | an honest key for i1; any prover ]
    ≤ n u^K.
  `bf_E`: `ZKCP.HasExtractionError` at error 0.

Further statements:
  `bf_many`: binding for many pairs (ZKCP/Optional.lean): the same bound (tC u + n u^K for a
    committer of at most tC queries: `bf_main`'s ε, ZKCP/PlainTrivial.lean), no number of pairs in
    it.

Notation: `α'`, `ε`, `ζ`: an `ℝ≥0∞` and two functions `ℕ → ℕ → ℝ≥0∞`: in `h` of `bf_void` the errors
in the fields `completeness`, `indexBinding`, `indexPrivacy` of `ZKCP.IsZKCPArg`; ζ's two arguments
(`tV`, `N` in `ZKCP.PrivacyFor`): natural numbers: a number of queries of V~, a number of sessions
(both: ZKCP/Defs.lean); `wrongExp A i Pt` (ZKCP/HonestKey.lean): an `OComp lam (Bool × X)`: the
experiment with the honest committer and any prover; `ZKCP.HasExtractionError`: ZKCP/Optional.lean.

Limits:
None of these sentences tells a protocol from a search through all indices. The one clause that
does: a bound on V's own queries where hiding still holds (ZKCP/HonestKeyVerGen.lean).
This file says nothing on the scheme against the definition with batches (ZKCP/Gen.lean). It says
nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import ZKCP.HonestKeyVerGen
import ZKCP.PlainTrivialProofs

set_option autoImplicit false

namespace TopC
open ZKCP
open scoped ENNReal

section BF
variable {lam : ℕ}

theorem dnc_bind {α β : Type} :
    ∀ (c : OComp lam α) (g : α → OComp lam β),
      c.DrawsNoCoin → (∀ a, (g a).DrawsNoCoin) → (c.bind g).DrawsNoCoin
  | .pure a, _, _, hg => hg a
  | .query _ k, g, h, hg => fun r => dnc_bind (k r) g (h r) hg
  | .sample _ _, _, h, _ => h.elim

theorem bfAsk_qb : ∀ qs : List Str, (bfAsk lam qs).QueryBound qs.length
  | [] => trivial
  | _ :: qs =>
    fun r =>
      OComp.QueryBound.bind (fun rs => (.pure (r :: rs) : OComp lam (List (Digest lam)))) 0
        (fun _ => trivial) (bfAsk lam qs) qs.length (bfAsk_qb qs)

theorem bfAsk_dnc : ∀ qs : List Str, (bfAsk lam qs).DrawsNoCoin
  | [] => trivial
  | _ :: qs => fun _ => dnc_bind _ _ (bfAsk_dnc qs) fun _ => trivial

variable (K M : ℕ) {I X W PP : Type} [Fintype I]

theorem bfSearch_qb (ivk : List (Digest lam)) :
    ∀ ps : List (I × Fin (M + 1)), (bfSearch lam K M ivk ps).QueryBound (ps.length * K)
  | [] => trivial
  | p :: ps => by
      rw [List.length_cons, Nat.succ_mul, Nat.add_comm (ps.length * K) K]
      unfold bfSearch
      refine OComp.QueryBound.bind _ _ (fun ds => ?_) _ _ ?_
      · split
        · trivial
        · exact bfSearch_qb ivk ps
      · have := bfAsk_qb (lam := lam) (bfPts K M p)
        rwa [bfPts_length] at this

theorem bfSearch_dnc (ivk : List (Digest lam)) :
    ∀ ps : List (I × Fin (M + 1)), (bfSearch lam K M ivk ps).DrawsNoCoin
  | [] => trivial
  | p :: ps => by
      unfold bfSearch
      refine dnc_bind _ _ (bfAsk_dnc _) fun ds => ?_
      split
      · trivial
      · exact bfSearch_dnc ivk ps

/-- This V asks f up to K |I| (M + 1) times: on every path at most that. -/
theorem bfV_qb (R : IndexedRelation I X W PP) (ivk : List (Digest lam)) (x : X) :
    ((bfArg lam K M R).V ivk x ()).QueryBound (Fintype.card (I × Fin (M + 1)) * K) := by
  have h := OComp.QueryBound.bind
    (fun o : Option (I × Fin (M + 1)) =>
      (.pure (o.elim false fun p =>
          @decide (∃ w, R.rel p.1 x w) (Classical.propDecidable _)) : OComp lam Bool))
    0 (fun _ => trivial) _ _ (bfSearch_qb (lam := lam) K M ivk (bfAll (I := I) M))
  have e : (bfAll (I := I) M).length = Fintype.card (I × Fin (M + 1)) := by simp [bfAll]
  rw [e] at h
  exact h

theorem bfV_dnc (R : IndexedRelation I X W PP) (ivk : List (Digest lam)) (x : X) :
    ((bfArg lam K M R).V ivk x ()).DrawsNoCoin :=
  dnc_bind _ _ (bfSearch_dnc K M ivk _) fun _ => trivial

open Classical in
/-- Under `hK`, `hx`, for each request x (and given some w0 : W): under an honest key for i1 the
brute-force V accepts no request that is false at i1, but for n u^K: from `bf_main`'s own
completeness, at the complement relation. -/
theorem bf_reject (hK : 0 < K) (R : IndexedRelation I X W PP) (w0 : W) (i1 : I)
    (x : X) (hx : ¬ ∃ w, R.rel i1 x w) :
    Pr (verKey (bfArg lam K M R) i1 x ()) (fun _ => {b | b = true}) ≤ bfAcc lam K M I := by
  let R' : IndexedRelation I X W PP := ⟨fun i x _ => ¬ ∃ w, R.rel i x w, R.pp⟩
  refine le_trans ?_ ((bf_main lam K M I X W PP R' w0 hK).completeness i1 x w0 hx)
  have e : completenessExp (bfArg lam K M R') i1 x w0 = verKey (bfArg lam K M R') i1 x () := rfl
  rw [e]
  unfold Pr PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  have c : (bfArg lam K M R').C i1 = (bfArg lam K M R).C i1 := rfl
  simp only [verKey, run_bind, prob_bind, c]
  refine expect_mono _ fun k => ?_
  rw [bfV_run, bfV_run, prob_pure, prob_pure]
  cases (bfAll M).find? fun p : I × Fin (M + 1) => decide ((bfPts K M p).map f = k.1) with
  | none => simp
  | some p =>
    by_cases h : ∃ w, R.rel p.1 x w
    · simp [R', h]
    · simp [h]

/-- Under `hK`:
**the brute-force scheme's hiding is void at its own verifier's number of queries, whatever the
simulator**: if it meets the definition (the form of the work that this protocol builds on:
lean/CREDITS.md, "Further work") with any α', ε, ζ, and the index matters (x true at i0, false at
i1, same public part; something true at i1), then
1 ≤ α' + n u^K + 2 ζ(n K, 0). -/
theorem bf_void (hK : 0 < K) (R : IndexedRelation I X W PP) (α' : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞)
    (h : IsZKCPArg R (bfArg lam K M R) α' ε ζ) (i0 i1 : I) (hpp : R.pp i0 = R.pp i1) (x : X) (w : W)
    (hx : R.rel i0 x w) (hx' : ¬ ∃ w, R.rel i1 x w) (x1 : X) (w1 : W) (hx1 : R.rel i1 x1 w1) :
    1 ≤ α' + bfAcc lam K M I +
        (ζ (Fintype.card (I × Fin (M + 1)) * K) 0 + ζ (Fintype.card (I × Fin (M + 1)) * K) 0) :=
  ver_constNote _ _ _ _ _ _ _ _ R _ α' _ ε ζ h () i0 i1 hpp x w hx
    (fun _ _ _ _ _ => rfl) x1 w1 hx1 (bf_reject K M hK R w i1 x hx') _
    (fun ivk => bfV_qb K M R ivk x) (fun ivk => bfV_dnc K M R ivk x)

/-- Under the hypotheses below (0 < K; the index matters): a lower bound on what this V asks, from
`bf_main`'s own ζ: any q that bounds V's queries on x at every key has
1 ≤ 2 n u^K + 2 q / (M + 1). -/
theorem bfV_lower (hK : 0 < K) (R : IndexedRelation I X W PP) (i0 i1 : I) (hpp : R.pp i0 = R.pp i1)
    (x : X) (w : W) (hx : R.rel i0 x w) (hx' : ¬ ∃ w, R.rel i1 x w) (x1 : X) (w1 : W)
    (hx1 : R.rel i1 x1 w1) (q : ℕ) (hq : ∀ ivk, ((bfArg lam K M R).V ivk x ()).QueryBound q) :
    1 ≤ bfAcc lam K M I + bfAcc lam K M I +
        ((q : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞) + (q : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞)) :=
  ver_constNote _ _ _ _ _ _ _ _ R _ _ _ _ _ (bf_main lam K M I X W PP R w hK).toIsZKCPArg
    () i0 i1 hpp x w hx (fun _ _ _ _ _ => rfl) x1 w1 hx1 (bf_reject K M hK R w i1 x hx')
    q hq (fun ivk => bfV_dnc K M R ivk x)

/-- Given some `w0 : W`, `x₀ : X`:
the optional "many sessions" of the work that this protocol builds on (lean/CREDITS.md, "Further
work"; ZKCP/Optional.lean) does not shut it out: same bound, no N -/
theorem bf_many (R : IndexedRelation I X W PP) (w0 : W) (x₀ : X) :
    HasSessionAugmentedBinding R (bfArg lam K M R)
      (fun tC _ _ => (tC : ℝ≥0∞) * ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ + bfAcc lam K M I) :=
  sessionAugmented_of_binding (bf_binding K M R w0)
    (fun v x π => by cases π; exact bfV_qb K M R v x)
    (fun v x π => by cases π; exact bfV_dnc K M R v x) x₀ ()

end BF


section BF2
variable {lam : ℕ} (K M : ℕ) {I X W PP : Type} [Fintype I]

open Classical in
/-- Under `hK`: the honest-key sentence holds of the brute-force scheme, for every prover, with
no bound on its queries; the chance is at most n u^K: from `bf_main`'s own completeness at the
relation "the index is i1". -/
theorem bf_W (hK : 0 < K) (R : IndexedRelation I X W PP) (i1 : I)
    (Pt : List (Digest lam) × Unit → OComp lam (X × Unit)) :
    Pr (wrongExp (bfArg lam K M R) i1 Pt) (fun _ => {o | o.1 = true ∧ o.2 ∉ R.L (some i1)}) ≤
      bfAcc lam K M I := by
  let R' : IndexedRelation I Unit Unit PP := ⟨fun i _ _ => i = i1, R.pp⟩
  refine le_trans ?_ ((bf_main lam K M I Unit Unit PP R' () hK).completeness i1 () () rfl)
  have e : completenessExp (bfArg lam K M R') i1 () () = verKey (bfArg lam K M R') i1 () () := rfl
  rw [e]
  unfold Pr PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((((bfArg lam K M R).C i1).bind fun k =>
        (Pt k).bind fun o =>
          ((bfArg lam K M R).V k.1 o.1 o.2).bind fun b =>
            (.pure (b, o.1) : OComp lam (Bool × X))).run f) _ ≤
    prob ((((bfArg lam K M R).C i1).bind fun k => (bfArg lam K M R').V k.1 () ()).run f) _
  rw [run_bind, prob_bind, run_bind, prob_bind]
  refine expect_mono _ fun k => ?_
  rw [bfV_run, prob_pure]
  cases hp : (bfAll M).find? fun p : I × Fin (M + 1) => decide ((bfPts K M p).map f = k.1) with
  | none => simpa using prob_le_one _ _
  | some p =>
    by_cases h : p.1 = i1
    · refine le_trans (le_of_eq ?_) (zero_le _)
      rw [run_bind, prob_bind]
      refine (expect_congr _ fun o => ?_).trans (expect_zero _)
      obtain ⟨x', ⟨⟩⟩ := o
      rw [run_bind, bfV_run, PMF.pure_bind]
      show prob (PMF.pure _) _ = 0
      rw [prob_pure, if_neg]
      rintro ⟨hacc, hbad⟩
      simp only [hp, Option.elim_some, decide_eq_true_eq] at hacc
      exact hbad (h ▸ hacc)
    · simpa [R', h] using prob_le_one _ _

theorem bfAsk_wt (f : Oracle lam) :
    ∀ qs : List Str, (bfAsk lam qs).withTrace.run f = PMF.pure (qs.map f, qs.map fun q => (q, f q))
  | [] => rfl
  | q :: qs => by
      show ((((bfAsk lam qs).bind fun rs => .pure (f q :: rs)).withTrace.bind fun out =>
          .pure (out.1, (q, f q) :: out.2)) : OComp lam (List (Digest lam) × Trace lam)).run f = _
      rw [run_bind, OComp.withTrace_bind, run_bind, bfAsk_wt f qs, PMF.pure_bind]
      simp [OComp.withTrace, OComp.run, OComp.bind, PMF.pure_bind]

open Classical in
theorem bfEi_honest (hK : 0 < K) (f : Oracle lam) (p0 : I × Fin (M + 1)) :
    bfEi lam K M ((bfPts K M p0).map f) ((bfPts K M p0).map fun q => (q, f q)) = some p0.1 := by
  unfold bfEi
  cases hp : (bfAll M).find? fun p : I × Fin (M + 1) =>
      decide (List.Forall₂ (fun q d => (q, d) ∈ (bfPts K M p0).map fun q => (q, f q))
            (bfPts K M p) ((bfPts K M p0).map f)) with
  | none =>
    have h1 := List.find?_eq_none.1 hp p0 (bfAll_mem M _)
    have h2 : ¬ List.Forall₂ (fun q d => (q, d) ∈ (bfPts K M p0).map fun q => (q, f q))
        (bfPts K M p0) ((bfPts K M p0).map f) := by
      simp at h1
    refine absurd ?_ h2
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun q hq => List.mem_map.2 ⟨q, hq, rfl⟩
  | some p =>
    have hF : List.Forall₂ (fun q d => (q, d) ∈ (bfPts K M p0).map fun q => (q, f q))
        (bfPts K M p) ((bfPts K M p0).map f) := by
      simpa using List.find?_some hp
    obtain ⟨q, l, hql⟩ := List.exists_cons_of_ne_nil (bfPts_ne_nil K M hK p)
    rw [hql] at hF
    obtain ⟨d, _, hqd, _, _⟩ := List.forall₂_cons_left_iff.1 hF
    obtain ⟨q', hq', he⟩ := List.mem_map.1 hqd
    have hq0 : q ∈ bfPts K M p0 := by
      have := (Prod.mk.inj he).1
      exact this ▸ hq'
    have hqp : q ∈ bfPts K M p := by rw [hql]; exact List.mem_cons_self
    rw [bfPts_disj K M hqp hq0]
    rfl

open Classical in
/-- Under `hK`:
**THE OPTIONAL "i* = i FOR THE HONEST COMMITTER" OF the work that this protocol builds on
(lean/CREDITS.md, "Further work"; ZKCP/Optional.lean) HOLDS OF THE
BRUTE-FORCE SCHEME WITH ERROR 0** -/
theorem bf_E (hK : 0 < K) (R : IndexedRelation I X W PP) (w0 : W) :
    HasExtractionError (bfArg lam K M R) (bfExt lam K M R w0) 0 := by
  intro i
  have h : ∀ f : Oracle lam,
      PrCoins f ((bfArg lam K M R).C i).withTrace {o | (bfExt lam K M R w0).Ei o.1.1 o.2 ≠ some i} =
        0 := by
    intro f
    unfold PrCoins
    show prob ((PMF.uniformOfFintype (Fin (M + 1))).bind fun σ =>
          (((bfAsk lam (bfPts K M (i, σ))).bind fun ds =>
            (.pure (ds, ()) : OComp lam (List (Digest lam) × Unit))).withTrace).run f) _ = 0
    rw [prob_bind]
    refine (expect_congr _ fun σ => ?_).trans (expect_zero _)
    rw [OComp.withTrace_bind, run_bind, bfAsk_wt, PMF.pure_bind]
    show prob (PMF.pure
          (((bfPts K M (i, σ)).map f, ()), ((bfPts K M (i, σ)).map fun q => (q, f q)) ++ [])) _ = 0
    rw [prob_pure, if_neg]
    intro hbad
    refine hbad ?_
    show bfEi lam K M _ _ = some i
    rw [List.append_nil]
    exact bfEi_honest K M hK f (i, σ)
  unfold Pr
  simp [h]

end BF2


end TopC
