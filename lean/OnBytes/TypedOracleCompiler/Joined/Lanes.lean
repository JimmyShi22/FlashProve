-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Lanes.lean: one bad event, with one bound, for any number of chains that are
checked against one set of oracles and one adversary. Four definitions and seven theorems.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean proves soundness of the compiled scheme in two halves. The
first is about one trace and has no probability: outside the two hash events (`EM`, `EF`:
Events.lean in that folder) and the state event of a chain's protocol (`StepEvent ℓ.step`, for its
`Lane` ℓ: Rooted.lean there), an accepted chain has its statement in its language
(`mem_of_accepted`). The second bounds the probability of these events, for three fixed lanes;
TwoLanes.lean there, for two.
Here is the second half for a list of lanes. So the first half can be used once for each lane, on
the same trace, and the events are paid once. (The three joined chains of one file are one protocol,
so one lane: nothing is summed there. Several lanes: several protocols over one wire record W.)

Main names:
  `stepL ℓs`: the entry causes the state event of one of the lanes of ℓs, or is a query that was
    asked before, now with another answer (`twice`, TwoLanes.lean).
  `BadL ℓs`: `EM`, or `EF`, or `stepL ℓs` at some entry of the trace.
  `badL_rare`: an algorithm with at most t queries causes `BadL ℓs` with probability at most
    t εs + 2 (t + 1)² / 2^lam, where εs lies, for each tag, above the sum of the bounds `c ℓ` on the
    round errors of the lanes with that tag. A query belongs to one tag. So lanes with different
    tags pay the greatest of their bounds, and lanes with the same tag pay the sum.
  `badL_mono`: `BadL ℓs` is never undone.
  `not_badL`: outside `BadL ℓs`: not `EM`, not `EF`, no lane's state event, and each query of the
    trace has one answer (`OneAns`).
  `stepAny ℓs`: the entry causes the state event of one of the lanes. `payAt c ℓs t₀`: what the
    lanes with the tag t₀ pay for one query: the sum of their bounds.
  `pr_step_at`, `pr_stepAny_at`, `pr_stepAny_le`: the bound for one query: for one lane; for all
    lanes at one tag; at any oracle.
  `payAt_le_of_pairwise`: if no two lanes of the list have the same tag and each bound is at most
    εs, then εs lies above what the lanes of each tag pay.

Limits: all lanes are lanes of one wire record W: one family of oracles. Each tag has its own depth
of the request tree (`QueryLayout.dReq`), and a lane is asked to be well formed at as many slots as the
request tree of its tag has leaves. Nothing here says what a lane's state function is, that a lane
is well formed (`Lane.OK`, a hypothesis), or how chains are joined. The budget t is the adversary's
with the verifier's own queries, as in SpecSoundG.lean of that folder: the clauses there speak of
traces in which the verifier's queries are answered.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.TwoLanes

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile (Tag)
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-! ## The event -/

/-- the entry e, after the trace pre, causes the state event of one of the lanes -/
def stepAny (ℓs : List (Lane W)) (pre : Tc W) (e : QA (typedOracleFamily lam W.K L)) : Prop :=
  ∃ ℓ ∈ ℓs, ℓ.step pre e

/-- the state event of one of the lanes, or one query with two answers -/
def stepL (ℓs : List (Lane W)) (pre : Tc W) (e : QA (typedOracleFamily lam W.K L)) : Prop :=
  stepAny ℓs pre e ∨ twice pre e

/-- the bad event of a list of lanes -/
def BadL (ℓs : List (Lane W)) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (stepL ℓs) tr

/-- what the lanes with the tag t₀ pay for one query: the sum of their bounds -/
def payAt (c : Lane W → ℝ≥0∞) (ℓs : List (Lane W)) (t₀ : Tag) : ℝ≥0∞ :=
  (ℓs.map fun ℓ => if ℓ.t = t₀ then c ℓ else 0).sum

/-- One lane and one query to the Fiat-Shamir oracle of the tag t₀: the lane's bound if t₀ is its
tag, and 0 otherwise. -/
theorem pr_step_at (ℓ : Lane W) (ok : ℓ.OK (2 ^ W.dReq ℓ.t)) {c : ℝ≥0∞}
    (b : Err.Below ℓ.ε c) (pre : Tc W) (t₀ : Tag) (q : FbIn lam L t₀) :
    pr (unif (FsAns lam W.K)) {a | ℓ.step pre (fbE t₀ q a)} ≤ if ℓ.t = t₀ then c else 0 := by
  split_ifs with h
  · subst h
    exact Lane.pr_step_le ℓ rfl ok b pre q
  · refine le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)
    intro a _ hs
    exact h (OracleName.fb.inj (Lane.step_oracle hs)).symm

/-- The bound for one query to the Fiat-Shamir oracle of the tag t₀, for all lanes. -/
theorem pr_stepAny_at (c : Lane W → ℝ≥0∞) (pre : Tc W) (t₀ : Tag) (q : FbIn lam L t₀) :
    ∀ ℓs : List (Lane W), (∀ ℓ ∈ ℓs, ℓ.OK (2 ^ W.dReq ℓ.t)) →
      (∀ ℓ ∈ ℓs, Err.Below ℓ.ε (c ℓ)) →
      pr (unif (FsAns lam W.K)) {a | stepAny ℓs pre (fbE t₀ q a)} ≤ payAt c ℓs t₀
  | [], _, _ => by
    refine le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)
    rintro a - ⟨ℓ, hℓ, -⟩
    cases hℓ
  | ℓ :: ℓs, ok, b => by
    have h1 := pr_step_at ℓ (ok ℓ List.mem_cons_self) (b ℓ List.mem_cons_self) pre t₀ q
    have h2 := pr_stepAny_at c pre t₀ q ℓs
      (fun x hx => ok x (List.mem_cons_of_mem _ hx)) fun x hx => b x (List.mem_cons_of_mem _ hx)
    refine le_trans (pr_mono _ ?_) ((pr_union_le _ _ _).trans (add_le_add h1 h2))
    rintro a ⟨x, hx, hs⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl hs
    · exact Or.inr ⟨x, hx, hs⟩

/-- The bound for one query, to any oracle. -/
theorem pr_stepAny_le {ℓs : List (Lane W)} (ok : ∀ ℓ ∈ ℓs, ℓ.OK (2 ^ W.dReq ℓ.t))
    (c : Lane W → ℝ≥0∞) (b : ∀ ℓ ∈ ℓs, Err.Below ℓ.ε (c ℓ)) {εs : ℝ≥0∞}
    (hε : ∀ t₀, payAt c ℓs t₀ ≤ εs) (pre : Tc W) (o : OracleName) (q : domOf lam L o) :
    pr (unif ((typedOracleFamily lam W.K L).Rng o)) {r | stepAny ℓs pre (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K L))} ≤
      εs := by
  by_cases h : ∃ t₀, o = OracleName.fb t₀
  · obtain ⟨t₀, rfl⟩ := h
    exact (pr_stepAny_at c pre t₀ q ℓs ok b).trans (hε t₀)
  · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - ⟨ℓ, -, hs⟩
    exact h ⟨ℓ.t, Lane.step_oracle hs⟩

/-- **The bad event of a list of lanes is rare**, under the hypotheses below: the lanes are well
formed, `c ℓ` bounds the round errors of ℓ, and εs lies above what the lanes of each tag pay
together. -/
theorem badL_rare {ℓs : List (Lane W)} (ok : ∀ ℓ ∈ ℓs, ℓ.OK (2 ^ W.dReq ℓ.t))
    (c : Lane W → ℝ≥0∞) (b : ∀ ℓ ∈ ℓs, Err.Below ℓ.ε (c ℓ)) {εs : ℝ≥0∞}
    (hε : ∀ t₀, payAt c ℓs t₀ ≤ εs) (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ)
    (hA : A.QueryBound t) :
    pr A.withTrace.law {o | BadL ℓs o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) (stepL ℓs) (fun _ => εs)
    (fun pre e he hs => hs.elim (fun ⟨_, _, h1⟩ => h1.1 he) fun h1 => h1.1 he)
    (fun pre o q hq => le_trans (pr_mono _ fun r hr => hr.elim id fun h3 => by
      obtain ⟨-, r', hr'⟩ := h3
      exact absurd hr' (hq r')) (pr_stepAny_le ok c b hε pre o q)) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (stepL ℓs) o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law {o | StepEvent (stepL ℓs) o.2} := pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

/-- the bad event is never undone -/
theorem badL_mono {ℓs : List (Lane W)} (tr tr' : Tc W) : BadL ℓs tr → BadL ℓs (tr ++ tr') := by
  rintro ((h | h) | h)
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- outside the bad event: neither hash event, no lane's state event, and each query has one
answer -/
theorem not_badL {ℓs : List (Lane W)} {tr : Tc W} (h : ¬ BadL ℓs tr) :
    ¬ EM tr ∧ ¬ EF tr ∧ (∀ ℓ ∈ ℓs, ¬ StepEvent ℓ.step tr) ∧ OneAns tr :=
  ⟨fun e => h (Or.inl (Or.inl e)), fun e => h (Or.inl (Or.inr e)),
    fun ℓ hℓ ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inl ⟨ℓ, hℓ, h2⟩⟩),
    oneAns_of_not_twice tr fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inr h2⟩)⟩

/-- lanes with different tags pay the greatest of their bounds: if each bound is at most εs and no
two lanes of the list have the same tag, εs lies above what the lanes of each tag pay -/
theorem payAt_le_of_pairwise (c : Lane W → ℝ≥0∞) {εs : ℝ≥0∞} (t₀ : Tag) :
    ∀ ℓs : List (Lane W), ℓs.Pairwise (fun a b => a.t ≠ b.t) → (∀ ℓ ∈ ℓs, c ℓ ≤ εs) →
      payAt c ℓs t₀ ≤ εs ∧ ((∀ ℓ ∈ ℓs, ℓ.t ≠ t₀) → payAt c ℓs t₀ = 0)
  | [], _, _ => ⟨zero_le _, fun _ => rfl⟩
  | ℓ :: ℓs, hp, hc => by
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.1 hp
    obtain ⟨i1, i2⟩ := payAt_le_of_pairwise c t₀ ℓs hp2 fun x hx => hc x (List.mem_cons_of_mem _ hx)
    have e : payAt c (ℓ :: ℓs) t₀ = (if ℓ.t = t₀ then c ℓ else 0) + payAt c ℓs t₀ := by
      simp [payAt]
    rw [e]
    refine ⟨?_, fun hne => ?_⟩
    · by_cases h : ℓ.t = t₀
      · rw [if_pos h, i2 fun x hx => h ▸ (hp1 x hx).symm, add_zero]
        exact hc ℓ List.mem_cons_self
      · rw [if_neg h, zero_add]
        exact i1
    · rw [if_neg (hne ℓ List.mem_cons_self), zero_add]
      exact i2 fun x hx => hne x (List.mem_cons_of_mem _ hx)

end TypedOracleCompiler.Joined
