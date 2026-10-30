-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/TwoIndices.lean: consequences of binding for many sessions and of strong privacy.

Not part of the definitions of ZKCP/Defs.lean. Consequences of the definitions of ZKCP/Defs.lean and
ZKCP/Optional.lean, for every relation and every scheme, under the hypotheses of their statements.
The two notions are this library's, not part of the definition in ZKCP/Defs.lean. `IndistOn` names
no simulator. `NoTwoAnswers` begins with an existential quantifier over a function Ei, because the
experiment (`multiBindingExp`, ZKCP/Optional.lean) outputs that function's value; the quantifier has
no effect: the event depends on the list of verdicts only, and the probability is the same for all
Ei (its proof is not part of this library).
  `NoTwoAnswers A key val ε`  no two answers. Read an instance as a question (key) with an answer
                              (val). No committer with at most t_C queries and prover with at most
                              t_P queries get, among up to N proofs under one key of the scheme, two
                              accepted instances with the same question and different answers,
                              except with probability ε t_C t_P N
  `noTwoAnswers_of`           it follows from index binding for many sessions (ZKCP/Optional.lean),
                              if for every index the answer is a function of the question
  `IndistOn R A ζ`            two indices, one environment. For any two indices with the same public
                              parameters and any environment all of whose instances are true for
                              both, the verifier's two real views are within 2 ζ in statistical
                              distance (not all hypotheses are named here: see `IndistOn`)
  `indistOn_of`               it follows from index privacy in the stronger form
  `IndistOn.event`            the same for one event
  `IndistOn.key_alone`        the key only: the environment that always declines is valid for every
                              index, so what a verifier sees without any session is within 2 ζ for
                              all pairs of indices with the same public parameters

Limits: `NoTwoAnswers`: nothing on whether an accepted answer is the right one for any index that
anybody has in mind; nothing on two proofs under two keys; nothing on a prover that sees honest
proofs first (the experiment has no session oracle). `IndistOn`: every instance that the environment
names is true for both indices (exactly: `ViewEnv.IsValid` at i and at i'), on every view, reachable
or not, and it is one function of the view, which does not know which index is used; so the
statement compares indices only on questions on which they agree; where ζ ≥ 1/2 it says nothing.
-/
import ZKCP.Basic
import ZKCP.Optional

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf K Y : Type}

/-- No two answers. In one experiment with a cheating committer with at most t_C queries and a
cheating prover with at most t_P queries that outputs up to N pairs, two accepted instances with the
same question and different answers have probability at most ε t_C t_P N. -/
def NoTwoAnswers (A : Arg lam I X W IVK ISK Pf) (key : X → K) (val : X → Y) (ε : ℕ → ℕ → ℕ → ℝ≥0∞) :
    Prop :=
  ∃ Ei : IVK → Trace lam → Option I,
    ∀ (tC tP N : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (List (X × Pf))),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Pr (multiBindingExp A Ei Ct Pt) (fun _ =>
          {o | o.2.length ≤ N ∧
            ∃ bx ∈ o.2, ∃ bx' ∈ o.2,
              bx.1 = true ∧ bx'.1 = true ∧ key bx.2 = key bx'.2 ∧ val bx.2 ≠ val bx'.2}) ≤ ε tC tP N

/-- `NoTwoAnswers` follows from index binding for many sessions, if for every index the answer is a
function of the question. -/
theorem noTwoAnswers_of (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf) (key : X → K)
    (val : X → Y) (ε : ℕ → ℕ → ℕ → ℝ≥0∞)
    (huniq : ∀ i x x', x ∈ R.L (some i) → x' ∈ R.L (some i) → key x = key x' → val x = val x')
    (h : HasSessionAugmentedBinding R A ε) : NoTwoAnswers A key val ε := by
  obtain ⟨Ei, hE⟩ := h
  refine ⟨Ei, fun tC tP N St Ct Pt hC hP => le_trans (Pr_mono _ ?_) (hE tC tP N St Ct Pt hC hP)⟩
  rintro ⟨iS, l⟩ ⟨hl, bx, hbx, bx', hbx', h1, h2, hk, hv⟩
  refine ⟨hl, ?_⟩
  by_contra hc
  have hall : ∀ b ∈ l, b.1 = true → b.2 ∈ R.L iS := fun b hb ht => by
    by_contra hn
    exact hc ⟨b, hb, ht, hn⟩
  have m1 := hall bx hbx h1
  have m2 := hall bx' hbx' h2
  cases iS with
  | none => exact m1
  | some i => exact hv (huniq i _ _ m1 m2 hk)

/-- Two indices, one environment. The environment is a function of the verifier's whole view, and it
may decline. -/
def IndistOn (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf) (ζ : ℕ → ℕ → ℝ≥0∞) :
    Prop :=
  ∀ (i i' : I), R.pp i = R.pp i' →
    ∀ Z : ViewEnv lam IVK X W Pf, Z.IsValid R i → Z.IsValid R i' →
      ∀ (tV : ℕ) (Vt : IVK → AdvVerifier lam X Pf) (N : ℕ), (∀ ivk, (Vt ivk).QueryBound tV) →
        SD (fun T => Pr (realExp A Vt Z i N) (fun _ => T))
            (fun T => Pr (realExp A Vt Z i' N) (fun _ => T)) ≤ ζ tV N + ζ tV N

/-- `IndistOn` follows from index privacy in the stronger form. -/
theorem indistOn_of (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
    (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (h : HasStrongIndexPrivacyWith R A S ζ) :
    IndistOn R A ζ := by
  intro i i' hpp Z hZ hZ' tV Vt N hV
  have h1 := (h i Z hZ tV Vt N hV).1
  have h2 := (h i' Z hZ' tV Vt N hV).1
  have e : idealExp R S Vt Z i' N = idealExp R S Vt Z i N := by
    unfold idealExp
    rw [hpp]
  rw [e] at h2
  refine SD_le_of_forall (fun E => ?_) (fun E => ?_)
  · calc _ ≤ prob (idealExp R S Vt Z i N) E + ζ tV N := le_add_of_SD_le h1 E
      _ ≤ (Pr (realExp A Vt Z i' N) (fun _ => E) + ζ tV N) + ζ tV N := by
        gcongr; exact le_add_of_SD_le' h2 E
      _ = _ := by rw [add_assoc]
  · calc _ ≤ prob (idealExp R S Vt Z i N) E + ζ tV N := le_add_of_SD_le h2 E
      _ ≤ (Pr (realExp A Vt Z i N) (fun _ => E) + ζ tV N) + ζ tV N := by
        gcongr; exact le_add_of_SD_le' h1 E
      _ = _ := by rw [add_assoc]

/-- `IndistOn` for one event on the verifier's view. -/
theorem IndistOn.event {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : IndistOn R A ζ) (i i' : I) (hpp : R.pp i = R.pp i')
    (Z : ViewEnv lam IVK X W Pf) (hZ : Z.IsValid R i) (hZ' : Z.IsValid R i')
    (tV : ℕ) (Vt : IVK → AdvVerifier lam X Pf) (N : ℕ)
    (hb : ∀ ivk, (Vt ivk).QueryBound tV) (T : Set (View lam IVK X Pf)) :
    Pr (realExp A Vt Z i N) (fun _ => T) ≤
      Pr (realExp A Vt Z i' N) (fun _ => T) + (ζ tV N + ζ tV N) :=
  le_add_of_SD_le (h i i' hpp Z hZ hZ' tV Vt N hb) T

/-- From `IndistOn`, the key only: the same bound without any session, for all pairs of indices with
the same public parameters. -/
theorem IndistOn.key_alone {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : IndistOn R A ζ) (i i' : I) (hpp : R.pp i = R.pp i') (tV : ℕ)
    (Vt : IVK → AdvVerifier lam X Pf) (N : ℕ) (hb : ∀ ivk, (Vt ivk).QueryBound tV) :
    SD (fun T => Pr (realExp A Vt (fun _ => none) i N) (fun _ => T))
        (fun T => Pr (realExp A Vt (fun _ => none) i' N) (fun _ => T)) ≤
      ζ tV N + ζ tV N :=
  h i i' hpp (fun _ => none) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) tV Vt N hb

end ZKCP
