-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstLazy.lean: expansion from a state, querying only the hash blocks that are needed.

`OComp.stateFirst` (Rom/StateFirst.lean) replaces a query to a chain oracle (an oracle with a long
answer) by a query for a state σ and the K queries dr (σ, 0), .., dr (σ, K - 1) to one further
oracle dr, one for each hash block. The oracles that return states, the unchanged ones and dr are
the second family of oracles (`stSpec`); the first is the family S before the step. Here an adaptive
rule (`NeedA`, Rom/NeedA.lean) decides for each j in turn, from the hash blocks obtained so far,
whether dr (σ, j) is queried; a hash block that is not queried is the all-zero block `dig0`, also in
what the rule sees later.

  `OComp.stateFirstA`, `stateFirstAArg`   An algorithm and a scheme under a rule.
  `ReadsBy`, `ReadOK`   The condition, for an algorithm and for a scheme: at every query the
      continuation is the same program after an answer and after that answer with the unqueried hash
      blocks replaced by `dig0`.
  `runEager_stateFirstA`   Under the condition, for every fixed choice of the oracle functions, the
      algorithm under the rule returns what `OComp.stateFirst` returns.
  `named_stateFirstA`   Hence, under `ReadOK`, the primitive with extractor and simulator named
      (`IsZKCPArgWith`, ZKCP/Gen.lean) passes from `stateFirstArg C A`, with the same extractor,
      simulator and bounds. (to `stateFirstAArg C need A`)
  `queryBound_stateFirstA`   If the rule queries nothing from the index `nb o q` on (`NeedA.Below`),
      a typed query costs at most 1 + `nb o q` queries. A query to an unchanged oracle is counted so
      too: take `nb o q` = 0 there, with a rule that is false there. The rule must be false from
      `nb o q` on also beyond K, so the rule that always queries meets this for no nb.
      `queryBound_stateFirstA_overOne` is the same count in queries to one hash function f
      (Rom/Family.lean).

Notation:
  B, α, ε, ζ: in `IsZKCPArgWith R A B E Sim α ε ζ` (ZKCP/Gen.lean): a natural number B, a number α
      and two functions ε, ζ of two natural numbers; its fields: `HasCompletenessError R A B α`,
      `HasIndexBindingWith R A E ε`, `HasIndexPrivacyWith R A B Sim ζ`
  `Gen.Arg` (ZKCP/Gen.lean): ARG = (C, P, V) over the family S; `A.C : I → OComp S (IVK × ISK)`: at
      an index i it returns ivk and isk; P takes isk and a batch, V takes ivk and one pair (x, π)
  the arguments of ε: natural numbers; in `HasIndexBindingWith` (ZKCP/Gen.lean) `ε tC tP`, with
      `Ct.QueryBound tC` and `(Pt st).QueryBound tP`
  the arguments of ζ: natural numbers; in `PrivacyFor` (ZKCP/Gen.lean) `ζ tV N`, with
      `(Vt ivk).QueryBound tV` (`AdvVerifier.QueryBound`, the same file); N counts batches

Limits: that a given rule meets the condition for a given scheme is a hypothesis; without the
condition `dig0` can show in a result. The bound on queries is coarser than the worst run: it counts
all indices below `nb o q`, queried or not, so a rule that queries a second value only after a first
was rejected is counted with both. Nothing is said about the average. That over f, for lam ≥ 1, a
state costs two queries (each on the whole typed query) and dr one is found by counting; it is no
theorem here. Only the three properties of `IsZKCPArgWith` carry over: the extraction error
(`Gen.HasExtractionError`, ZKCP/GenOptional.lean) depends on the honest committer's trace, which is
shorter under a rule, so it does not follow from equal outputs (ZKCP/GenSameRun.lean). (Refined and
adaptive completeness: see `sameRunAll_stateFirstA` and ZKCP/GenSameRun.lean.)
-/
import Rom.NeedA
import Rom.StateFirstKit2
import ZKCP.GenSameRun
import Rom.Cost

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {α β : Type}

/-- the queries to dr at a state under a rule: K indices from j on; acc: the hash blocks so far -/
def askAd (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) :
    (K j : ℕ) → (ℕ → Dg lam) → OComp (stSpec S lam C) (ℕ → Dg lam)
  | 0, _, acc => .pure acc
  | K + 1, j, acc =>
      match nd j acc with
      | true =>
        .query (S := stSpec S lam C) (.inr ()) (σ, j) fun r =>
          askAd σ nd K (j + 1) (Function.update acc j r)
      | false => askAd σ nd K (j + 1) acc

theorem runEager_askAd (f : Fam (stSpec S lam C))
    (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), (askAd C σ nd K j acc).runEager f =
      PMF.pure (maskFrom nd (fun i => f (.inr ()) (σ, i)) K j acc)
  | 0, _, _ => rfl
  | K + 1, j, acc => by
    unfold askAd maskFrom
    cases nd j acc with
    | true => exact runEager_askAd f σ nd K (j + 1) _
    | false => exact runEager_askAd f σ nd K (j + 1) _

theorem runEager_askDr (f : Fam (stSpec S lam C)) (σ : Dg lam × Dg lam) :
    ∀ (K off : ℕ),
      (askDr C σ off K).runEager f = PMF.pure fun i : Fin K => f (.inr ()) (σ, off + i.val)
  | 0, _ => by
    show PMF.pure _ = PMF.pure _
    congr 1
    funext i
    exact i.elim0
  | K + 1, off => by
    show ((askDr C σ (off + 1) K).bind fun rest =>
        .pure (Fin.cons (α := fun _ => Dg lam) (f (.inr ()) (σ, off)) rest)).runEager f = _
    rw [OComp.runEager_bind, runEager_askDr f σ K (off + 1)]
    refine (PMF.pure_bind _ _).trans ?_
    show PMF.pure _ = PMF.pure _
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · show f (.inr ()) (σ, off + 1 + i.val) = f (.inr ()) (σ, off + (i.val + 1))
      rw [Nat.add_assoc, Nat.add_comm 1]

namespace Link
variable {R : Type}
/-- The typed answer, with the hash blocks that the rule does not query replaced by dig0. -/
def mask : Link lam R → (ℕ → (ℕ → Dg lam) → Bool) → R → R
  | .plain, _, r => r
  | .chain K e, nd, r =>
    e.symm ((fun i : Fin K => maskFrom nd (extBl (e r).1) K 0 (acc0 lam) i.val), (e r).2)
end Link

/-- from the answer of the second family to the typed answer, under a rule -/
def expandA {R : Type} :
    (c : Link lam R) → (ℕ → (ℕ → Dg lam) → Bool) → c.Ans → OComp (stSpec S lam C) R
  | .plain, _, r => .pure r
  | .chain K e, nd, σ =>
    (askAd C σ nd K 0 (acc0 lam)).bind fun acc => .pure (e.symm ((fun i : Fin K => acc i.val), σ))

/-- the typed answer that belongs to an answer of the second family, the family being fixed -/
def typedOf {R : Type} (f : Fam (stSpec S lam C)) : (c : Link lam R) → c.Ans → R
  | .plain, r => r
  | .chain K e, σ => e.symm ((fun i : Fin K => f (.inr ()) (σ, i.val)), σ)

theorem runEager_expand {R : Type} (f : Fam (stSpec S lam C)) (c : Link lam R) (a : c.Ans) :
    (expand C c a).runEager f = PMF.pure (typedOf C f c a) := by
  cases c with
  | plain => rfl
  | chain K e =>
    show ((askDr C a 0 K).bind fun bl => .pure (e.symm (bl, a))).runEager f = _
    rw [OComp.runEager_bind, runEager_askDr]
    refine (PMF.pure_bind _ _).trans ?_
    show PMF.pure _ = PMF.pure _
    simp only [Nat.zero_add]
    rfl

theorem runEager_expandA {R : Type} (f : Fam (stSpec S lam C)) (c : Link lam R)
    (nd : ℕ → (ℕ → Dg lam) → Bool) (a : c.Ans) :
    (expandA C c nd a).runEager f = PMF.pure (c.mask nd (typedOf C f c a)) := by
  cases c with
  | plain => rfl
  | chain K e =>
    show ((askAd C a nd K 0 (acc0 lam)).bind fun acc =>
        .pure (e.symm ((fun i : Fin K => acc i.val), a))).runEager f = _
    rw [OComp.runEager_bind, runEager_askAd, PMF.pure_bind]
    show PMF.pure (e.symm _) =
      PMF.pure (e.symm
          ((fun i : Fin K =>
              maskFrom nd (extBl (e (e.symm ((fun i : Fin K => f (.inr ()) (a, i.val)), a))).1) K 0
                (acc0 lam) i.val),
            (e (e.symm ((fun i : Fin K => f (.inr ()) (a, i.val)), a))).2))
    rw [Equiv.apply_symm_apply]
    congr 3
    funext i
    rw [maskFrom_congr nd (bl' := extBl fun i : Fin K => f (.inr ()) (a, i.val)) K 0 (acc0 lam) fun i _ h2 => by
      unfold extBl
      rw [dif_pos (by omega)]]

/-- The same algorithm over the second family, under a rule. -/
def OComp.stateFirstA (need : NeedA S lam) : OComp S α → OComp (stSpec S lam C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).stateFirstA need
  | .query o q k =>
    .query (S := stSpec S lam C) (.inl o) q fun a =>
      (expandA C (C o) (need o q) a).bind fun r => (k r).stateFirstA need

/-- The condition: the program is the same after an answer and after `Link.mask` of that answer. -/
def ReadsBy (need : NeedA S lam) (c : OComp S α) : Prop :=
  c.FactorsBy fun o q r r' => r' = (C o).mask (need o q) r

/-- Under the condition the algorithm under the rule returns what OComp.stateFirst returns, for
every fixed family. -/
theorem runEager_stateFirstA
    (need : NeedA S lam) (f : Fam (stSpec S lam C)) (c : OComp S α) (h : ReadsBy C need c) :
    (c.stateFirstA C need).runEager f = (c.stateFirst C).runEager f := by
  induction c with
  | pure a => rfl
  | sample n k ih =>
    simp only [OComp.stateFirstA, OComp.stateFirst, OComp.runEager]
    congr 1
    funext r
    exact ih r (h r)
  | query o q k ih =>
    simp only [OComp.stateFirstA, OComp.stateFirst, OComp.runEager]
    rw [OComp.runEager_bind, OComp.runEager_bind, runEager_expandA, runEager_expand, PMF.pure_bind,
      PMF.pure_bind, ih _ (h.2 _), ← h.1 _ _ rfl]

variable {I X W PP IVK ISK Pf : Type}

def stateFirstAArg (need : NeedA S lam) (A : Gen.Arg S I X W IVK ISK Pf) :
    Gen.Arg (stSpec S lam C) I X W IVK ISK Pf where
  C := fun i => (A.C i).stateFirstA C need
  P := fun k b => (A.P k b).stateFirstA C need
  V := fun v x π => (A.V v x π).stateFirstA C need

/-- the condition for the three algorithms -/
def ReadOK (need : NeedA S lam) (A : Gen.Arg S I X W IVK ISK Pf) : Prop :=
  FacOK (fun o q r r' => r' = (C o).mask (need o q) r) A

variable {C}

theorem sameRunAll_stateFirstA
    {need : NeedA S lam} {A : Gen.Arg S I X W IVK ISK Pf} (h : ReadOK C need A) :
    (stateFirstAArg C need A).SameRunAll (stateFirstArg C A) :=
  ⟨fun i g => runEager_stateFirstA C need g (A.C i) (h.C i),
    fun k b g => runEager_stateFirstA C need g (A.P k b) (h.P k b),
    fun v x π g => runEager_stateFirstA C need g (A.V v x π) (h.V v x π)⟩

theorem named_stateFirstA_iff {need : NeedA S lam} {A : Gen.Arg S I X W IVK ISK Pf}
    (h : ReadOK C need A) (R : Gen.RelPair I X W PP) (B : ℕ)
    (E : Gen.Extractor (stSpec S lam C) I X W IVK Pf)
    (Sim : Gen.Simulator (stSpec S lam C) PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    Gen.IsZKCPArgWith R (stateFirstAArg C need A) B E Sim α ε ζ ↔
    Gen.IsZKCPArgWith R (stateFirstArg C A) B E Sim α ε ζ :=
  Gen.Arg.SameRunVia.isZKCPArgWith_iff (sameRunAll_stateFirstA h).toSameRun R B E Sim α ε ζ

/-- Under the condition `ReadOK` the three properties, with explicit extractor and simulator, carry
over to the scheme under a rule: the same relations, B, extractor, simulator and three bounds. -/
theorem named_stateFirstA {need : NeedA S lam} {A : Gen.Arg S I X W IVK ISK Pf}
    (h : ReadOK C need A) {R : Gen.RelPair I X W PP} {B : ℕ}
    {E : Gen.Extractor (stSpec S lam C) I X W IVK Pf}
    {Sim : Gen.Simulator (stSpec S lam C) PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (H : Gen.IsZKCPArgWith R (stateFirstArg C A) B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R (stateFirstAArg C need A) B E Sim α ε ζ :=
  (named_stateFirstA_iff h R B E Sim α ε ζ).2 H

/-- `ReadOK` holds if the three algorithms read their answers only up to a relation `ag` (`FacOK`),
and an answer and `Link.mask` of it are always in that relation. -/
theorem readOK_of_facOK {need : NeedA S lam} {A : Gen.Arg S I X W IVK ISK Pf}
    {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} (h : FacOK ag A)
    (hm : ∀ o q r, ag o q r ((C o).mask (need o q) r)) : ReadOK C need A :=
  FacOK.mono (fun o q r _ e => e ▸ hm o q r) h

/-! ## The rule that always queries -/

theorem mask_all {R : Type} (c : Link lam R) (r : R) : c.mask (fun _ _ => true) r = r := by
  cases c with
  | plain => rfl
  | chain K e =>
    show e.symm ((fun i : Fin K => maskFrom (fun _ _ => true) (extBl (e r).1) K 0 (acc0 lam) i.val),
          (e r).2) = r
    have h : (fun i : Fin K => maskFrom (fun _ _ => true) (extBl (e r).1) K 0 (acc0 lam) i.val) =
        (e r).1 := funext fun i => by
      rw [maskFrom_all, if_pos ⟨Nat.zero_le _, by have := i.isLt; omega⟩]
      unfold extBl
      rw [dif_pos i.isLt]
    rw [h, Prod.mk.eta, Equiv.symm_apply_apply]

/-- With the rule that always queries, the condition holds for every program. -/
theorem readsBy_all (c : OComp S α) : ReadsBy C (fun _ _ _ _ => true) c := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact ih
  | query o q k ih => exact ⟨fun r r' h => by rw [h, mask_all], ih⟩

/-- So the algorithm under that rule returns what `OComp.stateFirst` returns. -/
theorem stateFirstA_all (f : Fam (stSpec S lam C)) (c : OComp S α) :
    (c.stateFirstA C fun _ _ _ _ => true).runEager f = (c.stateFirst C).runEager f :=
  runEager_stateFirstA C _ f c (readsBy_all c)

/-! ## Queries -/

/-- a rule that queries nothing from index b on makes at most b − j queries from index j on -/
theorem queryBound_askAd (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) (b : ℕ)
    (hb : ∀ j acc, b ≤ j → nd j acc = false) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), (askAd C σ nd K j acc).QueryBound (b - j)
  | 0, _, _ => trivial
  | K + 1, j, acc => by
    unfold askAd
    cases h : nd j acc with
    | true =>
      have hj : j < b := by
        by_contra hn
        rw [hb j acc (by omega)] at h
        cases h
      obtain ⟨d, hd⟩ : ∃ d, b - j = d + 1 := ⟨b - j - 1, by omega⟩
      rw [hd]
      intro r
      have := queryBound_askAd σ nd b hb K (j + 1) (Function.update acc j r)
      rwa [show b - (j + 1) = d by omega] at this
    | false => exact (queryBound_askAd σ nd b hb K (j + 1) acc).mono (by omega)

theorem queryBound_expandA {R : Type} (c : Link lam R) (nd : ℕ → (ℕ → Dg lam) → Bool) (b : ℕ)
    (hb : ∀ j acc, b ≤ j → nd j acc = false) (a : c.Ans) :
    (expandA C c nd a).QueryBound b := by
  cases c with
  | plain => trivial
  | chain K e =>
    have h := (queryBound_askAd (C := C) a nd b hb K 0 (acc0 lam)).bind (t := 0)
      (g := fun acc =>
          (OComp.pure (e.symm ((fun i : Fin K => acc i.val), a)) : OComp (stSpec S lam C) R))
      fun _ => trivial
    exact h

/-- The queries of the algorithm under a rule that queries nothing from the index `nb o q` on: a
query costs 1 and at most `nb o q` queries to dr. -/
theorem queryBound_stateFirstA
    (need : NeedA S lam) (nb : (o : S.ι) → S.Dom o → ℕ) (hb : need.Below nb) (c : OComp S α) :
    ∀ t, c.CostBoundAt (fun o q => 1 + nb o q) t → (c.stateFirstA C need).QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    rw [show 1 + nb o q + t' = nb o q + t' + 1 by omega]
    intro a
    exact (queryBound_expandA (C o) (need o q) (nb o q) (hb o q) a).bind fun r => ih r t' (h r)

/-! ## Queries to the hash function f -/

theorem costBound_askAd (w : (stSpec S lam C).ι → ℕ) (σ : Dg lam × Dg lam)
    (nd : ℕ → (ℕ → Dg lam) → Bool) (b : ℕ) (hb : ∀ j acc, b ≤ j → nd j acc = false) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), (askAd C σ nd K j acc).CostBound w ((b - j) * w (.inr ()))
  | 0, _, _ => trivial
  | K + 1, j, acc => by
    unfold askAd
    cases h : nd j acc with
    | true =>
      have hj : j < b := by
        by_contra hn
        rw [hb j acc (by omega)] at h
        cases h
      refine ⟨(b - (j + 1)) * w (.inr ()), ?_, fun r => costBound_askAd w σ nd b hb K (j + 1) _⟩
      rw [show b - j = (b - (j + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    | false =>
      exact (costBound_askAd w σ nd b hb K (j + 1) acc).mono (Nat.mul_le_mul_right _ (by omega))

theorem costBound_expandA {R : Type} (w : (stSpec S lam C).ι → ℕ) (c : Link lam R)
    (nd : ℕ → (ℕ → Dg lam) → Bool) (b : ℕ) (hb : ∀ j acc, b ≤ j → nd j acc = false) (a : c.Ans) :
    (expandA C c nd a).CostBound w (b * w (.inr ())) := by
  cases c with
  | plain => trivial
  | chain K e =>
    have h := OComp.CostBound.bind (w := w) (t := 0)
      (g := fun acc =>
          (OComp.pure (e.symm ((fun i : Fin K => acc i.val), a)) : OComp (stSpec S lam C) R))
      (fun _ => trivial) (costBound_askAd (C := C) w a nd b hb K 0 (acc0 lam))
    exact h

/-- With weights, for a rule that queries nothing from the index `nb o q` on: a query costs the
weight of its oracle in the second family and `nb o q` times the weight of dr -/
theorem costBound_stateFirstA (w : (stSpec S lam C).ι → ℕ) (need : NeedA S lam)
    (nb : (o : S.ι) → S.Dom o → ℕ) (hb : need.Below nb) (c : OComp S α) :
    ∀ t, c.CostBoundAt (fun o q => w (.inl o) + nb o q * w (.inr ())) t →
      (c.stateFirstA C need).CostBound w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    refine ⟨nb o q * w (.inr ()) + t', by show w (.inl o) + nb o q * w (.inr ()) + t' = w (.inl o) + (nb o q * w (.inr ()) + t'); omega, fun a => ?_⟩
    exact OComp.CostBound.bind
      (fun r => ih r t' (h r)) (costBound_expandA w (C o) (need o q) (nb o q) (hb o q) a)

/-- The queries to the hash function f of the algorithm under a rule that queries nothing from the
index `nb o q` on, with the second family implemented by f (OComp.overOne): a typed query costs the
hash blocks of its oracle in the second family and `nb o q` times those of dr. (By a count, no
theorem: a state has two, dr one.) -/
theorem queryBound_stateFirstA_overOne (m : OracleCoding (stSpec S lam C) lam) (need : NeedA S lam)
    (nb : (o : S.ι) → S.Dom o → ℕ) (hb : need.Below nb) (c : OComp S α) (t : ℕ)
    (h : c.CostBoundAt (fun o q => m.blocks (.inl o) + nb o q * m.blocks (.inr ())) t) :
    ((c.stateFirstA C need).overOne m).QueryBound t :=
  queryBound_overOne_of_cost m _ t (costBound_stateFirstA m.blocks need nb hb c t h)

end Rom
