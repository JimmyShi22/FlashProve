-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Bridge.lean: for the family with one oracle, `rom lam`, the oracle algorithms, the measure and
the probabilities of Rom/ agree with those of ZKCP/Defs.lean.

* `toRom`, `ofRom`: the oracle algorithms `ZKCP.OComp lam α` and `Rom.OComp (rom lam) α` correspond
  node by node. The two maps are inverse to each other; `toRom` respects bind, `QueryBound`,
  `withTrace` and the run with the oracle fixed.
* `famEquiv`: a function f : {0,1}^* → {0,1}^lam is a family with one member. The correspondence is
  measurable both ways and carries the measure `ZKCP.U lam` to `Rom.U (rom lam)`.
-/
import ZKCP.Defs
import Rom.Measure

open MeasureTheory
open scoped ENNReal

namespace Rom

variable {lam : ℕ} {α β : Type}

/-! ### Oracle algorithms -/

/-- An oracle algorithm of ZKCP/Defs.lean as one over `rom lam`. -/
def toRom : ZKCP.OComp lam α → OComp (rom lam) α
  | .pure a => .pure a
  | .query q k => .query () q fun r => toRom (k r)
  | .sample n k => .sample n fun r => toRom (k r)

/-- An oracle algorithm over `rom lam` as one of ZKCP/Defs.lean. -/
def ofRom : OComp (rom lam) α → ZKCP.OComp lam α
  | .pure a => .pure a
  | .query _ q k => .query q fun r => ofRom (k r)
  | .sample n k => .sample n fun r => ofRom (k r)

@[simp] theorem ofRom_toRom (c : ZKCP.OComp lam α) : ofRom (toRom c) = c := by
  induction c with
  | pure a => rfl
  | query q k ih => simp only [toRom, ofRom, ih]
  | sample n k ih => simp only [toRom, ofRom, ih]

@[simp] theorem toRom_ofRom (c : OComp (rom lam) α) : toRom (ofRom c) = c := by
  induction c with
  | pure a => rfl
  | query o q k ih => cases o; simp only [toRom, ofRom, ih]
  | sample n k ih => simp only [toRom, ofRom, ih]

@[simp] theorem toRom_pure (a : α) : toRom (.pure a : ZKCP.OComp lam α) = .pure a := rfl

theorem toRom_bind (c : ZKCP.OComp lam α) (g : α → ZKCP.OComp lam β) :
    toRom (c.bind g) = (toRom c).bind fun a => toRom (g a) := by
  induction c with
  | pure a => rfl
  | query q k ih => simp only [ZKCP.OComp.bind, toRom, OComp.bind, ih]
  | sample n k ih => simp only [ZKCP.OComp.bind, toRom, OComp.bind, ih]

theorem queryBound_toRom (c : ZKCP.OComp lam α) (t : ℕ) :
    (toRom c).QueryBound t ↔ c.QueryBound t := by
  induction c generalizing t with
  | pure a => simp [toRom, OComp.QueryBound, ZKCP.OComp.QueryBound]
  | query q k ih =>
    cases t with
    | zero => simp [toRom, OComp.QueryBound, ZKCP.OComp.QueryBound]
    | succ t => simp only [toRom, OComp.QueryBound, ZKCP.OComp.QueryBound, ih]; exact Iff.rfl
  | sample n k ih => simp only [toRom, OComp.QueryBound, ZKCP.OComp.QueryBound, ih]

/-- A trace of ZKCP/Defs.lean as a trace over `rom lam`. -/
def trTo (tr : ZKCP.Trace lam) : Trace (rom lam) := tr.map fun e => ⟨(), e.1, e.2⟩

/-- A trace over `rom lam` as a trace of ZKCP/Defs.lean. -/
def trOf (tr : Trace (rom lam)) : ZKCP.Trace lam := tr.map fun e => (e.2.1, e.2.2)

@[simp] theorem trOf_trTo (tr : ZKCP.Trace lam) : trOf (trTo tr) = tr := by
  simp [trOf, trTo, Function.comp_def]

@[simp] theorem trTo_trOf (tr : Trace (rom lam)) : trTo (trOf tr) = tr := by
  simp only [trOf, trTo, List.map_map]
  conv_rhs => rw [← List.map_id tr]
  exact List.map_congr_left fun e _ => by obtain ⟨⟨⟩, q, r⟩ := e; rfl

lemma OComp.bind_assoc {S : OSpec} {γ : Type} (c : OComp S α)
    (g : α → OComp S β) (h : β → OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

theorem toRom_withTrace (c : ZKCP.OComp lam α) :
    toRom c.withTrace = (toRom c).withTrace.bind fun out => .pure (out.1, trOf out.2) := by
  induction c with
  | pure a => rfl
  | query q k ih =>
    simp only [toRom, OComp.withTrace, ZKCP.OComp.withTrace, OComp.bind,
      toRom_bind, ih, OComp.bind_assoc]
    rfl
  | sample n k ih => simp only [toRom, OComp.withTrace, ZKCP.OComp.withTrace, OComp.bind, ih]

/-! ### Oracles -/

/-- {0,1}^lam is the range of the one oracle. The two types are the same; they carry two
descriptions of the same σ-algebra (all subsets), and these two functions, both the identity, pass
from one to the other. -/
def rngTo (o : (rom lam).ι) : ZKCP.Digest lam → (rom lam).Rng o := fun r => r
def rngOf (o : (rom lam).ι) : (rom lam).Rng o → ZKCP.Digest lam := fun r => r

lemma measurable_rngTo (o : (rom lam).ι) : Measurable (rngTo (lam := lam) o) :=
  measurable_of_finite _
lemma measurable_rngOf (o : (rom lam).ι) : Measurable (rngOf (lam := lam) o) := measurable_from_top

/-- One function as a family with one member: famOf f = fun _ q => f q. -/
def famOf (f : ZKCP.Oracle lam) : Fam (rom lam) := fun o q => rngTo o (f q)

/-- A family with one member as one function. -/
def famBack (g : Fam (rom lam)) : ZKCP.Oracle lam := fun q => rngOf () (g () q)

lemma famOf_apply (f : ZKCP.Oracle lam) (o : (rom lam).ι) (q : ZKCP.Str) : famOf f o q = f q := rfl

lemma measurable_eval_oracle (q : ZKCP.Str) : Measurable fun f : ZKCP.Oracle lam => f q :=
  measurable_pi_apply q

lemma measurable_famOf : Measurable (famOf (lam := lam)) :=
  measurable_pi_iff.2 fun o =>
    measurable_pi_iff.2 fun q => (measurable_rngTo o).comp (measurable_eval_oracle q)

lemma measurable_famBack : Measurable (famBack (lam := lam)) := by
  refine measurable_pi_iff.2 fun q => ?_
  have h1 : Measurable fun g : Fam (rom lam) => g () := measurable_pi_apply (() : (rom lam).ι)
  have h2 : Measurable fun g : (rom lam).Dom () → (rom lam).Rng () => g q :=
    measurable_pi_apply (q : (rom lam).Dom ())
  exact (measurable_rngOf ()).comp (h2.comp h1)

/-- The correspondence of oracles, measurable in both directions. -/
def famEquiv : ZKCP.Oracle lam ≃ᵐ Fam (rom lam) where
  toFun := famOf
  invFun := famBack
  left_inv := fun _ => rfl
  right_inv := fun _ => by funext o q; cases o; rfl
  measurable_toFun := measurable_famOf
  measurable_invFun := measurable_famBack

theorem runEager_toRom (f : ZKCP.Oracle lam) (c : ZKCP.OComp lam α) :
    (toRom c).runEager (famOf f) = c.run f := by
  induction c with
  | pure a => rfl
  | query q k ih => exact ih (f q)
  | sample n k ih => simp only [toRom, OComp.runEager, ZKCP.OComp.run, ih]

theorem PrCoins_toRom (f : ZKCP.Oracle lam) (c : ZKCP.OComp lam α) (E : Set α) :
    PrCoins (famOf f) (toRom c) E = ZKCP.PrCoins f c E := by
  unfold PrCoins ZKCP.PrCoins ZKCP.prob Prob.pr
  rw [runEager_toRom]

/-! ### The measures -/

/-- One function as a function on the pairs (oracle, point). -/
def flatOf (f : ZKCP.Oracle lam) : Flat (rom lam) := fun p => rngTo p.1 (f p.2)

lemma measurable_flatOf : Measurable (flatOf (lam := lam)) :=
  measurable_pi_iff.2 fun p => (measurable_rngTo p.1).comp (measurable_eval_oracle p.2)

lemma U_map_flatOf : (ZKCP.U lam).map flatOf
    = Measure.infinitePi fun p : (Σ o : (rom lam).ι, (rom lam).Dom o) => unifM (rom lam) p.1 := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurable_flatOf (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : flatOf (lam := lam) ⁻¹' (Set.pi s t)
      = Set.pi ((s.image fun p => (p.2 : ZKCP.Str) : Finset ZKCP.Str) : Set ZKCP.Str)
          fun q => rngTo () ⁻¹' (t ⟨(), q⟩) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro h q ⟨⟨⟨⟩, q'⟩, hp, rfl⟩; exact h _ hp
    · rintro h ⟨⟨⟩, q⟩ hp; exact h q ⟨_, hp, rfl⟩
  rw [hpre, ZKCP.U, Measure.infinitePi_pi _ fun q _ => (Set.toFinite _).measurableSet,
    Finset.prod_image (fun p _ p' _ h => by
      obtain ⟨⟨⟩, q⟩ := p; obtain ⟨⟨⟩, q'⟩ := p'; simp only at h; rw [h])]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨⟨⟩, q⟩ := p
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.toFinite _).measurableSet,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (ht _)]
  rfl

/-- The measure U(λ) of ZKCP/Defs.lean, carried over to families with one member, is `U (rom lam)`.
-/
theorem U_map_famOf : (ZKCP.U lam).map famOf = U (rom lam) := by
  rw [U_eq_map_curry, ← U_map_flatOf,
    Measure.map_map (MeasurableEquiv.measurable _) measurable_flatOf]
  rfl

/-- The two probabilities agree, also for events that depend on the oracle. -/
theorem Pr_toRom (c : ZKCP.OComp lam α) (E : Fam (rom lam) → Set α) :
    Pr (toRom c) E = ZKCP.Pr c fun f => E (famOf f) := by
  unfold Pr ZKCP.Pr
  rw [← U_map_famOf]
  have h := lintegral_map_equiv
    (μ := ZKCP.U lam) (fun g => PrCoins g (toRom c) (E g)) (famEquiv (lam := lam))
  refine Eq.trans h (lintegral_congr fun f => ?_)
  exact PrCoins_toRom f c _

end Rom
