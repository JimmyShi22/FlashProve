-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstCB.lean: completeness and index binding under the expansion of answers from a state.

Rom/StateFirst.lean turns a scheme `A` over typed random oracles into `stateFirstArg C A`, in which
the long answer of a chain oracle (in the scheme, the rest of a Fiat-Shamir answer) is expanded from
a state of 2 `lam` bits; its oracles are the second family (`stSpec`), those of `A` the first. This
file proves two of the three clauses of `Spec.stateFirst`.

  `completeness_stateFirst`   The completeness error grows by n² / 2^(2 lam), n = nC + nP + B nV,
      where nC, nP, nV bound the queries of committer, prover and verifier at chain oracles.
  `binding_stateFirst`   If the extractor `E` reads only entries at the other oracles (`PlainOnly`),
      index binding with the bound ε for `E` gives index binding for `extSt C E` with the bound
      ε tC tP + n² / 2^(2 lam), n = tC + tP + nV.

Both follow from `mixClose_rawFirst` (Rom/StateFirstKit2.lean). For binding, the experiment is
written as one program in which the two adversaries query the second family of oracles and the
verifier the first (`mixBind`). The reduction (`downC`, `downP`) answers the adversaries from the
first family, from a table that it keeps (`Book`), which goes from the committer to the prover in
the state, and at a new query to dr from a fresh sample. If the extractor reads only unchanged
oracles (`PlainOnly`), the reduction applied to `mixBind` gives the binding experiment on `A`
(`ideal_mixBind`). Each query costs it at most one query (`queryBound_ideal_liftR`), so the
arguments of ε do not change.

Notation:
  dr: the added oracle of the second family: `.inr ()` of `stSpec S lam C` (Rom/StateFirst.lean); a
      query to it is an expansion query (state, counter), of type `(Dg lam × Dg lam) × ℕ`; an answer
      is a hash block

Limits: nothing about privacy (Rom/StateFirstPriv.lean), and nothing about one hash function f. nC,
nP, nV count queries at chain oracles only (`wCh`); tC and tP count all queries of the adversaries.
-/
import Rom.StateFirstKit2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))
  {I X W PP IVK ISK Pf : Type} {α β : Type}

/-! ## Completeness -/

theorem verifyAll_stateFirst (A : Gen.Arg S I X W IVK ISK Pf) (ivk : IVK) (l : List (X × Pf)) :
    Gen.verifyAll (stateFirstArg C A) ivk l = (Gen.verifyAll A ivk l).stateFirst C := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have e1 : Gen.verifyAll (stateFirstArg C A) ivk (s :: rest) = ((A.V ivk s.1 s.2).stateFirst C).bind fun c =>
        (Gen.verifyAll (stateFirstArg C A) ivk rest).bind fun cs => .pure (c && cs) := rfl
    have e2 : Gen.verifyAll A ivk (s :: rest) = (A.V ivk s.1 s.2).bind fun c =>
        (Gen.verifyAll A ivk rest).bind fun cs => .pure (c && cs) := rfl
    rw [e1, e2, ih]
    simp only [stateFirst_bind]
    rfl

theorem completenessExp_eq (A : Gen.Arg S I X W IVK ISK Pf) (i : I) (b : List (X × W)) :
    Gen.completenessExp A i b =
      (A.C i).bind fun key =>
        (A.P key.2 b).bind fun πs => Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val) := rfl

theorem completenessExp_stateFirst (A : Gen.Arg S I X W IVK ISK Pf) (i : I) (b : List (X × W)) :
    Gen.completenessExp (stateFirstArg C A) i b = (Gen.completenessExp A i b).stateFirst C := by
  have e1 : Gen.completenessExp (stateFirstArg C A) i b = ((A.C i).stateFirst C).bind fun key =>
      ((A.P key.2 b).stateFirst C).bind fun πs =>
        Gen.verifyAll (stateFirstArg C A) key.1 ((b.map Prod.fst).zip πs.val) := rfl
  rw [e1, completenessExp_eq]
  simp only [stateFirst_bind, verifyAll_stateFirst]

theorem costBoundAt_verifyAll (A : Gen.Arg S I X W IVK ISK Pf) {w : (o : S.ι) → S.Dom o → ℕ}
    {nV : ℕ} (hV : ∀ v x π, (A.V v x π).CostBoundAt w nV) (ivk : IVK) :
    ∀ l : List (X × Pf), (Gen.verifyAll A ivk l).CostBoundAt w (l.length * nV)
  | [] => trivial
  | s :: rest => by
    have e2 : Gen.verifyAll A ivk (s :: rest) = (A.V ivk s.1 s.2).bind fun c =>
        (Gen.verifyAll A ivk rest).bind fun cs => .pure (c && cs) := rfl
    rw [e2]
    have h1 : ∀ c : Bool, ((Gen.verifyAll A ivk rest).bind fun cs =>
          (.pure (c && cs) : OComp S Bool)).CostBoundAt
        w (rest.length * nV + 0) :=
      fun c =>
        OComp.CostBoundAt.bind (g := fun cs => (.pure (c && cs) : OComp S Bool)) (t := 0)
          (fun cs => OComp.CostBoundAt.pure _ 0) (costBoundAt_verifyAll A hV ivk rest)
    refine (OComp.CostBoundAt.bind h1 (hV ivk s.1 s.2)).mono ?_
    rw [List.length_cons, Nat.succ_mul]
    omega

theorem costBoundAt_completenessExp (A : Gen.Arg S I X W IVK ISK Pf) {w : (o : S.ι) → S.Dom o → ℕ}
    {B nC nP nV : ℕ} (hC : ∀ i, (A.C i).CostBoundAt w nC)
    (hP : ∀ k b, b.length ≤ B → (A.P k b).CostBoundAt w nP)
    (hV : ∀ v x π, (A.V v x π).CostBoundAt w nV) (i : I) (b : List (X × W)) (hb : b.length ≤ B) :
    (Gen.completenessExp A i b).CostBoundAt w (nC + nP + B * nV) := by
  rw [completenessExp_eq, Nat.add_assoc]
  refine OComp.CostBoundAt.bind
    (fun key => OComp.CostBoundAt.bind (fun πs => ?_) (hP key.2 b hb)) (hC i)
  refine (costBoundAt_verifyAll A hV key.1 _).mono (Nat.mul_le_mul_right _ ?_)
  rw [List.length_zip, List.length_map]
  omega

/-- If nC, nP, nV bound the queries of C, P, V at chain oracles, completeness carries over, with the
collision term added. -/
theorem completeness_stateFirst {C : ∀ o, Link lam (S.Rng o)} (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (α : ℝ≥0∞) (nC nP nV : ℕ)
    (hC : ∀ i, (A.C i).CostBoundAt (wCh C) nC)
    (hP : ∀ k b, b.length ≤ B → (A.P k b).CostBoundAt (wCh C) nP)
    (hV : ∀ v x π, (A.V v x π).CostBoundAt (wCh C) nV) (h : Gen.HasCompletenessError R A B α) :
    Gen.HasCompletenessError R (stateFirstArg C A) B
      (α + collP lam (nC + nP + B * nV) (nC + nP + B * nV)) := by
  intro i b hb
  have hm := mixClose_rawFirst (liftT C (Gen.completenessExp A i b)) (nC + nP + B * nV) 0
    (mixBound_liftT _ _ (costBoundAt_completenessExp A hC hP hV i b hb.1))
    (typedOnly_liftT _).rawFirst {c | c = false}
  rw [real_liftT, ← completenessExp_stateFirst, ideal_liftT, Pr_bind_pure, Nat.add_zero] at hm
  exact hm.trans (add_le_add (h i b hb) le_rfl)

/-! ## Index binding: traces -/

theorem Link.back_toAns {R : Type} (c : Link lam R) (r : R) :
    c.back (c.toAns r) = if c.isPlain then some r else none := by
  cases c <;> rfl

theorem plainTr_cons_inl (o : S.ι) (q : S.Dom o) (r : S.Rng o) (tr : Trace (stSpec S lam C)) :
    plainTr C ((⟨.inl o, q, (C o).toAns r⟩ : QA (stSpec S lam C)) :: tr) =
      if (C o).isPlain then (⟨o, q, r⟩ : QA S) :: plainTr C tr else plainTr C tr := by
  unfold plainTr
  rw [List.filterMap_cons]
  dsimp only
  rw [Link.back_toAns]
  cases (C o).isPlain <;> rfl

theorem plainTr_cons_dr (u : Unit) (p : (Dg lam × Dg lam) × ℕ)
    (r : Dg lam) (tr : Trace (stSpec S lam C)) :
    plainTr C ((⟨.inr u, p, r⟩ : QA (stSpec S lam C)) :: tr) = plainTr C tr := rfl

theorem plainOf_cons (o : S.ι) (q : S.Dom o) (r : S.Rng o) (tr : Trace S) :
    plainOf C ((⟨o, q, r⟩ : QA S) :: tr) =
      if (C o).isPlain then (⟨o, q, r⟩ : QA S) :: plainOf C tr else plainOf C tr := by
  unfold plainOf
  rw [List.filter_cons]

/-- The trace lemma: the adversary's entries at unchanged oracles (`plainTr`) are those of the
reduction's own trace (`plainOf`); an equality of programs. -/
theorem trace_ideal (c : OComp (stSpec S lam C) α) :
    ∀ b : Book S lam,
      ((ideal C false (liftR C c.withTrace) b).bind fun x =>
          (.pure (x.1.1, plainTr C x.1.2, x.2) : OComp S (α × Trace S × Book S lam))) =
        (ideal C false (liftR C c) b).withTrace.bind fun y =>
          .pure (y.1.1, plainOf C y.2, y.1.2) := by
  induction c with
  | pure a => intro b; rfl
  | sample n k ih => intro b; simp only [OComp.withTrace, liftR, ideal, OComp.bind, ih]
  | query x q k ih =>
    intro b
    match x, q, k, ih with
    | .inl o, q, k, ih =>
      simp only [OComp.withTrace, liftR, liftR_bind, ideal, ideal_bind, OComp.bind,
        OComp.bind_assoc, plainTr_cons_inl, plainOf_cons]
      congr 1
      funext r
      have h := congrArg (fun d : OComp S (α × Trace S × Book S lam) =>
        d.bind fun z =>
          (.pure (z.1,
              (if (C o).isPlain then (⟨o, q, r⟩ : QA S) :: z.2.1 else z.2.1),
              z.2.2) : OComp S (α × Trace S × Book S lam)))
        (ih ((C o).toAns r) (b.note C o q r))
      simpa only [OComp.bind_assoc, OComp.bind] using h
    | .inr u, p, k, ih =>
      simp only [OComp.withTrace, liftR, liftR_bind, ideal]
      cases drVal C b p with
      | some r =>
        simp only [ideal, ideal_bind, OComp.bind, OComp.bind_assoc, plainTr_cons_dr]
        exact ih r b
      | none =>
        simp only [OComp.withTrace, ideal, ideal_bind, OComp.bind,
          OComp.bind_assoc, plainTr_cons_dr]
        congr 1
        funext x
        exact ih _ _

/-! ## Index binding: numbers of queries -/

theorem queryBound_withTrace {S : OSpec} (c : OComp S α) :
    ∀ t, c.QueryBound t → c.withTrace.QueryBound t := by
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => OComp.QueryBound.bind (t := 0) (ih r t (h r)) fun _ => trivial

theorem queryBound_ideal_liftR (c : OComp (stSpec S lam C) α) :
    ∀ (b : Book S lam) (t : ℕ), c.QueryBound t → (ideal C false (liftR C c) b).QueryBound t := by
  induction c with
  | pure a => intro _ _ _; trivial
  | sample n k ih => exact fun b t h r => ih r b t (h r)
  | query x q k ih =>
    intro b t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      match x, q, k, ih, h with
      | .inl o, q, k, ih, h => exact fun r => ih _ _ t (h _)
      | .inr u, p, k, ih, h =>
        simp only [liftR, ideal]
        cases drVal C b p with
        | some r => exact (ih r b t (h r)).mono (Nat.le_succ t)
        | none => exact fun x => (ih _ _ t (h _)).mono (Nat.le_succ t)

/-! ## Index binding: the experiment -/

section Binding
variable (A : Gen.Arg S I X W IVK ISK Pf) (E : Gen.Extractor S I X W IVK Pf) {St : Type}
  (Ct : OComp (stSpec S lam C) (IVK × St)) (Pt : St → OComp (stSpec S lam C) (X × Pf))

/-- the binding experiment as one program: the two adversaries over the second family, then V over
the first -/
def mixBind : OComp (mixSpec C) (Gen.BindingOutcome I X W) :=
  (liftR C Ct.withTrace).bind fun o1 =>
      (liftR C (Pt o1.1.2).withTrace).bind fun o2 =>
          (liftT C (A.V o1.1.1 o2.1.1 o2.1.2)).bind fun c =>
    .pure ⟨c, E.Ei o1.1.1 (plainTr C o1.2), o2.1.1,
      E.Ew o1.1.1 (plainTr C o1.2) o2.1.1 o2.1.2 (plainTr C o2.2)⟩

theorem real_mixBind :
    real C (mixBind C A E Ct Pt) = Gen.bindingExp (stateFirstArg C A) (extSt C E) Ct Pt := by
  simp only [mixBind, real_bind, real_liftR, real_liftT, real]
  rfl

theorem rawFirst_mixBind : RawFirst C (mixBind C A E Ct Pt) :=
  rawFirst_liftR_bind _ fun _ =>
    rawFirst_liftR_bind _ fun _ =>
      (TypedOnly.bind (fun _ => by trivial) (typedOnly_liftT _)).rawFirst

theorem mixBound_mixBind {tC tP nV : ℕ} (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP)
    (hV : ∀ v x π, (A.V v x π).CostBoundAt (wCh C) nV) :
    MixBound C (mixBind C A E Ct Pt) nV (tC + tP) := by
  have h3 : ∀ (o1 : (IVK × St) × Trace (stSpec S lam C)) (o2 : (X × Pf) × Trace (stSpec S lam C)),
      MixBound C
        ((liftT C (A.V o1.1.1 o2.1.1 o2.1.2)).bind fun c =>
          (.pure ⟨c, E.Ei o1.1.1 (plainTr C o1.2), o2.1.1,
              E.Ew o1.1.1 (plainTr C o1.2) o2.1.1 o2.1.2 (plainTr C o2.2)⟩ :
            OComp (mixSpec C) (Gen.BindingOutcome I X W)))
        (nV + 0) (0 + 0) :=
    fun o1 o2 => MixBound.bind (fun _ => by trivial) (mixBound_liftT _ nV (hV _ _ _))
  have h2 := fun o1 : (IVK × St) × Trace (stSpec S lam C) =>
    MixBound.bind (h3 o1) (mixBound_liftR _ tP (queryBound_withTrace _ tP (hP o1.1.2)))
  exact (MixBound.bind h2 (mixBound_liftR _ tC (queryBound_withTrace _ tC hC))).mono
    (by omega) (by omega)

/-- the reduction for the committer; its table goes into the state -/
def downC : OComp S (IVK × (St × Book S lam)) :=
  (ideal C false (liftR C Ct) ⟨[], []⟩).bind fun x => .pure (x.1.1, (x.1.2, x.2))
/-- the reduction for the prover, from the table in the state -/
def downP (s : St × Book S lam) : OComp S (X × Pf) :=
  (ideal C false (liftR C (Pt s.1)) s.2).bind fun x => .pure x.1

/-- If the extractor reads only unchanged oracles (`PlainOnly`), the reduction applied to `mixBind`
is the binding experiment on A with the two reductions. -/
theorem ideal_mixBind (hE : PlainOnly C E) :
    ((ideal C false (mixBind C A E Ct Pt) ⟨[], []⟩).bind fun x => .pure x.1) =
      Gen.bindingExp A E (downC C Ct) (downP C Pt) := by
  have e2 : Gen.bindingExp A E (downC C Ct) (downP C Pt) = (downC C Ct).withTrace.bind fun o1 =>
      (downP C Pt o1.1.2).withTrace.bind fun o2 => (A.V o1.1.1 o2.1.1 o2.1.2).bind fun c =>
        .pure ⟨c, E.Ei o1.1.1 o1.2, o2.1.1, E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ := rfl
  calc
    ((ideal C false (mixBind C A E Ct Pt) ⟨[], []⟩).bind fun x => .pure x.1) =
        ((ideal C false (liftR C Ct.withTrace) ⟨[], []⟩).bind fun x =>
          (.pure (x.1.1, plainTr C x.1.2, x.2) :
            OComp S ((IVK × St) × Trace S × Book S lam))).bind fun z =>
          ((ideal C false (liftR C (Pt z.1.2).withTrace) z.2.2).bind fun x =>
              (.pure (x.1.1, plainTr C x.1.2, x.2) :
                OComp S ((X × Pf) × Trace S × Book S lam))).bind fun z' =>
            (A.V z.1.1 z'.1.1 z'.1.2).bind fun c =>
                .pure ⟨c, E.Ei z.1.1 z.2.1, z'.1.1, E.Ew z.1.1 z.2.1 z'.1.1 z'.1.2 z'.2.1⟩ := by
        simp only [mixBind, ideal_bind, ideal_liftT, ideal, OComp.bind_assoc, OComp.bind]
    _ = ((ideal C false (liftR C Ct) ⟨[], []⟩).withTrace.bind fun y =>
          (.pure (y.1.1, plainOf C y.2, y.1.2) :
            OComp S ((IVK × St) × Trace S × Book S lam))).bind fun z =>
          ((ideal C false (liftR C (Pt z.1.2)) z.2.2).withTrace.bind fun y =>
              (.pure (y.1.1, plainOf C y.2, y.1.2) :
                OComp S ((X × Pf) × Trace S × Book S lam))).bind fun z' =>
            (A.V z.1.1 z'.1.1 z'.1.2).bind fun c =>
                .pure ⟨c, E.Ei z.1.1 z.2.1, z'.1.1, E.Ew z.1.1 z.2.1 z'.1.1 z'.1.2 z'.2.1⟩ := by
        simp only [trace_ideal]
    _ = Gen.bindingExp A E (downC C Ct) (downP C Pt) := by
        rw [e2]
        simp only [downC, downP, withTrace_bind, OComp.withTrace, OComp.bind, OComp.bind_assoc,
          List.append_nil, ← hE.1, ← hE.2]

end Binding

/-- If V makes at most nV queries at chain oracles and the extractor reads only unchanged oracles
(`PlainOnly`), index binding carries over, with the collision term added. -/
theorem binding_stateFirst {C : ∀ o, Link lam (S.Rng o)} (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (E : Gen.Extractor S I X W IVK Pf)
    (ε : ℕ → ℕ → ℝ≥0∞) (nV : ℕ) (hV : ∀ v x π, (A.V v x π).CostBoundAt (wCh C) nV)
    (hE : PlainOnly C E) (h : Gen.HasIndexBindingWith R A E ε) :
    Gen.HasIndexBindingWith R (stateFirstArg C A) (extSt C E)
      (fun tC tP => ε tC tP + collP lam (tC + tP + nV) (tC + tP + nV)) := by
  intro tC tP St Ct Pt hC hP
  have hm := mixClose_rawFirst (mixBind C A E Ct Pt) nV (tC + tP)
    (mixBound_mixBind C A E Ct Pt hC hP hV) (rawFirst_mixBind C A E Ct Pt) (Gen.bindingBad R)
  have e : Pr (ideal C false (mixBind C A E Ct Pt) ⟨[], []⟩) (fun _ => {x | x.1 ∈ Gen.bindingBad R})
      = Pr (Gen.bindingExp A E (downC C Ct) (downP C Pt)) (fun _ => Gen.bindingBad R) := by
    rw [← ideal_mixBind C A E Ct Pt hE, Pr_bind_pure]
    rfl
  rw [real_mixBind, e, Nat.add_comm nV] at hm
  refine hm.trans (add_le_add (h tC tP _ (downC C Ct) (downP C Pt) ?_ fun s => ?_) le_rfl)
  · exact OComp.QueryBound.bind (t := 0) (queryBound_ideal_liftR C Ct _ tC hC) fun _ => trivial
  · exact OComp.QueryBound.bind (t := 0)
      (queryBound_ideal_liftR C (Pt s.1) _ tP (hP s.1)) fun _ => trivial

end Rom
