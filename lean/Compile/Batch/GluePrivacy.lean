-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GluePrivacy.lean: from privacy at the level of challengers, and consistency of the
simulating one, to index privacy in the sense of the definition (ZKCP/Gen.lean), for batches of any
size and any scheme (`[Inhabited IVK]`, `[Inhabited Pf]`). Proof of `Spec.gluePrivacyWith`
(Compile/Batch/SpecGlue.lean) (words of this library: lean/GLOSSARY.md).

  `fold`, `top`            the adversarial verifier and the environment of the definition as one
                           adversary, whose output is the view
  `top_totalBound`, `top_adm`   under the hypotheses of their statements, it is admissible
  `consistent_idealExp`    the clause on consistent answers
  `gluePrivacyWith`        the statement (the measure on the oracle functions disappears by
                           `Rom.Pr_eq_law`)

Notation: `Close`, `GAdm`, `asW`, `simOf`: Compile/Batch/SpecGlue.lean; `HasIndexPrivacyWith`,
`PrivacyFor`: ZKCP/Gen.lean (see `PrivacyFor`'s docstring and their text); `ζ`: an `ℕ → ℕ → ℝ≥0∞`;
in `Close` it stands as `ζ t n`, for at most t queries and n batches (see `Close`'s docstring); `B`:
a natural number; in `ValidBatch R B i b` (ZKCP/Gen.lean): a batch of at most B pairs, all in R_yes
for the index i; `Sm`: a `World S (SCall X) (GIn IVK Pf)` (Rom/World.lean): the challenger of an
experiment, together with the oracles; `Sm.Consistent`: `World.Consistent` (Rom/World.lean: see its
docstring); `Adv.TotalBound t N` (Rom/World.lean): at most t queries in all and at most N calls, on
every path; `tV`, `N`: natural numbers, bound in `PrivacyFor`, where N counts batches.
-/
import Compile.Batch.SpecGlue
import Rom.EagerLazy

noncomputable section

namespace Compile.GlueB

open Rom Prob ZKCP
open scoped ENNReal

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-! ## Small facts -/

theorem runLazy_pure {α : Type} (a : α) (T : Table S) :
    (pure a : OComp S α).runLazy T = PMF.pure (a, T) := rfl

theorem runLazy_query {α : Type} (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) (T : Table S) :
    (OComp.query o q k).runLazy T = (lazyAnswer T o q).bind fun a => (k a.1).runLazy a.2 := by
  unfold lazyAnswer
  simp only [OComp.runLazy]
  cases T o q with
  | none => simp only [PMF.bind_map, Function.comp_def]
  | some r => simp only [PMF.pure_bind]

/-- For as many proofs as slots: what a batch releases is the list of the own instances, each with
its proof. -/
theorem released_eq : ∀ (b : Gen.Batch X Wn) (πs : List Pf), πs.length = b.length →
    b.released πs = b.ownX.zip (ownPf b πs) ∧ (ownPf b πs).length = b.ownX.length
  | [], πs, _ => by simp [Gen.Batch.released, Gen.Batch.ownX, ownPf]
  | s :: b, [], h => by simp at h
  | s :: b, π :: πs, h => by
      obtain ⟨h1, h2⟩ := released_eq b πs (by simpa using h)
      simp only [Gen.Batch.released, Gen.Batch.ownX, ownPf] at h1 h2 ⊢
      cases hs : s.2.2 with
      | true => simp [List.zip_cons_cons, hs, h1, h2]
      | false => simp [List.zip_cons_cons, hs, h1, h2]

theorem fit_val [Inhabited Pf] (xs : List X) (l : List Pf) (h : l.length = xs.length) :
    (fit xs l).val = l := by
  refine List.ext_getElem (by simp [fit, h]) fun n h1 h2 => ?_
  simp [fit, List.getD_eq_getElem?_getD, h2]

theorem released_fit [Inhabited Pf] (b : Gen.Batch X Wn) (πs : Gen.Slots Pf b.pairs) :
    b.ownX.zip (fit b.ownX (ownPf b πs.val)).val = b.released πs.val := by
  obtain ⟨h1, h2⟩ := released_eq b πs.val (by rw [πs.property]; simp [Gen.Batch.pairs])
  rw [fit_val _ _ h2, h1]

/-! ## Verifier and environment as one adversary -/

variable [Inhabited IVK] [Inhabited Pf]

omit [Inhabited IVK] in
/-- The adversarial verifier and the environment, folded into one adversary. It keeps the view, asks
the environment at each request, makes the batch a call, and pairs the proofs that come back with
its own instances. Its output is the view. n is the number of batches still allowed. -/
def fold (Z : Gen.ViewEnv S IVK X Wn Pf) : Gen.AdvVerifier S X Pf → ℕ → Gen.View S IVK X Pf →
    Adv S (GCall X Wn) (GIn IVK Pf) (Gen.View S IVK X Pf)
  | .halt, _, v => .halt v
  | .query o q k, n, v => .query o q fun r => fold Z (k r) n { v with trace := v.trace ++ [⟨o, q, r⟩] }
  | .sample m k, n, v => .sample m fun r => fold Z (k r) n { v with coins := v.coins ++ [r.val] }
  | .request _, 0, v => .halt v
  | .request k, n + 1, v =>
      match Z v with
      | none => .halt v
      | some b => .call (.batch b) fun a =>
          fold Z (k (b.ownX.zip (fit b.ownX (listOf a)).val)) n
            { v with sessions := v.sessions ++ [b.ownX.zip (fit b.ownX (listOf a)).val] }

/-- The whole experiment as one adversary: first "setup", then the loop. -/
def top (Vt : IVK → Gen.AdvVerifier S X Pf) (Z : Gen.ViewEnv S IVK X Wn Pf) (N : ℕ) :
    Adv S (GCall X Wn) (GIn IVK Pf) (Gen.View S IVK X Pf) :=
  .call .setup fun a => fold Z (Vt (ivkOf a)) N ⟨ivkOf a, [], [], []⟩

/-! ## The real experiment -/

omit [Inhabited IVK] in
theorem realLoop_eq (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) (Z : Gen.ViewEnv S IVK X Wn Pf)
    (isk : ISK) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S),
      ((Gen.realLoop A Z isk V n v).runLazy T).map Prod.fst =
        (interact (realW A i) (fold Z V n v) (some isk, T)).map Prod.fst := by
  induction V with
  | halt => intro n v T; simp only [Gen.realLoop, fold, interact, runLazy_pure, PMF.pure_map]
  | query o q k ih =>
    intro n v T
    simp only [Gen.realLoop, fold, interact, runLazy_query, realW, World.ofOComp, PMF.map_bind,
      PMF.bind_map, Function.comp_def]
    refine congrArg _ (funext fun a => ?_)
    exact ih a.1 n _ a.2
  | sample m k ih =>
    intro n v T
    simp only [Gen.realLoop, fold, interact, OComp.runLazy, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n _ T)
  | request k ih =>
    intro n v T
    cases n with
    | zero => simp only [Gen.realLoop, fold, interact, runLazy_pure, PMF.pure_map]
    | succ n =>
      cases hZv : Z v with
      | none => simp only [Gen.realLoop, fold, hZv, interact, runLazy_pure, PMF.pure_map]
      | some b =>
        simp only [Gen.realLoop, fold, hZv, interact, realW, World.ofOComp, OComp.runLazy_bind,
          runLazy_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.bind_map,
          Function.comp_def, listOf, released_fit]
        refine congrArg _ (funext fun a => ?_)
        exact ih _ n _ a.2

/-- The real experiment is the run of the folded adversary against the real challenger. -/
theorem law_realExp (A : Gen.Arg S I X Wn IVK ISK Pf) (i : I) (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X Wn Pf) (N : ℕ) :
    (Gen.realExp A Vt Z i N).law =
      (interact (realW A i) (top Vt Z N) (none, Table.empty _)).map Prod.fst := by
  have e : Gen.realExp A Vt Z i N =
      (A.C i).bind fun o => Gen.realLoop A Z o.2 (Vt o.1) N ⟨o.1, [], [], []⟩ := rfl
  rw [e]
  simp only [OComp.law, top, interact, realW, World.ofOComp, OComp.runLazy_bind, runLazy_pure,
    PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine congrArg _ (funext fun a => ?_)
  exact realLoop_eq A i Z a.1.2 _ N _ a.2

/-! ## The ideal experiment -/

theorem idealLoop_eq (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ)
    (Z : Gen.ViewEnv S IVK X Wn Pf) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (s : Sm.σ), Gen.idealLoop (simOf PP Sm s₀) Z V n v s =
      (interact (asW Wn Sm) (fold Z V n v) s).map Prod.fst := by
  induction V with
  | halt => intro n v s; simp only [Gen.idealLoop, fold, interact, PMF.pure_map]
  | query o q k ih =>
    intro n v s
    simp only [Gen.idealLoop, fold, interact, PMF.map_bind]
    refine congrArg _ (funext fun a => ?_)
    exact ih a.1 n _ a.2
  | sample m k ih =>
    intro n v s
    simp only [Gen.idealLoop, fold, interact, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n _ s)
  | request k ih =>
    intro n v s
    cases n with
    | zero => simp only [Gen.idealLoop, fold, interact, PMF.pure_map]
    | succ n =>
      cases hZv : Z v with
      | none => simp only [Gen.idealLoop, fold, hZv, interact, PMF.pure_map]
      | some b =>
        simp only [Gen.idealLoop, fold, hZv, interact, PMF.map_bind]
        show ((Sm.reply s (.prove b.ownX)).map fun a => (fit b.ownX (listOf a.1), a.2)).bind _ =
          (Sm.reply s (.prove b.ownX)).bind _
        rw [PMF.bind_map]
        refine congrArg _ (funext fun a => ?_)
        exact ih _ n _ a.2

/-- The ideal experiment is the run of the folded adversary against the simulating challenger. -/
theorem idealExp_eq (R : Gen.RelPair I X Wn PP) (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ)
    (i : I) (Vt : IVK → Gen.AdvVerifier S X Pf) (Z : Gen.ViewEnv S IVK X Wn Pf) (N : ℕ) :
    Gen.idealExp R (simOf PP Sm s₀) Vt Z i N =
      (interact (asW Wn Sm) (top Vt Z N) s₀).map Prod.fst := by
  simp only [Gen.idealExp, top, interact, PMF.map_bind]
  show ((Sm.reply s₀ .setup).map fun a => (ivkOf a.1, a.2)).bind _ = (Sm.reply s₀ .setup).bind _
  rw [PMF.bind_map]
  refine congrArg _ (funext fun a => ?_)
  exact idealLoop_eq Sm s₀ Z _ N _ a.2

/-! ## Admissibility of the folded adversary -/

omit [Inhabited IVK] in
theorem fold_totalBound (Z : Gen.ViewEnv S IVK X Wn Pf) (V : Gen.AdvVerifier S X Pf) :
    ∀ (t n : ℕ) (v : Gen.View S IVK X Pf), V.QueryBound t → (fold Z V n v).TotalBound t n := by
  induction V with
  | halt => intro t n v _; trivial
  | query o q k ih =>
    intro t n v h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => ih r t n _ (h r)
  | sample m k ih => intro t n v h r; exact ih r t n _ (h r)
  | request k ih =>
    intro t n v h
    cases n with
    | zero => trivial
    | succ n =>
      cases hZv : Z v with
      | none => simp only [fold, hZv]; trivial
      | some b => simp only [fold, hZv]; exact fun a => ih _ t n _ (h _)

omit [Inhabited IVK] in
theorem fold_adm {ok : Gen.Batch X Wn → Prop} (Z : Gen.ViewEnv S IVK X Wn Pf)
    (hZ : ∀ v b, Z v = some b → ok b) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf), GAdm ok (fold Z V n v) true n := by
  induction V with
  | halt => intro n v; trivial
  | query o q k ih => intro n v r; exact ih r n _
  | sample m k ih => intro n v r; exact ih r n _
  | request k ih =>
    intro n v
    cases n with
    | zero => trivial
    | succ n =>
      cases hZv : Z v with
      | none => simp only [fold, hZv]; trivial
      | some b => simp only [fold, hZv]; exact ⟨rfl, hZ v b hZv, fun a => ih _ n _⟩

theorem top_totalBound (Vt : IVK → Gen.AdvVerifier S X Pf) (Z : Gen.ViewEnv S IVK X Wn Pf)
    (t N : ℕ) (h : ∀ ivk, (Vt ivk).QueryBound t) :
    (top Vt Z N).TotalBound t (N + 1) :=
  fun _ => fold_totalBound Z _ t N _ (h _)

theorem top_adm {ok : Gen.Batch X Wn → Prop} (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X Wn Pf) (hZ : ∀ v b, Z v = some b → ok b) (N : ℕ) :
    GAdm ok (top Vt Z N) false N :=
  ⟨rfl, fun _ => fold_adm Z hZ _ N _⟩

/-! ## The clause on consistent answers (`Gen.TraceConsistent`, ZKCP/Gen.lean) -/

section Consistent
variable {Sm : World S (SCall X) (GIn IVK Pf)} {seen : Sm.σ → Table S}

omit [Inhabited IVK] [Inhabited Pf] in
/-- Every query of the trace is, with its answer, in the table of the answers that the challenger
has given. -/
def Noted (seen : Sm.σ → Table S) (tr : Trace S) (s : Sm.σ) : Prop :=
  ∀ e ∈ tr, seen s e.1 e.2.1 = some e.2.2

omit [Inhabited IVK] [Inhabited Pf] in
theorem Noted.consistent {tr : Trace S} {s : Sm.σ} (h : Noted seen tr s) :
    Gen.TraceConsistent tr := by
  intro o q r r' h1 h2
  exact Option.some.inj ((h _ h1).symm.trans (h _ h2))

theorem consistent_idealLoop
    (hq : ∀ s o q, ∀ x ∈ (Sm.answer s o q).support,
      seen x.2 o q = some x.1 ∧ ∀ o' q' r', seen s o' q' = some r' → seen x.2 o' q' = some r')
    (hr : ∀ s m, ∀ x ∈ (Sm.reply s m).support, ∀ o q r, seen s o q = some r → seen x.2 o q = some r)
    (s₀ : Sm.σ) (Z : Gen.ViewEnv S IVK X Wn Pf) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (s : Sm.σ), Noted seen v.trace s →
      ∀ v' ∈ (Gen.idealLoop (simOf PP Sm s₀) Z V n v s).support, Gen.TraceConsistent v'.trace := by
  induction V with
  | halt =>
    intro n v s h v' hv'
    simp only [Gen.idealLoop, PMF.support_pure, Set.mem_singleton_iff] at hv'
    subst hv'
    exact h.consistent
  | query o q k ih =>
    intro n v s h v' hv'
    simp only [Gen.idealLoop, PMF.mem_support_bind_iff] at hv'
    obtain ⟨a, ha, hv'⟩ := hv'
    refine ih a.1 n _ a.2 ?_ v' hv'
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact (hq s o q a ha).2 _ _ _ (h e he)
    · rw [List.mem_singleton.1 he]
      exact (hq s o q a ha).1
  | sample m k ih =>
    intro n v s h v' hv'
    simp only [Gen.idealLoop, PMF.mem_support_bind_iff] at hv'
    obtain ⟨r, -, hv'⟩ := hv'
    refine ih r n _ s ?_ v' hv'
    exact h
  | request k ih =>
    intro n v s h v' hv'
    cases n with
    | zero =>
      simp only [Gen.idealLoop, PMF.support_pure, Set.mem_singleton_iff] at hv'
      subst hv'
      exact h.consistent
    | succ n =>
      cases hZv : Z v with
      | none =>
        simp only [Gen.idealLoop, hZv, PMF.support_pure, Set.mem_singleton_iff] at hv'
        subst hv'
        exact h.consistent
      | some b =>
        simp only [Gen.idealLoop, hZv, PMF.mem_support_bind_iff] at hv'
        obtain ⟨out, ho, hv'⟩ := hv'
        refine ih _ n _ out.2 ?_ v' hv'
        have ho' : out ∈
            ((Sm.reply s (.prove b.ownX)).map fun a => (fit b.ownX (listOf a.1), a.2)).support := ho
        rw [PMF.mem_support_map_iff] at ho'
        obtain ⟨a, ha, rfl⟩ := ho'
        exact fun e he => hr s _ a ha _ _ _ (h e he)

end Consistent

theorem consistent_idealExp (R : Gen.RelPair I X Wn PP) (Sm : World S (SCall X) (GIn IVK Pf))
    (s₀ : Sm.σ) (hc : Sm.Consistent) (i : I) (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X Wn Pf) (N : ℕ) :
    pr (Gen.idealExp R (simOf PP Sm s₀) Vt Z i N) {v | ¬ Gen.TraceConsistent v.trace} = 0 := by
  obtain ⟨seen, -, hq, hr⟩ := hc
  refine pr_eq_zero_of_forall_not_mem _ fun v' hv' => ?_
  simp only [Gen.idealExp, PMF.mem_support_bind_iff] at hv'
  obtain ⟨out, -, hv'⟩ := hv'
  have h :=
    consistent_idealLoop (seen := seen) hq hr s₀ Z _ N _ out.2 (fun e he => by simp at he) v' hv'
  exact fun hn => hn h

/-! ## The statement, in two forms -/

/-- From challengers to the definition, for batches of at most B slots, simulator named.
(not all hypotheses are named here: see the statement below)
(among its binders: `hc : Sm.Consistent`, `close : Close R A B (asW Wn Sm) s₀ ζ`; its conclusion:
`Gen.HasIndexPrivacyWith R A B (simOf PP Sm s₀) ζ`) -/
theorem privacyWith_of_world (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
    (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ) (ζ : ℕ → ℕ → ℝ≥0∞) (hc : Sm.Consistent)
    (close : Close R A B (asW Wn Sm) s₀ ζ) :
    Gen.HasIndexPrivacyWith R A B (simOf PP Sm s₀) ζ := by
  intro i Z hZ tV Vt N hV
  refine ⟨?_, consistent_idealExp R Sm s₀ hc i Vt Z N⟩
  have e1 : (fun T => Rom.Pr (Gen.realExp A Vt Z i N) fun _ => T) =
      pr (Gen.realExp A Vt Z i N).law :=
    funext fun T => Rom.Pr_eq_law _ T
  rw [e1, law_realExp A i Vt Z N, idealExp_eq R Sm s₀ i Vt Z N]
  exact close i _ (top Vt Z N) tV N (top_totalBound Vt Z tV N hV) (top_adm Vt Z hZ N)


end Compile.GlueB

namespace Compile.GlueB

open Rom Prob ZKCP

theorem gluePrivacyWith : Spec.gluePrivacyWith := fun _ _ _ _ _ _ _ _ _ _ R A B Sm s₀ ζ hc close =>
  privacyWith_of_world R A B Sm s₀ ζ hc close

end Compile.GlueB
