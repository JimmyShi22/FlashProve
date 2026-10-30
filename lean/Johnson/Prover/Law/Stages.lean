-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Stages.lean: FROM ONE STAGE OF A LONG PROGRAM TO THE NEXT, UNDER LAZILY SAMPLED
ORACLES: what the table that a stage returns still grants the stages behind it. For whoever joins
the committer, the seeds' queries and the three files' compiled provers into one program.

Main names.
  det_of_lazy   A PROGRAM WITHOUT COINS: the value of its lazy run is its value under EVERY oracle
    functions that complete the returned table, or any table that holds that table's entries.
    General in the family of oracles.
  PrFrom_bind_le_add   THE STAGE LEMMA: the first stage is bad with probability Pr[Bad]; after a
    good first stage, from the table that it returns, the event has probability at most ε: then
    the event has probability at most Pr[Bad] + ε. Prob.pr_bind_le_add (Prob/Count.lean) lifted to
    Rom.PrFrom. General in the family of oracles.
  PrFrom_le_of_det   two programs without coins, compared pointwise in the oracle functions: if
    c's value in E forces c''s value in E' under every g, then Pr[c in E] is at most Pr[c' in E'].
  PrFrom_union_le   the union bound. PrFrom_ask_new   a new query has a uniform answer.
  avoids_searchO, avoids_fsO, avoids_onFs, avoids_chainO, avoids_proveX   A CHAIN AT ANOTHER TAG
    never asks fb t: the prover's twin of chainB_tag (Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean).
  fresh_after_avoids   FreshFrom is kept by every program that never asks fb t.
  fresh_after_asksIn   FreshFrom is kept by every program none of whose queries is one of
    FreshFrom's places.

It adds no strength. Calls: Rom.Derive.runLazy_sub, Avoids.bind (Rom/Derive.lean); fb_kept,
fresh_of_kept (Johnson/Prover/Law/Asks.lean); none_of_asksIn (Johnson/Prover/Law/Keeps.lean).

Limits. det_of_lazy and the two laws on FreshFrom speak of the support of a run's law alone. Nothing
on a program with coins: fix the coins first. No program of several stages is defined here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Asks
import Johnson.Prover.Law.Search
import Rom.Cache

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Rom.Derive (Avoids.bind runLazy_sub Sub)
open scoped ENNReal

/-! ## General in the family of oracles -/

section
variable {S : OSpec} {α β : Type}

/-- **A program without coins: the value of its lazy run is its value under every completion of the
returned table**, and of every table that holds the returned table's entries. -/
theorem det_of_lazy (c : OComp S α) : c.NoCoin → ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support,
    ∀ T' : Table S, Sub x.2 T' → ∀ f : Fam S, c.det (T'.over f) = x.1 := by
  induction c with
  | pure a =>
    intro _ T x hx T' _ f
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    rfl
  | query o q k ih =>
    intro hc T x hx T' hs f
    cases hT : T o q with
    | some r =>
      simp only [OComp.runLazy, hT] at hx
      have h1 : T' o q = some r := hs o q r (runLazy_sub (k r) T x hx o q r hT)
      show (k (T'.over f o q)).det (T'.over f) = x.1
      rw [Table.over_of_some h1]
      exact ih r (hc r) T x hx T' hs f
    | none =>
      simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      have h1 : T' o q = some r :=
        hs o q r (runLazy_sub (k r) _ x hx o q r (Table.set_self T o q r))
      show (k (T'.over f o q)).det (T'.over f) = x.1
      rw [Table.over_of_some h1]
      exact ih r (hc r) _ x hx T' hs f
  | sample n k _ => exact fun hc => hc.elim

/-- **The stage lemma.** -/
theorem PrFrom_bind_le_add (T : Table S) (c : OComp S α) (g : α → OComp S β) (E : Set β)
    (Bad : Set α) {ε : ℝ≥0∞}
    (h : ∀ out ∈ (c.runLazy T).support, out.1 ∉ Bad → PrFrom out.2 (g out.1) E ≤ ε) :
    PrFrom T (c.bind g) E ≤ PrFrom T c Bad + ε := by
  rw [PrFrom_bind, PrFrom_eq_lazy T c Bad, pr_map]
  exact expect_le_pr_add (c.runLazy T) _ (Prod.fst ⁻¹' Bad) (fun out => PrFrom_le_one _ _ _)
    fun out ho hb => h out ho hb

/-- **Two programs without coins, compared pointwise in the oracle functions.** -/
theorem PrFrom_le_of_det {c : OComp S α} {c' : OComp S β} (hc : c.NoCoin) (hc' : c'.NoCoin)
    (T : Table S) {E : Set α} {E' : Set β} (h : ∀ g, c.det g ∈ E → c'.det g ∈ E') :
    PrFrom T c E ≤ PrFrom T c' E' := by
  classical
  unfold PrFrom PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  show pr (c.runEager (T.over f)) E ≤ pr (c'.runEager (T.over f)) E'
  rw [hc.runEager, hc'.runEager, pr_pure, pr_pure]
  by_cases h1 : c.det (T.over f) ∈ E
  · rw [if_pos h1, if_pos (h _ h1)]
  · rw [if_neg h1]
    exact zero_le _

/-- The union bound. -/
theorem PrFrom_union_le (T : Table S) (c : OComp S α) (E F : Set α) :
    PrFrom T c (E ∪ F) ≤ PrFrom T c E + PrFrom T c F := by
  rw [PrFrom_eq_lazy, PrFrom_eq_lazy, PrFrom_eq_lazy]
  exact pr_union_le _ _ _

end

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A query that is new in the table has a uniform answer. -/
theorem PrFrom_ask_new (t : Tag) (x : FbIn lam L t) (T : Table (typedOracleFamily lam K L))
    (hnew : T (OracleName.fb t) x = none) (E : Set (FsAns lam K)) :
    PrFrom T (askTypedOracle (L := L) (K := K) (OracleName.fb t) x) E = pr (unif (FsAns lam K)) E := by
  have h : (askTypedOracle (L := L) (K := K) (OracleName.fb t) x).runLazy T =
      (unif (FsAns lam K)).bind fun ans => PMF.pure (ans, T.set (OracleName.fb t) x ans) := by
    show OComp.runLazy (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) x OComp.pure) T = _
    simp only [OComp.runLazy]
    rw [hnew]
    rfl
  have e : (fun ans : FsAns lam K =>
      (PMF.pure (ans, T.set (OracleName.fb t) x ans)).map Prod.fst) = PMF.pure := by
    funext ans
    rw [PMF.pure_map]
  have h2 : ((askTypedOracle (L := L) (K := K) (OracleName.fb t) x).runLazy T).map Prod.fst =
      unif (FsAns lam K) := by
    rw [h]
    exact (PMF.map_bind _ _ _).trans ((congrArg (PMF.bind _) e).trans (PMF.bind_pure _))
  rw [PrFrom_eq_lazy, h2]
  rfl

/-! ## A chain at another tag -/

theorem avoids_searchO {t : Tag} {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (hask : ∀ β, (ask β).Avoids (OracleName.fb t)) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal ask α fuel n).Avoids (OracleName.fb t)
  | 0, _ => trivial
  | fuel + 1, n =>
    Avoids.bind (hask _) fun a => by
      by_cases hk : gr.ok (chal a.1) = true
      · rw [if_pos hk]
        trivial
      · rw [if_neg hk]
        exact avoids_searchO gr chal ask hask α fuel (n + 1)

theorem avoids_fsO {t : Tag} {C P : Type} (gr : Option (GrW C P)) (cap : ℕ)
    (chal : (Fin K → Dig lam) → C) (ask : P → TypedOracleComputation lam K L (FsAns lam K))
    (hask : ∀ β, (ask β).Avoids (OracleName.fb t)) (α : P) : (fsO gr cap chal ask α).Avoids (OracleName.fb t) := by
  cases gr with
  | none => exact Avoids.bind (hask _) fun _ => trivial
  | some q => exact avoids_searchO q chal ask hask α _ _

theorem avoids_onFs {t : Tag} {P β : Type} (i : ℕ) (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β))
    (hk : ∀ p, (k p).Avoids (OracleName.fb t)) : ∀ o, (onFs i k o).Avoids (OracleName.fb t)
  | none => trivial
  | some p => hk p

/-- **A chain at the tag t' never asks fb t, if t' is not t.** -/
theorem avoids_chainO {t t' : Tag} (ht : t' ≠ t) (cms : List (Dig lam)) (x : Option X)
    (co : Coins lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t') (annOf L t')) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t' cms x co cap s A W embS embP i ph σ).Avoids (OracleName.fb t)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    have hfb : OracleName.fb t' ≠ OracleName.fb t := fun h => ht (OracleName.fb.inj h)
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact Avoids.bind (avoids_treesO t _ _ _ _ _ _ _) fun _ =>
            Avoids.bind (avoids_fsO _ _ _ _ (fun _ => avoids_askV t _ _ hfb) _)
              (avoids_onFs _ _ fun _ =>
                Avoids.bind (avoids_chainO ht cms x co cap s A W _ _ _ _ _) fun _ => trivial)
        | false =>
          exact Avoids.bind (avoids_treesO t _ _ _ _ _ _ _) fun _ =>
            Avoids.bind (avoids_fsO _ _ _ _ (fun _ => avoids_askV t _ _ hfb) _)
              (avoids_onFs _ _ fun _ =>
                Avoids.bind (avoids_chainO ht cms x co cap s A W _ _ _ _ _) fun _ => trivial)
      | join ρ =>
        exact Avoids.bind (avoids_treesO t _ _ _ _ _ _ _) fun _ =>
          Avoids.bind (avoids_treesO t _ _ _ _ _ _ _) fun _ =>
          Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun _ =>
          Avoids.bind (avoids_askV t _ _ (by intro h; cases h)) fun _ =>
          Avoids.bind (avoids_climbO t _ _ _) fun _ =>
            Avoids.bind (avoids_fsO _ _ _ _ (fun _ => avoids_askV t _ _ hfb) _)
              (avoids_onFs _ _ fun _ =>
                Avoids.bind (avoids_chainO ht cms x co cap s A W _ _ _ _ _) fun _ => trivial)

/-- **The compiled prover of a file at the tag t' never asks fb t, if t' is not t.** -/
theorem avoids_proveX {t t' : Tag} (ht : t' ≠ t) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t') (annOf L t')) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) :
    (proveX t' Q wq embS embP xin cms x y xt σ co cap).Avoids (OracleName.fb t) :=
  Avoids.bind (avoids_chainO ht cms (xin x) co cap _ _ _ _ _ _ _ _) fun _ => trivial

/-! ## FreshFrom behind a stage -/

section
variable {α : Type} {t : Tag} {s : Shape} {A : RoundSplits s}
  {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {T : Table (typedOracleFamily lam K L)}

/-- **FreshFrom is kept by every program that never asks fb t.** -/
theorem fresh_after_avoids {c : TypedOracleComputation lam K L α} (h : c.Avoids (OracleName.fb t))
    (hT : FreshFrom t s A embP i T) : ∀ x ∈ (c.runLazy T).support, FreshFrom t s A embP i x.2 :=
  fun _ hx => fresh_of_kept hT fun q => fb_kept h hx q

/-- **FreshFrom is kept by every program none of whose queries is one of FreshFrom's places.** -/
theorem fresh_after_asksIn {P : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf lam L o → Prop}
    {c : TypedOracleComputation lam K L α} (h : c.AsksIn P)
    (off : ∀ q : FbIn lam L t, (∃ z, q.plain = embP z ∧ q.round = i + PlainPart.depth s A z) →
      ¬ P (OracleName.fb t) q)
    (hT : FreshFrom t s A embP i T) : ∀ x ∈ (c.runLazy T).support, FreshFrom t s A embP i x.2 :=
  fun _ hx q hq => Law.none_of_asksIn h hx (off q hq) (hT q hq)

end

end OnBytes.Prover

#print axioms OnBytes.Prover.det_of_lazy
#print axioms OnBytes.Prover.PrFrom_bind_le_add
#print axioms OnBytes.Prover.PrFrom_le_of_det
#print axioms OnBytes.Prover.PrFrom_union_le
#print axioms OnBytes.Prover.PrFrom_ask_new
#print axioms OnBytes.Prover.avoids_chainO
#print axioms OnBytes.Prover.avoids_proveX
#print axioms OnBytes.Prover.fresh_after_avoids
#print axioms OnBytes.Prover.fresh_after_asksIn
