-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/DeriveWith.lean: the committer's coins derived from one seed, for every prover that replays the
key (`Replays`).

Rom/SpecDerive.lean derives all coins of the committer C from one seed, through an auxiliary oracle
that the scheme A avoids (`ArgAvoids`), and keeps (i, seed) in place of isk; its prover repeats the
whole of C. The proofs of Sections 5 and 6 of Rom/Derive.lean use that prover through one property
only (`Replays`, below): after C's derived run, on every table that contains what that run returns,
it behaves as the prover P of the scheme with the key that C has returned. Here the theorem is
stated for every prover with this property (`deriveWith`); if A avoids the auxiliary oracle (hA),
the prover of Rom/SpecDerive.lean has it (`replays_derived`).

In the term t / (number of seeds), t bounds the adversary's queries to all oracles, not only its
queries to the auxiliary oracle: the bound is valid, and looser than with the smaller count.

Sections 1 to 4 of Rom/Derive.lean, and its lemmas on traces and seeds, are used as they are. The
proofs are those of Sections 5 and 6 of Rom/Derive.lean, with the second run of C replaced by the
property; the theorem for the scheme of Rom/SpecDerive.lean is not in this library. (No declaration
states it; it follows from `deriveWith` with `replays_derived`, by `derivedWith_derived`.)

Notation:
  `α`; `ε`, `ζ`: `ℝ≥0∞`; `ℕ → ℕ → ℝ≥0∞`: the last arguments of `Gen.HasCompletenessError R A B α`,
    `Gen.HasIndexBindingWith R A E ε`, `Gen.HasIndexPrivacyWith R A B Sim ζ` (ZKCP/Gen.lean), the
    three fields of `Gen.IsZKCPArgWith R A B E Sim α ε ζ`
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `E`: `Gen.Extractor S I X W IVK Pf`; `Sim`: `Gen.Simulator S PP IVK X Pf` (ZKCP/Gen.lean)
  `ε`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.HasIndexBindingWith R A E ε` (ZKCP/Gen.lean) it stands as `ε tC tP`,
    with `Ct.QueryBound tC` and `∀ st, (Pt st).QueryBound tP`; `Ct : OComp S (IVK × St)`,
    `Pt : St → OComp S (X × Pf)`
  `ζ`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.PrivacyFor R A Sim ζ i Z` (ZKCP/Gen.lean) it stands as `ζ tV N`, with
    `∀ ivk, (Vt ivk).QueryBound tV`; N counts batches
  `σ`: `SeedOracle S` (Rom/SpecDerive.lean): an auxiliary oracle, used as a source of coins;
    `σ.bias n`: the distance of a derived sample from a uniform one; `c.pathBias σ`: the supremum,
    over the paths of the algorithm, of the sum along the path of the distances of the derived
    samples from uniform ones
-/
import Rom.Derive

open scoped ENNReal
open Prob

namespace Rom

open ZKCP

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- The prover P' replays the key. (A table with derived coins is glue s T R: a table T, overlaid at
the queries of the seed s by the record R of the derived answers.) After a derived run of C i under
the seed s, which has returned the table x.2.1, the record x.2.2 and the key x.1: on glue s T x.2.2,
for every table T that contains x.2.1 and with the record held fixed, P' (i, s) behaves as P with
that key: the two runs have the same law, the table that they return included. (An entry of T at a
query of the seed is hidden by the record.) -/
def Replays (A : Gen.Arg S I X W IVK ISK Pf) (σ : SeedOracle S)
    (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b)) : Prop :=
  ∀ i s, ∀ x ∈ (Derive.runRec σ (A.C i) 0 (Table.empty S) fun _ => none).support, ∀ T,
    Derive.Sub x.2.1 T →
    ∀ b, (P' (i, s) b).runLazy (Derive.glue σ s T x.2.2) =
      (A.P x.1.2 b).runLazy (Derive.glue σ s T x.2.2)

/-- The derived scheme with the prover P'. -/
def derivedWith (A : Gen.Arg S I X W IVK ISK Pf) (σ : SeedOracle S)
    (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b)) :
    Gen.Arg S I X W IVK (I × Fin (σ.sd + 1)) Pf where
  C := (derived A σ).C
  P := P'
  V := A.V

namespace Derive

variable (A : Gen.Arg S I X W IVK ISK Pf)
  {σ : SeedOracle S} {P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b)}

/-- Under hA, the prover that repeats the whole of C replays the key. -/
theorem replays_derived (hA : ArgAvoids A σ.o) : Replays A σ (derived A σ).P := by
  intro i s x hx T hT b
  show (((A.C i).derive σ s 0).bind fun out => A.P out.2 b).runLazy (glue σ s T x.2.2) = _
  rw [OComp.runLazy_bind, runLazy_derive σ s _ (hA.C i),
    runRec_again σ (A.C i) 0 _ _ x hx T x.2.2 hT (SubR.refl _), PMF.pure_map, PMF.pure_bind]

theorem verifyAll_derivedWith (σ : SeedOracle S)
    (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b)) (ivk : IVK) :
    ∀ l : List (X × Pf), Gen.verifyAll (derivedWith A σ P') ivk l = Gen.verifyAll A ivk l
  | [] => rfl
  | (x, π) :: rest => by
      simp only [Gen.verifyAll, verifyAll_derivedWith σ P' ivk rest]
      rfl

/-! ## Completeness -/

/-- Under hA, hr: one honest batch of the derived scheme on `glue s T R` has the output distribution
of A's honest batch on T. -/
theorem session_with {s : Fin (σ.sd + 1)} {i : I} {T : Table S} {R : Rec σ} {isk : ISK}
    (hA : ArgAvoids A σ.o) (ivk : IVK) (bt : List (X × W))
    (hr : (P' (i, s) bt).runLazy (glue σ s T R) = (A.P isk bt).runLazy (glue σ s T R)) :
    ((Gen.sessionExp (derivedWith A σ P') ivk (i, s) bt).runLazy (glue σ s T R)).map Prod.fst =
      ((Gen.sessionExp A ivk isk bt).runLazy T).map Prod.fst := by
  have e : (Gen.sessionExp (derivedWith A σ P') ivk (i, s) bt).runLazy (glue σ s T R) =
      (Gen.sessionExp A ivk isk bt).runLazy (glue σ s T R) := by
    show ((P' (i, s) bt).bind fun πs : Gen.Slots Pf bt =>
        Gen.verifyAll (derivedWith A σ P') ivk ((bt.map Prod.fst).zip πs.val)).runLazy _ =
      ((A.P isk bt).bind fun πs : Gen.Slots Pf bt =>
        Gen.verifyAll A ivk ((bt.map Prod.fst).zip πs.val)).runLazy _
    simp only [verifyAll_derivedWith]
    rw [OComp.runLazy_bind, OComp.runLazy_bind, hr]
  rw [e, runLazy_glue σ s _ (avoids_sessionExp A hA ivk isk bt), PMF.map_comp]
  rfl

theorem completenessExp_with (σ : SeedOracle S)
    (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b))
    (i : I) (bt : List (X × W)) :
    Gen.completenessExp (derivedWith A σ P') i bt = OComp.sample σ.sd fun s =>
      ((A.C i).derive σ s 0).bind fun a => Gen.sessionExp (derivedWith A σ P') a.1 (i, s) bt := by
  show OComp.sample σ.sd (fun s =>
      (((A.C i).derive σ s 0).bind fun out => OComp.pure (out.1, (i, s))).bind fun x =>
        Gen.sessionExp (derivedWith A σ P') x.1 x.2 bt) = _
  refine congrArg _ (funext fun s => ?_)
  rw [OComp.bind_assoc]
  rfl

/-- the first derived run, as a run on a table and a record -/
theorem runLazy_derive_empty (hA : ArgAvoids A σ.o) (i : I) (s : Fin (σ.sd + 1)) :
    ((A.C i).derive σ s 0).runLazy (Table.empty S) =
      (runRec σ (A.C i) 0 (Table.empty S) (fun _ => none)).map fun x =>
        (x.1, glue σ s x.2.1 x.2.2) := by
  have h := runLazy_derive σ s (A.C i) (hA.C i) 0 (Table.empty S) (fun _ => none)
  rwa [glue_empty] at h

/-- Completeness, under hA, hP: the derived experiment is within the bias of the committer's coins
of the experiment of A. (In law it is the experiment with biased coins of the committer.) -/
theorem tv_completeness_with
    (hA : ArgAvoids A σ.o) (hP : Replays A σ P') (i : I) (bt : List (X × W)) :
    tv (Gen.completenessExp (derivedWith A σ P') i bt).law (Gen.completenessExp A i bt).law ≤
      (A.C i).pathBias σ := by
  have h1 : (Gen.completenessExp (derivedWith A σ P') i bt).law =
      (runB σ (A.C i) (Table.empty S)).bind fun y =>
        ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst := by
    rw [completenessExp_with, OComp.law]
    simp only [OComp.runLazy, PMF.map_bind]
    refine (congrArg _ (funext fun s => ?_)).trans (PMF.bind_const _ _)
    rw [map_fst_runLazy_bind, runLazy_derive_empty A hA, PMF.bind_map,
      ← map_runRec σ (A.C i) 0 (Table.empty S) (fun _ => none) (fun _ _ => rfl), PMF.bind_map]
    refine bind_congr_support fun x hx => ?_
    exact session_with A hA x.1.1 bt (hP i s x hx x.2.1 (Sub.refl _) bt)
  have h2 : (Gen.completenessExp A i bt).law =
      ((A.C i).runLazy (Table.empty S)).bind fun y =>
        ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst :=
    map_fst_runLazy_bind (A.C i) (fun x => Gen.sessionExp A x.1 x.2 bt) _
  rw [h1, h2]
  exact (tv_bind_left_le _ _ _).trans (tv_runB_le σ (A.C i) _)

/-! ## Privacy -/

/-- Identical until bad, under hA. Fix the seed s, the key, and a table T₀ and a record R such that
on glue s T R, for every T that extends T₀, the prover P' behaves as P with the key. Then, under the
hypotheses below, the derived loop on glue s T R and the loop of A on T give the same probability to
every view without a query of s. -/
theorem loop_eqOff_with (hA : ArgAvoids A σ.o) (Z : Gen.ViewEnv S IVK X W Pf) (i : I)
    (s : Fin (σ.sd + 1)) (key : IVK × ISK) (T₀ : Table S) (R : Rec σ)
    (hrep : ∀ T₃, Sub T₀ T₃ →
      ∀ b, (P' (i, s) b).runLazy (glue σ s T₃ R) = (A.P key.2 b).runLazy (glue σ s T₃ R))
    (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S), Sub T₀ T →
      EqOff (Bad σ s)
        (((Gen.realLoop (derivedWith A σ P') Z (i, s) V n v).runLazy (glue σ s T R)).map Prod.fst)
        (((Gen.realLoop A Z key.2 V n v).runLazy T).map Prod.fst) := by
  induction V with
  | halt =>
    intro n v T _
    simp only [Gen.realLoop]
    show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
    rw [PMF.pure_map, PMF.pure_map]
    exact EqOff.refl _ _
  | query o q k ih =>
    intro n v T hT
    have hgood : glue σ s T R o q = T o q →
        (∀ r, (glue σ s T R).set o q r = glue σ s (T.set o q r) R) →
        EqOff (Bad σ s)
          (((Gen.realLoop (derivedWith A σ P') Z (i, s) (.query o q k) n v).runLazy
            (glue σ s T R)).map Prod.fst)
          (((Gen.realLoop A Z key.2 (.query o q k) n v).runLazy T).map Prod.fst) := by
      intro hg hset
      cases hq : T o q with
      | some r =>
        simp only [Gen.realLoop, OComp.runLazy, hg, hq]
        exact ih r n _ T hT
      | none =>
        simp only [Gen.realLoop, OComp.runLazy, hg, hq, PMF.map_bind]
        refine EqOff.bind _ fun r _ => ?_
        rw [hset r]
        exact ih r n _ _ (hT.trans (sub_set hq r))
    by_cases ho : o = σ.o
    · subst ho
      by_cases hp : IsPt σ s q
      · exact EqOff.of_support (bad_of_query _ Z _ hp k n v _) (bad_of_query _ Z _ hp k n v _)
      · exact hgood (glue_not_pt hp) fun r => glue_set_not_pt hp r
    · exact hgood (congrFun (glue_of_ne ho) q) fun r => glue_set_of_ne ho q r
  | sample m k ih =>
    intro n v T hT
    simp only [Gen.realLoop, OComp.runLazy, PMF.map_bind]
    exact EqOff.bind _ fun r _ => ih r n _ T hT
  | request k ih =>
    intro n v T hT
    cases n with
    | zero =>
      show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
      rw [PMF.pure_map, PMF.pure_map]
      exact EqOff.refl _ _
    | succ n =>
      simp only [Gen.realLoop]
      cases hZ : Z v with
      | none =>
        show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
        rw [PMF.pure_map, PMF.pure_map]
        exact EqOff.refl _ _
      | some b =>
        show EqOff _
          ((((P' (i, s) b.pairs).bind fun πs =>
              Gen.realLoop (derivedWith A σ P') Z (i, s) (k (b.released πs.val)) n
                { v with sessions := v.sessions ++ [b.released πs.val] }).runLazy
            (glue σ s T R)).map Prod.fst)
          ((((A.P key.2 b.pairs).bind fun πs =>
              Gen.realLoop A Z key.2 (k (b.released πs.val)) n
                { v with sessions := v.sessions ++ [b.released πs.val] }).runLazy T).map Prod.fst)
        rw [map_fst_runLazy_bind, hrep T hT, map_fst_runLazy_bind,
          runLazy_glue σ s _ (hA.P _ _), PMF.bind_map]
        exact EqOff.bind _ fun y hy => ih _ n _ _ (hT.trans (runLazy_sub _ T y hy))

theorem realExp_with (σ : SeedOracle S)
    (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b))
    (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X W Pf) (i : I) (N : ℕ) :
    Gen.realExp (derivedWith A σ P') Vt Z i N = OComp.sample σ.sd fun s => ((A.C i).derive σ s 0).bind fun a =>
      Gen.realLoop (derivedWith A σ P') Z (i, s) (Vt a.1) N ⟨a.1, [], [], []⟩ := by
  show OComp.sample σ.sd (fun s =>
      (((A.C i).derive σ s 0).bind fun out => OComp.pure (out.1, (i, s))).bind fun x =>
        Gen.realLoop (derivedWith A σ P') Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) = _
  refine congrArg _ (funext fun s => ?_)
  rw [OComp.bind_assoc]
  rfl

/-- The real experiment of index privacy, under hA, hP, hV: the derived committer and the prover P'
change the law of the adversary's view by at most t / (number of seeds), and the bias. -/
theorem tv_real_le_with (hA : ArgAvoids A σ.o) (hP : Replays A σ P')
    (Vt : IVK → Gen.AdvVerifier S X Pf) (Z : Gen.ViewEnv S IVK X W Pf) (i : I)
    (N t : ℕ) (hV : ∀ ivk, (Vt ivk).QueryBound t) :
    tv (Gen.realExp (derivedWith A σ P') Vt Z i N).law (Gen.realExp A Vt Z i N).law ≤
      (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) + (A.C i).pathBias σ := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : (IVK × ISK) × Table S → PMF (Gen.View S IVK X Pf), K = fun y =>
    ((Gen.realLoop A Z y.1.2 (Vt y.1.1) N ⟨y.1.1, [], [], []⟩).runLazy y.2).map Prod.fst := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (runB σ (A.C i) (Table.empty S)).bind K := ⟨_, rfl⟩
  have hreal : (Gen.realExp A Vt Z i N).law = ((A.C i).runLazy (Table.empty S)).bind K := by
    rw [hK]
    exact map_fst_runLazy_bind
      (A.C i) (fun x => Gen.realLoop A Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) _
  have hQreal : tv Q (Gen.realExp A Vt Z i N).law ≤ (A.C i).pathBias σ := by
    rw [hQ, hreal]
    exact (tv_bind_left_le _ _ _).trans (tv_runB_le σ (A.C i) _)
  have hQ' : Q =
      (runRec σ (A.C i) 0 (Table.empty S) (fun _ => none)).bind fun x => K (x.1, x.2.1) := by
    rw [hQ, ← map_runRec σ (A.C i) 0 (Table.empty S) (fun _ => none) (fun _ _ => rfl), PMF.bind_map]
    rfl
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Fin (σ.sd + 1) → PMF (Gen.View S IVK X Pf), Ps = fun s =>
    ((((A.C i).derive σ s 0).bind fun a =>
            Gen.realLoop (derivedWith A σ P') Z (i, s) (Vt a.1) N ⟨a.1, [], [], []⟩).runLazy
          (Table.empty S)).map Prod.fst := ⟨_, rfl⟩
  have hlaw : (Gen.realExp (derivedWith A σ P') Vt Z i N).law =
      (unif (Fin (σ.sd + 1))).bind Ps := by
    rw [realExp_with, OComp.law, hPs]
    simp only [OComp.runLazy, PMF.map_bind]
  have hoff : ∀ s, EqOff (Bad σ s) (Ps s) Q := by
    intro s
    rw [hPs, hQ', hK]
    show EqOff _ ((OComp.runLazy (OComp.bind _ _) _).map Prod.fst) _
    rw [map_fst_runLazy_bind, runLazy_derive_empty A hA, PMF.bind_map]
    refine EqOff.bind _ fun x hx => ?_
    exact loop_eqOff_with A hA Z i s x.1 x.2.1 x.2.2 (fun T₃ hT₃ b => hP i s x hx T₃ hT₃ b)
      (Vt x.1.1) N _ x.2.1 (Sub.refl _)
  have htv : ∀ s, tv (Ps s) Q ≤ pr Q (Bad σ s) := fun s => by
    rw [tv_comm]
    exact tv_le_pr_of_eq_off Q (Ps s) (Bad σ s) fun u hu => (hoff s u hu).symm
  have hlen : ∀ u ∈ Q.support, u.trace.length ≤ t := by
    intro u hu
    rw [hQ, hK] at hu
    obtain ⟨y, -, hu⟩ := (PMF.mem_support_bind_iff _ _ _).1 hu
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hu
    have h := realLoop_length A Z y.1.2 (Vt y.1.1) t N _ y.2 (hV _) x hx
    simpa using h
  have hsum : ∑ s, pr Q (Bad σ s) ≤ (t : ℝ≥0∞) := by
    simp only [pr_eq_expect]
    rw [← expect_finset_sum]
    refine expect_le_of_forall_le Q fun u hu => ?_
    rw [Finset.sum_boole]
    refine Nat.cast_le.2 (le_trans ?_ (hlen u hu))
    convert card_seeds_le σ u.trace
  have h1 : tv (Gen.realExp (derivedWith A σ P') Vt Z i N).law Q ≤ (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) := by
    have hc : Q = (unif (Fin (σ.sd + 1))).bind fun _ => Q := (PMF.bind_const _ _).symm
    rw [hlaw]
    conv_lhs => rw [hc]
    refine (tv_unif_bind_le Ps fun _ => Q).trans ?_
    rw [Fintype.card_fin]
    exact ENNReal.div_le_div_right ((Finset.sum_le_sum fun s _ => htv s).trans hsum) _
  exact (tv_triangle _ Q _).trans (add_le_add h1 hQreal)

end Derive

/-! ## The theorem -/

/-- For one seed, counters as labels (the j-th coin is read at the query `σ.pt s j`:
Rom/SpecDerive.lean) and the coins of the committer, under hA, hb (b bounds the path bias of every
C i) and hP (P' replays the key): if A has `IsZKCPArgWith`, so has the derived scheme,
with the same extractor and simulator; the completeness error grows by b, index binding is
unchanged, the privacy error grows by t / (number of seeds) + b. -/
theorem deriveWith {R : Gen.RelPair I X W PP} {A : Gen.Arg S I X W IVK ISK Pf} {σ : SeedOracle S}
    {P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b)} {B : ℕ}
    {E : Gen.Extractor S I X W IVK Pf} {Sim : Gen.Simulator S PP IVK X Pf} {α b : ℝ≥0∞}
    {ε ζ : ℕ → ℕ → ℝ≥0∞} (hA : ArgAvoids A σ.o) (hb : ∀ i, (A.C i).pathBias σ ≤ b)
    (hP : Replays A σ P') (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R (derivedWith A σ P') B E Sim (α + b) ε
      (fun t N => ζ t N + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) + b) := by
  refine ⟨?_, fun tC tP St Ct Pt h1 h2 => h.indexBinding tC tP St Ct Pt h1 h2, ?_⟩
  · intro i bt hv
    have h0 := h.completeness i bt hv
    rw [Pr_eq_law] at h0 ⊢
    exact ((tv_le_iff.1 ((Derive.tv_completeness_with A hA hP i bt).trans (hb i))
        {c | c = false}).1).trans
      (add_le_add h0 le_rfl)
  · intro i Z hZ tV Vt N hV
    obtain ⟨h1, h2⟩ := h.indexPrivacy i Z hZ tV Vt N hV
    refine ⟨?_, h2⟩
    have e1 : (fun T => Rom.Pr (Gen.realExp (derivedWith A σ P') Vt Z i N) (fun _ => T)) =
        pr (Gen.realExp (derivedWith A σ P') Vt Z i N).law :=
      funext fun T => Pr_eq_law _ T
    have e2 : (fun T => Rom.Pr (Gen.realExp A Vt Z i N) (fun _ => T)) =
        pr (Gen.realExp A Vt Z i N).law :=
      funext fun T => Pr_eq_law _ T
    rw [e2] at h1
    rw [e1]
    refine (sd_triangle _ (pr (Gen.realExp A Vt Z i N).law) _).trans ?_
    have h3 : sd (pr (Gen.realExp (derivedWith A σ P') Vt Z i N).law)
          (pr (Gen.realExp A Vt Z i N).law) ≤
        (tV : ℝ≥0∞) / (σ.sd + 1 : ℕ) + b :=
      (Derive.tv_real_le_with A hA hP Vt Z i N tV hV).trans (add_le_add le_rfl (hb i))
    refine (add_le_add h3 h1).trans (le_of_eq ?_)
    ring

/-- with the prover that repeats the whole of C, the scheme is that of Rom/SpecDerive.lean -/
theorem derivedWith_derived (A : Gen.Arg S I X W IVK ISK Pf) (σ : SeedOracle S) :
    derivedWith A σ (derived A σ).P = derived A σ := rfl

end Rom
