-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Blocks.lean: a uniform sample with many outcomes made from several small samples
(`OComp.blocks`); and a scheme whose committer is replaced by a close one (`replaceC`).

In Rom/SpecDerive.lean one answer of the auxiliary oracle (`SeedOracle`) replaces one uniform
sample. In the intended use an answer has λ bits, and some samples of a committer have far more
outcomes than 2^λ (the randomness of an encoding). So, before the coins are derived, `OComp.blocks`
replaces every sample by small samples. A `CoinPlan` says how: each small sample has w + 1 outcomes
(in the intended use as many as the auxiliary oracle has answers), and its map φ gives the outcome.
Every small sample is a `sample` node, and there is one running counter for all small samples of a
run: the label of a small sample is its number in the run (Rom/SpecDerive.lean).

In Lean names the small samples of a sample are its `blocks`, and a sample is a toss: `tossN`. They
are not to be confused with the hash blocks of an answer, `OracleCoding.blocks` in Rom/Family.lean.

  `tv_blocks_le`     The run with samples made from small ones is within `pathBiasB` of the true
                     run, from every table.
  `pathBias_blocks`  If one answer of the auxiliary oracle gives a small sample without bias, the
                     derived form has no bias.

Notation:
  `β`: `CoinPlan`: how a uniform sample is made from small ones; `β.m n`: the number of small
    samples for a sample with n + 1 outcomes; `β.φ n`: `(Fin (β.m n) → Fin (β.w + 1)) → Fin (n + 1)`
  `σ`: `SeedOracle S` (Rom/SpecDerive.lean): an auxiliary oracle, used as a source of coins;
    `σ.bias n`: the distance of a derived sample from a uniform one; `c.pathBias σ`: the supremum,
    over the paths of the algorithm, of the sum along the path of the distances of the derived
    samples from uniform ones
  `c.runLazy T` (Rom/OComp.lean): lazy sampling from a table: an entry is sampled when it is first
    queried; `T`: `Table S` (Rom/OSpec.lean): a partial table: what lazy sampling has fixed so far
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `E`: `Gen.Extractor S I X W IVK Pf`; `Sim`: `Gen.Simulator S PP IVK X Pf` (ZKCP/Gen.lean)
  `α` in `replaceC`: `ℝ≥0∞`: the last argument of `Gen.HasCompletenessError R A B α` (ZKCP/Gen.lean)
  `ε`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.HasIndexBindingWith R A E ε` (ZKCP/Gen.lean) it stands as `ε tC tP`,
    with `Ct.QueryBound tC` and `∀ st, (Pt st).QueryBound tP`; `Ct : OComp S (IVK × St)`,
    `Pt : St → OComp S (X × Pf)`
  `ζ`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.PrivacyFor R A Sim ζ i Z` (ZKCP/Gen.lean) it stands as `ζ tV N`, with
    `∀ ivk, (Vt ivk).QueryBound tV`; N counts batches
-/
import Rom.DeriveWith
import Prob.Count
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {α γ : Type}

/-- how a uniform sample is made from small ones -/
structure CoinPlan where
  /-- a small sample has w + 1 outcomes -/
  w : ℕ
  /-- the number of small samples for a sample with n + 1 outcomes -/
  m : ℕ → ℕ
  φ : (n : ℕ) → (Fin (m n) → Fin (w + 1)) → Fin (n + 1)

/-- the distance of a sample made from small ones from a uniform one -/
def CoinPlan.bias (β : CoinPlan) (n : ℕ) : ℝ≥0∞ :=
  tv ((PMF.uniformOfFintype (Fin (β.m n) → Fin (β.w + 1))).map (β.φ n))
    (PMF.uniformOfFintype (Fin (n + 1)))

namespace OComp

/-- m uniform samples with w + 1 outcomes in a row -/
def tossN (w : ℕ) : (m : ℕ) → ((Fin m → Fin (w + 1)) → OComp S α) → OComp S α
  | 0, f => f fun i => i.elim0
  | m + 1, f => .sample w fun r => tossN w m fun v => f (Fin.cons r v)

/-- The algorithm with every uniform sample made from small ones. -/
def blocks (β : CoinPlan) : OComp S α → OComp S α
  | .pure a => .pure a
  | .query o q k => .query o q fun r => (k r).blocks β
  | .sample n k => tossN β.w (β.m n) fun v => (k (β.φ n v)).blocks β

/-- the supremum, over the paths of the algorithm, of the sum along the path of the biases of its
samples -/
def pathBiasB (β : CoinPlan) : OComp S α → ℝ≥0∞
  | .pure _ => 0
  | .query _ _ k => ⨆ r, (k r).pathBiasB β
  | .sample n k => β.bias n + ⨆ r, (k r).pathBiasB β

theorem tossN_bind (w : ℕ) (g : α → OComp S γ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (tossN w m f).bind g = tossN w m fun v => (f v).bind g
  | 0, _ => rfl
  | m + 1, f => by
      simp only [tossN, OComp.bind]
      exact congrArg _ (funext fun r => tossN_bind w g m _)

theorem blocks_bind (β : CoinPlan) (c : OComp S α) (g : α → OComp S γ) :
    (c.bind g).blocks β = (c.blocks β).bind fun a => (g a).blocks β := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    simp only [OComp.bind, blocks]
    exact congrArg _ (funext ih)
  | sample n k ih =>
    simp only [OComp.bind, blocks]
    rw [tossN_bind]
    exact congrArg _ (funext fun v => ih _)

theorem avoids_tossN {o : S.ι} (w : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, (f v).Avoids o) → (tossN w m f).Avoids o
  | 0, _, h => h _
  | m + 1, _, h => fun _ => avoids_tossN w m _ fun _ => h _

theorem Avoids.blocks {o : S.ι} (β : CoinPlan) {c : OComp S α} (h : c.Avoids o) :
    (c.blocks β).Avoids o := by
  induction c with
  | pure a => exact trivial
  | query o' q k ih => exact ⟨h.1, fun r => ih r (h.2 r)⟩
  | sample n k ih => exact avoids_tossN _ _ _ fun v => ih _ (h _)

/-- m small samples are a uniform tuple. -/
theorem runLazy_tossN (w : ℕ) (T : Table S) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α), (tossN w m f).runLazy T =
      (PMF.uniformOfFintype (Fin m → Fin (w + 1))).bind fun v => (f v).runLazy T
  | 0, f => by
      have e : PMF.uniformOfFintype (Fin 0 → Fin (w + 1)) = PMF.pure fun i => i.elim0 := by
        refine PMF.ext fun v => ?_
        rw [PMF.uniformOfFintype_apply, PMF.pure_apply, if_pos (Subsingleton.elim _ _)]
        simp
      rw [e, PMF.pure_bind]
      rfl
  | m + 1, f => by
      have e : PMF.uniformOfFintype (Fin (m + 1) → Fin (w + 1)) =
          (PMF.uniformOfFintype (Fin (w + 1))).bind fun r =>
            (PMF.uniformOfFintype (Fin m → Fin (w + 1))).map fun v =>
                (Fin.cons r v : Fin (m + 1) → Fin (w + 1)) := by
        have h := map_unif_equiv (Fin.consEquiv fun _ : Fin (m + 1) => Fin (w + 1))
        rw [unif_prod] at h
        rw [← show Prob.unif (Fin (m + 1) → Fin (w + 1)) = PMF.uniformOfFintype _ from rfl, ← h]
        unfold Prob.prod
        rw [PMF.map_bind]
        refine congrArg _ (funext fun r => ?_)
        rw [PMF.map_comp]
        rfl
      simp only [tossN, OComp.runLazy]
      rw [e, PMF.bind_bind]
      refine congrArg _ (funext fun r => ?_)
      rw [runLazy_tossN w T m, PMF.bind_map]
      rfl

/-- The run with samples made from small ones is within `pathBiasB` of the true run, from every
table. -/
theorem tv_blocks_le (β : CoinPlan) (c : OComp S α) :
    ∀ T : Table S, tv ((c.blocks β).runLazy T) (c.runLazy T) ≤ c.pathBiasB β := by
  induction c with
  | pure a =>
    intro T
    simp only [blocks, tv_self]
    exact zero_le _
  | query o q k ih =>
    intro T
    cases hT : T o q with
    | some r =>
      simp only [blocks, OComp.runLazy, hT, pathBiasB]
      exact (ih r T).trans (le_iSup (fun r => (k r).pathBiasB β) r)
    | none =>
      simp only [blocks, OComp.runLazy, hT, pathBiasB]
      exact tv_bind_right_le_of_forall _ _ _ fun r _ =>
        (ih r _).trans (le_iSup (fun r => (k r).pathBiasB β) r)
  | sample n k ih =>
    intro T
    simp only [blocks, OComp.runLazy, pathBiasB]
    rw [runLazy_tossN]
    have h1 : ((PMF.uniformOfFintype (Fin (β.m n) → Fin (β.w + 1))).bind fun v =>
          ((k (β.φ n v)).blocks β).runLazy T) =
        ((PMF.uniformOfFintype (Fin (β.m n) → Fin (β.w + 1))).map (β.φ n)).bind fun r =>
          ((k r).blocks β).runLazy T := by
      rw [PMF.bind_map]; rfl
    rw [h1]
    exact tv_bind_le_of_forall _ _ _ _ fun r =>
      (ih r T).trans (le_iSup (fun r => (k r).pathBiasB β) r)

theorem pathBias_tossN (σ : SeedOracle S) {w : ℕ} (hw : σ.bias w = 0) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, (f v).pathBias σ = 0) → (tossN w m f).pathBias σ = 0
  | 0, _, h => h _
  | m + 1, f, h => by
      simp only [tossN, pathBias, hw, zero_add]
      exact ENNReal.iSup_eq_zero.2 fun r => pathBias_tossN σ hw m _ fun v => h _

/-- If one answer of the auxiliary oracle gives a small sample without bias, the derived form has no
bias. -/
theorem pathBias_blocks (σ : SeedOracle S) (β : CoinPlan) (hw : σ.bias β.w = 0) (c : OComp S α) :
    (c.blocks β).pathBias σ = 0 := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    simp only [blocks, pathBias]
    exact ENNReal.iSup_eq_zero.2 ih
  | sample n k ih => exact pathBias_tossN σ hw _ _ fun v => ih _

end OComp

/-! ## A scheme with another committer -/

open ZKCP

variable {I X W PP IVK ISK Pf : Type}

/-- the scheme A with the committer C' -/
def withC (A : Gen.Arg S I X W IVK ISK Pf) (C' : I → OComp S (IVK × ISK)) :
    Gen.Arg S I X W IVK ISK Pf := ⟨C', A.P, A.V⟩

section WithC
variable (A : Gen.Arg S I X W IVK ISK Pf) (C' : I → OComp S (IVK × ISK))

theorem verifyAll_withC (ivk : IVK) :
    ∀ l : List (X × Pf), Gen.verifyAll (withC A C') ivk l = Gen.verifyAll A ivk l
  | [] => rfl
  | (x, π) :: rest => by
      simp only [Gen.verifyAll, verifyAll_withC ivk rest]
      rfl

theorem sessionExp_withC (ivk : IVK) (isk : ISK) (b : List (X × W)) :
    Gen.sessionExp (withC A C') ivk isk b = Gen.sessionExp A ivk isk b := by
  show ((A.P isk b).bind fun πs : Gen.Slots Pf b =>
      Gen.verifyAll (withC A C') ivk ((b.map Prod.fst).zip πs.val)) = _
  simp only [verifyAll_withC]
  rfl

theorem realLoop_withC (Z : Gen.ViewEnv S IVK X W Pf) (isk : ISK) (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf),
      Gen.realLoop (withC A C') Z isk V n v = Gen.realLoop A Z isk V n v := by
  induction V with
  | halt => intro n v; rfl
  | query o q k ih =>
    intro n v
    simp only [Gen.realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | sample m k ih =>
    intro n v
    simp only [Gen.realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Gen.realLoop]
      cases Z v with
      | none => rfl
      | some b => exact congrArg _ (funext fun πs => ih _ n _)

variable {A C'}

/-- The committer replaced by one whose run from the empty table is within b: completeness error α +
b, index binding unchanged, index privacy ζ + b, with the same extractor and the same simulator.
(not all hypotheses are named here: see the statement below) -/
theorem replaceC {R : Gen.RelPair I X W PP} {B : ℕ} {E : Gen.Extractor S I X W IVK Pf}
    {Sim : Gen.Simulator S PP IVK X Pf} {α b : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (hC : ∀ i, tv ((C' i).runLazy (Table.empty S)) ((A.C i).runLazy (Table.empty S)) ≤ b)
    (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R (withC A C') B E Sim (α + b) ε (fun t N => ζ t N + b) := by
  refine ⟨?_, fun tC tP St Ct Pt h1 h2 => h.indexBinding tC tP St Ct Pt h1 h2, ?_⟩
  · intro i bt hv
    have h0 := h.completeness i bt hv
    rw [Pr_eq_law] at h0 ⊢
    have e1 : (Gen.completenessExp (withC A C') i bt).law =
        ((C' i).runLazy (Table.empty S)).bind fun y =>
          ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst := by
      have p : Gen.completenessExp (withC A C') i bt =
          (C' i).bind fun x => Gen.sessionExp A x.1 x.2 bt := by
        show ((C' i).bind fun x => Gen.sessionExp (withC A C') x.1 x.2 bt) = _
        simp only [sessionExp_withC]
      rw [p]
      exact Derive.map_fst_runLazy_bind
        (C' i) (fun x => Gen.sessionExp A x.1 x.2 bt) (Table.empty S)
    have e2 : (Gen.completenessExp A i bt).law =
        ((A.C i).runLazy (Table.empty S)).bind fun y =>
          ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst :=
      Derive.map_fst_runLazy_bind (A.C i) (fun x => Gen.sessionExp A x.1 x.2 bt) _
    have ht : tv (Gen.completenessExp (withC A C') i bt).law (Gen.completenessExp A i bt).law ≤
        b := by
      rw [e1, e2]
      exact (tv_bind_left_le _ _ _).trans (hC i)
    exact ((tv_le_iff.1 ht {c | c = false}).1).trans (add_le_add h0 le_rfl)
  · intro i Z hZ tV Vt N hV
    obtain ⟨h1, h2⟩ := h.indexPrivacy i Z hZ tV Vt N hV
    refine ⟨?_, h2⟩
    have e1 : (fun T => Rom.Pr (Gen.realExp (withC A C') Vt Z i N) (fun _ => T)) =
        pr (Gen.realExp (withC A C') Vt Z i N).law :=
      funext fun T => Pr_eq_law _ T
    have e2 : (fun T => Rom.Pr (Gen.realExp A Vt Z i N) (fun _ => T)) =
        pr (Gen.realExp A Vt Z i N).law :=
      funext fun T => Pr_eq_law _ T
    rw [e2] at h1
    rw [e1]
    refine (sd_triangle _ (pr (Gen.realExp A Vt Z i N).law) _).trans ?_
    have l1 : (Gen.realExp (withC A C') Vt Z i N).law =
        ((C' i).runLazy (Table.empty S)).bind fun y =>
          ((Gen.realLoop A Z y.1.2 (Vt y.1.1) N ⟨y.1.1, [], [], []⟩).runLazy y.2).map Prod.fst := by
      have p : Gen.realExp (withC A C') Vt Z i N =
          (C' i).bind fun x => Gen.realLoop A Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩ := by
        show ((C' i).bind fun x => Gen.realLoop (withC A C') Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) = _
        simp only [realLoop_withC]
      rw [p]
      exact Derive.map_fst_runLazy_bind
        (C' i) (fun x => Gen.realLoop A Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) (Table.empty S)
    have l2 : (Gen.realExp A Vt Z i N).law =
        ((A.C i).runLazy (Table.empty S)).bind fun y =>
          ((Gen.realLoop A Z y.1.2 (Vt y.1.1) N ⟨y.1.1, [], [], []⟩).runLazy y.2).map Prod.fst :=
      Derive.map_fst_runLazy_bind (A.C i)
        (fun x => Gen.realLoop A Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) _
    have h3 : sd (pr (Gen.realExp (withC A C') Vt Z i N).law) (pr (Gen.realExp A Vt Z i N).law) ≤
        b := by
      have ht : tv (Gen.realExp (withC A C') Vt Z i N).law (Gen.realExp A Vt Z i N).law ≤ b := by
        rw [l1, l2]
        exact (tv_bind_left_le _ _ _).trans (hC i)
      exact ht
    refine (add_le_add h3 h1).trans (le_of_eq ?_)
    ring

end WithC

end Rom
