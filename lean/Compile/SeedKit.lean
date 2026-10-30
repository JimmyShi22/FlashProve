-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedKit.lean: lemmas for a prover that derives a part of the committer's run again
(`OComp.derive`, Rom/SpecDerive.lean: each sample is computed from the answer of an auxiliary oracle
at a seed and a counter; words of this library: lean/GLOSSARY.md).

  Part 1  `Tosses n c`: every path of the oracle algorithm c has exactly n uniform samples.
          `Wt μ n c`: samples of the total weight n; with the weights of Rom/Blocks.lean this is the
          number of small samples (`Wt.tosses_blocks`). If the first part has exactly n samples on
          every path (`Tosses`), the derived form of a sequence is the sequence of the derived
          forms, the second with its counter moved by n (`derive_bind`), and likewise for the run on
          a table and a record (`runRec_bind`).
  Part 2  `ORel r c c'`: two oracle algorithms with the same queries and the same samples, whose
          results are related by r. If r determines the second result from the first, c' is c
          followed by that function (`ORel.eq_map`).
  Part 3  `Par N₀ δ r c c'`: two token programs, the first run on a store vs with at least N₀ + δ
          strings, the second on the store without the δ strings after the first N₀
          (`Life2.viewVals`): same queries, same samples, results related by r, and the stores stay
          related. Rules for the constructors and for sequences. A token of the second program is
          shown to the first through `Life2.up`.

Notation: `σ`: a `SeedOracle S` (Rom/SpecDerive.lean): "An auxiliary oracle, used as a source of
coins"; `s`: an element of Fin (σ.sd + 1); "seeds are the elements of Fin (sd + 1)" (there); `j`: a
natural number; "j is the number of samples so far" (`OComp.derive`, there); `T`: a `Table S`
(Rom/OSpec.lean): "A partial table: what lazy sampling has fixed so far."; `R`: a `Derive.Rec σ`
(Rom/Derive.lean): "the record of the derived answers".

The token language (tokens: `Tok`, `Step`, Rom/Defer.lean; stores: `erase`, Compile/Star.lean) is a
device of this library.
-/
import Compile.EraseKit
import Compile.Step1_life2_Virt
import Rom.Blocks

open Rom

namespace Compile
namespace Seed

variable {S : OSpec} {α β γ : Type}

/-! ## Part 1. The number and the weight of the uniform samples -/

/-- every path of the algorithm has exactly n uniform samples -/
inductive Tosses : ℕ → OComp S α → Prop
  | pure (a : α) : Tosses 0 (.pure a)
  | query {n : ℕ} (o : S.ι) (q : S.Dom o) {k : S.Rng o → OComp S α} (h : ∀ r, Tosses n (k r)) :
      Tosses n (.query o q k)
  | sample {n : ℕ} (m : ℕ) {k : Fin (m + 1) → OComp S α} (h : ∀ r, Tosses n (k r)) :
      Tosses (n + 1) (.sample m k)

theorem Tosses.bind {n m : ℕ} {c : OComp S α} {g : α → OComp S β}
    (hc : Tosses n c) (hg : ∀ a, Tosses m (g a)) : Tosses (n + m) (c.bind g) := by
  induction hc with
  | pure a => simpa [OComp.bind] using hg a
  | query o q _ ih => exact .query o q ih
  | @sample n m' k _ ih =>
    have e : n + 1 + m = n + m + 1 := by omega
    rw [e]
    exact .sample m' ih

theorem Tosses.cast {n m : ℕ} {c : OComp S α} (h : Tosses n c) (e : n = m) : Tosses m c := e ▸ h

/-- every path of the algorithm has uniform samples of the total weight n; a sample with m + 1
outcomes has the weight μ m -/
inductive Wt (μ : ℕ → ℕ) : ℕ → OComp S α → Prop
  | pure (a : α) : Wt μ 0 (.pure a)
  | query {n : ℕ} (o : S.ι) (q : S.Dom o) {k : S.Rng o → OComp S α} (h : ∀ r, Wt μ n (k r)) :
      Wt μ n (.query o q k)
  | sample {n : ℕ} (m : ℕ) {k : Fin (m + 1) → OComp S α} (h : ∀ r, Wt μ n (k r)) :
      Wt μ (n + μ m) (.sample m k)

theorem Wt.cast {μ : ℕ → ℕ} {n m : ℕ} {c : OComp S α} (h : Wt μ n c) (e : n = m) : Wt μ m c := e ▸ h

theorem Wt.bind {μ : ℕ → ℕ} {n m : ℕ} {c : OComp S α} {g : α → OComp S β}
    (hc : Wt μ n c) (hg : ∀ a, Wt μ m (g a)) : Wt μ (n + m) (c.bind g) := by
  induction hc with
  | pure a => simpa [OComp.bind] using hg a
  | query o q _ ih => exact .query o q ih
  | @sample n m' k _ ih => exact (Wt.sample m' ih).cast (by omega)

/-- with the weight 1 for every sample, the weight is the number of samples -/
theorem Wt.tosses {n : ℕ} {c : OComp S α} (h : Wt (fun _ => 1) n c) : Tosses n c := by
  induction h with
  | pure a => exact .pure a
  | query o q _ ih => exact .query o q ih
  | sample m _ ih => exact .sample m ih

theorem tosses_tossN (w : ℕ) {n : ℕ} :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, Tosses n (f v)) → Tosses (n + m) (OComp.tossN w m f)
  | 0, _, h => h _
  | m + 1, _, h => .sample w fun _ => tosses_tossN w m _ fun _ => h _

/-- Every path of `c.blocks pl` has exactly n samples, if c has the weight n where a sample with
m + 1 outcomes weighs `pl.m m`, the number of small samples that it is made from. -/
theorem Wt.tosses_blocks (pl : CoinPlan) {n : ℕ} {c : OComp S α} (h : Wt pl.m n c) :
    Tosses n (c.blocks pl) := by
  induction h with
  | pure a => exact .pure a
  | query o q _ ih => exact .query o q ih
  | sample m _ ih => exact tosses_tossN _ _ _ fun v => ih _

/-- The bias along a path is at most the weight of the path times b, if a sample with k + 1 outcomes
has a bias of at most μ k · b. -/
theorem Wt.pathBiasB_le (pl : CoinPlan) {μ : ℕ → ℕ} {b : ENNReal} (hb : ∀ k, pl.bias k ≤ μ k * b)
    {n : ℕ} {c : OComp S α} (h : Wt μ n c) : c.pathBiasB pl ≤ n * b := by
  induction h with
  | pure a => exact zero_le _
  | query o q _ ih => exact iSup_le ih
  | @sample n m k _ ih =>
    show pl.bias m + ⨆ r, (k r).pathBiasB pl ≤ ((n + μ m : ℕ) : ENNReal) * b
    rw [Nat.cast_add, add_mul, add_comm]
    exact add_le_add (iSup_le ih) (hb m)

variable (σ : SeedOracle S)

/-- The derived form of a sequence (under `Tosses`). -/
theorem derive_bind (s : Fin (σ.sd + 1)) {n : ℕ} {c : OComp S α}
    (hc : Tosses n c) (g : α → OComp S β) :
    ∀ j, (c.bind g).derive σ s j = (c.derive σ s j).bind fun a => (g a).derive σ s (j + n) := by
  induction hc with
  | pure a => intro j; rfl
  | query o q _ ih =>
    intro j
    simp only [OComp.bind, OComp.derive]
    exact congrArg _ (funext fun r => ih r j)
  | @sample n m k _ ih =>
    intro j
    simp only [OComp.bind, OComp.derive]
    refine congrArg _ (funext fun d => ?_)
    rw [ih _ (j + 1)]
    have e : j + 1 + n = j + (n + 1) := by omega
    rw [e]

/-- The run of such a sequence on a table and a record. -/
theorem runRec_bind {n : ℕ} {c : OComp S α} (hc : Tosses n c) (g : α → OComp S β) :
    ∀ (j : ℕ) (T : Table S) (R : Derive.Rec σ), Derive.runRec σ (c.bind g) j T R =
      (Derive.runRec σ c j T R).bind fun x => Derive.runRec σ (g x.1) (j + n) x.2.1 x.2.2 := by
  induction hc with
  | pure a =>
    intro j T R
    simp only [OComp.bind, Derive.runRec, PMF.pure_bind]
    rfl
  | query o q _ ih =>
    intro j T R
    simp only [OComp.bind, Derive.runRec]
    cases T o q with
    | some r => exact ih r j T R
    | none =>
      simp only [PMF.bind_bind]
      exact congrArg _ (funext fun r => ih r j _ R)
  | @sample n m k _ ih =>
    intro j T R
    have e : j + 1 + n = j + (n + 1) := by omega
    simp only [OComp.bind, Derive.runRec]
    cases R j with
    | some d =>
      simp only []
      rw [ih _ (j + 1) T R, e]
    | none =>
      simp only [PMF.bind_bind]
      refine congrArg _ (funext fun d => ?_)
      rw [ih _ (j + 1) T _, e]

/-! ## Part 2. Algorithms of the same shape -/

/-- the same queries, the same uniform samples, related results -/
inductive ORel (r : α → β → Prop) : OComp S α → OComp S β → Prop
  | pure {a : α} {b : β} (h : r a b) : ORel r (.pure a) (.pure b)
  | query (o : S.ι) (q : S.Dom o) {k : S.Rng o → OComp S α}
      {k' : S.Rng o → OComp S β} (h : ∀ x, ORel r (k x) (k' x)) :
      ORel r (.query o q k) (.query o q k')
  | sample (n : ℕ) {k : Fin (n + 1) → OComp S α}
      {k' : Fin (n + 1) → OComp S β} (h : ∀ x, ORel r (k x) (k' x)) :
      ORel r (.sample n k) (.sample n k')

theorem ORel.bind {δ' : Type} {r : α → β → Prop} {r' : γ → δ' → Prop} {c : OComp S α}
    {c' : OComp S β} {g : α → OComp S γ} {g' : β → OComp S δ'} (h : ORel r c c')
    (hg : ∀ a b, r a b → ORel r' (g a) (g' b)) :
    ORel r' (c.bind g) (c'.bind g') := by
  induction h with
  | pure h => exact hg _ _ h
  | query o q _ ih => exact .query o q ih
  | sample n _ ih => exact .sample n ih

theorem ORel.mono {r r' : α → β → Prop} {c : OComp S α} {c' : OComp S β}
    (h : ORel r c c') (hr : ∀ a b, r a b → r' a b) : ORel r' c c' := by
  induction h with
  | pure h => exact .pure (hr _ _ h)
  | query o q _ ih => exact .query o q ih
  | sample n _ ih => exact .sample n ih

/-- For c and c' in `ORel r`: if the relation determines the second result from the first, the
second algorithm is the first followed by that function. -/
theorem ORel.eq_map {r : α → β → Prop} {c : OComp S α} {c' : OComp S β} (h : ORel r c c')
    (G : α → β) (hr : ∀ a b, r a b → b = G a) :
    c' = c.bind fun a => .pure (G a) := by
  induction h with
  | pure h => rw [hr _ _ h]; rfl
  | query o q _ ih => exact congrArg _ (funext ih)
  | sample n _ ih => exact congrArg _ (funext ih)

theorem orel_tossN {r : α → β → Prop} (w : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α) (f' : (Fin m → Fin (w + 1)) → OComp S β),
      (∀ v, ORel r (f v) (f' v)) → ORel r (OComp.tossN w m f) (OComp.tossN w m f')
  | 0, _, _, h => h _
  | m + 1, _, _, h => .sample w fun _ => orel_tossN w m _ _ fun _ => h _

theorem ORel.blocks {r : α → β → Prop} {c : OComp S α} {c' : OComp S β}
    (h : ORel r c c') (bk : CoinPlan) :
    ORel r (c.blocks bk) (c'.blocks bk) := by
  induction h with
  | pure h => exact .pure h
  | query o q _ ih => exact .query o q ih
  | sample n _ ih => exact orel_tossN _ _ _ _ fun v => ih _

theorem ORel.tosses {r : α → β → Prop} {c : OComp S α} {c' : OComp S β} (h : ORel r c c') :
    ∀ {n : ℕ}, Tosses n c → Tosses n c' := by
  induction h with
  | pure _ => intro n hn; cases hn; exact .pure _
  | query o q _ ih => intro n hn; cases hn with | query _ _ h' => exact .query o q fun x => ih x (h' x)
  | sample m _ ih => intro n hn; cases hn with | sample _ h' => exact .sample m fun x => ih x (h' x)

/-! ## Part 3. Programs with tokens on two stores -/

open Life2 (up viewVals length_viewVals viewVals_append getD_viewVals)

variable {sp : Split S} (N₀ δ : ℕ)

/-- the relation of the outcomes of two erased programs: results related, stores related -/
def Out (r : α → β → Prop) (o : α × List Bits) (o' : β × List Bits) : Prop :=
  r o.1 o'.1 ∧ o'.2 = viewVals N₀ δ o.2 ∧ N₀ + δ ≤ o.2.length

/-- The two programs run alike, the first on a store with at least N₀ + δ strings, the second on the
store without the δ strings after the first N₀. -/
def Par (r : α → β → Prop) (c : Step S sp α) (c' : Step S sp β) : Prop :=
  ∀ vs : List Bits,
    N₀ + δ ≤ vs.length → ORel (Out N₀ δ r) (erase c vs) (erase c' (viewVals N₀ δ vs))

variable {N₀ δ}

theorem Par.pure {r : α → β → Prop} {a : α} {b : β} (h : r a b) :
    Par N₀ δ r (Step.pure a : Step S sp α) (Step.pure b) :=
  fun _ hv => .pure ⟨h, rfl, hv⟩

theorem Par.bind {δ' : Type} {r : α → β → Prop} {r' : γ → δ' → Prop} {c : Step S sp α}
    {c' : Step S sp β} {g : α → Step S sp γ} {g' : β → Step S sp δ'} (h : Par N₀ δ r c c')
    (hg : ∀ a b, r a b → Par N₀ δ r' (g a) (g' b)) :
    Par N₀ δ r' (c.bind g) (c'.bind g') := fun vs hv => by
  rw [erase_bind, erase_bind]
  refine (h vs hv).bind fun o o' ho => ?_
  rw [ho.2.1]
  exact hg _ _ ho.1 o.2 ho.2.2

theorem Par.mono {r r' : α → β → Prop} {c : Step S sp α} {c' : Step S sp β}
    (h : Par N₀ δ r c c') (hr : ∀ a b, r a b → r' a b) : Par N₀ δ r' c c' :=
  fun vs hv => (h vs hv).mono fun _ _ ho => ⟨hr _ _ ho.1, ho.2⟩

theorem Par.sample {r : α → β → Prop} (n : ℕ) {k : Fin (n + 1) → Step S sp α}
    {k' : Fin (n + 1) → Step S sp β} (h : ∀ x, Par N₀ δ r (k x) (k' x)) :
    Par N₀ δ r (Step.sample n k) (Step.sample n k') :=
  fun vs hv => .sample n fun x => h x vs hv

theorem Par.plain {r : α → β → Prop} (o : S.ι) (q : S.Dom o) {k : S.Rng o → Step S sp α}
    {k' : S.Rng o → Step S sp β} (h : ∀ x, Par N₀ δ r (k x) (k' x)) :
    Par N₀ δ r (Step.plain o q k) (Step.plain o q k') :=
  fun vs hv => .query o q fun x => h x vs hv

theorem up_of_le {t : ℕ} (h : N₀ ≤ t) : up N₀ δ t = t + δ := by
  unfold up
  rw [if_neg (by omega)]

/-- a new token of the second program is a number t ≥ N₀; the first program sees `up` t -/
theorem Par.fresh {r : α → β → Prop} (ℓ : ℕ) {k : Tok → Step S sp α} {k' : Tok → Step S sp β}
    (h : ∀ t, N₀ ≤ t → Par N₀ δ r (k (up N₀ δ t)) (k' t)) :
    Par N₀ δ r (Step.fresh ℓ k) (Step.fresh ℓ k') := fun vs hv => by
  have hl := length_viewVals hv
  refine .sample _ fun x => ?_
  have e : vs.length = up N₀ δ (viewVals N₀ δ vs).length := by rw [up_of_le (by omega)]; omega
  rw [← viewVals_append hv, e]
  exact h _ (by omega) _ (by simp only [List.length_append]; omega)

theorem Par.marked {r : α → β → Prop} (o : S.ι) {t : Tok} {us : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k : sp.Vis o → Tok → Step S sp α} {k' : sp.Vis o → Tok → Step S sp β}
    (h : ∀ v t', N₀ ≤ t' → Par N₀ δ r (k v (up N₀ δ t')) (k' v t')) :
    Par N₀ δ r (Step.marked o (up N₀ δ t) (us.map (up N₀ δ)) pt inj k)
      (Step.marked o t us pt inj k') := fun vs hv => by
  have hl := length_viewVals hv
  have hus : ((us.map (up N₀ δ)).map fun u => vs.getD u []) =
      us.map fun u => (viewVals N₀ δ vs).getD u [] := by
    rw [List.map_map]
    exact List.map_congr_left fun v _ => (getD_viewVals hv v).symm
  simp only [erase, hus, getD_viewVals hv]
  refine .query o _ fun x => ?_
  have e : vs.length = up N₀ δ (viewVals N₀ δ vs).length := by rw [up_of_le (by omega)]; omega
  rw [← viewVals_append hv, e]
  exact h _ _ (by omega) _ (by simp only [List.length_append]; omega)

theorem Par.reveal {r : α → β → Prop} {ts : List Tok} {k : List Bits → Step S sp α}
    {k' : List Bits → Step S sp β} (h : ∀ w, Par N₀ δ r (k w) (k' w)) :
    Par N₀ δ r (Step.reveal (ts.map (up N₀ δ)) k) (Step.reveal ts k') := fun vs hv => by
  have hts : ((ts.map (up N₀ δ)).map fun u => vs.getD u []) =
      ts.map fun u => (viewVals N₀ δ vs).getD u [] := by
    rw [List.map_map]
    exact List.map_congr_left fun v _ => (getD_viewVals hv v).symm
  simp only [erase, hts]
  exact h _ vs hv

end Seed
end Compile
