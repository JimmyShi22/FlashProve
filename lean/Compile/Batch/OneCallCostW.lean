-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostW.lean: the weight for the counts of Compile/Batch/SpecOneCall.lean: what a
typed query costs, at its answer, under the rule `ruleT W nb m`. Below, `Std m`
(Compile/Batch/NeedTable.lean): the encoding splits answers as Compile/Batch/ImplOf.lean does;
`Test0 W` (Compile/Batch/SpecOneCall.lean): the checks depend on block 0 alone. (Words of this
library: lean/GLOSSARY.md.)

  `pre`, `wR`   `pre w`: a weight for the programs before `realQ` (Compile/Batch/Oracles.lean:
                queries to ghost names `fbw` become queries to `fb`): at a ghost name `fbw t j` what
                w is at `fb t`; elsewhere w. wR W nb m := pre (numA m (ruleT W nb m)): the rule's
                weight, before `realQ`
  `nbAll`, `num_nbAll`, `wR_le_all`
      under `Std m`: wR o q r ≤ (needOf nbAll m).num o q at all queries, `nbAll` the table that
      marks every block. So every part whose bound in Compile/Batch/NeedCostP.lean does not depend
      on nb carries over by `Compile.CostP.SWV.of_swa`
  `numA_none`, `wR_fail`, `numA_some`
      at a Fiat-Shamir query (wR at a ghost name `fbw t j` is, by definition, numA at `fb t`):
      without proof-of-work bits at most nb t (round) + 1; under `Std m`, `Test0 W` a failed attempt
      that is not the last: exactly 1; under `Std m` any attempt, if 1 ≤ nb t (round): at most nb t
      (round) + 1 (`cntSt_congr`, `cnt_eq_cntSt`: the two ways to count marked indices)
  `TryW`   `TryW W nb m w a bf`: what the counting lemmas require of a weight w: `Std m`; never more
           than the rule asks for; a Fiat-Shamir query of round i weighs at most bf t i (with
           proof-of-work bits: if the table marks a block there); a failed attempt that is not the
           last at most a
  `tryW_numA`, `pre_le`   under `Std m`, `Test0 W` the rule's own weight meets it with a = 1, bf t i
                          = nb t i + 1; under `TryW`: pre w ≤ wR

The counting lemmas are generic in what an attempt weighs. They are used at another weight than the
rule's own, `wF` of Compile/Batch/CutQueries.lean (`tryW_wF`, Compile/Batch/CutQueriesSum.lean).

Limits: nothing about any program of the scheme.
-/
import Compile.Batch.OneCall
import Compile.Batch.NeedCostP
import Compile.CostV

noncomputable section

namespace Compile.Batch
namespace OneCall
open Iop Rom ZKCP
open Compile.Batch.Need (needOf Std num_fb_le)

theorem cntFrom_le {lam : ℕ} (nd : ℕ → (ℕ → Dg lam) → Bool) (bl : ℕ → Dg lam) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), cntFrom nd bl K j acc ≤ K
  | 0, _, _ => le_rfl
  | K + 1, j, acc => by
    unfold cntFrom
    cases nd j acc with
    | true =>
      have := cntFrom_le nd bl K (j + 1) (Function.update acc j (bl j)); show 1 + _ ≤ _; omega
    | false => have := cntFrom_le nd bl K (j + 1) acc; show cntFrom nd bl K (j + 1) acc ≤ _; omega

/-- no rule asks for more blocks than the answer has -/
theorem numA_le_blocks {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (need : NeedA S lam) (o : S.ι)
    (q : S.Dom o) (r : S.Rng o) :
    numA m need o q r ≤ m.blocks o :=
  cntFrom_le _ _ _ _ _

theorem numA_congr {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) {need need' : NeedA S lam} {o : S.ι}
    {q : S.Dom o} (h : need o q = need' o q) (r : S.Rng o) :
    numA m need o q r = numA m need' o q r := by
  unfold numA
  rw [h]

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)
  (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam W.K L) lam)

/-- A weight, for the programs before `realQ`: at a ghost name `fbw t j` what it is at `fb t`. -/
def pre {K : ℕ} (w : (o : OracleName) → domOf lam L o → rngOf lam K o → ℕ) :
    (o : OracleName) → domOf lam L o → rngOf lam K o → ℕ
  | .fbw t _, q, r => w (.fb t) q r
  | o, q, r => w o q r

/-- A bound for `pre w` on c is a bound for w on `realQ c`, for any weight w. -/
theorem costV_realQ_pre {K : ℕ} (w : (o : OracleName) → domOf lam L o → rngOf lam K o → ℕ)
    {α : Type} (c : TypedOracleComputation lam K L α) :
    ∀ t, c.CostBoundV (pre w) t → (realQ c).CostBoundV w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    intro t h
    cases o <;> exact fun r => let ⟨t', e, h'⟩ := h r; ⟨t', e, ih r t' h'⟩

/-- The rule's weight, before `realQ`. -/
def wR : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ := pre (numA m (ruleT W nb m))

theorem costV_realQ {α : Type} (c : TypedOracleComputation lam W.K L α) :
    ∀ t, c.CostBoundV (wR W nb m) t → (realQ c).CostBoundV (numA m (ruleT W nb m)) t :=
  costV_realQ_pre _ c

/-- the table that marks every block -/
def nbAll (K : ℕ) : Tag → ℕ → ℕ := fun _ _ => K + 1

variable {W nb m}

theorem num_nbAll (hm : Std m) (o : OracleName) (q : domOf lam L o) :
    (needOf (nbAll W.K) m).num o q = m.blocks o := by
  have h : needOf (nbAll W.K) m o q = fun _ => true := by
    funext j
    have hj : j.val < blk W.K o := lt_of_lt_of_eq j.isLt (hm.blocks o)
    cases o with
    | fb t => exact decide_eq_true (.inr hj)
    | fbw t k => exact decide_eq_true (.inr hj)
    | _ => rfl
  unfold Rom.Need.num
  rw [h, cnt_all]

/-- Under `Std m`: at all queries the weight is at most that of the table which marks every block.
-/
theorem wR_le_all (hm : Std m) (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o) :
    wR W nb m o q r ≤ (needOf (nbAll W.K) m).num o q := by
  rw [num_nbAll hm]
  cases o with
  | fbw t k =>
    exact (numA_le_blocks m (ruleT W nb m) (.fb t) q r).trans
      (le_of_eq ((hm.blocks (.fb t)).trans (hm.blocks (.fbw t k)).symm))
  | leaf => exact numA_le_blocks m (ruleT W nb m) .leaf q r
  | node => exact numA_le_blocks m (ruleT W nb m) .node q r
  | rleaf => exact numA_le_blocks m (ruleT W nb m) .rleaf q r
  | rnode => exact numA_le_blocks m (ruleT W nb m) .rnode q r
  | fb t => exact numA_le_blocks m (ruleT W nb m) (.fb t) q r
  | g t => exact numA_le_blocks m (ruleT W nb m) (.g t) q r
  | ann => exact numA_le_blocks m (ruleT W nb m) .ann q r
  | other => exact numA_le_blocks m (ruleT W nb m) .other q r

/-- under `Std m`: at the oracle g: at most 1 -/
theorem wR_g (hm : Std m) (t : Tag) (q : domOf lam L (.g t)) (r : rngOf lam W.K (.g t)) :
    wR W nb m (.g t) q r ≤ 1 :=
  (numA_le_blocks m (ruleT W nb m) (.g t) q r).trans (le_of_eq (hm.blocks (.g t)))

/-! ## At a Fiat-Shamir query -/

theorem cntSt_congr {st st' : ℕ → Bool} :
    ∀ (n j : ℕ), (∀ i, j ≤ i → i < j + n → st i = st' i) → cntSt st n j = cntSt st' n j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    unfold cntSt
    rw [h j le_rfl (by omega), cntSt_congr n (j + 1) fun i h1 h2 => h i (by omega) (by omega)]

/-- the two ways to count marked indices -/
theorem cnt_eq_cntSt (f : ℕ → Bool) :
    ∀ (n j : ℕ), cnt n (fun i : Fin n => f (j + i.val)) = cntSt f n j
  | 0, _ => rfl
  | n + 1, j => by
    show (if f (j + 0) then 1 else 0) + cnt n (fun i : Fin n => f (j + (i.val + 1))) =
      (if f j then 1 else 0) + cntSt f n (j + 1)
    rw [Nat.add_zero, ← cnt_eq_cntSt f n (j + 1)]
    congr 2
    funext i
    rw [Nat.add_assoc, Nat.add_comm 1]

/-- without proof-of-work bits: at most nb t (round) + 1 -/
theorem numA_none (t : Tag) (q : FbIn lam L t)
    (r : rngOf lam W.K (.fb t)) (h : tryInfoT W t q.plain = none) :
    numA m (ruleT W nb m) (.fb t) q r ≤ nb t q.round + 1 := by
  have e : numA m (ruleT W nb m) (.fb t) q r = numA m (NeedA.ofNeed (needOf nb m)) (.fb t) q r :=
    numA_congr (o := OracleName.fb t) m (ruleT_none W nb m h) r
  rw [e, (ofNeedA _ lam m (needOf nb m)).2.2 (.fb t) q r]
  exact num_fb_le nb m t q

/-- Under `Std m`: any attempt of a round in which the table marks a block costs at most nb + 1:
block 0, which the rule asks for in any case, is one of the marked. -/
theorem numA_some (hm : Std m) (t : Tag) (q : FbIn lam L t) (r : rngOf lam W.K (.fb t))
    {x : (Blk lam W.K → Bool) × Bool} (h : tryInfoT W t q.plain = some x) (h1 : 1 ≤ nb t q.round) :
    numA m (ruleT W nb m) (.fb t) q r ≤ nb t q.round + 1 := by
  have hb : m.blocks (.fb t) = W.K + 1 := hm.blocks _
  let f : ℕ → Bool := fun v => decide (v = W.K ∨ v < nb t q.round)
  have e1 : numA m (ruleT W nb m) (.fb t) q r ≤ 1 + cntSt f W.K 1 := by
    unfold numA
    have hb1 : m.blocks (.fb t) - 1 = W.K := by omega
    rw [ruleT_some W nb m h, cntFrom_ndTest' _ _ _ _ (by omega : 0 < m.blocks (.fb t))]
    refine Nat.add_le_add_left ?_ 1
    split
    · rw [hb1]
      refine le_of_eq (cntSt_congr _ _ fun i _ h3 => ?_)
      show (if hh : i < m.blocks (.fb t) then needOf nb m (.fb t) q ⟨i, hh⟩ else false) = f i
      rw [dif_pos (by omega)]
      rfl
    · exact Nat.zero_le _
  have e2 : 1 + cntSt f W.K 1 = cnt (W.K + 1) fun i : Fin (W.K + 1) => f i.val := by
    show _ = (if f 0 then 1 else 0) + cnt W.K fun i : Fin W.K => f (i.val + 1)
    have f0 : f 0 = true := decide_eq_true (.inr h1)
    rw [f0, if_pos rfl, ← cnt_eq_cntSt f W.K 1]
    congr 2
    funext i
    rw [Nat.add_comm]
  exact e1.trans (e2 ▸ Compile.Need.cnt_le_of _ W.K _)

/-- Under `Std m`, `Test0 W`: a failed attempt that is not the last costs exactly 1. Stated of numA
at fb t; wR at fb t and at a ghost name fbw t j is that number by definition (pre). -/
theorem wR_fail (hm : Std m) (h0 : Test0 W) (t : Tag) (q : FbIn lam L t)
    (r : rngOf lam W.K (.fb t)) (hf : failsAt W t q r.1 = true) :
    numA m (ruleT W nb m) (.fb t) q r = 1 :=
  failCostsOne I X lam L W nb m hm h0 t q r hf

/-! ## What the counting lemmas require of a weight -/

/-- What the counting lemmas require of a weight w (on the queries of the algorithms after `realQ`),
with two data: a: what a failed attempt that is not the last weighs at most; bf t i: what any
Fiat-Shamir query of round i of protocol t weighs at most (with proof-of-work bits: if the table
marks a block there). -/
structure TryW (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam W.K L) lam)
    (w : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ) (a : ℕ) (bf : Tag → ℕ → ℕ) : Prop where
  std : Std m
  /-- never more than the rule asks for -/
  le : ∀ o q r, w o q r ≤ numA m (ruleT W nb m) o q r
  none : ∀ t (q : FbIn lam L t) r, tryInfoT W t q.plain = none → w (.fb t) q r ≤ bf t q.round
  some : ∀ t (q : FbIn lam L t) r x,
    tryInfoT W t q.plain = some x → 1 ≤ nb t q.round → w (.fb t) q r ≤ bf t q.round
  fail : ∀ t (q : FbIn lam L t) r, failsAt W t q r.1 = true → w (.fb t) q r ≤ a

/-- The rule's own weight, under `Std m`, `Test0 W`: a failed attempt that is not the last 1, any
attempt nb t i + 1 (if the table marks a block in its round). -/
theorem tryW_numA (hm : Std m) (h0 : Test0 W) :
    TryW W nb m (numA m (ruleT W nb m)) 1 (fun t i => nb t i + 1) where
  std := hm
  le := fun _ _ _ => le_rfl
  none := fun t q r h => numA_none t q r h
  some := fun t q r _ h h1 => numA_some hm t q r h h1
  fail := fun t q r hf => le_of_eq (wR_fail hm h0 t q r hf)

theorem pre_le {w : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ} {a : ℕ} {bf : Tag → ℕ → ℕ}
    (TW : TryW W nb m w a bf) (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o) :
    pre w o q r ≤ wR W nb m o q r := by
  cases o with
  | fbw t k => exact TW.le (.fb t) q r
  | leaf => exact TW.le .leaf q r
  | node => exact TW.le .node q r
  | rleaf => exact TW.le .rleaf q r
  | rnode => exact TW.le .rnode q r
  | fb t => exact TW.le (.fb t) q r
  | g t => exact TW.le (.g t) q r
  | ann => exact TW.le .ann q r
  | other => exact TW.le .other q r

end OneCall
end Compile.Batch
