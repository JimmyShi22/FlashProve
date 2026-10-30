-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Pads.lean: if lay is additive and each answer has a pad, a message coin that
contributes only to it, by a non-zero factor, then Mends holds, and MendsOff holds under Clear.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. Two lemmas of linear algebra, in which no distribution is named. They hold
for every sender S over any field and all weights w, if lay is additive (Additive).
  mends_of_pads      If S has pads at w, then Mends w holds. Mends is a premise of Spec.sendExact.
  mendsOff_of_clear  If S has pads at w and the sets U, Kn and KnT satisfy Clear, then
                     MendsOff w U Kn KnT holds. MendsOff is a premise of Spec.sendFresh.
  Pads S w   The pads: for each answer i a coin pad i and a factor β i ≠ 0. The value x at the coin
             pad k, with 0 at all other coins, contributes β k * x to answer k and 0 to the others.
  Reads      Answer i reads a coin of U: some value at one coin of U, with 0 at all other coins,
             contributes to it.
  Clear      A condition on the three sets of Spec.sendFresh. U is the set whose coins that
             statement concludes, under its premises, to be uniform and independent of what is
             disclosed together with the coins in Kn and KnT. Kn and KnT are the known message coins
             and tail coins. Clear says: U and Kn are disjoint. No pad is in U. The pad of an answer
             that reads a coin of U is not in Kn. In a row with a tail coin in KnT, neither a coin
             of U nor such a pad contributes to an entry of the message.

Limits. Each answer has one pad of one coin, which contributes to no other answer. An answer in an
extension of degree three, read over the subfield as three answers with a pad of three coins, fits
only if the answers are read so that each coin contributes to only one of the three. The instance
of Johnson/SendSim/At/Bridge.lean does so: its answers are the coordinates of y / β, not of y.
Both lemmas require that lay is additive everywhere; Mends and MendsOff require less (AddsAt).

How it fits. At the instance of the general model, mendsOff_of_clear is applied by mendsOffOf
(Johnson/SendSim/At/ClearOfFold.lean), which serves rowsFresh, and by mendsOffOfAny
(Johnson/SendSim/At/FoldAny.lean), which serves rowsFreshAny. No file of Johnson/SendSim/ applies
mends_of_pads: at the instance, Mends is proved directly (mendsOf, Johnson/SendSim/At/MendsOf.lean).

The other names.
  padFor, wt_padFor   the family with v i / β i at pad i and 0 elsewhere; it contributes v.
  sumU                the family with δ at the coins of U and 0 elsewhere.
  form_add, form_zero, lay_zero, lay_sum, wt_add, wt_zero, wt_sum   form is additive; so are lay and
                      wt if Additive holds.

Notes. Clear here is Sender.Clear, a condition in the general model. The condition "clear" on a book
(Johnson/SendSim/At/Fresh.lean) is another one. At the instance its two cases of spending imply this
one for suitable pads, under the premises of Spec.clearOfMask and Spec.clearOfFold
(Johnson/SendSim/At/ClearOf.lean).
Clear is stated coin by coin and entry by entry, at the given weights. So it holds in more cases
than a condition on whole messages would.
-/
import Johnson.SendSim.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim
open OnBytes.LinkSim

variable {K : Type} [Field K]

namespace Sender
variable (S : Sender K)

/-- Pads at the weights w: each answer has a coin of its own, its pad, which contributes to this
answer with a non-zero factor and to no other answer. -/
structure Pads (w : S.Ans → S.Row → ℕ → K) where
  /-- the pad of each answer, a message coin -/
  pad : S.Ans → S.Cn
  /-- the factor of each answer's pad -/
  β : S.Ans → K
  /-- no factor is 0 -/
  ne : ∀ i, β i ≠ 0
  /-- the value x at pad k, with 0 at all other coins, contributes β k * x to answer k and 0 to
  every other answer -/
  share : ∀ (i k : S.Ans) (x : K), S.wt w (Pi.single (pad k) x) i = if i = k then β i * x else 0

/-- Answer i reads a coin of U: some value a at some coin u of U, with 0 at all other coins,
contributes to answer i. -/
def Reads (w : S.Ans → S.Row → ℕ → K) (U : Finset S.Cn) (i : S.Ans) : Prop :=
  ∃ u ∈ U, ∃ a : K, S.wt w (Pi.single u a) i ≠ 0

/-- The condition on the sets U, Kn and KnT of Spec.sendFresh under which, if lay is additive, pads
give MendsOff (mendsOff_of_clear). -/
structure Clear (w : S.Ans → S.Row → ℕ → K) (Pd : S.Pads w) (U Kn : Finset S.Cn)
    (KnT : Finset S.TailCoin) : Prop where
  /-- no coin is in both U and Kn -/
  apart : ∀ u ∈ U, u ∉ Kn
  /-- no pad is in U -/
  padU : ∀ i, Pd.pad i ∉ U
  /-- the pad of an answer that reads a coin of U is not in Kn -/
  padKn : ∀ i, S.Reads w U i → Pd.pad i ∉ Kn
  /-- in a row with a tail coin in KnT, no coin of U contributes to an entry of the message -/
  rowU : ∀ x ∈ KnT, ∀ u ∈ U, ∀ (a : K), ∀ j < S.l x.1, S.lay (Pi.single u a) x.1 j = 0
  /-- in such a row, the pad of an answer that reads a coin of U contributes to no entry either -/
  rowPad : ∀ x ∈ KnT, ∀ i, S.Reads w U i → ∀ (a : K), ∀ j < S.l x.1,
    S.lay (Pi.single (Pd.pad i) a) x.1 j = 0

variable {S}

theorem lay_zero (hA : S.Additive) : S.lay 0 = 0 := by
  have h := hA 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem form_add (w m m' : S.Row → ℕ → K) : S.form w (m + m') = S.form w m + S.form w m' := by
  unfold form
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => mul_add _ _ _

theorem form_zero (w : S.Row → ℕ → K) : S.form w 0 = 0 := by
  unfold form
  exact Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun j _ => mul_zero _

theorem wt_add (hA : S.Additive) (w : S.Ans → S.Row → ℕ → K) (s s' : S.Cn → K) :
    S.wt w (s + s') = S.wt w s + S.wt w s' := by
  funext i
  show S.form (w i) (S.lay (s + s')) = _
  rw [hA, form_add]
  rfl

theorem wt_zero (hA : S.Additive) (w : S.Ans → S.Row → ℕ → K) : S.wt w 0 = 0 := by
  funext i
  show S.form (w i) (S.lay 0) = _
  rw [lay_zero hA, form_zero]
  rfl

theorem wt_sum (hA : S.Additive) (w : S.Ans → S.Row → ℕ → K) {ι : Type} (T : Finset ι)
    (f : ι → S.Cn → K) : S.wt w (∑ t ∈ T, f t) = ∑ t ∈ T, S.wt w (f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using wt_zero hA w
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wt_add hA, ih]

theorem lay_sum (hA : S.Additive) {ι : Type} (T : Finset ι) (f : ι → S.Cn → K) :
    S.lay (∑ t ∈ T, f t) = ∑ t ∈ T, S.lay (f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using lay_zero hA
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA, ih]

/-- The family of message coins with v k / β k at the pad of each answer k, and 0 elsewhere. -/
def padFor {w : S.Ans → S.Row → ℕ → K} (Pd : S.Pads w) (v : S.Ans → K) : S.Cn → K :=
  ∑ k, Pi.single (Pd.pad k) (v k / Pd.β k)

/-- If lay is additive, padFor Pd v contributes v i to each answer i. -/
theorem wt_padFor (hA : S.Additive) {w : S.Ans → S.Row → ℕ → K} (Pd : S.Pads w) (v : S.Ans → K) :
    S.wt w (padFor Pd v) = v := by
  funext i
  unfold padFor
  rw [wt_sum hA, Finset.sum_apply]
  simp only [Pd.share]
  rw [Finset.sum_ite_eq Finset.univ i, if_pos (Finset.mem_univ i)]
  exact mul_div_cancel₀ _ (Pd.ne i)

/-- If lay is additive and S has pads at w, then Mends w holds: for any values v of the answers, the
family padFor Pd v, at which lay is additive, contributes exactly v to the answers. -/
theorem mends_of_pads (hA : S.Additive) {w : S.Ans → S.Row → ℕ → K} (Pd : S.Pads w) : S.Mends w :=
  fun v => ⟨padFor Pd v, fun a => hA a _, wt_padFor hA Pd v⟩

/-- The family of message coins with δ u at each coin u of U, and 0 at all other coins. -/
def sumU (U : Finset S.Cn) (δ : U → K) : S.Cn → K := ∑ u : U, Pi.single (u : S.Cn) (δ u)

theorem sumU_mem (U : Finset S.Cn) (δ : U → K) (u : U) : sumU U δ u = δ u := by
  unfold sumU
  rw [Finset.sum_apply, Finset.sum_eq_single u]
  · exact Pi.single_eq_same _ _
  · intro b _ hb
    exact Pi.single_eq_of_ne (fun h => hb (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ u) h

theorem sumU_not (U : Finset S.Cn) (δ : U → K) {k : S.Cn} (hk : k ∉ U) : sumU U δ k = 0 := by
  unfold sumU
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun b _ => Pi.single_eq_of_ne (fun h => hk ?_) _
  rw [h]
  exact b.2

/-- If lay is additive and answer i reads no coin of U, then sumU U δ contributes 0 to answer i. -/
theorem wt_sumU_of_not (hA : S.Additive) (w : S.Ans → S.Row → ℕ → K) (U : Finset S.Cn)
    (δ : U → K) {i : S.Ans} (hi : ¬ S.Reads w U i) : S.wt w (sumU U δ) i = 0 := by
  unfold sumU
  rw [wt_sum hA, Finset.sum_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_contra h
  exact hi ⟨b, b.2, δ b, h⟩

theorem padFor_apply {w : S.Ans → S.Row → ℕ → K} (Pd : S.Pads w) (v : S.Ans → K) (k : S.Cn) :
    padFor Pd v k = ∑ i, if k = Pd.pad i then v i / Pd.β i else 0 := by
  unfold padFor
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => Pi.single_apply _ _ _

/-- If lay is additive, S has pads at w, and U, Kn and KnT satisfy Clear, then MendsOff w U Kn KnT
holds: each change δ of the coins in U extends to a family of message coins, at which lay is
additive, that is 0 on Kn and contributes 0 to every answer and to the message of every row with a
tail coin in KnT. The family is sumU U δ plus the values at the pads that cancel its contribution to
the answers. -/
theorem mendsOff_of_clear (hA : S.Additive) {w : S.Ans → S.Row → ℕ → K} (Pd : S.Pads w)
    {U Kn : Finset S.Cn} {KnT : Finset S.TailCoin} (hC : S.Clear w Pd U Kn KnT) :
    S.MendsOff w U Kn KnT := by
  intro δ
  have hv : ∀ i, ¬ S.Reads w U i → (-S.wt w (sumU U δ)) i / Pd.β i = 0 := fun i hi => by
    rw [Pi.neg_apply, wt_sumU_of_not hA w U δ hi, neg_zero, zero_div]
  refine ⟨sumU U δ + padFor Pd (-S.wt w (sumU U δ)), fun a => hA a _, fun u => ?_, fun k hk => ?_,
    ?_, fun x hx j hj => ?_⟩
  · rw [Pi.add_apply, sumU_mem, padFor_apply, Finset.sum_eq_zero, add_zero]
    intro i _
    exact if_neg fun (h : (u : S.Cn) = Pd.pad i) => hC.padU i (h ▸ u.2)
  · rw [Pi.add_apply, sumU_not U δ (fun h => hC.apart k h hk), padFor_apply, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : k = Pd.pad i
    · rw [if_pos h]
      exact hv i fun hr => hC.padKn i hr (h ▸ hk)
    · exact if_neg h
  · rw [wt_add hA, wt_padFor hA]
    exact add_neg_cancel _
  · rw [hA]
    show S.lay (sumU U δ) x.1 j + S.lay (padFor Pd (-S.wt w (sumU U δ))) x.1 j = 0
    have h1 : S.lay (sumU U δ) x.1 j = 0 := by
      unfold sumU
      rw [lay_sum hA, Finset.sum_apply, Finset.sum_apply]
      exact Finset.sum_eq_zero fun b _ => hC.rowU x hx b b.2 _ j hj
    have h2 : S.lay (padFor Pd (-S.wt w (sumU U δ))) x.1 j = 0 := by
      unfold padFor
      rw [lay_sum hA, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hr : S.Reads w U i
      · exact hC.rowPad x hx i hr _ j hj
      · rw [hv i hr, Pi.single_zero, lay_zero hA]
        rfl
    rw [h1, h2, add_zero]

end Sender

end OnBytes.SendSim

#print axioms OnBytes.SendSim.Sender.wt_padFor
#print axioms OnBytes.SendSim.Sender.mends_of_pads
#print axioms OnBytes.SendSim.Sender.mendsOff_of_clear
