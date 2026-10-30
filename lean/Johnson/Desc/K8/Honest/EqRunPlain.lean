-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqRunPlain.lean: THE RUN OF EQUALITY WEIGHTS AT CONSECUTIVE INDICES (EqRun,
OnBytes/Model/FormF.lean) HAS AT EACH INDEX THE PLAIN PRODUCT eqPlainF, AS WORDS. Definitions and
lemmas; none of the library's goals. On field words, arrays and numbers: no ledger, no block, no
prover; nothing on completeness, soundness or hiding.

  `eqFactor z idx v`, `eqPre z idx v`, `eqPlainF_fold`, `eqPlainF_pre`   the factor of coordinate v;
      the product of the first v factors, in eqPlainF's own order; eqPlainF is the product of all
  `getD_setE_self`, `getD_setE_ne`   an array of field words behind one writing. The library has the
      pair, general in the type, in four files that this one does not import
      (OnBytes/Tie/Pv/Tail/EndLoopsB.lean, OnBytes/Tie/Pv/Led/LedPort.lean,
      OnBytes/Tie/Pv/Psc/PscFork.lean, OnBytes/Tie/Pv/Psc/Run/PscHide.lean): WRITTEN ONCE MORE
  **`eqFill_spec`**   what the refilling does: the size stays; the products up to v stay; where
      product v is right, so are those from v to v + count
  `RunGood r`, `start_good`, `next_good`, `steps_good`   the run holds the products of its own
      index: at its start, behind a step, behind i steps
  **`bit_above`**, `eqPre_next`   above the highest bit in which idx and idx + 1 differ their bits
      are the same; so the products of the coordinates whose bits stay
  **`eqAt_plain`**   eqAt z first i (Johnson/Desc/First/TailClaims/AgainMeans.lean) is eqPlainF z
      (first + i): no premise
Limits. Nothing on the product's value.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.TailClaims.AgainMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.TailClaims (eqAt stepsOn)

/-- The factor of coordinate v in eq(z, idx). -/
def eqFactor (z : Array E) (idx v : Nat) : E :=
  if idx.testBit (z.size - 1 - v) then z.getD v zeroE else subE oneE (z.getD v zeroE)

/-- The product of the factors of the first v coordinates, in the order of `eqPlainF`. -/
def eqPre (z : Array E) (idx : Nat) : Nat → E
  | 0 => oneE
  | v + 1 => mulE (eqPre z idx v) (eqFactor z idx v)

theorem eqPlainF_fold (z : Array E) (idx : Nat) : ∀ n : Nat,
    (List.range n).foldl
      (fun p v =>
        let x := z.getD v zeroE
        mulE p (if idx.testBit (z.size - 1 - v) then x else subE oneE x)) oneE = eqPre z idx n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, eqPlainF_fold z idx n]
    rfl

/-- The plain product is the product of all the factors. -/
theorem eqPlainF_pre (z : Array E) (idx : Nat) : eqPlainF z idx = eqPre z idx z.size :=
  eqPlainF_fold z idx z.size

theorem getD_setE_self (a : Array E) {j : Nat} (hj : j < a.size) (v d : E) :
    (a.set! j v).getD j d = v := by
  rw [Array.set!_eq_setIfInBounds]
  simp [Array.getD, hj]

theorem getD_setE_ne (a : Array E) {j k : Nat} (h : j ≠ k) (v d : E) :
    (a.set! j v).getD k d = a.getD k d := by
  rw [Array.set!_eq_setIfInBounds]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

/-- **What the refilling does**: the size stays; the products up to v stay; where product v is
right, so are those from v to v + count. -/
theorem eqFill_spec (z : Array E) (idx : Nat) : ∀ (count v : Nat) (pre : Array E),
    v + count < pre.size → pre.getD v zeroE = eqPre z idx v →
    (EqRun.fill z idx count v pre).size = pre.size ∧
      (∀ w, w ≤ v → (EqRun.fill z idx count v pre).getD w zeroE = pre.getD w zeroE) ∧
      ∀ w, v ≤ w → w ≤ v + count → (EqRun.fill z idx count v pre).getD w zeroE = eqPre z idx w
  | 0, v, pre, _, h0 => by
    refine ⟨rfl, fun _ _ => rfl, fun w h1 h2 => ?_⟩
    obtain rfl : w = v := by omega
    exact h0
  | count + 1, v, pre, hs, h0 => by
    have hsz : (pre.set! (v + 1) (mulE (pre.getD v zeroE) (eqFactor z idx v))).size = pre.size := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    have h1 : (pre.set! (v + 1) (mulE (pre.getD v zeroE) (eqFactor z idx v))).getD (v + 1) zeroE =
        eqPre z idx (v + 1) := by
      rw [getD_setE_self pre (by omega), h0]
      rfl
    obtain ⟨a1, a2, a3⟩ := eqFill_spec z idx count (v + 1)
      (pre.set! (v + 1) (mulE (pre.getD v zeroE) (eqFactor z idx v))) (by rw [hsz]; omega) h1
    have e : EqRun.fill z idx (count + 1) v pre = EqRun.fill z idx count (v + 1)
        (pre.set! (v + 1) (mulE (pre.getD v zeroE) (eqFactor z idx v))) := rfl
    rw [e]
    refine ⟨a1.trans hsz, fun w hw => ?_, fun w hw1 hw2 => ?_⟩
    · rw [a2 w (by omega), getD_setE_ne pre (by omega)]
    · rcases Nat.eq_or_lt_of_le hw1 with rfl | hlt
      · rw [a2 v (by omega), getD_setE_ne pre (by omega)]
        exact h0
      · exact a3 w hlt (by omega)

/-- The run holds the products of its own index. -/
def RunGood (r : EqRun) : Prop :=
  r.pre.size = r.z.size + 1 ∧ ∀ w, w ≤ r.z.size → r.pre.getD w zeroE = eqPre r.z r.idx w

theorem start_good (z : Array E) (idx : Nat) : RunGood (EqRun.start z idx) := by
  have hs : (Array.replicate (z.size + 1) oneE : Array E).size = z.size + 1 := Array.size_replicate
  have h0 : (Array.replicate (z.size + 1) oneE : Array E).getD 0 zeroE = eqPre z idx 0 := by
    simp [Array.getD, eqPre]
  obtain ⟨a1, -, a3⟩ := eqFill_spec z idx z.size 0 (Array.replicate (z.size + 1) oneE)
    (by rw [hs]; omega) h0
  refine ⟨a1.trans hs, fun w hw => a3 w (Nat.zero_le _) ?_⟩
  have hw' : w ≤ z.size := hw
  omega

/-- Above the highest bit in which idx and idx + 1 differ, their bits are the same. -/
theorem bit_above (idx j : Nat) (h : Nat.log2 (idx ^^^ (idx + 1)) < j) :
    (idx + 1).testBit j = idx.testBit j := by
  have h1 : idx ^^^ (idx + 1) < 2 ^ j :=
    Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) h)
  have h2 := Nat.testBit_lt_two_pow h1
  rw [Nat.testBit_xor] at h2
  cases ha : idx.testBit j <;> cases hb : (idx + 1).testBit j <;> simp [ha, hb] at h2 ⊢

/-- The products of the coordinates whose bits stay are the same at the next index. -/
theorem eqPre_next (z : Array E) (idx : Nat) : ∀ w : Nat,
    (∀ u, u < w → Nat.log2 (idx ^^^ (idx + 1)) < z.size - 1 - u) →
    eqPre z (idx + 1) w = eqPre z idx w
  | 0, _ => rfl
  | w + 1, h => by
    show mulE (eqPre z (idx + 1) w) (eqFactor z (idx + 1) w) =
      mulE (eqPre z idx w) (eqFactor z idx w)
    rw [eqPre_next z idx w fun u hu => h u (by omega)]
    unfold eqFactor
    rw [bit_above idx _ (h w (by omega))]

theorem next_good (r : EqRun) (h : RunGood r) : RunGood r.next := by
  obtain ⟨hs, hp⟩ := h
  have key : ∀ v, v ≤ r.z.size →
      (∀ u, u < v → Nat.log2 (r.idx ^^^ (r.idx + 1)) < r.z.size - 1 - u) →
      RunGood { r with idx := r.idx + 1,
                       pre := EqRun.fill r.z (r.idx + 1) (r.z.size - v) v r.pre } := by
    intro v hv hb
    obtain ⟨a1, a2, a3⟩ := eqFill_spec r.z (r.idx + 1) (r.z.size - v) v r.pre (by rw [hs]; omega)
      (by rw [hp v hv, eqPre_next r.z r.idx v hb])
    refine ⟨a1.trans hs, fun w hw => ?_⟩
    have hw' : w ≤ r.z.size := hw
    by_cases hwv : w ≤ v
    · show (EqRun.fill r.z (r.idx + 1) (r.z.size - v) v r.pre).getD w zeroE =
        eqPre r.z (r.idx + 1) w
      rw [a2 w hwv, hp w hw', eqPre_next r.z r.idx w fun u hu => hb u (by omega)]
    · exact a3 w (by omega) (by omega)
  unfold EqRun.next
  dsimp only
  split
  · exact key 0 (Nat.zero_le _) fun u hu => absurd hu (Nat.not_lt_zero _)
  · exact key _ (by omega) fun u hu => by omega

theorem steps_good : ∀ (i : Nat) (r : EqRun), RunGood r →
    RunGood (stepsOn r i) ∧ (stepsOn r i).z = r.z ∧ (stepsOn r i).idx = r.idx + i
  | 0, _, h => ⟨h, rfl, rfl⟩
  | i + 1, r, h => by
    obtain ⟨a1, a2, a3⟩ := steps_good i r.next (next_good r h)
    refine ⟨a1, a2, ?_⟩
    show (stepsOn r.next i).idx = r.idx + (i + 1)
    rw [a3]
    show r.idx + 1 + i = r.idx + (i + 1)
    omega

/-- **THE RUNNING PRODUCT IS THE PLAIN PRODUCT, AS WORDS**: the value that the run from `first` has
i indices further on is eq(z, first + i) by `eqPlainF`. -/
theorem eqAt_plain (z : Array E) (first i : Nat) : eqAt z first i = eqPlainF z (first + i) := by
  obtain ⟨⟨-, hp⟩, hz, hi⟩ := steps_good i (EqRun.start z first) (start_good z first)
  unfold eqAt EqRun.value
  rw [hp _ (Nat.le_refl _), hz, hi, eqPlainF_pre]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqPlainF_fold
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPlainF_pre
#print axioms VerifiableInference.Desc.First.K8.Honest.getD_setE_self
#print axioms VerifiableInference.Desc.First.K8.Honest.getD_setE_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.eqFill_spec
#print axioms VerifiableInference.Desc.First.K8.Honest.start_good
#print axioms VerifiableInference.Desc.First.K8.Honest.bit_above
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPre_next
#print axioms VerifiableInference.Desc.First.K8.Honest.next_good
#print axioms VerifiableInference.Desc.First.K8.Honest.steps_good
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAt_plain
