-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecordOK.lean: the programs' sample map of one row (`recZ`,
OnBytes/Slice/RecordRead.lean) has the library's property of a sample map, on the vectors whose pad
entries lie in the base field.

`recZ l lg s` is the library's `Sample.padPow` along `splitEntry`, with all l entries as entries
proper, of which those from l - 3 s on are never hit. Here the entries are parted in earnest
(`entryEquiv`), the answers of `recZ` are shown to be those of `Sample.padPow` on the l - 3 s
entries before the pads and the 3 s pad entries (`recZ_val`), and the library's law
`ood_okOn_padPow` (Cb/Gen/OodDecPadPowProofs.lean) is carried over.

Main definitions: `entryEquiv`, `padZ`.
Main theorems.
 `splitEntry_eq`, `recZ_val`   `splitEntry` is the parting; the answers agree.
 `entryBits_inj`        numbers below 2^lg with the same lg lowest binary digits are equal.
 `readE_theta`, `theta_indep`   1, X, X^2, as the program's `thetaE` is read in the extension field,
                        are independent over the base field.
 `recZ_okOn`            a vector other than 0 whose pad entries lie in the base field has all
                        answers 0 at no more than `err` seeds; `err` is the s-th power of max (lg
                        |E|^(lg - 1) (|E| - 1), |E|^lg), of (|E|^lg (|E| - 1))^s seeds.

What is not claimed. ON VECTORS WITH PAD ENTRIES OUTSIDE THE BASE FIELD THE PROPERTY FAILS (the
library's own word). No bound on the seeds at which a record does not single one table out
(`DecR.coll`) IN THIS FILE: OnBytes/Slice/RecordColl.lean has one. That `recZ` is the programs'
sample map is a reading of their text (OnBytes/Slice/RecordRead.lean). (Of the Lean port one part is
shown: the coefficients of its row of a record's answer are `recZ`'s matrix: `coefAt_recRow`,
OnBytes/Slice/BlkRecRow.lean. Of the C++ programs nothing is shown.) A count of seeds: nothing on
how the program draws them. Nothing on any hash function.

-/
import OnBytes.Slice.RecordRead
import Cb.Gen.OodDecPadPowProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood

variable (l lg s : ℕ)

/-- **The entries of a row's message, parted**: those before the pads; then, for each answer, three
pad entries. Asked: the message has room for its pads. -/
def entryEquiv (h : 3 * s ≤ l) : Fin l ≃ Fin (l - 3 * s) ⊕ Fin s × Fin 3 where
  toFun p :=
    if hp : p.val < l - 3 * s then .inl ⟨p.val, hp⟩
    else .inr (⟨(p.val - (l - 3 * s)) / 3, by have := p.isLt; omega⟩,
      ⟨(p.val - (l - 3 * s)) % 3, Nat.mod_lt _ (by decide)⟩)
  invFun x :=
    match x with
    | .inl j => ⟨j.val, by have := j.isLt; omega⟩
    | .inr n => ⟨l - 3 * s + 3 * n.1.val + n.2.val, by
        have := n.1.isLt
        have := n.2.isLt
        omega⟩
  left_inv p := by
    by_cases hp : p.val < l - 3 * s
    · simp only [dif_pos hp]
    · simp only [dif_neg hp]
      exact Fin.ext (by show l - 3 * s + 3 * ((p.val - (l - 3 * s)) / 3) +
        (p.val - (l - 3 * s)) % 3 = p.val; omega)
  right_inv x := by
    match x with
    | .inl j => simp only [dif_pos j.isLt]
    | .inr n =>
      have h1 := n.1.isLt
      have h2 := n.2.isLt
      have hn : ¬ l - 3 * s + 3 * n.1.val + n.2.val < l - 3 * s := by omega
      simp only [dif_neg hn]
      refine congrArg Sum.inr (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · show (l - 3 * s + 3 * n.1.val + n.2.val - (l - 3 * s)) / 3 = n.1.val
        omega
      · show (l - 3 * s + 3 * n.1.val + n.2.val - (l - 3 * s)) % 3 = n.2.val
        omega

/-- `splitEntry` is that parting, with an entry before the pads kept as an entry of the message. -/
theorem splitEntry_eq (h : 3 * s ≤ l) (p : Fin l) :
    splitEntry l s p = Sum.map (Fin.castLE (Nat.sub_le l (3 * s))) id (entryEquiv l s h p) := by
  have hl := p.isLt
  unfold splitEntry
  by_cases hp : p.val < l - 3 * s
  · rw [dif_neg (fun c => by omega)]
    show _ = Sum.map _ id (if hp : p.val < l - 3 * s then _ else _)
    rw [dif_pos hp]
    rfl
  · rw [dif_pos ⟨by omega, by omega⟩]
    show _ = Sum.map _ id (if hp : p.val < l - 3 * s then _ else _)
    rw [dif_neg hp]
    rfl

/-- The library's sample map with pads, on the entries before the pads and the pad entries. -/
@[reducible] noncomputable def padZ : Sample GE (Fin (l - 3 * s) ⊕ Fin s × Fin 3) :=
  Sample.padPow GE (Fin lg) (Fin (l - 3 * s)) (Fin 3) NZ (fun j t => j.val.testBit t.val)
    (fun t => readE (thetaE t.val)) (fun β => β.val) s

/-- **The answers of `recZ` are the answers of the library's sample map with pads**, on the vector
read along the parting. -/
theorem recZ_val (h : 3 * s ≤ l) (ρ : (recZ l lg s).D) (v : Fin l → GE) :
    (recZ l lg s).val ρ v = (padZ l lg s).val ρ (v ∘ (entryEquiv l s h).symm) := by
  funext i
  show ∑ p, (recZ l lg s).mat ρ i p * v p =
    ∑ x, (padZ l lg s).mat ρ i x * v ((entryEquiv l s h).symm x)
  rw [← Equiv.sum_comp (entryEquiv l s h)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Equiv.symm_apply_apply]
  congr 1
  show Sum.elim _ _ (splitEntry l s p) = Sum.elim _ _ (entryEquiv l s h p)
  rw [splitEntry_eq l s h p]
  cases entryEquiv l s h p <;> rfl

/-- Numbers below 2^lg with the same lg lowest binary digits are equal. -/
theorem entryBits_inj (hl : l - 3 * s ≤ 2 ^ lg) :
    Function.Injective fun (j : Fin (l - 3 * s)) (t : Fin lg) => j.val.testBit t.val := by
  intro a b hab
  refine Fin.ext (Nat.eq_of_testBit_eq fun t => ?_)
  by_cases ht : t < lg
  · exact congrFun hab ⟨t, ht⟩
  · have hp : 2 ^ lg ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (hl.trans hp)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (hl.trans hp))]

/-- The program's `thetaE t`, read in the extension field: the triple with 1 at place t. -/
theorem readE_theta (t : ℕ) :
    readE (thetaE t) =
      ⟨if t = 0 then 1 else 0, if t = 1 then 1 else 0, if t = 2 then 1 else 0⟩ := by
  show (⟨toF (if t = 0 then 1 else 0), toF (if t = 1 then 1 else 0),
    toF (if t = 2 then 1 else 0)⟩ : GE) = _
  congr 1 <;> split <;> first | exact toF_one | exact toF_zero

/-- **1, X, X^2, as the program's `thetaE` is read, are independent over the base field**: three pad
entries in the base field stand for the element of the extension field with these coordinates. -/
theorem theta_indep :
    Function.Injective (padVal (F := GF) fun t : Fin 3 => readE (thetaE t.val)) := by
  have e : ∀ c : Fin 3 → GF,
      padVal (F := GF) (fun t : Fin 3 => readE (thetaE t.val)) c = ⟨c 0, c 1, c 2⟩ := by
    intro c
    unfold padVal
    rw [Fin.sum_univ_three]
    simp only [readE_theta]
    ext <;> simp
  intro c c' h
  rw [e, e] at h
  funext t
  fin_cases t
  · exact congrArg (·.c0) h
  · exact congrArg (·.c1) h
  · exact congrArg (·.c2) h

/-- **THE PROGRAMS' SAMPLE MAP HAS THE LIBRARY'S PROPERTY OF A SAMPLE MAP, ON THE VECTORS WHOSE PAD
ENTRIES LIE IN THE BASE FIELD**: such a vector other than 0 has all answers 0 at no more than
`err` seeds. From the library's `ood_okOn_padPow`. Asked: the message has room for its pads; the
entries before the pads are at most 2^lg. -/
theorem recZ_okOn (h : 3 * s ≤ l) (hl : l - 3 * s ≤ 2 ^ lg) :
    (recZ l lg s).OKOn fun v =>
      ∀ p : Fin l, l - 3 * s ≤ p.val → v p ∈ Set.range (algebraMap GF GE) := by
  intro v hv hne
  have hk := ood_okOn_padPow GF GE (Fin lg) (Fin (l - 3 * s)) (Fin 3) NZ
    (fun j t => j.val.testBit t.val) (fun t => readE (thetaE t.val)) (fun β => β.val) s
    (entryBits_inj l lg s hl) Subtype.val_injective (fun β => β.2) theta_indep
    (v ∘ (entryEquiv l s h).symm)
    (fun n => hv _ (by
      show l - 3 * s ≤ l - 3 * s + 3 * n.1.val + n.2.val
      omega))
    (fun h0 => hne (funext fun p => by
      have := congrFun h0 (entryEquiv l s h p)
      simpa using this))
  have e : (fun ρ : (recZ l lg s).D => (recZ l lg s).val ρ v = 0) =
      fun ρ => (padZ l lg s).val ρ (v ∘ (entryEquiv l s h).symm) = 0 :=
    funext fun ρ => by rw [recZ_val l lg s h ρ v]
  rw [e]
  exact hk

end OnBytes.Slice
