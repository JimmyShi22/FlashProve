-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnParts.lean: what the chain of a layers' sub-proof's own rounds (Cb/Pv/Lay/Own.lean)
needs of the product layers, the merge and the rounds that open them.

The chain takes each sumcheck as parameters of Cb/Pv/Lay/Sum.lean and each drawing round with a
bound on its bad draws. Here the product layer (Cb/Pv/Lay/Prod.lean) and the merge
(Cb/Pv/Lay/Merge.lean) are given as such parameters, with no kept map, and two bounds are proved in
the form in which the chain asks them.

Main names:
  `noKept`: no kept map.
  `ProdL.toSum`, `ProdL.ksum_iff`, `ProdL.kval_iff`: the product layer as parameters of Sum.lean;
    what its input claim says; what its rows on the end values say.
  `MergeL.toSum`, `MergeL.ksum_iff`, `MergeL.kval_iff`: the same of the merge.
  `law_groups`: sent scalars that split identities, in n groups of ns, all under the powers of one
    drawn element: at most ns - 1 draws are bad.
  `law_join`: n gaps under the equality weights of a drawn point of g coordinates, n at most 2^g: at
    most g * |E|^(g - 1) points are bad.

Limits: as in the files named. Nothing is said on the honest prover, on completeness or on zero
knowledge.
-/
import Cb.Pv.Lay.Own
import Cb.Pv.Lay.Squares
import Cb.Pv.Lay.WeightsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- No kept map. -/
@[reducible] def noKept {St J : Type} (S : LdPartSm E St J) : KeptSm S where
  B := Empty
  Fb := fun _ _ b => b.elim
  kt := fun b => b.elim

/-- With no kept map the conditions are those on the revealed maps. -/
theorem noKept_ok {St J : Type} [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S)
    (da : S.A → Fin S.k → ℕ) (h : S.OK M da) : (noKept S).OK M da (fun b => b.elim) :=
  ⟨h, fun _ _ b => b.elim, fun b => b.elim, fun b => b.elim⟩

omit [Fintype E] in
/-- With no kept map the summand is that of the revealed maps. -/
theorem noKept_val {St J : Type} (S : LdPartSm E St J) (st : St) (m : J → E) (z : Fin S.k → E) :
    (noKept S).val st m z = S.val st m z := by
  unfold KeptSm.val
  simp

namespace ProdL
variable (L : ProdL E)

/-- The product layer as parameters of Cb/Pv/Lay/Sum.lean. -/
@[reducible] def toSum : SumL E where
  St := L.St
  J := L.J
  S := L.Sm
  M := L.Mk
  Q := noKept L.Sm
  da := fun _ _ => 1
  db := fun b => b.elim
  ok := noKept_ok L.Sm L.Mk _ L.ok
  Rd := L.Rd

/-- The input claim in the chain's form is the record's own. -/
theorem ksum_iff (t : E) (st : L.St) (m : L.J → E) :
    L.toSum.T.SumHolds (t, st) m ↔ L.T.SumHolds (t, st) m := by
  rw [(noKept L.Sm).sum_iff L.Mk, ldPartPsc_sum E]
  simp only [noKept_val]

/-- The claim on an end value in the chain's form is the record's own. -/
theorem kval_iff (o : L.toSum.T.par.Out) (m : L.J → E) (b : Bool) :
    L.toSum.T.par.EHolds o m b ↔
      Blocks.ext L.k (L.vm o.st m b)
        (Blocks.nat fun i => (noKept L.Sm).outPt L.Mk o (L.e.symm i)) +
          m (L.cAt b) * (noKept L.Sm).outB L.Mk o = o.vals b :=
  (noKept L.Sm).val_iff L.Mk o m b

end ProdL

namespace MergeL
variable (L : MergeL E)

/-- The merge as parameters of Cb/Pv/Lay/Sum.lean. -/
@[reducible] def toSum : SumL E where
  St := L.St
  J := L.J
  S := L.Sm
  M := L.Mk
  Q := noKept L.Sm
  da := fun _ _ => 2
  db := fun b => b.elim
  ok := noKept_ok L.Sm L.Mk _ L.ok
  Rd := L.Rd

/-- The input claim in the chain's form is the record's own. -/
theorem ksum_iff (t : E) (st : L.St) (m : L.J → E) :
    L.toSum.T.SumHolds (t, st) m ↔ L.T.SumHolds (t, st) m := by
  rw [(noKept L.Sm).sum_iff L.Mk, ldPartPsc_sum E]
  simp only [noKept_val]

/-- The claim on an end value in the chain's form is the record's own. -/
theorem kval_iff (o : L.toSum.T.par.Out) (m : L.J → E) :
    L.toSum.T.par.EHolds o m () ↔
      L.f o.st m ((noKept L.Sm).outPt L.Mk o) + m L.cAt * (noKept L.Sm).outB L.Mk o = o.vals () :=
  (noKept L.Sm).val_iff L.Mk o m ()

end MergeL

/-! ### Two bounds on bad draws -/

variable {M : Type}

/-- Sent scalars that split identities, in groups. Identity (i, t) says a i t = c i t. Of the sent
scalars it is
claimed that s (i, t) - k i t = c i t (k: a mask). If the claim behind the draw gives, for each
group i, that
the batch of the gaps a i t + k i t - s (i, t) under the powers of the drawn element is 0, and Q,
then at most
ns - 1 draws are bad. -/
theorem law_groups {X S : Type} (n ns : ℕ) (rd : S → Fin n → Fin ns → E)
    (a c k : X → M → Fin n → Fin ns → E) (Q P : X → M → Prop) (L : X → S → M → Prop)
    (T : (X × S) × E → M → Prop)
    (hP : ∀ x m, (∀ i t, a x m i t = c x m i t) → Q x m → P x m)
    (hL : ∀ x s m, L x s m → ∀ i t, rd s i t - k x m i t = c x m i t)
    (hT : ∀ x s β m, T ((x, s), β) m →
      (∀ i, ∑ t : Fin ns, β ^ (t : ℕ) * (a x m i t + k x m i t - rd s i t) = 0) ∧ Q x m)
    (x : X) (m : M) (h : ¬ P x m) (s : S) (hs : L x s m) :
    cnt (fun β : E => T ((x, s), β) m) ≤ ns - 1 := by
  classical
  by_cases hQ : Q x m
  · have h1 : ∃ i, (fun t => a x m i t + k x m i t - rd s i t) ≠ 0 := by
      by_contra hc
      refine h (hP x m (fun i t => ?_) hQ)
      have h2 : (fun t => a x m i t + k x m i t - rd s i t) = 0 := by
        by_contra h3
        exact hc ⟨i, h3⟩
      have e1 : a x m i t + k x m i t - rd s i t = 0 := congrFun h2 t
      have e2 := hL x s m hs i t
      linear_combination e1 + e2
    obtain ⟨i, hi⟩ := h1
    refine le_trans (cnt_mono fun β hβ => ?_) (ok_powers E ns _ hi)
    exact (hT x s β m hβ).1 i
  · exact le_trans (le_of_eq (cnt_false fun β hβ => hQ (hT x s β m hβ).2)) (Nat.zero_le _)

/-- Gaps under the equality weights of a drawn point. If the claim before the draw says that n gaps
are 0 and Q,
and the claim behind it gives that their sum under the weights is 0, and Q, then at most g * |E|^(g
- 1) points
are bad. -/
theorem law_join {X : Type} (g n : ℕ) (hn : n ≤ 2 ^ g) (gap : X → M → Fin n → E) (Q P : X → M →
    Prop)
    (T : X × (Fin g → E) → M → Prop) (hP : ∀ x m, (∀ i, gap x m i = 0) → Q x m → P x m)
    (hT : ∀ x p m, T (x, p) m → ∑ i, (Evader.eqNum E g n).ze p i * gap x m i = 0 ∧ Q x m)
    (x : X) (m : M) (h : ¬ P x m) :
    cnt (fun p : Fin g → E => T (x, p) m) ≤ g * Fintype.card E ^ (g - 1) := by
  classical
  by_cases hQ : Q x m
  · have h1 : gap x m ≠ 0 := fun h0 => h (hP x m (fun i => congrFun h0 i) hQ)
    refine le_trans (cnt_mono fun p hp => ?_) (ok_eqNum E g n hn (gap x m) h1)
    exact (hT x p m hp).1
  · exact le_trans (le_of_eq (cnt_false fun p hp => hQ (hT x p m hp).2)) (Nat.zero_le _)

end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.ProdL.ksum_iff
#print axioms Cb.Pv.Lay.MergeL.ksum_iff
#print axioms Cb.Pv.Lay.law_groups
#print axioms Cb.Pv.Lay.law_join
