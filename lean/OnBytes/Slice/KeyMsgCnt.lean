-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyMsgCnt.lean: the seeds of a sending are fair, and the library's counts for a seed's
round are the closed arithmetic.

OnBytes/Slice/KeyMsgOm.lean states four things of a sent message's sample and of the seeds of a
sending, and does not prove them. This file proves the four, and the like of the fourth for the
round in which two messages' seeds are drawn.

The prefix is fair (cutPt_fibre, seeds1_isFair, seedsOK_isFair). A member reads the first "bits"
coordinates of a joint point of c coordinates, and the factor. Where bits ≤ c, the joint seeds that
give one seed of the member differ in the other c - bits coordinates alone, so they number at most
the field's size to that power.

The counts (padErr_eq, seed_cnt, seedOK_cnt). The number of the library's row with a pad is a
maximum of two products in the numbers of coordinates, of field elements and of factors; there are
as many factors as field elements other than 0. The library's count for a seed's round is a sum over
the members; for one member it is seedCnt, for two the sum of two.

Main theorems: cutPt_fibre, card_units_GE, padErr_eq, seeds1_isFair, seedsOK_isFair, seed_cnt,
seedOK_cnt.

Not claimed. That any plan pays for these counts. Fairness where a member's cube has more
coordinates than the joint point. That the seeds are the program's.
-/
import Cb.Ld.LdSendFam
import OnBytes.Slice.KeyMsgOm

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-- **The joint seeds that give one seed of a member** number at most the field's size to the number
of coordinates that the member does not read. -/
theorem cutPt_fibre (c bits : ℕ) (h : bits ≤ c) (ρ : (Fin bits → GE) × GEˣ) :
    cnt (fun s : (Fin c → GE) × GEˣ => cutPt c bits s = ρ) ≤ Fintype.card GE ^ (c - bits) := by
  have hc : Fintype.card (Fin (c - bits) → GE) = Fintype.card GE ^ (c - bits) := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [← hc, ← Nat.card_eq_fintype_card]
  unfold cnt
  refine Nat.card_le_card_of_injective
    (fun (s : {s : (Fin c → GE) × GEˣ // cutPt c bits s = ρ}) (t : Fin (c - bits)) =>
      s.1.1 ⟨bits + t.val, by omega⟩) ?_
  rintro ⟨s, hs⟩ ⟨s', hs'⟩ hh
  apply Subtype.ext
  have h2 : s.2 = s'.2 := (congrArg Prod.snd hs).trans (congrArg Prod.snd hs').symm
  have h1 : s.1 = s'.1 := by
    funext t
    by_cases ht : t.val < bits
    · have a := congrFun (congrArg Prod.fst hs) ⟨t.val, ht⟩
      have b := congrFun (congrArg Prod.fst hs') ⟨t.val, ht⟩
      simp only [cutPt] at a b
      rw [dif_pos t.isLt] at a b
      exact a.trans b.symm
    · have e : bits + (t.val - bits) = t.val := by omega
      have h3 := congrFun hh ⟨t.val - bits, by omega⟩
      have h4 : ∀ u : Fin c → GE, u ⟨bits + (t.val - bits), by omega⟩ = u t := fun u =>
        congrArg u (Fin.ext e)
      rw [← h4 s.1, ← h4 s'.1]
      exact h3
  exact Prod.ext h1 h2

/-- There are as many factors as field elements other than 0. -/
theorem card_units_GE : Fintype.card GEˣ = Fintype.card GE - 1 := by
  classical
  convert Fintype.card_units (α := GE)

/-- In a finite field there are as many units as elements, less one: for a type variable K and for
any instance i of `Fintype K`. -/
theorem card_units_of {K : Type} [Field K] (i : Fintype K) [Fintype Kˣ] :
    Fintype.card Kˣ = @Fintype.card K i - 1 := by
  classical
  convert Fintype.card_units (α := K)

/-- The number of a standard oracle message's sample map, over any field E. m, q, u: the numbers of
its coordinates, of the elements of E and of its factors. Stated over a variable field E and
variable numbers m, q, u, so that no number of elements is computed. -/
theorem stdM_err_of {E P : Type} [Fintype P] [Field E] [Fintype E] (S : StdM E P) (m q u : ℕ)
    (hm : Fintype.card S.μ = m) (hq : Fintype.card E = q) (hu : Fintype.card S.B = u) :
    S.om.Z.err = max (m * q ^ (m - 1) * u) (q ^ m) := by
  subst hm hq hu
  rfl

/-- **The sample map's number is the closed arithmetic.** `Fintype.card GE` takes an instance
argument, and two occurrences of it can carry instance terms that are equal but not written alike.
The numbers q and u are taken from the goal (the last two holes `_`), so that the right side is
`padErr`'s own, and the three numbers are linked by `Fintype.card_congr`, which holds for any two
instances. -/
theorem padErr_eq : padErr_stmt := fun M A => by
  unfold padErr
  exact @stdM_err_of GE M.Ps _ _ _ (stdAt M A) M.cubeBits _ _
    (Eq.trans (@Fintype.card_congr _ _ _ _ (Equiv.refl (Fin M.cubeBits))) (Fintype.card_fin _))
    (@Fintype.card_congr _ _ _ _ (Equiv.refl GE))
    (Eq.trans (@Fintype.card_congr _ _ _ _ (Equiv.refl GEˣ)) (card_units_of _))

/-- **The prefix is fair**, where the member's bits are no more than the joint point's. -/
theorem seeds1_isFair : seeds1_fair := fun _ A c h _ ρ => cutPt_fibre c A.bits h ρ

/-- The same for the two members of one round. -/
theorem seedsOK_isFair : seedsOK_fair := fun _ _ AO AK c hO hK a ρ => by
  cases a
  · exact cutPt_fibre c AO.bits hO ρ
  · exact cutPt_fibre c AK.bits hK ρ

/-- **The library's count for a seed's round of one member is the closed arithmetic.** -/
theorem seed_cnt : seed_cnt_eq := fun M A c => by
  unfold ldSendFamErr seedCnt
  rw [Fintype.sum_unique, padErr_eq M A]

/-- **The library's count for the round with two members is the sum of two.** -/
theorem seedOK_cnt (MO MK : Mb) (AO : MbAt MO) (AK : MbAt MK) (c : ℕ) :
    ldSendFamErr (sigOK MO MK AO AK) (seedsOK MO MK AO AK c) (fun b => if b then AK.L else AO.L) =
      seedCnt c AO.bits AO.L + seedCnt c AK.bits AK.L := by
  unfold ldSendFamErr seedCnt
  rw [Fintype.sum_bool, Nat.add_comm]
  show Fintype.card GE ^ (c - AO.bits) * (AO.L.choose 2 * (omAt MO AO).Z.err) +
    Fintype.card GE ^ (c - AK.bits) * (AK.L.choose 2 * (omAt MK AK).Z.err) = _
  rw [padErr_eq MO AO, padErr_eq MK AK]

end OnBytes.Slice

#print axioms OnBytes.Slice.cutPt_fibre
#print axioms OnBytes.Slice.card_units_GE
#print axioms OnBytes.Slice.card_units_of
#print axioms OnBytes.Slice.stdM_err_of
#print axioms OnBytes.Slice.padErr_eq
#print axioms OnBytes.Slice.seeds1_isFair
#print axioms OnBytes.Slice.seedsOK_isFair
#print axioms OnBytes.Slice.seed_cnt
#print axioms OnBytes.Slice.seedOK_cnt
