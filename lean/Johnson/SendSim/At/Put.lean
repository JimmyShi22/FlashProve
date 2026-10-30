-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Put.lean: for all P, ride and s, the coins put s hold the value s n at the slot
and coordinate of each name n, and 0 at every tail coin.
Terms: Johnson/SendSim/At/Sim.lean; put, slot, name, number: Johnson/SendSim/At/Bridge.lean, "Terms
of the instance". Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. put s is defined as a sum over all names; the lemmas say what these coins
hold. A coordinate is one of the three coordinates of an element of the extension field over the
base field. No statement has a premise on P or ride.
  coinAt_put      coinAt reads the value s n off put s at the slot and coordinate of the name n.
  coinAt_put_tail   coinAt reads 0 off put s at every entry of every row's tail.
  seatC_inj       Two names in CoinN with the same oracle message, slot and coordinate are equal.

How it fits. Johnson/SendSim/At/Names.lean and Johnson/SendSim/At/Cells.lean use the first
(Names.lean also the second, for a lemma that nothing uses), on the way to rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). Other files
of Johnson/SendSim/At/ use the helpers below, for example Onto.lean (co_inj, for readOnto),
Additive.lean (put_e, put_f) and PadsOf.lean (seatC_inj). The proofs rest on seat_inj (two different
slots within the sizes whose coins are in the same field have different numbers, also across oracle
messages), seat_in and word_eq (Johnson/Desc/ProofFile/Honest/K1/Seat.lean).

The other names.
  dg_le, co_val, co_inj   a main row has at most three coordinates; co t has the value t for t < 3;
                  co is injective below 3.
  seatC_ok, seatT_ok   the slot of a name, and of an entry of a tail, is within its oracle message's
                  sizes (Seat.ok).
  seatC_lt, seatT_lt   their coordinates are below 3.
  seatC_zero      a name whose coin is in the base field has the coordinate 0.
  seatC_ne_seatT  a name's slot is not a slot in a tail.
  sum_pick, sum_none   a sum over all names in which one name, or none, contributes.
  put_e, put_f    the two fields of put, written out; by rfl.
-/
import Johnson.SendSim.At.Bridge

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

theorem dg_le (k : ℕ) : dg P k ≤ 3 := by
  unfold dg
  split <;> omega

theorem co_val {t : ℕ} (h : t < 3) : (co t).val = t := Nat.mod_eq_of_lt h

theorem co_inj {t t' : ℕ} (h : t < 3) (h' : t' < 3) (e : co t = co t') : t = t' := by
  have := congrArg Fin.val e
  rwa [co_val h, co_val h'] at this

/-- The slot of a name in CoinN is within its oracle message's sizes (Seat.ok). -/
theorem seatC_ok (n : CoinN P ride) :
    (seatC P ride n).1.ok P.codes (shapeAt P n.1) (ride n.1) := by
  obtain ⟨k, v⟩ := n
  rcases v with ⟨i | i, t⟩ | ⟨i, t⟩
  · have hw : (stepsOf P.codes (shapeAt P k) (ride k)).word ≠ 0 := fun h => by
      have := i.isLt
      unfold stp at this
      omega
    have e := (word_eq P.codes (shapeAt P k) (ride k) hw).1
    have hi : i.val <
        (shapeAt P k).mainRows * (P.codes.base.getD (shapeAt P k).code default).ell := by
      have := i.isLt
      unfold stp at this
      omega
    have hl : 0 < (P.codes.base.getD (shapeAt P k).code default).ell := by
      rcases Nat.eq_zero_or_pos (P.codes.base.getD (shapeAt P k).code default).ell with h | h
      · rw [h, Nat.mul_zero] at hi
        omega
      · exact h
    exact ⟨hw, (Nat.div_lt_iff_lt_mul hl).2 hi, Nat.mod_lt _ hl⟩
  · exact i.isLt
  · exact i.isLt

/-- The slot of an entry of a row's tail is within its oracle message's sizes. -/
theorem seatT_ok (ρ : RowN P) (q : Fin (codeAt P ρ).r) :
    (seatT P ρ q.val).1.ok P.codes (shapeAt P ρ.1) (ride ρ.1) := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · exact ⟨r.isLt, q.isLt⟩
  · exact ⟨r.isLt, q.isLt⟩

theorem seatC_lt (n : CoinN P ride) : (seatC P ride n).2 < 3 := by
  obtain ⟨k, v⟩ := n
  rcases v with ⟨i | i, t⟩ | ⟨i, t⟩
  · exact lt_of_lt_of_le t.isLt (dg_le P k)
  · exact lt_of_lt_of_le t.isLt (dg_le P k)
  · exact t.isLt

theorem seatT_lt (ρ : RowN P) (q : ℕ) : (seatT P ρ q).2 < 3 := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · exact lt_of_lt_of_le t.isLt (dg_le P k)
  · exact t.isLt

/-- A name whose coin is in the base field has the coordinate 0. -/
theorem seatC_zero (n : CoinN P ride)
    (h : (seatC P ride n).1.inE (shapeAt P n.1) = false) : (seatC P ride n).2 = 0 := by
  obtain ⟨k, v⟩ := n
  rcases v with ⟨i | i, t⟩ | ⟨i, t⟩
  · have h3 : ((shapeAt P k).mainDeg == 3) = false := h
    have hd : dg P k = 1 := by simp [dg, h3]
    have := t.isLt
    show t.val = 0
    omega
  · have h3 : ((shapeAt P k).mainDeg == 3) = false := h
    have hd : dg P k = 1 := by simp [dg, h3]
    have := t.isLt
    show t.val = 0
    omega
  · cases h

/-- Two names in CoinN with the same oracle message, the same slot and the same coordinate are
equal. -/
theorem seatC_inj (n n' : CoinN P ride) (hk : n.1 = n'.1)
    (hs : seatC P ride n = seatC P ride n') : n = n' := by
  obtain ⟨k, v⟩ := n
  obtain ⟨k', v'⟩ := n'
  have hk' : k = k' := hk
  subst hk'
  rcases v with ⟨i | i, t⟩ | ⟨i, t⟩ <;> rcases v' with ⟨i' | i', t'⟩ | ⟨i', t'⟩ <;>
    simp only [seatC, Prod.mk.injEq, Seat.word.injEq, Seat.pad.injEq, Seat.mask.injEq,
      reduceCtorEq, false_and] at hs
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    have e : i.val = i'.val := by
      rw [← Nat.div_add_mod i.val (P.codes.base.getD (shapeAt P k).code default).ell,
        ← Nat.div_add_mod i'.val (P.codes.base.getD (shapeAt P k).code default).ell, h1, h2]
    rw [Fin.ext e, Fin.ext h3]
  · rw [Fin.ext hs.1, Fin.ext hs.2]
  · rw [Fin.ext hs.1, Fin.ext hs.2]

/-- A name's slot is never the slot of an entry of a tail. -/
theorem seatC_ne_seatT (n : CoinN P ride) (ρ : RowN P) (q : ℕ) :
    (seatC P ride n).1 ≠ (seatT P ρ q).1 := by
  obtain ⟨k, v⟩ := n
  obtain ⟨k', v'⟩ := ρ
  rcases v with ⟨i | i, t⟩ | ⟨i, t⟩ <;> rcases v' with ⟨r, t'⟩ | ⟨r, t'⟩ <;>
    simp [seatC, seatT]

/-- A sum over all names of "if p n' then s n' else 0" is s n, if p holds at n and at no other name.
-/
theorem sum_pick (s : CoinN P ride → GF) (n : CoinN P ride) (p : CoinN P ride → Prop)
    [DecidablePred p] (hn : p n) (hu : ∀ n', p n' → n' = n) :
    (∑ n' : CoinN P ride, if p n' then s n' else 0) = s n := by
  rw [Finset.sum_eq_single n]
  · rw [if_pos hn]
  · intro n' _ hne
    rw [if_neg fun h => hne (hu n' h)]
  · intro h
    exact absurd (Finset.mem_univ n) h

theorem sum_none (s : CoinN P ride → GF) (p : CoinN P ride → Prop) [DecidablePred p]
    (hu : ∀ n', ¬ p n') : (∑ n' : CoinN P ride, if p n' then s n' else 0) = 0 :=
  Finset.sum_eq_zero fun n' _ => if_neg (hu n')

theorem put_e (s : CoinN P ride → GF) (i : Fin (dueR P ride).e) :
    (put P ride s).e i = against fun t => ∑ n : CoinN P ride,
      if (seatC P ride n).1.inE (shapeAt P n.1) = true ∧
        (seatC P ride n).1.no P ride n.1 = i.val ∧ co (seatC P ride n).2 = t
      then s n else 0 := rfl

theorem put_f (s : CoinN P ride → GF) (i : Fin (dueR P ride).f) :
    (put P ride s).f i = ∑ n : CoinN P ride,
      if (seatC P ride n).1.inE (shapeAt P n.1) = false ∧
        (seatC P ride n).1.no P ride n.1 = i.val
      then s n else 0 := rfl

/-- For every s and every name n, coinAt reads the value s n off put s at the slot and coordinate of
n. -/
theorem coinAt_put (s : CoinN P ride → GF) (n : CoinN P ride) :
    coinAt P ride (put P ride s) n.1 (seatC P ride n) = s n := by
  have hin := seat_in P ride n.1 (seatC P ride n).1 n.1.isLt (seatC_ok P ride n)
  unfold coinAt
  by_cases hE : (seatC P ride n).1.inE (shapeAt P n.1) = true
  · rw [if_pos hE]
    rw [if_pos hE] at hin
    rw [ce_eq _ _ _ hin]
    rw [put_e, crd_against]
    refine sum_pick P ride s n _ ⟨hE, rfl, rfl⟩ fun n' h => ?_
    obtain ⟨hk, hs⟩ := seat_inj P ride n'.1 n.1 _ _ (seatC_ok P ride n') (seatC_ok P ride n)
      (h.1.trans hE.symm) h.2.1
    exact seatC_inj P ride n' n (Fin.ext hk)
      (Prod.ext hs (co_inj (seatC_lt P ride n') (seatC_lt P ride n) h.2.2))
  · have hF : (seatC P ride n).1.inE (shapeAt P n.1) = false := by
      cases h : (seatC P ride n).1.inE (shapeAt P n.1)
      · rfl
      · exact absurd h hE
    rw [if_neg hE]
    rw [if_neg hE] at hin
    unfold cf
    rw [dif_pos hin, put_f]
    refine sum_pick P ride s n _ ⟨hF, rfl⟩ fun n' h => ?_
    obtain ⟨hk, hs⟩ := seat_inj P ride n'.1 n.1 _ _ (seatC_ok P ride n') (seatC_ok P ride n)
      (h.1.trans hF.symm) h.2
    exact seatC_inj P ride n' n (Fin.ext hk)
      (Prod.ext hs ((seatC_zero P ride n' h.1).trans (seatC_zero P ride n hF).symm))

/-- For every s, coinAt reads 0 off put s at the slot and coordinate of every entry of a row's tail.
-/
theorem coinAt_put_tail (s : CoinN P ride → GF) (ρ : RowN P) (q : Fin (codeAt P ρ).r) :
    coinAt P ride (put P ride s) ρ.1 (seatT P ρ q.val) = 0 := by
  have hin := seat_in P ride ρ.1 (seatT P ρ q.val).1 ρ.1.isLt (seatT_ok P ride ρ q)
  unfold coinAt
  by_cases hE : (seatT P ρ q.val).1.inE (shapeAt P ρ.1) = true
  · rw [if_pos hE]
    rw [if_pos hE] at hin
    rw [ce_eq _ _ _ hin]
    rw [put_e, crd_against]
    refine sum_none P ride s _ fun n' h => ?_
    exact seatC_ne_seatT P ride n' ρ q.val
      (seat_inj P ride n'.1 ρ.1 _ _ (seatC_ok P ride n') (seatT_ok P ride ρ q)
        (h.1.trans hE.symm) h.2.1).2
  · have hF : (seatT P ρ q.val).1.inE (shapeAt P ρ.1) = false := by
      cases h : (seatT P ρ q.val).1.inE (shapeAt P ρ.1)
      · rfl
      · exact absurd h hE
    rw [if_neg hE]
    rw [if_neg hE] at hin
    unfold cf
    rw [dif_pos hin, put_f]
    refine sum_none P ride s _ fun n' h => ?_
    exact seatC_ne_seatT P ride n' ρ q.val
      (seat_inj P ride n'.1 ρ.1 _ _ (seatC_ok P ride n') (seatT_ok P ride ρ q)
        (h.1.trans hF.symm) h.2).2

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.seatC_inj
#print axioms OnBytes.SendSim.At.coinAt_put
#print axioms OnBytes.SendSim.At.coinAt_put_tail
