-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Onto.lean: if the job fits its place, readC is surjective: every value of the
instance's coins is readC of some value of the honest sender's coins. The proof of Spec.readOnto.
Terms: Johnson/SendSim/At/Sim.lean; readC, put, slot, name, number: Johnson/SendSim/At/Bridge.lean,
"Terms of the instance". Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Arithmetic on the numbers of slots and finite sums; no distribution is named.
  readOnto     Spec.readOnto: if the job fits its place (sendFits), readC is surjective. The proof
               does not use the premise.
  coinAt_putG  Let N be a finite type of names, each with an oracle message, a slot and a
               coordinate. Suppose that each oracle message is below P.sent.size, that the slots are
               within the sizes, that each coordinate is one that the slot's field has, and that two
               different names differ in oracle message, slot or coordinate. Then coinAt reads each
               value s n off putG s at the name n.

How it fits. Johnson/SendSim/At/ReadUnif.lean uses readOnto for readUnif, which serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean);
Johnson/SendSim/At/SpentUnif.lean uses it too. Johnson/SendSim/At/ClearOf.lean and the files after
it use TailN. The proof of coinAt_putG follows that of coinAt_put (Johnson/SendSim/At/Put.lean) and
rests on seat_inj and seat_in (Johnson/Desc/ProofFile/Honest/K1/Seat.lean).

The other names.
  putG, putG_e, putG_f   put for such a type N; its two fields, by rfl.
  sum_pickG    a sum over all names to which only one name contributes.
  TailN, AllN  the names of the tail coins: a row and a number in its tail; the names of all coins
               of the instance: CoinN or TailN.
  keyK, keyS   the oracle message of a name in AllN; its slot and coordinate.
  seatT_zero, seatT_inj   the analogues for TailN of seatC_zero and seatC_inj
               (Johnson/SendSim/At/Put.lean).
-/
import Johnson.SendSim.At.Put

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

section General
variable {N : Type} [Fintype N] (kK : N → ℕ) (kS : N → Seat × ℕ)

/-- Coins of the sender made from values s at the names in N, where kK gives a name's oracle message
and kS its slot and coordinate. A coin of the base field is the sum of the values of the names in
that field with its number. A coordinate of a coin of the extension field is the sum of the values
of the names in that field with its number and that coordinate. So a coin is 0 where there is no
such name. -/
def putG (s : N → GF) : Cs (dueR P ride) where
  f := fun i => ∑ n : N,
    if (kS n).1.inE (shapeAt P (kK n)) = false ∧ (kS n).1.no P ride (kK n) = i.val then s n else 0
  e := fun i => against fun t => ∑ n : N,
    if (kS n).1.inE (shapeAt P (kK n)) = true ∧ (kS n).1.no P ride (kK n) = i.val ∧
      co (kS n).2 = t
    then s n else 0

theorem putG_e (s : N → GF) (i : Fin (dueR P ride).e) :
    (putG P ride kK kS s).e i = against fun t => ∑ n : N,
      if (kS n).1.inE (shapeAt P (kK n)) = true ∧ (kS n).1.no P ride (kK n) = i.val ∧
        co (kS n).2 = t
      then s n else 0 := rfl

theorem putG_f (s : N → GF) (i : Fin (dueR P ride).f) :
    (putG P ride kK kS s).f i = ∑ n : N,
      if (kS n).1.inE (shapeAt P (kK n)) = false ∧ (kS n).1.no P ride (kK n) = i.val
      then s n else 0 := rfl

theorem sum_pickG (s : N → GF) (n : N) (p : N → Prop) [DecidablePred p] (hn : p n)
    (hu : ∀ n', p n' → n' = n) : (∑ n' : N, if p n' then s n' else 0) = s n := by
  rw [Finset.sum_eq_single n]
  · rw [if_pos hn]
  · intro n' _ hne
    rw [if_neg fun h => hne (hu n' h)]
  · intro h
    exact absurd (Finset.mem_univ n) h

/-- If every name's oracle message is below P.sent.size, its slot is within the sizes, its
coordinate is below 3 and is 0 in the base field, and no two names share oracle message, slot and
coordinate, then coinAt reads s n off putG s at the name n. -/
theorem coinAt_putG (hlt : ∀ n, kK n < P.sent.size)
    (hok : ∀ n, (kS n).1.ok P.codes (shapeAt P (kK n)) (ride (kK n))) (h3 : ∀ n, (kS n).2 < 3)
    (h0 : ∀ n, (kS n).1.inE (shapeAt P (kK n)) = false → (kS n).2 = 0)
    (hinj : ∀ n n', kK n = kK n' → kS n = kS n' → n = n') (s : N → GF) (n : N) :
    coinAt P ride (putG P ride kK kS s) (kK n) (kS n) = s n := by
  have hin := seat_in P ride (kK n) (kS n).1 (hlt n) (hok n)
  unfold coinAt
  by_cases hE : (kS n).1.inE (shapeAt P (kK n)) = true
  · rw [if_pos hE]
    rw [if_pos hE] at hin
    rw [ce_eq _ _ _ hin, putG_e, crd_against]
    refine sum_pickG s n _ ⟨hE, rfl, rfl⟩ fun n' h => ?_
    obtain ⟨hk, hs⟩ := seat_inj P ride (kK n') (kK n) _ _ (hok n') (hok n) (h.1.trans hE.symm) h.2.1
    exact hinj n' n hk (Prod.ext hs (co_inj (h3 n') (h3 n) h.2.2))
  · have hF : (kS n).1.inE (shapeAt P (kK n)) = false := by
      cases h : (kS n).1.inE (shapeAt P (kK n))
      · rfl
      · exact absurd h hE
    rw [if_neg hE]
    rw [if_neg hE] at hin
    unfold cf
    rw [dif_pos hin, putG_f]
    refine sum_pickG s n _ ⟨hF, rfl⟩ fun n' h => ?_
    obtain ⟨hk, hs⟩ := seat_inj P ride (kK n') (kK n) _ _ (hok n') (hok n) (h.1.trans hF.symm) h.2
    exact hinj n' n hk (Prod.ext hs ((h0 n' h.1).trans (h0 n hF).symm))

end General

theorem seatT_zero (ρ : RowN P) (q : ℕ)
    (h : (seatT P ρ q).1.inE (shapeAt P ρ.1) = false) : (seatT P ρ q).2 = 0 := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · have h3 : ((shapeAt P k).mainDeg == 3) = false := h
    have hd : dg P k = 1 := by simp [dg, h3]
    have := t.isLt
    show t.val = 0
    omega
  · cases h

/-- The names of the tail coins: a row and a number below the length of its tail. -/
abbrev TailN : Type := (ρ : RowN P) × Fin (codeAt P ρ).r

theorem seatT_inj (x x' : TailN P) (hk : x.1.1 = x'.1.1)
    (hs : seatT P x.1 x.2.val = seatT P x'.1 x'.2.val) : x = x' := by
  obtain ⟨⟨k, v⟩, q⟩ := x
  obtain ⟨⟨k', v'⟩, q'⟩ := x'
  have hk' : k = k' := hk
  subst hk'
  rcases v with ⟨r, t⟩ | ⟨r, t⟩ <;> rcases v' with ⟨r', t'⟩ | ⟨r', t'⟩ <;>
    simp only [seatT, Prod.mk.injEq, Seat.tail.injEq, Seat.maskTail.injEq, reduceCtorEq,
      false_and] at hs
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    have e1 : r = r' := Fin.ext h1
    have e3 : t = t' := Fin.ext h3
    subst e1
    subst e3
    have e2 : q = q' := Fin.ext h2
    rw [e2]
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    have e1 : r = r' := Fin.ext h1
    have e3 : t = t' := Fin.ext h3
    subst e1
    subst e3
    have e2 : q = q' := Fin.ext h2
    rw [e2]

/-- The names of all coins of the instance: a message coin's name or a tail coin's name. -/
abbrev AllN : Type := CoinN P ride ⊕ TailN P

/-- The number of the oracle message of a name in AllN. -/
def keyK : AllN P ride → ℕ := Sum.elim (fun n => n.1.val) fun x => x.1.1.val

/-- The slot and the coordinate of a name in AllN. -/
def keyS : AllN P ride → Seat × ℕ := Sum.elim (seatC P ride) fun x => seatT P x.1 x.2.val

/-- Proof of Spec.readOnto: a value of the instance's coins is readC of putG of it, by coinAt_putG
at the names AllN. The premise that the job fits its place is not used. -/
theorem readOnto : Spec.readOnto := by
  intro P ride _ a
  have key := coinAt_putG P ride (keyK P ride) (keyS P ride)
    (fun n => by rcases n with n | x <;> [exact n.1.isLt; exact x.1.1.isLt])
    (fun n => by rcases n with n | x <;> [exact seatC_ok P ride n; exact seatT_ok P ride x.1 x.2])
    (fun n => by rcases n with n | x <;> [exact seatC_lt P ride n; exact seatT_lt P x.1 x.2.val])
    (fun n => by
      rcases n with n | x <;> [exact seatC_zero P ride n; exact seatT_zero P x.1 x.2.val])
    (fun n n' hk hs => by
      rcases n with n | x <;> rcases n' with n' | x'
      · exact congrArg Sum.inl (seatC_inj P ride n n' (Fin.ext hk) hs)
      · exact absurd (congrArg Prod.fst hs) (seatC_ne_seatT P ride n x'.1 x'.2.val)
      · exact absurd (congrArg Prod.fst hs).symm (seatC_ne_seatT P ride n' x.1 x.2.val)
      · exact congrArg Sum.inr (seatT_inj P x x' (Fin.ext hk) hs))
    (Sum.elim a.1 fun x => a.2 x.1 x.2)
  refine ⟨putG P ride (keyK P ride) (keyS P ride) (Sum.elim a.1 fun x => a.2 x.1 x.2), ?_⟩
  refine Prod.ext (funext fun n => key (.inl n)) (funext fun ρ => funext fun q => key (.inr ⟨ρ, q⟩))

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.coinAt_putG
#print axioms OnBytes.SendSim.At.readOnto
