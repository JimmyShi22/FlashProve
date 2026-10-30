-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Cells.lean: if the job fits its place, then in an oracle message that is not sent
along each entry of the messages of the honest sender's rows, at no data, is one coin or 0; and
which coin put s has at a slot.
Terms: Johnson/SendSim/At/Sim.lean; put, slot, name, number: Johnson/SendSim/At/Bridge.lean, "Terms
of the instance". Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves; no distribution is named. rd_cases and the lemmas on put s hold for every
value of the coins; the _zc lemmas are at coins that are all 0. The rows of one oracle message have
four arrays (Rd): main and mask hold the rows' messages, mainTl and maskTl their tails. rdAt reads
an entry of an array, in the extension field.
  rd_cases   If the job fits its place (sendFits), k < P.sent.size and oracle message k is not sent
             along (ride k = none), then for all coins c each entry of main and mask in rowsR at no
             data is 0, or is the coin at a slot that is within the sizes (Seat.ok) and located at
             that entry (Seat.place).
  coinNo_put_e, coinNo_put_f   At a slot within the sizes that is not in a tail (inMsg), put s has
             this coin: in the extension field, the element whose coordinates are the values of s at
             the slot's three names; in the base field, the value of s at the slot's one name.
  coinNo_put_zero   So that coin is 0 if s is 0 at all names of the slot.
  mainE_zc, mainF_zc, mask_zc, rd_zc   At no data and coins that are all 0 the entries of main are
             0, and so are those of mask if ride k = none.

How it fits. Johnson/SendSim/At/PadsOf.lean uses rd_cases and the three lemmas on put s;
Johnson/SendSim/At/MendsOf.lean and Johnson/SendSim/At/Single.lean use coinNo_put_zero. They serve
mendsOf, so rowsExact (Johnson/SendSim/At/RowsExact.lean), and the model's premise MendsOff, so
rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny
(Johnson/SendSim/At/FreshWideProofs.lean). The proofs rest on seat_reads
(Johnson/Desc/ProofFile/Honest/K1/SeatReads.lean), read_place and no_other
(Johnson/Desc/ProofFile/Honest/K1/NoOther.lean, which also defines Rd and rdAt), exists_name
(Johnson/SendSim/At/Names.lean) and coinAt_put (Johnson/SendSim/At/Put.lean).
-/
import Johnson.Desc.ProofFile.Honest.K1.NoOther
import Johnson.SendSim.At.Split

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- At no data and coins that are all 0, every entry of the main rows over the extension field is 0.
-/
theorem mainE_zc (k r j : ℕ) :
    (rowsR P ride (fun _ _ _ => none) (zc _) k).mainE r j = 0 := by
  have h := mainE_add P ride (fun _ _ _ => none) (zc _) k (zc _) r j
  rw [zc_add] at h
  exact left_eq_add.mp h

/-- The same for the main rows over the base field. -/
theorem mainF_zc (k r j : ℕ) :
    (rowsR P ride (fun _ _ _ => none) (zc _) k).mainF r j = 0 := by
  have h := mainF_add P ride (fun _ _ _ => none) (zc _) k (zc _) r j
  rw [zc_add] at h
  exact left_eq_add.mp h

/-- The same for the mask rows of an oracle message that is not sent along. -/
theorem mask_zc (k r j : ℕ) (hr : ride k = none) :
    (rowsR P ride (fun _ _ _ => none) (zc _) k).mask r j = 0 := by
  rw [mask_eq, hr]
  simp only [ce_zc, ite_self]

/-- The three lemmas above in terms of rdAt: if ride k = none, then at no data and coins that are
all 0 every entry of the arrays main and mask is 0. -/
theorem rd_zc (k : ℕ) (hr : ride k = none) (tb : Rd) (ht : tb = .main ∨ tb = .mask) (r j : ℕ) :
    rdAt (rowsR P ride (fun _ _ _ => none) (zc _) k) ((shapeAt P k).mainDeg == 3) tb r j = 0 := by
  rcases ht with rfl | rfl
  · show Rows.main _ _ r j = 0
    unfold Rows.main
    rw [mainE_zc, mainF_zc, map_zero, ite_self]
  · exact mask_zc P ride k r j hr

/-- If the job fits its place (sendFits), k < P.sent.size and ride k = none, then at no data each
entry of the arrays main and mask of oracle message k is the coin at a slot that is within the sizes
and located at that entry, or it is 0. -/
theorem rd_cases (hf : sendFits P ride = true) (k : ℕ) (hk : k < P.sent.size)
    (hr : ride k = none) (c : Cs (dueR P ride)) (tb : Rd) (ht : tb = .main ∨ tb = .mask)
    (r j : ℕ) :
    (∃ y : Seat, y.ok P.codes (shapeAt P k) (ride k) ∧
      y.place P.codes (shapeAt P k) (ride k) = (tb, r, j) ∧
      rdAt (rowsR P ride (fun _ _ _ => none) c k) ((shapeAt P k).mainDeg == 3) tb r j =
        coinNo c (y.inE (shapeAt P k)) (y.no P ride k)) ∨
    rdAt (rowsR P ride (fun _ _ _ => none) c k) ((shapeAt P k).mainDeg == 3) tb r j = 0 := by
  by_cases h : ∃ y : Seat, y.ok P.codes (shapeAt P k) (ride k) ∧
      y.place P.codes (shapeAt P k) (ride k) = (tb, r, j)
  · obtain ⟨y, hy, hp⟩ := h
    refine .inl ⟨y, hy, hp, ?_⟩
    rw [← seat_reads P ride _ c k y hf hk hr hy, read_place, hp]
  · refine .inr ?_
    rw [no_other P ride _ c (zc _) k tb r j (fun _ => hr) fun y hy hp => h ⟨y, hy, hp⟩]
    exact rd_zc P ride k hr tb ht r j

variable (s : CoinN P ride → GF)

/-- At a slot y of the extension field that is within the sizes and not in a tail: if s has the
value g t at each name of oracle message k with the slot y and the coordinate t, then the coin of
put s at the slot's number is the element with the coordinates g. -/
theorem coinNo_put_e (k : Fin P.sent.size) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg y = true)
    (hE : y.inE (shapeAt P k) = true) (g : Fin 3 → GF)
    (hg : ∀ (t : Fin 3) (n : CoinN P ride), n.1 = k → seatC P ride n = (y, t.val) → s n = g t) :
    coinNo (put P ride s) (y.inE (shapeAt P k)) (y.no P ride k) = against g := by
  unfold coinNo
  rw [hE, if_pos rfl]
  refine ext_crd fun t => ?_
  rw [crd_against]
  obtain ⟨n, hk, hs⟩ := exists_name P ride k y t.val hy hm t.isLt fun e => by rw [hE] at e; cases e
  have h := coinAt_put P ride s n
  rw [hs, hk] at h
  unfold coinAt at h
  simp only [hE, if_true, co_fin] at h
  rw [h]
  exact hg t n hk hs

/-- The same at a slot of the base field: if s has the value g at each name of oracle message k with
the slot y, then the coin of put s at the slot's number is g, embedded in the extension field. -/
theorem coinNo_put_f (k : Fin P.sent.size) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg y = true)
    (hE : y.inE (shapeAt P k) = false) (g : GF)
    (hg : ∀ n : CoinN P ride, n.1 = k → seatC P ride n = (y, 0) → s n = g) :
    coinNo (put P ride s) (y.inE (shapeAt P k)) (y.no P ride k) = algebraMap GF GE g := by
  unfold coinNo
  rw [hE]
  simp only [Bool.false_eq_true, if_false]
  obtain ⟨n, hk, hs⟩ := exists_name P ride k y 0 hy hm (by norm_num) fun _ => rfl
  have h := coinAt_put P ride s n
  rw [hs, hk] at h
  unfold coinAt at h
  simp only [hE, Bool.false_eq_true, if_false] at h
  rw [h, hg n hk hs]

/-- At a slot y that is within the sizes and not in a tail: if s is 0 at every name of oracle
message k with the slot y, then the coin of put s at the slot's number is 0. -/
theorem coinNo_put_zero (k : Fin P.sent.size) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg y = true)
    (h0 : ∀ n : CoinN P ride, n.1 = k → (seatC P ride n).1 = y → s n = 0) :
    coinNo (put P ride s) (y.inE (shapeAt P k)) (y.no P ride k) = 0 := by
  cases hE : y.inE (shapeAt P k)
  · have := coinNo_put_f P ride s k y hy hm hE 0 fun n hk hs => h0 n hk (by rw [hs])
    rw [hE] at this
    rw [this, map_zero]
  · have := coinNo_put_e P ride s k y hy hm hE (fun _ => 0) fun t n hk hs => h0 n hk (by rw [hs])
    rw [hE] at this
    rw [this]
    exact ext_crd fun t => by rw [crd_against, crd_zero]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rd_cases
#print axioms OnBytes.SendSim.At.coinNo_put_zero
