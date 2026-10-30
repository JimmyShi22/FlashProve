-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/MendsOf.lean: under four public premises, the message coins' contribution can
give the instance's answers any values, by a family of message coins at which lay is additive. The
proof of Spec.mendsOf.
Terms: Johnson/SendSim/At/Sim.lean; for Mends and AddsAt, Johnson/SendSim/Defs.lean; sender, wOf,
put, name, RidesZero: Johnson/SendSim/At/Bridge.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. Algebra; no distribution is named.
  mendsOf     Spec.mendsOf, which is written out, with its four premises, in
              Johnson/SendSim/At/Bridge.lean. For given values v, the family is the sum, over the
              answers a, of the value v a at the coin that share_of gives for a. Of a table that is
              sent along the proof uses only RidesZero (a table that is sent along has entries 0 in
              its 2 ^ h rows if its coins are all 0).
  OffRide     a family of message coins that is 0 at every coin of an oracle message that is sent
              along.
  addsAt_off  If the job fits its place and RidesZero holds, lay is additive at every such family
              (Sender.AddsAt).
  mask_add_off, entry_add_off, layN_add_off   Under the same premises, the field mask of rowsR, a
              row's entry, and lay are additive at a sum whose second summand is 0 at the coins of
              every table that is sent along.
  wt_add_off, wt_zero_off, wt_sum_off   Under the same premises, the contributions of such families
              to the answers add.

Limits. RidesZero is a premise here; it holds for every ride (ridesZero,
Johnson/SendSim/At/RideLay.lean).

How it fits. mends_paid (Johnson/SendSim/At/Paid.lean) is mendsOf without RidesZero;
Johnson/SendSim/At/JoinRows.lean uses it as the premise Mends of sendExact, for rowsExact
(Johnson/SendSim/At/RowsExact.lean). Johnson/SendSim/At/Single.lean uses layN. The proofs rest on
share_of (Johnson/SendSim/At/PadsOf.lean), coinNo_put_zero (Johnson/SendSim/At/Cells.lean), put_add
(Johnson/SendSim/At/Additive.lean) and Sender.form_add (Johnson/SendSim/Pads.lean).

The other names.
  layN, wtN   lay and wt of the instance, stated with the types CoinN, RowN and AnsN.
  rideC_put_off   put of such a family is 0 at the coins of every table that is sent along.
  offRide_zero, offRide_add, offRide_sum, offRide_single   0, sums, and one coin of an oracle
              message that is not sent along, are such families.

Notes. seedsFit is a premise of Spec.mendsOf. The proof does not use it.
-/
import Johnson.SendSim.At.PadsOf

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- A family of message coins that is 0 at every coin of an oracle message that is a table sent
along. -/
def OffRide (s : CoinN P ride → GF) : Prop := ∀ n : CoinN P ride, ride n.1 ≠ none → s n = 0

variable {P ride}

/-- If s is such a family (OffRide), the coins put s are 0 at the coins of every table that is sent
along. -/
theorem rideC_put_off (s : CoinN P ride → GF) (hs : OffRide P ride s) (k : Fin P.sent.size)
    (R : Ride) (hr : ride k = some R) : rideC P ride (put P ride s) k R = 0 := by
  funext i
  show rideC P ride (put P ride s) k R i = 0
  unfold rideC
  split
  · rename_i hi
    have hy : (Seat.mask i).ok P.codes (shapeAt P k) (ride k) := by
      show i < (stepsOf P.codes (shapeAt P k) (ride k)).mask
      simpa [stepsOf, hr] using hi
    have h := coinNo_put_zero P ride s k (.mask i) hy rfl fun n hn _ =>
      hs n (by rw [hn, hr]; simp)
    unfold coinNo Seat.no at h
    simp only [Seat.inE, if_true] at h
    rwa [mask_no] at h
  · rfl

/-- mask_add (Johnson/SendSim/At/Rows.lean), under its other two premises, with RidesZero in place
of RidesAdd, if c' is 0 at the coins of the table that is sent along as oracle message k. -/
theorem mask_add_off (hf : sendFits P ride = true) (hZ : RidesZero ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c c' : Cs (dueR P ride)) (k : ℕ)
    (hk : k < P.sent.size) (h0 : ∀ R, ride k = some R → rideC P ride c' k R = 0) (r j : ℕ) :
    (rowsR P ride data (addC c c') k).mask r j =
      (rowsR P ride data c k).mask r j + (rowsR P ride (fun _ _ _ => none) c' k).mask r j := by
  rw [mask_eq, mask_eq, mask_eq]
  cases hr : ride k with
  | none =>
    simp only
    split
    · exact ce_add c c' _
    · rw [add_zero]
  | some R =>
    simp only
    split
    · rename_i hg
      rw [rideC_add, h0 R hr, add_zero,
        hZ k R hr r j (by rw [← rows_of_ride P ride k hf hk R hr]; exact hg.1), add_zero]
    · rw [add_zero]

/-- entry_add (Johnson/SendSim/At/Additive.lean), under its other premise, with RidesZero in place
of RidesAdd, if c' is 0 at the coins of every table that is sent along. -/
theorem entry_add_off (hf : sendFits P ride = true) (hZ : RidesZero ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c c' : Cs (dueR P ride))
    (h0 : ∀ (k : Fin P.sent.size) R, ride k = some R → rideC P ride c' k R = 0) (ρ : RowN P)
    (j : ℕ) :
    entry P (rowsR P ride data (addC c c')) ρ j =
      entry P (rowsR P ride data c) ρ j + entry P (rowsR P ride (fun _ _ _ => none) c') ρ j := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · show (if (shapeAt P k).mainDeg == 3 then _ else _) =
      (if (shapeAt P k).mainDeg == 3 then _ else _) + if (shapeAt P k).mainDeg == 3 then _ else _
    split
    · rw [mainE_add, crd_add]
    · rw [mainF_add]
  · show crd t _ = crd t _ + crd t _
    rw [mask_add_off hf hZ data c c' k k.isLt (h0 k), crd_add]

/-- The instance's lay, stated with the types CoinN and RowN. -/
def layN (s : CoinN P ride → GF) : RowN P → ℕ → GF :=
  entry P (rowsR P ride (fun _ _ _ => none) (put P ride s))

/-- If the job fits its place (sendFits) and RidesZero holds, layN (a + s) = layN a + layN s for
every family s with OffRide. -/
theorem layN_add_off (hf : sendFits P ride = true) (hZ : RidesZero ride)
    (a s : CoinN P ride → GF) (hs : OffRide P ride s) : layN (a + s) = layN a + layN s := by
  funext ρ j
  show entry P (rowsR P ride (fun _ _ _ => none) (put P ride (a + s))) ρ j =
    entry P (rowsR P ride (fun _ _ _ => none) (put P ride a)) ρ j +
      entry P (rowsR P ride (fun _ _ _ => none) (put P ride s)) ρ j
  rw [put_add]
  exact entry_add_off hf hZ _ _ _ (fun k R hr => rideC_put_off s hs k R hr) ρ j

/-- If the job fits its place (sendFits) and RidesZero holds, the instance's lay is additive at
every family s with OffRide (Sender.AddsAt). -/
theorem addsAt_off (hf : sendFits P ride = true) (hZ : RidesZero ride) (s : CoinN P ride → GF)
    (hs : OffRide P ride s) : (sender P ride).AddsAt s :=
  fun a => layN_add_off hf hZ a s hs

theorem offRide_zero : OffRide P ride 0 := fun _ _ => rfl

theorem offRide_add {s s' : CoinN P ride → GF} (h : OffRide P ride s) (h' : OffRide P ride s') :
    OffRide P ride (s + s') := fun n hn => by
  rw [Pi.add_apply, h n hn, h' n hn, add_zero]

theorem offRide_sum {ι : Type} (T : Finset ι) (f : ι → CoinN P ride → GF)
    (h : ∀ a ∈ T, OffRide P ride (f a)) : OffRide P ride (∑ a ∈ T, f a) := fun n hn => by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha n hn

theorem offRide_single [DecidableEq (CoinN P ride)] (n : CoinN P ride) (hn : ride n.1 = none)
    (x : GF) : OffRide P ride (Pi.single n x) := fun n' hn' => by
  rw [Pi.single_apply, if_neg fun e => hn' (by rw [e, hn])]

variable (ds : List Fmt.Drawn)

/-- The message coins' contribution to the instance's answers (wt) at the weights wOf, stated with
the types CoinN and AnsN. -/
def wtN (s : CoinN P ride → GF) (a : AnsN P) : GF := (sender P ride).form (wOf P ds a) (layN s)

/-- If the job fits its place (sendFits) and RidesZero holds, wtN (s + s') = wtN s + wtN s' for
every family s' with OffRide. -/
theorem wt_add_off (hf : sendFits P ride = true) (hZ : RidesZero ride)
    (s s' : CoinN P ride → GF) (hs' : OffRide P ride s') :
    wtN ds (s + s') = wtN ds s + wtN ds s' := by
  funext a
  show (sender P ride).form (wOf P ds a) (layN (s + s')) = _
  rw [layN_add_off hf hZ s s' hs']
  exact Sender.form_add (S := sender P ride) (wOf P ds a) (layN s) (layN s')

/-- Under the same two premises, the family 0 contributes 0 to every answer. -/
theorem wt_zero_off (hf : sendFits P ride = true) (hZ : RidesZero ride) :
    wtN (P := P) (ride := ride) ds 0 = 0 := by
  have h := wt_add_off ds hf hZ 0 0 offRide_zero
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- Under the same two premises, wtN of a finite sum of families with OffRide is the sum of their
wtN. -/
theorem wt_sum_off (hf : sendFits P ride = true) (hZ : RidesZero ride) {ι : Type} (T : Finset ι)
    (f : ι → CoinN P ride → GF) (h : ∀ a ∈ T, OffRide P ride (f a)) :
    wtN ds (∑ a ∈ T, f a) = ∑ a ∈ T, wtN ds (f a) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using wt_zero_off ds hf hZ
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (f a),
      wt_add_off ds hf hZ _ _ (h a (Finset.mem_insert_self a T)),
      ih fun b hb => h b (Finset.mem_insert_of_mem hb), add_comm]

/-- Proof of Spec.mendsOf. The family is the sum, over the answers a, of the value v a at the coin
that share_of gives for a. The premise seedsFit is not used. -/
theorem mendsOf : Spec.mendsOf := by
  intro P ride ds hf hZ _ hβ v
  classical
  choose pad hpad using fun a : AnsN P => share_of ds hf hβ a.1 a.2.1 a.2.2
  have hoff : ∀ a ∈ (Finset.univ : Finset (AnsN P)),
      OffRide P ride (Pi.single (pad a) (v a) : CoinN P ride → GF) := fun a _ =>
    offRide_single _ (by
      rw [(hpad a).1]
      exact fits_noRide P ride a.1 hf a.1.isLt (by have := a.2.1.isLt; omega)) _
  refine ⟨(∑ a : AnsN P, (Pi.single (pad a) (v a) : CoinN P ride → GF) : CoinN P ride → GF),
    addsAt_off hf hZ _ (offRide_sum _ _ hoff), ?_⟩
  show wtN ds (∑ a : AnsN P, (Pi.single (pad a) (v a) : CoinN P ride → GF)) = v
  rw [wt_sum_off ds hf hZ _ _ hoff]
  funext b
  rw [Finset.sum_apply, Finset.sum_eq_single b]
  · have h := (hpad b).2 b.1 b.2.1 b.2.2 (v b)
    rw [if_pos ⟨rfl, rfl, rfl⟩] at h
    exact h
  · intro a _ hne
    have h := (hpad a).2 b.1 b.2.1 b.2.2 (v a)
    rw [if_neg fun hh => hne (ans_ext b a hh.1 hh.2.1 hh.2.2).symm] at h
    exact h
  · intro h
    exact absurd (Finset.mem_univ b) h

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.addsAt_off
#print axioms OnBytes.SendSim.At.mendsOf
