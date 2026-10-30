-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ClearOfFold.lean: if the job fits its place, the challenge consists of exactly
the seeds and no seed's factor is 0, the condition FoldSpender on a book implies the general model's
condition Sender.Clear at some pads, and MaskSpender or FoldSpender implies the model's premise
MendsOff. The proofs of Spec.clearOfFold and Spec.mendsOffOf.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for MendsOff,
Johnson/SendSim/Defs.lean; sender, wOf, slot, name, number: Johnson/SendSim/At/Bridge.lean. Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves. The lemmas are about sets of names, numbers of slots and contributions; no
distribution is named. Both statements are written out in Johnson/SendSim/At/ClearOf.lean.
  mendsOffOf   Spec.mendsOffOf: under MaskSpender or FoldSpender, the model's premise MendsOff.
  clearOfFold  Spec.clearOfFold: under FoldSpender, Sender.Clear at some pads.

Limits. The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. Johnson/SendSim/At/JoinRows.lean uses mendsOffOf as the premise MendsOff of sendFresh,
for rowsFresh (Johnson/SendSim/At/RowsFresh.lean). Johnson/SendSim/At/FoldAny.lean uses the four
helpers below for rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean). The proofs rest on padsAt
(Johnson/SendSim/At/PadSeat.lean), clearOfMask (Johnson/SendSim/At/ClearOfMask.lean), additive_paid
(Johnson/SendSim/At/Paid.lean) and Sender.mendsOff_of_clear (Johnson/SendSim/Pads.lean).

The other names.
  spent_fold   if p spends by one entry, the first R.count mask coins of oracle message k, which is
               the table R that is sent along, then a name in spentN is a coin of k in the extension
               field.
  no_reads     in that case, if the job fits its place, no coin in spentN contributes to any answer.
  mask_of_ride   if the job fits its place, a row of a table that is sent along is a mask row.
  rowOf_lt     a mask row's number is below its oracle message's number of mask rows.

Notes. FoldSpender requires that the table has one row (R.h = 0). The proof of clearOfFold does not
use that, nor seedsFit.
-/
import Johnson.SendSim.At.ClearOfMask
import Johnson.SendSim.At.Paid

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

/-- If oracle message k is the table R that is sent along, and p spends by the one entry e, which
holds R.count coins of the extension field from maskStart P ride k on, then a name u in spentN is a
coin of oracle message k, in the extension field, whose number is among the spent numbers. -/
theorem spent_fold (k : ℕ) (R : Ride) (e : Ahead) (hr : ride k = some R)
    (hsp : Bk.spentBy o p = [e]) (hc : e.count = ⟨0, R.count⟩)
    (hst : e.start.e = maskStart P ride k) (u : CoinN P ride) (hu : u ∈ spentN P ride Bk o p) :
    u.1.val = k ∧ (seatC P ride u).1.inE (shapeAt P u.1) = true ∧
      (seatC P ride u).1.no P ride u.1 ∈ eAll (Bk.spentBy o p) := by
  have h := (mem_namesOf _ _ u).1 hu
  unfold inNos at h
  cases hE : (seatC P ride u).1.inE (shapeAt P u.1)
  · rw [hE, hsp] at h
    simp [fAll, fOf, hc] at h
  · rw [hE, if_pos rfl] at h
    have h' := h
    rw [hsp] at h'
    simp only [eAll, List.foldr_cons, List.foldr_nil, Finset.union_empty, eOf, hc, hst,
      Finset.mem_Ico] at h'
    obtain ⟨i, hi⟩ : ∃ i, (seatC P ride u).1.no P ride u.1 = maskStart P ride k + i :=
      ⟨_, (Nat.add_sub_cancel' h'.1).symm⟩
    have hy : (Seat.mask i).ok P.codes (shapeAt P k) (ride k) := by
      show i < (stepsOf P.codes (shapeAt P k) (ride k)).mask
      have : i < R.count := by omega
      simpa [stepsOf, hr] using this
    exact ⟨(seat_inj P ride u.1 k _ (.mask i) (seatC_ok P ride u) hy hE
      (by rw [no_mask]; exact hi)).1, rfl, h⟩

/-- If the job fits its place (sendFits), a row of an oracle message that is sent along is a mask
row. -/
theorem mask_of_ride (hf : sendFits P ride = true) (ρ : RowN P) (R : Ride)
    (hr : ride ρ.1 = some R) : tbOf ρ = .mask := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · exfalso
    have hfit := fits_ride P ride k R hf k.isLt hr
    simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
    have := r.isLt
    omega
  · rfl

/-- A mask row's number is below its oracle message's number of mask rows. -/
theorem rowOf_lt (ρ : RowN P) (h : tbOf ρ = .mask) : rowOf ρ < (shapeAt P ρ.1).maskRows := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · cases h
  · exact r.isLt

/-- Under the premises of spent_fold, if the job fits its place (sendFits), no coin in spentN
contributes to any answer of the instance (Sender.Reads is false). -/
theorem no_reads (ds : List Fmt.Drawn) (hf : sendFits P ride = true) (k : ℕ) (R : Ride) (e : Ahead)
    (hr : ride k = some R) (hsp : Bk.spentBy o p = [e]) (hc : e.count = ⟨0, R.count⟩)
    (hst : e.start.e = maskStart P ride k) (a : AnsN P) :
    ¬ (sender P ride).Reads (wOf P ds) (spentN P ride Bk o p) a := by
  rintro ⟨u, hu, x, hx⟩
  have hk : a.1 = (show CoinN P ride from u).1 := by
    by_contra h
    exact hx (wt_other_msg (inst := (sender P ride).decCn) ds hf u x a h)
  have h1 := (spent_fold k R e hr hsp hc hst u hu).1
  have h2 : ride a.1 = none := fits_noRide P ride a.1 hf a.1.isLt (by have := a.2.1.isLt; omega)
  rw [hk, h1, hr] at h2
  cases h2

/-- Proof of Spec.clearOfFold, with the pads of padsAt. It uses neither seedsFit nor FoldSpender's
clause that the table has one row. -/
theorem clearOfFold : Spec.clearOfFold := by
  intro P ride ds Bk ord o p hf _ hβ F
  obtain ⟨k, R, e, _, hr, _, hsp, hc, hst, htl⟩ := F.one
  obtain ⟨Pd, hPd⟩ := padsAt ds hf hβ
  refine ⟨Pd, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu hk
    obtain ⟨-, hE, hno⟩ := spent_fold k R e hr hsp hc hst u hu
    have h := (mem_namesOf _ _ u).1 hk
    unfold inNos at h
    rw [hE, if_pos rfl] at h
    exact Finset.disjoint_left.1 F.unknown hno h
  · intro a hu
    have h1 := (spent_fold k R e hr hsp hc hst (Pd.pad a) hu).1
    have h2 : ride a.1 = none := fits_noRide P ride a.1 hf a.1.isLt (by have := a.2.1.isLt; omega)
    rw [hPd.msg a] at h1
    rw [h1, hr] at h2
    cases h2
  · intro a hR
    exact absurd hR (no_reads ds hf k R e hr hsp hc hst a)
  · intro x hx u hu a j _
    by_contra hne
    have hk : (show TailN P from x).1.1 = (show CoinN P ride from u).1 := by
      by_contra h
      exact hne (lay_other_msg (inst := (sender P ride).decCn) hf u a x.1 j h)
    have h1 : ((show TailN P from x).1.1 : ℕ) = k := by
      rw [hk]
      exact (spent_fold k R e hr hsp hc hst u hu).1
    subst h1
    have hm := mask_of_ride hf (show TailN P from x).1 R hr
    obtain ⟨hkn, hq⟩ := known_tail x hx hm
    exact htl _ (rowOf_lt _ hm) _ hq hkn
  · intro x _ a hR
    exact absurd hR (no_reads ds hf k R e hr hsp hc hst a)

/-- Proof of Spec.mendsOffOf: Sender.mendsOff_of_clear at the pads of clearOfMask or of clearOfFold.
-/
theorem mendsOffOf : Spec.mendsOffOf := by
  intro P ride ds Bk ord o p hf hs hβ h
  rcases h with M | F
  · obtain ⟨Pd, hC⟩ := clearOfMask P ride ds Bk ord o p hf hs hβ M
    exact Sender.mendsOff_of_clear (additive_paid P ride hf) Pd hC
  · obtain ⟨Pd, hC⟩ := clearOfFold P ride ds Bk ord o p hf hs hβ F
    exact Sender.mendsOff_of_clear (additive_paid P ride hf) Pd hC

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.clearOfFold
#print axioms OnBytes.SendSim.At.mendsOffOf
