-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ClearOfMask.lean: if the job fits its place, the challenge consists of exactly
the seeds and no seed's factor is 0, the condition MaskSpender on a book implies that the instance
has pads at which the sets of spent and known coins satisfy the general model's condition
Sender.Clear. The proof of Spec.clearOfMask.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for Sender.Clear,
Johnson/SendSim/Pads.lean; sender, wOf, slot, name, number: Johnson/SendSim/At/Bridge.lean. Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves. The lemmas are about sets of names, numbers of slots and contributions; no
distribution is named. MaskSpender is one of the three cases of SpenderClear
(Johnson/SendSim/At/Fresh.lean, "clear").
  clearOfMask  Spec.clearOfMask, the statement of the title, which is written out in
               Johnson/SendSim/At/ClearOf.lean.

Limits. The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. Johnson/SendSim/At/ClearOfFold.lean uses clearOfMask for mendsOffOf, which gives the
model's premise MendsOff for rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The three sets spentN,
knownN and knownT are in ClearOf.lean too; Sender.Reads is in Johnson/SendSim/Pads.lean. The proof
rests on padsAt (Johnson/SendSim/At/PadSeat.lean), on lay_other_msg, lay_cell and wt_other_msg
(Johnson/SendSim/At/Single.lean), and on free_lt and free_not_pad
(Johnson/Desc/ProofFile/Honest/K1/Fence.lean).

The other names.
  mem_namesOf, mem_tailsOf   membership in namesOf and tailsOf, written out.
  spent_mask, spent_free   under MaskSpender, which slot, oracle message and number a name in spentN
               has.
  reads_spent  if the job fits its place, under MaskSpender: the oracle message of an answer to
               which a coin in spentN contributes (Sender.Reads) has mask rows and a spent free
               entry.
  known_tail   the number of a name in knownT in a mask row is maskTailNo and is among the known
               numbers.

Notes. seedsFit is a premise of Spec.clearOfMask. The proof does not use it.
-/
import Johnson.Desc.ProofFile.Honest.K1.Fence
import Johnson.SendSim.At.ClearOf
import Johnson.SendSim.At.PadSeat

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride}

/-- A name is in namesOf NE NF exactly if its coin, by field and number, is in the pair NE, NF. -/
theorem mem_namesOf (NE NF : Finset ℕ) (n : CoinN P ride) :
    n ∈ namesOf P ride NE NF ↔
      inNos NE NF ((seatC P ride n).1.inE (shapeAt P n.1)) ((seatC P ride n).1.no P ride n.1) := by
  simp only [namesOf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same for a tail coin's name and tailsOf. -/
theorem mem_tailsOf (NE NF : Finset ℕ) (x : TailN P) :
    x ∈ tailsOf P ride NE NF ↔
      inNos NE NF ((seatT P x.1 x.2.val).1.inE (shapeAt P x.1.1))
        ((seatT P x.1 x.2.val).1.no P ride x.1.1) := by
  simp only [tailsOf, Finset.mem_filter, Finset.mem_univ, true_and]

variable {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

/-- Under MaskSpender, a name u in spentN has a coin in the extension field whose number is among
the spent numbers; its oracle message is not sent along and has an answer; and its slot is a mask
coin whose number j is below freeMaskEntries. -/
theorem spent_mask (M : MaskSpender P ride Bk ord o p) (u : CoinN P ride)
    (hu : u ∈ spentN P ride Bk o p) :
    (seatC P ride u).1.inE (shapeAt P u.1) = true ∧
      (seatC P ride u).1.no P ride u.1 ∈ eAll (Bk.spentBy o p) ∧
      ride u.1 = none ∧ (shapeAt P u.1).answers ≠ 0 ∧
      ∃ j, (seatC P ride u).1 = .mask j ∧
        j < OnBytes.Send.freeMaskEntries (shapeAt P u.1).maskRows (maskCodeAt P u.1).ell
          (shapeAt P u.1).answers := by
  have h := (mem_namesOf _ _ u).1 hu
  unfold inNos at h
  cases hE : (seatC P ride u).1.inE (shapeAt P u.1)
  · rw [hE, M.noF] at h
    simp at h
  · rw [hE, if_pos rfl] at h
    obtain ⟨k, hk, hr, ha, hfree⟩ := M.free _ h
    unfold freeNo at hfree
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 hfree
    have hj' := Finset.mem_range.1 hj
    have hy : (Seat.mask j).ok P.codes (shapeAt P k) (ride k) := by
      show j < (stepsOf P.codes (shapeAt P k) (ride k)).mask
      have := free_lt _ _ _ j (Nat.pos_of_ne_zero ha) hj'
      simpa [stepsOf, hr] using this
    obtain ⟨e1, e2⟩ := seat_inj P ride u.1 k _ (.mask j) (seatC_ok P ride u) hy hE
      (by rw [no_mask]; exact e.symm)
    rw [← e1] at hr ha hj'
    exact ⟨rfl, h, hr, ha, j, e2, hj'⟩

/-- Under MaskSpender, a name u in spentN is a mask coin j of an oracle message that is not sent
along, has an answer and has mask rows, and maskStart + j is in freeNo and among the spent numbers.
-/
theorem spent_free (M : MaskSpender P ride Bk ord o p) (u : CoinN P ride)
    (hu : u ∈ spentN P ride Bk o p) :
    ride u.1 = none ∧ (shapeAt P u.1).answers ≠ 0 ∧ (shapeAt P u.1).maskRows ≠ 0 ∧
      ∃ j, (seatC P ride u).1 = .mask j ∧
      maskStart P ride u.1 + j ∈ freeNo P ride u.1 ∧
      maskStart P ride u.1 + j ∈ eAll (Bk.spentBy o p) := by
  obtain ⟨-, hno, hr, ha, j, hs, hj⟩ := spent_mask M u hu
  rw [hs, no_mask] at hno
  refine ⟨hr, ha, fun h0 => ?_, j, hs, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩, hno⟩
  unfold OnBytes.Send.freeMaskEntries at hj
  rw [h0] at hj
  simp at hj

/-- For a name x in knownT whose row is a mask row: the number maskTailNo of that entry of the row's
tail is among the known numbers, and the entry is below the mask code's r. -/
theorem known_tail (x : TailN P) (hx : x ∈ knownT P ride Bk ord o p) (hm : tbOf x.1 = .mask) :
    maskTailNo P ride x.1.1 (rowOf x.1) x.2.val ∈ eAll (Bk.knownBy ord o p) ∧
      x.2.val < (maskCodeAt P x.1.1).r := by
  obtain ⟨⟨k, v⟩, q⟩ := x
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · cases hm
  · have h := (mem_tailsOf _ _ _).1 hx
    unfold inNos at h
    have h' : (Seat.maskTail r.val q.val).no P ride k ∈ eAll (Bk.knownBy ord o p) := h
    rw [no_maskTail] at h'
    exact ⟨h', q.isLt⟩

variable (ds : List Fmt.Drawn)

/-- If the job fits its place (sendFits) and MaskSpender holds: if some coin in spentN contributes
to the answer a (Sender.Reads), then a's oracle message has mask rows, and some number in its freeNo
is among the spent numbers. -/
theorem reads_spent (hf : sendFits P ride = true) (M : MaskSpender P ride Bk ord o p) (a : AnsN P)
    (hR : (sender P ride).Reads (wOf P ds) (spentN P ride Bk o p) a) :
    (shapeAt P a.1).maskRows ≠ 0 ∧ ∃ j, maskStart P ride a.1 + j ∈ freeNo P ride a.1 ∧
      maskStart P ride a.1 + j ∈ eAll (Bk.spentBy o p) := by
  obtain ⟨u, hu, x, hx⟩ := hR
  have hk : a.1 = (show CoinN P ride from u).1 := by
    by_contra h
    exact hx (wt_other_msg (inst := (sender P ride).decCn) ds hf u x a h)
  obtain ⟨-, -, hz, j, -, h1, h2⟩ := spent_free M u hu
  rw [← hk] at hz h1 h2
  exact ⟨hz, j, h1, h2⟩

/-- Proof of Spec.clearOfMask, with the pads of padsAt. -/
theorem clearOfMask : Spec.clearOfMask := by
  intro P ride ds Bk ord o p hf _ hβ M
  obtain ⟨Pd, hPd⟩ := padsAt ds hf hβ
  refine ⟨Pd, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu hk
    obtain ⟨hE, hno, -⟩ := spent_mask M u hu
    have h := (mem_namesOf _ _ u).1 hk
    unfold inNos at h
    rw [hE, if_pos rfl] at h
    exact Finset.disjoint_left.1 M.unknown hno h
  · intro a hu
    obtain ⟨-, -, -, -, j, hs, hj⟩ := spent_mask M (Pd.pad a) hu
    rw [hPd.seat a] at hs
    rw [hPd.msg a] at hj
    by_cases hz : (shapeAt P a.1).maskRows = 0
    · obtain ⟨n, hn⟩ := padSeat_main (P := P) a.1 a.2.1 a.2.2 hz
      rw [hn] at hs
      cases hs
    · unfold padSeat at hs
      rw [if_neg hz] at hs
      exact free_not_pad _ _ _ a.2.1.val j hj (Seat.mask.inj hs).symm
  · intro a hR hk
    obtain ⟨hz, j, h1, h2⟩ := reads_spent ds hf M a hR
    have ha : (shapeAt P a.1).answers ≠ 0 := by have := a.2.1.isLt; omega
    have hc := (M.clear a.1 j a.1.isLt (fits_noRide P ride a.1 hf a.1.isLt ha) ha h1 h2).1 a.2.1
      a.2.1.isLt
    have h := (mem_namesOf _ _ (Pd.pad a)).1 hk
    rw [hPd.seat a, hPd.msg a] at h
    obtain ⟨hE, hno⟩ := padSeat_mask (ride := ride) a.1 a.2.1 a.2.2 hz
    unfold inNos at h
    rw [hE, if_pos rfl, hno] at h
    exact hc h
  · intro x hx u hu a j _
    by_contra hne
    have hk : (show TailN P from x).1.1 = (show CoinN P ride from u).1 := by
      by_contra h
      exact hne (lay_other_msg (inst := (sender P ride).decCn) hf u a x.1 j h)
    obtain ⟨hr, ha, -, ju, hs, h1, h2⟩ := spent_free M u hu
    rw [← hk] at hr ha h1 h2
    have hp : (seatC P ride u).1.place P.codes (shapeAt P (show TailN P from x).1.1)
        (ride (show TailN P from x).1.1) = (tbOf x.1, rowOf x.1, j) := by
      by_contra h
      exact hne (lay_cell (inst := (sender P ride).decCn) hf u a x.1 j hr h)
    rw [hs] at hp
    obtain ⟨hkn, hq⟩ := known_tail x hx (congrArg Prod.fst hp).symm
    rw [← show _ = rowOf (show TailN P from x).1 from congrArg (fun z => z.2.1) hp] at hkn
    exact ((M.clear _ ju (show TailN P from x).1.1.isLt hr ha h1 h2).2 _ hq).1 hkn
  · intro x hx a hR b j _
    by_contra hne
    have hk : (show TailN P from x).1.1 = a.1 := by
      by_contra h
      exact hne (lay_other_msg (inst := (sender P ride).decCn) hf (Pd.pad a) b x.1 j
        (by rw [hPd.msg a]; exact h))
    obtain ⟨hz, ju, h1, h2⟩ := reads_spent ds hf M a hR
    have ha : (shapeAt P a.1).answers ≠ 0 := by have := a.2.1.isLt; omega
    have hr : ride a.1 = none := fits_noRide P ride a.1 hf a.1.isLt ha
    rw [← hk] at hr ha h1 h2 hz
    have hp : (seatC P ride (Pd.pad a)).1.place P.codes (shapeAt P (show TailN P from x).1.1)
        (ride (show TailN P from x).1.1) = (tbOf x.1, rowOf x.1, j) := by
      by_contra h
      exact hne (lay_cell (inst := (sender P ride).decCn) hf (Pd.pad a) b x.1 j hr h)
    rw [hPd.seat a, hk,
      padSeat_place hf a.1 a.2.1 a.2.2 a.1.isLt a.2.1.isLt (by rw [← hk]; exact hz)] at hp
    obtain ⟨hkn, hq⟩ := known_tail x hx (congrArg Prod.fst hp).symm
    have hrow : rowOf (show TailN P from x).1 =
        (shapeAt P (show TailN P from x).1.1).maskRows - 1 :=
      (congrArg (fun z => z.2.1) hp).symm.trans (by rw [hk])
    rw [hrow] at hkn
    exact ((M.clear _ ju (show TailN P from x).1.1.isLt hr ha h1 h2).2 _ hq).2 hkn

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.clearOfMask
