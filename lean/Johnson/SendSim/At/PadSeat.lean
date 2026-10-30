-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/PadSeat.lean: the slot of each answer's pad as an explicit term (padSeat); and,
if the job fits its place and no seed's factor is 0, pads of the instance (Sender.Pads) that are at
these slots.
Terms: Johnson/SendSim/At/Sim.lean; padNo: Johnson/SendSim/At/Fresh.lean; sender, slot, name,
number, the instance's answers: Johnson/SendSim/At/Bridge.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Algebra; no distribution is named.
  padSeat        For the name (k, i, s) of an answer, the slot and coordinate of the answer's coin.
                 With mask rows it is the mask coin at entry ell - answers + i of the last mask row,
                 with the coordinate s. Without, it is the pad's coin number e * i + t in the last
                 main row: t = 0 with the coordinate s over the extension field, t = s with the
                 coordinate 0 over the base field.
  padsAt         If the job fits its place (sendFits) and no seed's factor is 0, the instance has
                 pads Pd with PadsAt: the pad of each answer a is a coin of a's oracle message at
                 the slot and coordinate padSeat.
  share_at       Under the same premises, a name at a slot with PadFacts for (k, i, s) contributes
                 its value to the answer (k, i, s) and 0 to every other answer.
  padSeat_facts  If the job fits its place, padSeat has PadFacts.
  padSeat_mask, padSeat_place   With mask rows: the coin is in the extension field and its number is
                 padNo; if the job fits its place, the slot is located in the last mask row.
  padSeat_main   Without mask rows: the slot is an entry of a pad in a main row.

Limits. The names at the slots padSeat are obtained by choice (exists_name,
Johnson/SendSim/At/Names.lean).

How it fits. Johnson/SendSim/At/ClearOfMask.lean, Johnson/SendSim/At/ClearOfFold.lean and
Johnson/SendSim/At/FoldAny.lean take their pads from padsAt, for rowsFresh
(Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean).
Spec.padsOf (Johnson/SendSim/At/Bridge.lean) states only that pads exist. The model's condition on
the spent and the known coins (Sender.Clear) speaks of the pads themselves, so it needs to know
which coin is an answer's pad; padsAt keeps that. The proof of share_at is that of share_of
(Johnson/SendSim/At/PadsOf.lean), at a slot that is given as an argument. PadFacts is defined in
Johnson/SendSim/At/PadAt.lean, Sender.Pads and Sender.Clear in Johnson/SendSim/Pads.lean.
-/
import Johnson.SendSim.At.Single

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The slot and the coordinate of the coin of the instance's answer (k, i, s): with mask rows a
mask coin in the last mask row, without them a coin of the pad in the last main row. -/
def padSeat (k i : ℕ) (s : Fin 3) : Seat × ℕ :=
  if (shapeAt P k).maskRows = 0 then
    (if (shapeAt P k).mainDeg == 3 then (.pad ((K1.Msg.of P.codes (shapeAt P k)).e * i + 0), s.val)
      else (.pad ((K1.Msg.of P.codes (shapeAt P k)).e * i + s.val), 0))
  else
    (.mask
      (((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) *
        (shapeAt P k).maskRows + ((shapeAt P k).maskRows - 1)), s.val)

variable {P ride}

/-- If the job fits its place (sendFits), k < P.sent.size and i is an answer of oracle message k,
then padSeat P k i s has PadFacts for some t, tb, r and j. -/
theorem padSeat_facts (hf : sendFits P ride = true) (k i : ℕ) (s : Fin 3) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) :
    ∃ t tb r j, PadFacts P ride k i s (padSeat P k i s).1 (padSeat P k i s).2 t tb r j := by
  unfold padSeat
  by_cases hz : (shapeAt P k).maskRows = 0
  · rw [if_pos hz]
    have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = false := by
      show ((shapeAt P k).maskRows != 0) = false
      simp [hz]
    by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · rw [if_pos h3]
      have he : (K1.Msg.of P.codes (shapeAt P k)).e = 1 := by
        unfold K1.Msg.e
        rw [hK, Bool.false_or]
        exact if_pos h3
      exact ⟨_, _, _, _, pad_facts_main hf k i s hk hi hz s.val 0 (by rw [he]; norm_num) s.isLt
        (Or.inl ⟨h3, rfl, rfl⟩)⟩
    · rw [if_neg h3]
      have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
      have he : (K1.Msg.of P.codes (shapeAt P k)).e = 3 := by
        unfold K1.Msg.e
        rw [hK, Bool.false_or]
        exact if_neg h3
      exact ⟨_, _, _, _, pad_facts_main hf k i s hk hi hz 0 s.val (by rw [he]; exact s.isLt)
        (by norm_num) (Or.inr ⟨h3', rfl, rfl⟩)⟩
  · rw [if_neg hz]
    exact ⟨_, _, _, _, pad_facts_mask hf k i s hk hi hz⟩

/-- If oracle message k has mask rows, the coin at padSeat is in the extension field and its number
is padNo P ride k i. -/
theorem padSeat_mask (k i : ℕ) (s : Fin 3) (hz : (shapeAt P k).maskRows ≠ 0) :
    (padSeat P k i s).1.inE (shapeAt P k) = true ∧
      (padSeat P k i s).1.no P ride k = padNo P ride k i := by
  unfold padSeat
  rw [if_neg hz]
  exact ⟨rfl, no_mask k _⟩

/-- If the job fits its place (sendFits), k < P.sent.size, i is an answer of oracle message k and it
has mask rows, padSeat is located at entry ell - answers + i of the last mask row. -/
theorem padSeat_place (hf : sendFits P ride = true) (k i : ℕ) (s : Fin 3) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) (hz : (shapeAt P k).maskRows ≠ 0) :
    (padSeat P k i s).1.place P.codes (shapeAt P k) (ride k) = (.mask, (shapeAt P k).maskRows - 1,
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) := by
  unfold padSeat
  rw [if_neg hz]
  exact (pad_facts_mask hf k i s hk hi hz).place

/-- If oracle message k has no mask row, padSeat is an entry of a pad in a main row. -/
theorem padSeat_main (k i : ℕ) (s : Fin 3) (hz : (shapeAt P k).maskRows = 0) :
    ∃ n, (padSeat P k i s).1 = .pad n := by
  unfold padSeat
  rw [if_pos hz]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

variable [inst : DecidableEq (CoinN P ride)] (ds : List Fmt.Drawn)

/-- If the job fits its place (sendFits), no seed's factor is 0, PadFacts holds for (k, i, s) at the
slot y and coordinate co, and n is a name of oracle message k at (y, co), then the family with the
value x at n and 0 elsewhere contributes x to the answer (k, i, s) and 0 to every other answer. -/
theorem share_at (hf : sendFits P ride = true) (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0)
    (k : Fin P.sent.size) (i : Fin (shapeAt P k).answers) (s : Fin 3) (y : Seat) (co t : ℕ)
    (tb : Rd) (r j : ℕ) (F : PadFacts P ride k i s y co t tb r j) (n : CoinN P ride)
    (hn : n.1 = k) (hs : seatC P ride n = (y, co)) (k' : Fin P.sent.size)
    (i' : Fin (shapeAt P k').answers) (s' : Fin 3) (x : GF) :
    (sender P ride).wt (wOf P ds) (Pi.single n x : CoinN P ride → GF) ⟨k', (i', s')⟩ =
      if k'.val = k.val ∧ i'.val = i.val ∧ s' = s then x else 0 := by
  have hr' : ride k' = none := fits_noRide P ride k' hf k'.isLt (by have := i'.isLt; omega)
  have hy : (seatC P ride n).1 = y := by rw [hs]
  rw [wt_eq P ride ds hf]
  by_cases hk : k' = k
  · subst hk
    rw [form_one P.codes (shapeAt P k') _ _ _ _ tb F.tbs r j F.rlt F.jlt
      fun tb' r' j' ht hne => rd_single hf n x k' hr' tb' ht r' j' fun h => hne (by
        rw [← h.2, hy, F.place]), F.part, F.idx,
      K1.Msg.weight_pad _ _ _ i'.val i.val t i.isLt F.tlt]
    by_cases hi : i.val = i'.val
    · have hb : readE (seedAt P ds i'.val).2 ≠ 0 :=
        hβ _ (seedAt_mem P ds k' i'.val k'.isLt i'.isLt)
      rw [if_pos hi, mul_assoc]
      unfold bInv
      rw [inv_mul_cancel_left₀ hb, rd_single_at hf k' hr' i s y co t tb r j F n hn hs x s']
      by_cases e : s' = s
      · rw [if_pos e, if_pos ⟨rfl, hi.symm, e⟩]
      · rw [if_neg e, if_neg fun h => e h.2.2]
    · rw [if_neg hi, zero_mul, mul_zero, crd_zero, if_neg fun h => hi h.2.1.symm]
  · rw [form_none P.codes (shapeAt P k') _ _ _ _
      (fun r' j' => rd_single hf n x k' hr' .main (.inl rfl) r' j' fun h => hk (h.1.trans hn))
      (fun r' j' => rd_single hf n x k' hr' .mask (.inr rfl) r' j' fun h => hk (h.1.trans hn)),
      mul_zero, crd_zero, if_neg fun h => hk (Fin.ext h.1)]

omit inst in
/-- Pads of the instance that are at padSeat: the pad of each answer a is a coin of a's oracle
message (msg), and its slot and coordinate are padSeat at a (seat). -/
structure PadsAt (Pd : (sender P ride).Pads (wOf P ds)) : Prop where
  msg : ∀ a : AnsN P, (show CoinN P ride from Pd.pad a).1 = a.1
  seat : ∀ a : AnsN P, seatC P ride (Pd.pad a) = padSeat P a.1 a.2.1 a.2.2

omit inst in
/-- If the job fits its place (sendFits) and no seed's factor is 0, the instance has pads with
PadsAt. -/
theorem padsAt (hf : sendFits P ride = true) (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) :
    ∃ Pd : (sender P ride).Pads (wOf P ds), PadsAt ds Pd := by
  have ex : ∀ a : AnsN P, ∃ n : CoinN P ride, n.1 = a.1 ∧
      seatC P ride n = padSeat P a.1 a.2.1 a.2.2 := fun a => by
    obtain ⟨t, tb, r, j, F⟩ := padSeat_facts hf a.1 a.2.1 a.2.2 a.1.isLt a.2.1.isLt
    exact exists_name P ride a.1 _ _ F.ok F.inMsg F.co3 F.co0
  choose pad hpad using ex
  refine ⟨⟨pad, fun _ => 1, fun _ => one_ne_zero, fun a b x => ?_⟩, ⟨fun a => (hpad a).1,
    fun a => (hpad a).2⟩⟩
  obtain ⟨t, tb, r, j, F⟩ := padSeat_facts hf b.1 b.2.1 b.2.2 b.1.isLt b.2.1.isLt
  have h : (sender P ride).wt (wOf P ds) (Pi.single (pad b) x) a = _ :=
    share_at (inst := (sender P ride).decCn) ds hf hβ b.1 b.2.1 b.2.2 _ _ t tb r j F (pad b)
      (hpad b).1 (hpad b).2 a.1 a.2.1 a.2.2 x
  rw [h, one_mul]
  by_cases e : a = b
  · subst e
    rw [if_pos ⟨rfl, rfl, rfl⟩, if_pos rfl]
  · rw [if_neg e, if_neg fun hh => e (ans_ext a b hh.1 hh.2.1 hh.2.2)]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.padSeat_facts
#print axioms OnBytes.SendSim.At.share_at
#print axioms OnBytes.SendSim.At.padsAt
