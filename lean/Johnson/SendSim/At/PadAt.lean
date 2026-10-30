-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/PadAt.lean: if the job fits its place, then for each name of an answer of the
instance (oracle message k, answer i, coordinate s) there is a slot that holds the answer's pad, and
its entry has K1's own index of that pad's entry (K1.Msg.padIdx).
Terms: Johnson/SendSim/At/Sim.lean; slot, name: Johnson/SendSim/At/Bridge.lean, "Terms of the
instance". Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions, and arithmetic on public numbers.
  PadFacts       What is stated, for the name (k, i, s), of a slot y, a coordinate co, a power t of
                 θ, and the array tb, row r and entry j at which the slot is located. The twelve
                 fields are described one by one at the structure. The main one, idx: the index of
                 that entry is K1.Msg.padIdx i t.
  pad_facts      If the job fits its place (sendFits), k < P.sent.size and i is an answer of oracle
                 message k, then some y, co, t, tb, r, j have PadFacts.
  pad_facts_mask   Under the same premises, with mask rows: the pad of answer i is the mask coin at
                 entry ell - answers + i of the last mask row, with its three coordinates.
  pad_facts_main   Under the same premises, with no mask row: it is the pad's coin number e * i + t
                 in the last main row. Over the extension field e = 1, t = 0, with three
                 coordinates; over the base field e = 3, t = s, with the coordinate 0.
  pad_count      With no mask row and at least one answer, the pad has e coins for each answer.
  partOf, rowsOf, lenOf   for an array: K1's part (main or mask), the number of its rows, and the
                 logarithm of its rows' length.

How it fits. Johnson/SendSim/At/PadsOf.lean uses pad_facts for share_of, so for mendsOf and
rowsExact (Johnson/SendSim/At/RowsExact.lean). Johnson/SendSim/At/PadSeat.lean uses pad_facts_mask
and pad_facts_main for padsAt, so for rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The proofs rest
on what sendFits implies for one oracle message (fits_pad and its neighbours,
Johnson/Desc/ProofFile/Honest/K1/PadLaw.lean). K1.Msg.padIdx is defined in
Johnson/Desc/K1/Law/Means2.lean; the arrays (Rd) in Johnson/Desc/ProofFile/Honest/K1/NoOther.lean.
-/
import Johnson.SendSim.At.Cells
import Johnson.SendSim.At.Seeds

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- K1's part (main or mask) of one of the four arrays of an oracle message's rows. -/
def partOf : Rd → Part
  | .mask | .maskTl => .mask
  | .main | .mainTl => .main

/-- The number of rows of an array: the oracle message's main rows or its mask rows. -/
def rowsOf (s : OracleShape) : Rd → ℕ
  | .mask | .maskTl => s.maskRows
  | .main | .mainTl => s.mainRows

/-- The logarithm logEll of the message length of an array's rows, from the main code or the mask
code. -/
def lenOf (codes : Codes) (s : OracleShape) : Rd → ℕ
  | .mask | .maskTl => (codes.mask.getD s.maskCode default).logEll
  | .main | .mainTl => (codes.base.getD s.code default).logEll

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- What is stated of the pad of the instance's answer (k, i, s): a slot y with a coordinate co, the
power t of θ, and the array tb, row r and entry j at which the slot is located. -/
structure PadFacts (k i : ℕ) (s : Fin 3) (y : Seat) (co t : ℕ) (tb : Rd) (r j : ℕ) : Prop where
  /-- the slot is within the oracle message's sizes -/
  ok : y.ok P.codes (shapeAt P k) (ride k)
  /-- the slot is not in a tail -/
  inMsg : inMsg y = true
  /-- the coordinate is below 3 -/
  co3 : co < 3
  /-- the coordinate is 0 if the slot's coin is in the base field -/
  co0 : y.inE (shapeAt P k) = false → co = 0
  /-- the array tb holds rows' messages -/
  tbs : tb = .main ∨ tb = .mask
  /-- the slot is located at entry j of row r of tb -/
  place : y.place P.codes (shapeAt P k) (ride k) = (tb, r, j)
  /-- r is below the array's number of rows -/
  rlt : r < rowsOf (shapeAt P k) tb
  /-- j is below 2 ^ logEll of the array's code -/
  jlt : j < 2 ^ lenOf P.codes (shapeAt P k) tb
  /-- tb is the part of the oracle message in which K1 has the pads -/
  part : partOf tb = (K1.Msg.of P.codes (shapeAt P k)).padPart
  /-- t is below e, the number of entries of one answer's pad -/
  tlt : t < (K1.Msg.of P.codes (shapeAt P k)).e
  /-- the entry's index is K1's index of entry t of the pad of answer i -/
  idx : r + j * 2 ^ K1.clog (rowsOf (shapeAt P k) tb) =
    (K1.Msg.of P.codes (shapeAt P k)).padIdx i t
  /-- in the extension field t = 0 and co = s; in the base field t = s and co = 0 -/
  kind : (y.inE (shapeAt P k) = true ∧ t = 0 ∧ co = s.val) ∨
    (y.inE (shapeAt P k) = false ∧ t = s.val ∧ co = 0)

variable {P ride}

/-- If the job fits its place (sendFits), k < P.sent.size, i is an answer of oracle message k and it
has mask rows, PadFacts holds at the mask coin at entry ell - answers + i of the last mask row. -/
theorem pad_facts_mask (hf : sendFits P ride = true) (k i : ℕ) (s : Fin 3) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) (hz : (shapeAt P k).maskRows ≠ 0) :
    PadFacts P ride k i s
      (.mask (((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) *
        (shapeAt P k).maskRows + ((shapeAt P k).maskRows - 1))) s.val 0 .mask
      ((shapeAt P k).maskRows - 1)
      ((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) := by
  have ha : (shapeAt P k).answers ≠ 0 := by omega
  have hr := fits_noRide P ride k hf hk ha
  have hL := two_logEll_mask P.codes _ (fits_lengths P ride hf) (fits_maskCode P ride k hf hk hz)
  have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = true := by
    show ((shapeAt P k).maskRows != 0) = true
    simpa using hz
  have he : (K1.Msg.of P.codes (shapeAt P k)).e = 1 := by
    unfold K1.Msg.e
    rw [hK]
    rfl
  have hfit : (shapeAt P k).answers ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
    have h := fits_pad P ride k hf hk ha
    unfold K1.Msg.padFits at h
    rw [hK, he] at h
    have h' := of_decide_eq_true h
    simp only [if_true, Nat.one_mul] at h'
    rw [← hL]
    exact h'
  have hj : (P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i <
      (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by omega
  have hm : 0 < (shapeAt P k).maskRows := Nat.pos_of_ne_zero hz
  refine ⟨?_, rfl, s.isLt, (fun h => by cases h), Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inl ⟨rfl, rfl, rfl⟩⟩
  · show _ < (stepsOf P.codes (shapeAt P k) (ride k)).mask
    have e : (stepsOf P.codes (shapeAt P k) (ride k)).mask = (shapeAt P k).maskRows *
        (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by simp [stepsOf, hr]
    rw [e, Nat.mul_comm (shapeAt P k).maskRows]
    exact lt_mul _ _ _ _ hj (by omega)
  · show (Rd.mask, _ % (shapeAt P k).maskRows, _ / (shapeAt P k).maskRows) = _
    rw [Nat.add_comm _ ((shapeAt P k).maskRows - 1), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega), Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  · show (shapeAt P k).maskRows - 1 < (shapeAt P k).maskRows
    omega
  · show _ < 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll
    rw [hL]
    exact hj
  · show Part.mask = if _ then Part.mask else Part.main
    rw [if_pos hK]
  · rw [he]
    norm_num
  · unfold K1.Msg.padIdx K1.Msg.padRows K1.Msg.padLen
    rw [he, if_pos hK, if_pos hK]
    show _ = ((shapeAt P k).maskRows - 1) +
      (2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logEll - 1 * (shapeAt P k).answers +
        1 * i + 0) * 2 ^ K1.clog (shapeAt P k).maskRows
    rw [hL, Nat.one_mul, Nat.one_mul, Nat.add_zero]
    rfl

/-- An oracle message with an answer and no mask row has e pad coins for each answer, where e is
K1.Msg.e. -/
theorem pad_count (k : ℕ) (ha : (shapeAt P k).answers ≠ 0) (hz : (shapeAt P k).maskRows = 0) :
    (stepsOf P.codes (shapeAt P k) (ride k)).pad =
      (K1.Msg.of P.codes (shapeAt P k)).e * (shapeAt P k).answers := by
  have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = false := by
    show ((shapeAt P k).maskRows != 0) = false
    simp [hz]
  unfold K1.Msg.e
  rw [hK, Bool.false_or]
  show (if ((shapeAt P k).maskRows == 0 && (shapeAt P k).answers != 0) = true then
    (if ((shapeAt P k).mainDeg == 3) = true then 1 else 3) * (shapeAt P k).answers else 0) = _
  rw [if_pos (by simp [hz, ha])]
  rfl

/-- If the job fits its place (sendFits), k < P.sent.size, i is an answer of oracle message k and it
has no mask row, PadFacts holds at the pad's coin number e * i + t in the last main row, for t < e
and co < 3 as the last premise pairs them with s. -/
theorem pad_facts_main (hf : sendFits P ride = true) (k i : ℕ) (s : Fin 3) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) (hz : (shapeAt P k).maskRows = 0) (co t : ℕ)
    (ht : t < (K1.Msg.of P.codes (shapeAt P k)).e) (hco : co < 3)
    (hkind : (((shapeAt P k).mainDeg == 3) = true ∧ t = 0 ∧ co = s.val) ∨
      (((shapeAt P k).mainDeg == 3) = false ∧ t = s.val ∧ co = 0)) :
    PadFacts P ride k i s (.pad ((K1.Msg.of P.codes (shapeAt P k)).e * i + t)) co t .main
      ((shapeAt P k).mainRows - 1)
      ((P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad +
        ((K1.Msg.of P.codes (shapeAt P k)).e * i + t)) := by
  have ha : (shapeAt P k).answers ≠ 0 := by omega
  have hm := fits_main P ride k hf hk hz
  have hL := two_logEll_base P.codes _ (fits_lengths P ride hf)
    (fits_code P ride k hf hk (Nat.ne_of_gt hm))
  have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = false := by
    show ((shapeAt P k).maskRows != 0) = false
    simp [hz]
  have hp := pad_count (ride := ride) k ha hz
  have hfit : (K1.Msg.of P.codes (shapeAt P k)).e * (shapeAt P k).answers ≤
      (P.codes.base.getD (shapeAt P k).code default).ell := by
    have h := fits_pad P ride k hf hk ha
    unfold K1.Msg.padFits at h
    rw [hK] at h
    have h' := of_decide_eq_true h
    simp only [Bool.false_eq_true, if_false] at h'
    rw [← hL]
    exact h'
  have hn : (K1.Msg.of P.codes (shapeAt P k)).e * i + t <
      (K1.Msg.of P.codes (shapeAt P k)).e * (shapeAt P k).answers := by
    have h1 : (K1.Msg.of P.codes (shapeAt P k)).e * (i + 1) ≤
        (K1.Msg.of P.codes (shapeAt P k)).e * (shapeAt P k).answers := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at h1
    omega
  refine ⟨?_, rfl, hco, ?_, Or.inl rfl, rfl, ?_, ?_, ?_, ht, ?_, hkind⟩
  · show _ < (stepsOf P.codes (shapeAt P k) (ride k)).pad
    rw [hp]
    exact hn
  · intro h
    rcases hkind with ⟨h3, -, -⟩ | ⟨-, -, h0⟩
    · have h' : ((shapeAt P k).mainDeg == 3) = false := h
      rw [h3] at h'
      cases h'
    · exact h0
  · show (shapeAt P k).mainRows - 1 < (shapeAt P k).mainRows
    omega
  · show _ < 2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll
    rw [hL, hp]
    omega
  · show Part.main = if _ then Part.mask else Part.main
    rw [if_neg (by rw [hK]; simp)]
  · unfold K1.Msg.padIdx K1.Msg.padRows K1.Msg.padLen
    rw [if_neg (by rw [hK]; simp), if_neg (by rw [hK]; simp), hp]
    show _ = ((shapeAt P k).mainRows - 1) +
      (2 ^ (P.codes.base.getD (shapeAt P k).code default).logEll -
        (K1.Msg.of P.codes (shapeAt P k)).e * (shapeAt P k).answers +
        (K1.Msg.of P.codes (shapeAt P k)).e * i + t) * 2 ^ K1.clog (shapeAt P k).mainRows
    rw [hL, Nat.add_assoc]
    rfl

/-- If the job fits its place (sendFits), k < P.sent.size and i is an answer of oracle message k,
then for each coordinate s some slot, coordinate, power of θ, array, row and entry have PadFacts. -/
theorem pad_facts (hf : sendFits P ride = true) (k i : ℕ) (s : Fin 3) (hk : k < P.sent.size)
    (hi : i < (shapeAt P k).answers) :
    ∃ y co t tb r j, PadFacts P ride k i s y co t tb r j := by
  by_cases hz : (shapeAt P k).maskRows = 0
  · have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = false := by
      show ((shapeAt P k).maskRows != 0) = false
      simp [hz]
    by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · have he : (K1.Msg.of P.codes (shapeAt P k)).e = 1 := by
        unfold K1.Msg.e
        rw [hK, Bool.false_or]
        exact if_pos h3
      exact ⟨_, _, _, _, _, _, pad_facts_main hf k i s hk hi hz s.val 0 (by rw [he]; norm_num)
        s.isLt (Or.inl ⟨h3, rfl, rfl⟩)⟩
    · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
      have he : (K1.Msg.of P.codes (shapeAt P k)).e = 3 := by
        unfold K1.Msg.e
        rw [hK, Bool.false_or]
        exact if_neg h3
      exact ⟨_, _, _, _, _, _, pad_facts_main hf k i s hk hi hz 0 s.val (by rw [he]; exact s.isLt)
        (by norm_num) (Or.inr ⟨h3', rfl, rfl⟩)⟩
  · exact ⟨_, _, _, _, _, _, pad_facts_mask hf k i s hk hi hz⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.pad_facts
