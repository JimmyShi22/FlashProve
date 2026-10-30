-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Counts.lean: THE COUNTS OF THE CODE SWITCH's SENDING AGAINST
THE SHARED SENDING's: two texts count the coins of an oracle message: `messageDue`, `dueBefore`,
`sendingDue` (Honest/K2/Part.lean), with the numbers that `messageRows` (Honest/K2/Sending.lean)
reckons for itself, and `K1.dueMsg`, `K1.startR`, `K1.dueR` (Honest/K1/Coins.lean). HERE THEY ARE
SHOWN TO BE ONE, under the shared sending's public test and where no message is a masking word.
The definitions that the statements speak of, statements and proofs.

  `padOf`, `padAtOf`, `inMainOf`, `fromE`, `countF`, `inMaskOf`, `laidDue`   THE NUMBERS THAT
                 `messageRows` RECKONS FOR ITSELF, under names: the pad's places in a main row;
                 which of the pad's coins stands at a place; the main rows' coins; where the mask
                 rows' coins begin; the coins of the base field; the mask rows' coins; the whole
                 count
  `rideAs`       a fold's row variables as the shared sending's riding table
  `ShapeFits`    what the shared sending's test says of one message
  `NoWord`, `noWord`, `noWord_yes`   no message of the sending has main rows and no sample: every
                 message with a main row is sampled; the same as a public test with code
  `Reads.flatMap_range`, `Reads.find_none`, `Reads.find_at`, `Reads.index_inj`,
  `Reads.padAt_numbers`   on lists and numbers
  `steps_pad_mask`, `steps_pad_main`, `padOf_mask`, `padOf_main`, `padOf_eq`, `padOf_length`   THE
                 PAD's PLACES, in their order, are the last places of the last main row
  `padAtOf_eq`   so the two texts tell one coin's number at every place of a main row
  `messageDue_laid`   the count that the part takes for a message is the count that its laying asks
  `steps_word`, `steps_main`, `steps_mask`, `messageDue_shared`   and is the shared sending's count
  `sendingPar_sent`, `sendingPar_shape`, `shapeFits_of`   the test, message by message
  `dueBefore_zero`, `dueBefore_succ`, `dueBefore_le`, `dueBefore_shared`, `sendingDue_shared`   the
                 counts in front of a message, and the whole sending's

Limits. Counts and places alone: no sentence on what a coin is for. A masking word (main rows and no
sample) is counted by the shared sending and not by the switch's text: `NoWord` shuts it out, and
whether a sending of the plan has one is not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Sending
import Johnson.Desc.ProofFile.Honest.K2.Law.Room
import Johnson.Desc.ProofFile.Honest.K1.PadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open Reads

/-! ## 1 The numbers that `messageRows` reckons for itself, under names -/

/-- The indices of the pad's places in the main table, in the pad's order; none where the message
has a mask row. -/
def padOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : List Nat :=
  if s.maskRows != 0 then []
  else ((VerifiableInference.Desc.Own.padMade codes s).getD []).map (·.index)

/-- Which of the pad's coins stands at place j of main row b; none: no pad's place. -/
def padAtOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (b j : Nat) : Option Nat :=
  ((padOf codes s).zipIdx.find? (·.1 == b + j * 2 ^ OnBytes.ceilLog2 s.mainRows)).map (·.2)

/-- The coins of the main rows: tails, then the pad. -/
def inMainOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat :=
  s.mainRows * (codes.base.getD s.code default).r + (padOf codes s).length

/-- Where, among the message's coins of the extension field, the mask rows' coins begin. -/
def fromE (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat :=
  if s.mainDeg == 3 then inMainOf codes s else 0

/-- The message's coins of the base field. -/
def countF (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat :=
  if s.mainDeg == 3 then 0 else inMainOf codes s

/-- The coins of the mask rows' entries; of a fresh mask: the coefficients. -/
def inMaskOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) : Nat :=
  match fold with
  | some n => 2 * n + 1
  | none => s.maskRows * (codes.mask.getD s.maskCode default).ell

/-- The count that a message's laying asks of its stretch. -/
def laidDue (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) : Due :=
  ⟨countF codes s,
    fromE codes s + inMaskOf codes s fold + s.maskRows * (codes.mask.getD s.maskCode default).r⟩

/-- A fold's row variables as the shared sending's riding table, at a message's shape. -/
def rideAs (s : OnBytes.OracleShape) (fold : Option Nat) : Option K1.Ride :=
  fold.map fun n => ⟨n, OnBytes.ceilLog2 s.maskRows⟩

/-- **What the shared sending's public test says of one message**: the plan's test on a sent shape;
the pad in a main row is no longer than the row; a riding table fits the shape. -/
structure ShapeFits (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) :
    Prop where
  shape : VerifiableInference.Desc.Own.sentShapeFits codes s = true
  pad : (K1.stepsOf codes s (rideAs s fold)).pad ≤ (codes.base.getD s.code default).ell
  ride : ∀ n, fold = some n → K1.rideFits codes s ⟨n, OnBytes.ceilLog2 s.maskRows⟩ = true

/-- No message of the sending has main rows and no sample: every message with a main row is
sampled. -/
def NoWord (sent : Array OnBytes.OracleNotice) : Prop :=
  ∀ k, k < sent.size →
    (sent.getD k default).shape.mainRows = 0 ∨ (sent.getD k default).shape.answers ≠ 0

/-- The same as a public test with code: every message with a main row is sampled. -/
def noWord (sent : Array OnBytes.OracleNotice) : Bool :=
  (List.range sent.size).all fun k =>
    (sent.getD k default).shape.mainRows == 0 || (sent.getD k default).shape.answers != 0

/-- The test's yes gives the sentence. -/
theorem noWord_yes {sent : Array OnBytes.OracleNotice} (h : noWord sent = true) : NoWord sent := by
  intro k hk
  simp only [noWord, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne] at h
  exact h k hk

/-! ## 2 On lists and numbers -/

namespace Reads

/-- A list made block by block, e entries a block, is the list made entry by entry. -/
theorem flatMap_range {α : Type} (g : Nat → α) (e : Nat) : ∀ a : Nat,
    ((List.range a).flatMap fun i => (List.range e).map fun t => g (e * i + t)) =
      (List.range (e * a)).map g
  | 0 => by simp
  | a + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range g e a, Nat.mul_succ, List.range_add,
      List.map_append]
    simp only [List.map_map, Function.comp_def, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]

/-- A key that no member bears is not found. -/
theorem find_none {g : Nat → Nat} {N key : Nat} (h : ∀ p, p < N → g p ≠ key) :
    ((List.range N).map g).zipIdx.find? (·.1 == key) = none := by
  rw [List.find?_eq_none]
  intro x hx hq
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at hx
  obtain ⟨p, hp, hgp⟩ := Option.map_eq_some_iff.1 hx
  exact h p (List.mem_range.1 (List.mem_of_getElem? hp)) (hgp.trans (beq_iff_eq.1 hq))

/-- Where no two members bear one key, member number p is found by its key, with its number. -/
theorem find_at {g : Nat → Nat} (hg : ∀ p q, g p = g q → p = q) : ∀ (N p : Nat), p < N →
    ((List.range N).map g).zipIdx.find? (·.1 == g p) = some (g p, p)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, p, h => by
    rw [List.range_succ, List.map_append, List.zipIdx_append, List.find?_append]
    by_cases hp : p < N
    · rw [find_at hg N p hp]
      rfl
    · obtain rfl : p = N := by omega
      rw [find_none (g := g) (N := p) (key := g p) fun q hq e =>
        absurd (hg q p e) (Nat.ne_of_lt hq)]
      simp

/-- Row and place are told by the index in a table. -/
theorem index_inj {n b b' j j' : Nat} (hb : b < n) (hb' : b' < n)
    (h : b + j * 2 ^ OnBytes.ceilLog2 n = b' + j' * 2 ^ OnBytes.ceilLog2 n) : b = b' ∧ j = j' := by
  have h1 := Johnson.Prover.Send.split_index b j n hb
  have h2 := Johnson.Prover.Send.split_index b' j' n hb'
  rw [Johnson.Prover.Send.clog_eq] at h1 h2
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- Among the indices of the last N places of the last of n rows of length L, in their order: the
index of place j of row b is found just where it is one of them, and then under the number
j - (L - N). -/
theorem padAt_numbers {n L N b j : Nat} (hN : N ≤ L) (hb : b < n) (hj : j < L) :
    ((((List.range N).map fun p => (n - 1) + (L - N + p) * 2 ^ OnBytes.ceilLog2 n).zipIdx.find?
        (·.1 == b + j * 2 ^ OnBytes.ceilLog2 n)).map (·.2)) =
      if N != 0 && b + 1 == n && decide (L - N ≤ j) && decide (j < L) then some (j - (L - N))
      else none := by
  have hinj : ∀ p q, (n - 1) + (L - N + p) * 2 ^ OnBytes.ceilLog2 n =
      (n - 1) + (L - N + q) * 2 ^ OnBytes.ceilLog2 n → p = q := by
    intro p q e
    have := (index_inj (n := n) (by omega) (by omega) e).2
    omega
  by_cases hc : b + 1 = n ∧ L - N ≤ j
  · have hkey : b + j * 2 ^ OnBytes.ceilLog2 n =
        (n - 1) + (L - N + (j - (L - N))) * 2 ^ OnBytes.ceilLog2 n := by
      have e1 : b = n - 1 := by omega
      have e2 : L - N + (j - (L - N)) = j := by omega
      rw [e2, e1]
    have hyes : (N != 0 && b + 1 == n && decide (L - N ≤ j) && decide (j < L)) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨by omega, hc.1⟩, hc.2⟩, hj⟩
    have hfind := find_at (g := fun p => (n - 1) + (L - N + p) * 2 ^ OnBytes.ceilLog2 n) hinj N
      (j - (L - N)) (by omega)
    rw [if_pos hyes, hkey]
    exact congrArg (Option.map (·.2)) hfind
  · have hno : ¬ (N != 0 && b + 1 == n && decide (L - N ≤ j) && decide (j < L)) = true := by
      intro h
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at h
      exact hc ⟨h.1.1.2, h.1.2⟩
    have hfind := find_none (g := fun p => (n - 1) + (L - N + p) * 2 ^ OnBytes.ceilLog2 n) (N := N)
      (key := b + j * 2 ^ OnBytes.ceilLog2 n) fun p _ e => by
        have h := index_inj (n := n) (by omega) hb e
        exact hc ⟨by omega, by omega⟩
    rw [if_neg hno]
    exact congrArg (Option.map (·.2)) hfind

end Reads

/-! ## 3 The pad's places -/

/-- A message with a mask row has no pad in a main row, by the shared sending's count. -/
theorem steps_pad_mask {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {ρ : Option K1.Ride}
    (hz : s.maskRows ≠ 0) : (K1.stepsOf codes s ρ).pad = 0 := by
  have h : (s.maskRows == 0) = false := beq_eq_false_iff_ne.2 hz
  simp only [K1.stepsOf, h, Bool.false_and, Bool.false_eq_true, if_false]

/-- A message without one: one coin an answer over the extension field, three over the base
field. -/
theorem steps_pad_main {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {ρ : Option K1.Ride}
    (hz : s.maskRows = 0) :
    (K1.stepsOf codes s ρ).pad = (if s.mainDeg == 3 then 1 else 3) * s.answers := by
  by_cases ha : s.answers = 0
  · have h : (s.answers != 0) = false := by
      rw [ha]
      rfl
    simp only [K1.stepsOf, h, Bool.and_false, Bool.false_eq_true, if_false]
    rw [ha, Nat.mul_zero]
  · have h : (s.answers != 0) = true := bne_iff_ne.2 ha
    simp only [K1.stepsOf, hz, h, beq_self_eq_true, Bool.and_self, if_true]

/-- With a mask row: no place. -/
theorem padOf_mask {codes : OnBytes.Codes} {s : OnBytes.OracleShape} (hz : s.maskRows ≠ 0) :
    padOf codes s = [] :=
  if_pos (bne_iff_ne.2 hz)

/-- Without one, where the pad is no longer than the row. -/
theorem padOf_main {codes : OnBytes.Codes} {s : OnBytes.OracleShape} (hz : s.maskRows = 0)
    (hm : 0 < s.mainRows)
    (hle : (if s.mainDeg == 3 then 1 else 3) * s.answers ≤ (codes.base.getD s.code default).ell) :
    padOf codes s = (List.range ((if s.mainDeg == 3 then 1 else 3) * s.answers)).map fun p =>
      (s.mainRows - 1) + ((codes.base.getD s.code default).ell -
        (if s.mainDeg == 3 then 1 else 3) * s.answers + p) * 2 ^ OnBytes.ceilLog2 s.mainRows := by
  have h0 : (s.maskRows != 0) = false := by
    rw [hz]
    rfl
  have hk : (OnBytes.Send.cube codes s).hasMask = false := by
    show decide (0 < s.maskRows) = false
    rw [hz]
    rfl
  have hb : (OnBytes.Send.cube codes s).mainRowBits = OnBytes.ceilLog2 s.mainRows := by
    show (if decide (0 < s.mainRows) = true then OnBytes.ceilLog2 s.mainRows else 0) = _
    rw [if_pos (decide_eq_true hm)]
  unfold padOf
  rw [if_neg (by rw [h0]; exact Bool.false_ne_true)]
  unfold VerifiableInference.Desc.Own.padMade
  simp only [hk, hb, Bool.false_or, Bool.false_eq_true, if_false]
  rw [if_neg (Nat.not_lt.2 hle), Option.getD_some, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, Nat.add_assoc]
  exact flatMap_range (fun p => (s.mainRows - 1) + ((codes.base.getD s.code default).ell -
    (if s.mainDeg == 3 then 1 else 3) * s.answers + p) * 2 ^ OnBytes.ceilLog2 s.mainRows) _ _

/-- **The pad's places, in their order, are the last places of the last main row**: as many as the
shared sending counts. -/
theorem padOf_eq {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) :
    padOf codes s = (List.range (K1.stepsOf codes s (rideAs s fold)).pad).map fun p =>
      (s.mainRows - 1) + ((codes.base.getD s.code default).ell -
        (K1.stepsOf codes s (rideAs s fold)).pad + p) * 2 ^ OnBytes.ceilLog2 s.mainRows := by
  by_cases hz : s.maskRows = 0
  · have hm : 0 < s.mainRows := by
      have h := H.shape
      simp only [VerifiableInference.Desc.Own.sentShapeFits, Bool.and_eq_true,
        decide_eq_true_eq] at h
      have := h.1.1.1
      omega
    have hp := H.pad
    rw [steps_pad_main hz] at hp ⊢
    exact padOf_main hz hm hp
  · rw [steps_pad_mask hz, padOf_mask hz]
    rfl

/-- So many places. -/
theorem padOf_length {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) :
    (padOf codes s).length = (K1.stepsOf codes s (rideAs s fold)).pad := by
  rw [padOf_eq H, List.length_map, List.length_range]

/-- **The two texts tell one coin's number at every place of a main row.** The right side is the
shared sending's own test, at its own count of the pad. -/
theorem padAtOf_eq {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) {b j : Nat} (hb : b < s.mainRows)
    (hj : j < (codes.base.getD s.code default).ell) :
    padAtOf codes s b j =
      if (K1.stepsOf codes s (rideAs s fold)).pad != 0 && b + 1 == s.mainRows &&
          decide ((codes.base.getD s.code default).ell -
            (K1.stepsOf codes s (rideAs s fold)).pad ≤ j) &&
          decide (j < (codes.base.getD s.code default).ell) then
        some (j - ((codes.base.getD s.code default).ell -
          (K1.stepsOf codes s (rideAs s fold)).pad))
      else none := by
  unfold padAtOf
  rw [padOf_eq H]
  exact padAt_numbers H.pad hb hj

/-! ## 4 One message's count -/

/-- **The count that the part takes for a message is the count that its laying asks.** -/
theorem messageDue_laid {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) : messageDue codes s fold = laidDue codes s fold := by
  have hl := padOf_length H
  cases fold with
  | some n =>
    have hr := H.ride n rfl
    simp only [K1.rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    have hm0 : s.mainRows = 0 := hr.1.1.1.1.2
    have hz : s.maskRows ≠ 0 := by
      rw [hr.1.1.1.2]
      exact Nat.ne_of_gt (Nat.two_pow_pos _)
    have e0 : inMainOf codes s = 0 := by
      simp only [inMainOf, padOf_mask hz, hm0, Nat.zero_mul, List.length_nil, Nat.add_zero]
    have e1 : countF codes s = 0 := by
      unfold countF
      rw [e0, ite_self]
    have e2 : fromE codes s = 0 := by
      unfold fromE
      rw [e0, ite_self]
    show (⟨0, 2 * n + 1 + s.maskRows * (codes.mask.getD s.maskCode default).r⟩ : Due) =
      ⟨countF codes s, fromE codes s + (2 * n + 1) +
        s.maskRows * (codes.mask.getD s.maskCode default).r⟩
    rw [e1, e2, Nat.zero_add]
  | none =>
    by_cases hz : s.maskRows = 0
    · rw [steps_pad_main hz] at hl
      by_cases h3 : (s.mainDeg == 3) = true
      · rw [if_pos h3, Nat.one_mul] at hl
        simp only [messageDue, laidDue, countF, fromE, inMainOf, inMaskOf, h3, hl, hz,
          bne_self_eq_false, Bool.false_eq_true, if_false, if_true, Nat.zero_mul, Nat.add_zero]
      · rw [if_neg h3] at hl
        simp only [messageDue, laidDue, countF, fromE, inMainOf, inMaskOf, h3, hl, hz,
          bne_self_eq_false, Bool.false_eq_true, if_false, Nat.zero_mul, Nat.add_zero]
    · have h0 : (s.maskRows != 0) = true := bne_iff_ne.2 hz
      by_cases h3 : (s.mainDeg == 3) = true
      · simp only [messageDue, laidDue, countF, fromE, inMainOf, inMaskOf, padOf_mask hz, h0, h3,
          if_true, List.length_nil, Nat.add_zero, Nat.mul_add, Nat.add_assoc]
      · simp only [messageDue, laidDue, countF, fromE, inMainOf, inMaskOf, padOf_mask hz, h0, h3,
          if_true, Bool.false_eq_true, if_false, List.length_nil, Nat.add_zero, Nat.mul_zero,
          Nat.mul_add, Nat.zero_add]

/-- At a message that is no masking word the shared sending counts no word. -/
theorem steps_word {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {ρ : Option K1.Ride}
    (hw : s.mainRows = 0 ∨ s.answers ≠ 0) : (K1.stepsOf codes s ρ).word = 0 := by
  have h : (s.mainRows != 0 && s.answers == 0) = false := by
    rcases hw with h | h
    · rw [bne_eq_false_iff_eq.2 h, Bool.false_and]
    · rw [beq_eq_false_iff_ne.2 h, Bool.and_false]
  simp only [K1.stepsOf, h, Bool.false_eq_true, if_false]

/-- There the two texts count the main rows' coins alike. -/
theorem steps_main {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) (hw : s.mainRows = 0 ∨ s.answers ≠ 0) :
    (K1.stepsOf codes s (rideAs s fold)).main = inMainOf codes s := by
  unfold K1.Steps.main inMainOf
  rw [steps_word hw, padOf_length H, Nat.add_zero]
  rfl

/-- The two texts count the mask rows' coins alike. -/
theorem steps_mask (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) :
    (K1.stepsOf codes s (rideAs s fold)).mask = inMaskOf codes s fold := by
  cases fold with
  | some n => rfl
  | none => rfl

/-- **And it is the shared sending's count**, at a message that is no masking word. -/
theorem messageDue_shared {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {fold : Option Nat}
    (H : ShapeFits codes s fold) (hw : s.mainRows = 0 ∨ s.answers ≠ 0) :
    messageDue codes s fold = K1.dueMsg codes s (rideAs s fold) := by
  rw [messageDue_laid H]
  unfold K1.dueMsg laidDue countF fromE
  show _ = (if (s.mainDeg == 3) = true then
      (⟨0, (K1.stepsOf codes s (rideAs s fold)).main + (K1.stepsOf codes s (rideAs s fold)).mask +
        s.maskRows * (codes.mask.getD s.maskCode default).r⟩ : Due)
    else ⟨(K1.stepsOf codes s (rideAs s fold)).main, (K1.stepsOf codes s (rideAs s fold)).mask +
      s.maskRows * (codes.mask.getD s.maskCode default).r⟩)
  rw [steps_main H hw, steps_mask]
  by_cases h3 : (s.mainDeg == 3) = true
  · rw [if_pos h3, if_pos h3, if_pos h3]
  · rw [if_neg h3, if_neg h3, if_neg h3, Nat.zero_add]

/-! ## 5 The sending -/

/-- The core's public letter holds the sending's messages. -/
theorem sendingPar_sent (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    (sendingPar codes sent).sent = sent := by
  show (([("", sent)] : List (String × Array OnBytes.OracleNotice)).flatMap
    (·.2.toList)).toArray = sent
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- And so their shapes. -/
theorem sendingPar_shape (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (k : Nat) :
    Johnson.Prover.Send.shapeAt (sendingPar codes sent) k = (sent.getD k default).shape := by
  unfold Johnson.Prover.Send.shapeAt
  rw [sendingPar_sent]

/-- The riding tables, message by message. -/
theorem rideOf_as (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat)) (k : Nat) :
    rideOf sent fresh k = rideAs (sent.getD k default).shape (foldAt fresh k) :=
  rfl

/-- **The shared sending's public test, message by message.** -/
theorem shapeFits_of {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {k : Nat}
    (hk : k < sent.size) : ShapeFits codes (sent.getD k default).shape (foldAt fresh k) := by
  have hk' : k < (sendingPar codes sent).sent.size := by
    rw [sendingPar_sent]
    exact hk
  have h1 := K1.fits_shape _ _ k hf hk'
  have h2 := K1.pad_le_of_fits _ _ k hf hk'
  rw [sendingPar_shape] at h1 h2
  refine ⟨h1, h2, fun n hn => ?_⟩
  have h3 := hf
  simp only [K1.sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h3
  have h4 := (h3.2 k hk').2
  rw [sendingPar_shape, rideOf_as, hn] at h4
  exact h4

/-- In front of the first message: no coin. -/
theorem dueBefore_zero (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) : dueBefore codes sent fresh 0 = ⟨0, 0⟩ := by
  unfold dueBefore
  rw [List.take_zero]
  rfl

/-- The next message's coins begin behind this message's. -/
theorem dueBefore_succ (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) {n : Nat} (hn : n < sent.size) :
    dueBefore codes sent fresh (n + 1) = (dueBefore codes sent fresh n).plus
      (messageDue codes (sent.getD n default).shape (foldAt fresh n)) := by
  have hl : n < sent.toList.length := by
    rw [Array.length_toList]
    exact hn
  have hx : sent.toList[n] = sent.getD n default := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn, Option.getD_some,
      Array.getElem_toList]
  unfold dueBefore
  rw [List.take_succ_eq_append_getElem hl, List.zipIdx_append, List.foldl_append, hx,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hl), Nat.zero_add]
  rfl

/-- The counts in front grow with the message's number. -/
theorem dueBefore_le (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) {k : Nat} : ∀ n, k ≤ n → n ≤ sent.size →
    (dueBefore codes sent fresh k).f ≤ (dueBefore codes sent fresh n).f ∧
      (dueBefore codes sent fresh k).e ≤ (dueBefore codes sent fresh n).e := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ n _ ih =>
    intro hs
    have h := ih (Nat.le_of_succ_le hs)
    rw [dueBefore_succ codes sent fresh hs]
    exact ⟨Nat.le_trans h.1 (Nat.le_add_right _ _), Nat.le_trans h.2 (Nat.le_add_right _ _)⟩

/-- **The counts in front of a message are the shared sending's.** -/
theorem dueBefore_shared {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent) :
    ∀ n, n ≤ sent.size →
      dueBefore codes sent fresh n = K1.startR (sendingPar codes sent) (rideOf sent fresh) n
  | 0, _ => dueBefore_zero codes sent fresh
  | n + 1, hn => by
    rw [dueBefore_succ codes sent fresh hn, K1.startR_succ,
      dueBefore_shared hf hw n (Nat.le_of_succ_le hn), sendingPar_shape, rideOf_as,
      messageDue_shared (shapeFits_of hf hn) (hw n hn)]
    rfl

/-- **The sending's count is the shared sending's.** -/
theorem sendingDue_shared {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)}
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) (hw : NoWord sent) :
    sendingDue codes sent fresh = K1.dueR (sendingPar codes sent) (rideOf sent fresh) := by
  unfold sendingDue K1.dueR
  rw [sendingPar_sent]
  exact dueBefore_shared hf hw _ (Nat.le_refl _)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.noWord_yes
#print axioms ProofFile.Honest.K2.Reads.flatMap_range
#print axioms ProofFile.Honest.K2.Reads.find_none
#print axioms ProofFile.Honest.K2.Reads.find_at
#print axioms ProofFile.Honest.K2.Reads.index_inj
#print axioms ProofFile.Honest.K2.Reads.padAt_numbers
#print axioms ProofFile.Honest.K2.steps_pad_mask
#print axioms ProofFile.Honest.K2.steps_pad_main
#print axioms ProofFile.Honest.K2.padOf_mask
#print axioms ProofFile.Honest.K2.padOf_main
#print axioms ProofFile.Honest.K2.padOf_eq
#print axioms ProofFile.Honest.K2.padOf_length
#print axioms ProofFile.Honest.K2.padAtOf_eq
#print axioms ProofFile.Honest.K2.messageDue_laid
#print axioms ProofFile.Honest.K2.steps_word
#print axioms ProofFile.Honest.K2.steps_main
#print axioms ProofFile.Honest.K2.steps_mask
#print axioms ProofFile.Honest.K2.messageDue_shared
#print axioms ProofFile.Honest.K2.sendingPar_sent
#print axioms ProofFile.Honest.K2.sendingPar_shape
#print axioms ProofFile.Honest.K2.rideOf_as
#print axioms ProofFile.Honest.K2.shapeFits_of
#print axioms ProofFile.Honest.K2.dueBefore_zero
#print axioms ProofFile.Honest.K2.dueBefore_succ
#print axioms ProofFile.Honest.K2.dueBefore_le
#print axioms ProofFile.Honest.K2.dueBefore_shared
#print axioms ProofFile.Honest.K2.sendingDue_shared
#print axioms ProofFile.Honest.K2.padOf
#print axioms ProofFile.Honest.K2.padAtOf
#print axioms ProofFile.Honest.K2.inMainOf
#print axioms ProofFile.Honest.K2.fromE
#print axioms ProofFile.Honest.K2.countF
#print axioms ProofFile.Honest.K2.inMaskOf
#print axioms ProofFile.Honest.K2.laidDue
#print axioms ProofFile.Honest.K2.rideAs
#print axioms ProofFile.Honest.K2.ShapeFits
#print axioms ProofFile.Honest.K2.NoWord
#print axioms ProofFile.Honest.K2.noWord
