-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6ByBlocks.lean: the four clauses of PlanK6 (Law/K6Cut.lean) on the
plan's numbers, at the terms seatLay and plAt (Law/PlanK6At.lean), FROM A CHEAP TEST WITH CODE, BY
BLOCKS.
Definitions with code and theorems.

Why. The four clauses speak of every row of symbols and every column of the head's matrices (some
10 ^ 7 elements at the full size) and of every entry of the mask row in use. But the number that a
seat names hangs on the matrix alone, and an array is laid in a few blocks, each a whole rectangle
of its message's table (Johnson/Desc/LaidAt.lean). So the members are asked once a matrix, and the
blocks once a member.

What is said. seat := seatLay Wp lay6 num; pl := plAt n rb.
  blockIn, insideB, inMsg_of_inside   every block of the array ends inside the main table of a
      message of the shape s: then every element that is laid lies inside (InMsg).
  copyIn cs arr msR N n ok   segment 24's group has a member of msR with the number n; and whichever
      member sits there with that number is sent at the segment's moment 0 and has a shape at which
      ok says yes.  inCopy_of: then InCopy cs arr (ms0 msR N) msR N 24 n mask row place, wherever ok
      gives InMsg at that place.
  matC   at matrix number a of the head's list: the array that the label names is there; just one
      tenant of the group bears its message's number; copyIn at insideB.
  maskOk, inMsg_of_mask   the shape has 2 ^ rb mask rows at least, and its mask code is long enough
      for ns entries laid as plAt lays them.
  **planK6C**   THE TEST: matC at every matrix but number NHf + 2 and those beyond NHf + 3 (no
      column of these is one of the four ranges'); one tenant bears n; copyIn at maskOk.
  **planK6_of_C**   under Meaning.laidThere Wp (sizesOf Wp) lay6 = true: planK6C = true gives the
      four clauses, in the words of PlanK6's fields named, seats, maskNamed, maskIn.

Letters under "there is" in the top statement: none.
What it does not give. One way alone. laidThere is a premise (other files have a cheap road to it).
PlanK6's first two fields (made, follows) are not touched. The full size alone (24 is a literal).
Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6At
import Johnson.Desc.Kinds.Law.LaidOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open OnBytes.Model.Verify (borderOf)
open Johnson.Pack (pMain pMask)
open VerifiableInference.Desc renaming laidAt → laidAtD, arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem seatOf numOf InMsg namedOnce)

variable (cs : OnBytes.Codes)

/-- The block ends inside the main table of a message of the shape s. -/
def blockIn (s : OnBytes.OracleShape) (b : LaidBlock) : Bool :=
  Decidable.decide (lastRowOf b < s.mainRows) && Decidable.decide (lastPlaceOf b < (pMain cs s).ell)

/-- So does every block of the array. -/
def insideB (s : OnBytes.OracleShape) (A : ReqArray) : Bool := A.blocks.all (blockIn cs s)

theorem inMsg_of_inside {s : OnBytes.OracleShape} {A : ReqArray} (h : insideB cs s A = true)
    {i c r p : ℕ} (hl : laidAtD A i c = some (r, p)) : InMsg cs s false r p := by
  unfold laidAtD at hl
  obtain ⟨b, hb, hi⟩ := List.exists_of_findSome?_eq_some hl
  obtain ⟨hr, hp⟩ := laidIn_le hi
  have hk := List.all_eq_true.1 h b hb
  unfold blockIn at hk
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨by omega, by omega⟩

variable (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)

/-- A member of msR sits in segment 24's group with the number n; whichever does is sent at the
segment's moment 0 and has a shape at which ok says yes. -/
def copyIn (n : ℕ) (ok : OnBytes.OracleShape → Bool) : Bool :=
  (msR.any fun y =>
      Decidable.decide (seatOf y ∈ N.group 24) && Decidable.decide (numOf arr y = n)) &&
    msR.all fun y =>
      !(Decidable.decide (seatOf y ∈ N.group 24) && Decidable.decide (numOf arr y = n)) ||
        (Decidable.decide (seatOf y ∈ N.sent 24 0) && ok (y.1.l.get y.2).1)

theorem inCopy_of {n : ℕ} {ok : OnBytes.OracleShape → Bool} (h : copyIn arr msR N n ok = true)
    {mask : Bool} {row place : ℕ} (hok : ∀ s, ok s = true → InMsg cs s mask row place) :
    InCopy cs arr (ms0 msR N) msR N 24 n mask row place := by
  unfold copyIn at h
  rw [Bool.and_eq_true] at h
  obtain ⟨y, hy, hy2⟩ := List.any_eq_true.1 h.1
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hy2
  refine ⟨⟨y, hy, hy2.1, hy2.2⟩, fun z hz hg hn => ?_⟩
  have h1 := List.all_eq_true.1 h.2 z hz
  rw [decide_eq_true hg, decide_eq_true hn] at h1
  have h2 : (Decidable.decide (seatOf z ∈ N.sent 24 0) && ok (z.1.l.get z.2).1) = true := by
    simpa using h1
  rw [Bool.and_eq_true] at h2
  exact ⟨List.mem_filter.2 ⟨hz, h2.1⟩, hok _ h2.2⟩

variable (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- The test at matrix number a of the head's list. -/
def matC (a : ℕ) : Bool :=
  match arrayOfD lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => false
  | some A =>
    namedOnce arr N 24 (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message) &&
      copyIn arr msR N (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message) fun s =>
        insideB cs s A

/-- The shape has room for ns entries of the mask row, laid as plAt lays them. -/
def maskOk (ns rb : ℕ) (s : OnBytes.OracleShape) : Bool :=
  Decidable.decide (2 ^ rb ≤ s.maskRows) &&
    (ns == 0 || Decidable.decide ((ns - 1) / 2 ^ rb < (pMask cs s).ell))

theorem inMsg_of_mask {ns rb : ℕ} {s : OnBytes.OracleShape} (h : maskOk cs ns rb s = true) {j : ℕ}
    (hj : j < ns) : InMsg cs s true (j % 2 ^ rb) (j / 2 ^ rb) := by
  unfold maskOk at h
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  have hp : 0 < 2 ^ rb := Nat.pos_of_ne_zero (by simp)
  unfold InMsg
  rw [if_pos rfl]
  refine ⟨lt_of_lt_of_le (Nat.mod_lt _ hp) h.1, ?_⟩
  rcases h.2 with e | e
  · have : ns = 0 := by simpa using e
    omega
  · exact lt_of_le_of_lt (Nat.div_le_div_right (by omega)) e

variable (n rb : ℕ)

/-- **THE TEST.** -/
def planK6C : Bool :=
  ((List.range (Meaning.sizesOf Wp 24).NM).all fun a =>
      a == Wp.hS.NHf + 2 || Decidable.decide (Wp.hS.NHf + 3 < a) ||
        matC cs arr msR N Wp lay6 num a) &&
    namedOnce arr N 24 n && copyIn arr msR N n (maskOk cs Wp.H.ns rb)

/-- A column of the four ranges stands in no other matrix. -/
theorem four_matrix {h : OnBytes.Model.Head.Shape} {L : OnBytes.Model.Head.HL}
    {b : OnBytes.Model.Head.Border} {a c : ℕ} (hc : ColFour h L b a c) :
    a ≠ h.NHf + 2 ∧ ¬ h.NHf + 3 < a := by
  rcases hc with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> constructor <;> omega

/-- **A yes of the cheap test gives PlanK6's four clauses on the plan's numbers, at the terms.** -/
theorem planK6_of_C (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (h : planK6C cs arr msR N Wp lay6 num n rb = true) :
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      InCopy cs arr (ms0 msR N) msR N 24 (seatLay Wp lay6 num 24 μ r c).1 false
        (seatLay Wp lay6 num 24 μ r c).2.1 (seatLay Wp lay6 num 24 μ r c).2.2) ∧
    (∀ j, j < Wp.H.ns → namedOnce arr N 24 (plAt n rb j).1 = true) ∧
    (∀ j, j < Wp.H.ns → InCopy cs arr (ms0 msR N) msR N 24 (plAt n rb j).1
      (plAt n rb j).2.1 (plAt n rb j).2.2.1 (plAt n rb j).2.2.2) := by
  unfold planK6C at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hM, hn⟩, hm⟩ := h
  have key : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true ∧
      InCopy cs arr (ms0 msR N) msR N 24 (seatLay Wp lay6 num 24 μ r c).1 false
        (seatLay Wp lay6 num 24 μ r c).2.1 (seatLay Wp lay6 num 24 μ r c).2.2 := by
    intro μ r c hr hc hf
    obtain ⟨f1, f2⟩ := four_matrix hf
    have hμ := hM μ.val (List.mem_range.2 μ.isLt)
    have hμ' : matC cs arr msR N Wp lay6 num μ.val = true := by
      rw [Bool.or_eq_true, Bool.or_eq_true] at hμ
      rcases hμ with (e | e) | e
      · exact absurd (eq_of_beq e) f1
      · exact absurd (of_decide_eq_true e) f2
      · exact e
    obtain ⟨A, x, hA, -, -, hl, hs⟩ :=
      Meaning.seat_of_laidThere T num (by norm_num : 24 < 25) μ hr hc
    unfold matC at hμ'
    rw [hA, Bool.and_eq_true] at hμ'
    have hs' : seatLay Wp lay6 num 24 μ r c =
        (num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message, x.1, x.2) := hs
    rw [hs']
    exact ⟨hμ'.1, inCopy_of cs arr msR N hμ'.2 fun s hk => inMsg_of_inside cs hk hl⟩
  exact ⟨fun μ r c hr hc hf => (key μ r c hr hc hf).1, fun μ r c hr hc hf => (key μ r c hr hc hf).2,
    fun _ _ => hn, fun j hj => inCopy_of cs arr msR N hm fun s hk => inMsg_of_mask cs hk hj⟩

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.inMsg_of_inside
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.inCopy_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_of_C
