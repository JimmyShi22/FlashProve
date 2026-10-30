-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSendRead.lean: the sample row and the seeds of the program's sending block, over
the field.

In the sending block (OnBytes/Iop/Send.lean) the verifier draws seeds, each a point and a factor,
and keeps for each answer of a sampled oracle message a sample row: a linear form of the whole
message, made from a seed, with the answer as its target. OnBytes/Slice/BlkSend.lean gives the
coefficients of that row, read in the field, in terms of the program's seed. This file writes the
same functions on elements of the field, so that the row can be named from a point, a factor and an
answer that were read off a written transcript, and says that the program's functions, read, are
these.

Main definitions (namespace SendF).
 `front`     the factor in front of the equality vector for one of a message's two tables.
 `table`     the weight of an entry of a table under a point.
 `padW`, `padSum`   what the places of the pad add to it.
 `form`      the sample row, with its target.
 `seedsOf`   the drawn elements, cut into seeds. `readSeed`: how a seed is read.
Main theorems: `read_front`, `read_table`, `read_padSum`, `read_form`, `read_seedsOf`.

Not claimed. Nothing on a run of the block. Nothing on what a sample is good for. The basis elements
of a pad's places are public constants of the program and are read where they are used.

-/
import OnBytes.Slice.BlkSend
import OnBytes.Slice.BlkRowRead

set_option autoImplicit false

namespace OnBytes.Slice

/-- A member of a list of elements that were read; 0 beyond the end. -/
theorem getD_map_readE (l : List E) (t : ℕ) : (l.map readE).getD t 0 = readE (l.getD t zeroE) := by
  rw [← readE_zero, List.getD_map]

/-- A list of the program's elements as a function of the place, from the list that was read. -/
theorem readL_eq_getD (l : List E) : readL l = fun t => (l.map readE).getD t 0 :=
  funext fun t => (getD_map_readE l t).symm

namespace SendF

/-- The factor in front of the equality vector for one of the two tables: it fixes the cube's
coordinates above the table (Send.front). -/
def front (z : List GE) (c : SampleCube) (tableBits : ℕ) (mask : Bool) : GE :=
  if !(c.hasMain && c.hasMask) then 1
  else
    (if mask then z.getD (c.bits - 1) 0 else 1 - z.getD (c.bits - 1) 0) *
      (((z.take (c.bits - 1)).drop tableBits).map fun x => 1 - x).prod

/-- The program's factor, read. -/
theorem read_front (z : List E) (c : SampleCube) (tableBits : ℕ) (mask : Bool) :
    readE (Send.front z c tableBits mask) = front (z.map readE) c tableBits mask := by
  unfold Send.front front
  by_cases h : (!(c.hasMain && c.hasMask)) = true
  · rw [if_pos h, if_pos h]
    exact readE_one
  · rw [if_neg h, if_neg h]
    dsimp only
    rw [readE_foldOneSub, getD_map_readE, ← List.map_take, ← List.map_drop, List.map_map]
    refine congrArg₂ (· * ·) ?_ rfl
    cases mask
    · exact (readE_sub _ _).trans (by rw [readE_one]; rfl)
    · rfl

/-- The weight of entry i of a table of a message of the shape s under the point z. -/
def table (codes : Codes) (s : OracleShape) (z : List GE) (part : Part) (i : ℕ) : GE :=
  front z (Send.cube codes s) (partBits (Send.cube codes s) part) (part == .mask) *
    eqW (min (partBits (Send.cube codes s) part) z.length) (fun t => z.getD t 0) i

/-- The program's weight, read. -/
theorem read_table (codes : Codes) (s : OracleShape) (z : List E) (part : Part) (i : ℕ) :
    tableW codes s z part i = table codes s (z.map readE) part i := by
  rw [tableW_eq, read_front, readL_eq_getD]
  unfold table
  rw [List.length_map]

/-- The coefficient that a place of the pad has in the row of an answer: the factor times the
place's basis element in its own answer's row, else 0. -/
def padW (beta : GE) (answer : ℕ) (p : PadPlace) : GE :=
  if p.answer == answer then beta * readE p.basis else 0

/-- What the places of the pad add to the weights under the point: at each of them the weight is
taken away and the pad's coefficient is put in. -/
def padSum (codes : Codes) (s : OracleShape) (z : List GE) (beta : GE) (answer : ℕ)
    (places : List PadPlace) (part : Part) (i : ℕ) : GE :=
  (places.map fun p => if p.part == part && p.index == i then
    padW beta answer p - table codes s z p.part p.index else 0).sum

/-- The same for the program's seed, read. -/
theorem read_padSum (codes : Codes) (s : OracleShape) (seed : SampleSeed) (answer : ℕ)
    (places : List PadPlace) (part : Part) (i : ℕ) :
    Slice.padSum codes s seed answer places part i =
      padSum codes s (seed.z.map readE) (readE seed.beta) answer places part i := by
  unfold Slice.padSum padSum
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [read_table]
  rfl

/-- **The sample row** of the oracle message number o, of the shape s, for one answer: the seed is
the point z and the factor beta, places are the places of the pad, y is the answer. -/
def form (codes : Codes) (s : OracleShape) (o : ℕ) (places : List PadPlace) (z : List GE)
    (beta : GE) (answer : ℕ) (y : GE) : RowF where
  coef o' part i :=
    if o' = o then
      (if hasPart (Send.cube codes s) part then table codes s z part i else 0) +
        padSum codes s z beta answer places part i
    else 0
  target := y

/-- **The program's sample row with an answer as its target, read.** -/
theorem read_form (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) (y : E) :
    ∃ places, Send.pad codes s = some places ∧
      readRow { row with target := y } =
        form codes s o places (seed.z.map readE) (readE seed.beta) answer (readE y) := by
  obtain ⟨places, hp, _⟩ := coefAt_form codes s o seed answer row h .main 0
  refine ⟨places, hp, ?_⟩
  unfold readRow form
  refine congrArg₂ RowF.mk (funext fun o' => funext fun part => funext fun i => ?_) rfl
  show coefAt row o' part i = _
  by_cases ho : o' = o
  · subst ho
    obtain ⟨pl, hp', hc⟩ := coefAt_form codes s o' seed answer row h part i
    obtain rfl : pl = places := Option.some.inj (hp'.symm.trans hp)
    rw [if_pos rfl, hc, read_table, read_padSum]
  · rw [if_neg ho]
    exact coefAt_form_other codes s o seed answer row h o' ho part i

/-- The drawn elements of a round of seeds, cut into n seeds, each of bits coordinates and a
factor. Nothing unless there are exactly n (bits + 1) elements (Send.seedsOf). -/
def seedsOf (bits : ℕ) : ℕ → List GE → Option (List (List GE × GE))
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, l =>
    match l.drop bits with
    | [] => none
    | beta :: rest => (seedsOf bits n rest).map fun t => (l.take bits, beta) :: t

/-- How a seed is read: its point and its factor. -/
def readSeed (s : SampleSeed) : List GE × GE := (s.z.map readE, readE s.beta)

/-- **The program's seeds, read**, are the seeds cut out of the drawn elements, read. -/
theorem read_seedsOf (bits : ℕ) : ∀ (n : ℕ) (l : List E),
    (Send.seedsOf bits n l).map (·.map readSeed) = seedsOf bits n (l.map readE)
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, l => by
    rw [Send.seedsOf, seedsOf, ← List.map_drop]
    cases l.drop bits with
    | nil => rfl
    | cons b rest =>
      show ((Send.seedsOf bits n rest).map _).map _ = (seedsOf bits n (rest.map readE)).map _
      rw [← read_seedsOf bits n rest, Option.map_map, Option.map_map, ← List.map_take]
      rfl

end SendF

end OnBytes.Slice
