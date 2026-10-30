-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TensorLaws.lean: what the entries of a structured vector read as.

A Tensor (OnBytes/Iop/Tensor.lean) is a vector of product form, and a Form is a sum of tensors and
single entries. The laws say what an entry reads as in any commutative ring K under a reading of the
program's field elements (Model.Reading: a map that takes the program's 0, 1, sums, differences and
products to those of K; it need not be one-to-one), and how the calls that the batching of rows uses
change the entries: scale, insertChoice, add, addEntry, addForm. Model.Reading.gl
(OnBytes/Model/HideLaws.lean) is the reading in the library's extension field; OnBytes/Slice/ uses
the laws at it.

Main definitions: pairsVal, Tensor.denseVal, unshift, shiftIn.
Main theorems: pairsAt_val, Tensor.entry_val, Tensor.entry_scale, Tensor.entry_insertChoice,
Form.entry_val, Form.entry_add, Form.entry_addEntry, Form.entry_addForm, Form.entry_insertChoice.

What is not claimed. Every equation on entries is between readings, not between the program's words.
The laws on insertChoice need that pos is at most the number of variables. No law here on fixLow,
addTo, dot, tensorBelow or onTable. Nothing on soundness. The program does not import this file.
-/
import OnBytes.Model.HideLaws
import OnBytes.Iop.Tensor

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Bits of an index -/

/-- The remainder by 2 m, from the lowest bit and the half's remainder by m. -/
theorem mod_two_mul (x m : Nat) : x % (2 * m) = x % 2 + 2 * (x / 2 % m) := Nat.mod_mul

/-- Two numbers agree in their low n + 1 bits exactly if they agree in the lowest bit and their
halves agree in the low n bits. -/
theorem mod_pow_succ_eq_iff (x y n : Nat) :
    x % 2 ^ (n + 1) = y % 2 ^ (n + 1) ↔ x % 2 = y % 2 ∧ x / 2 % 2 ^ n = y / 2 % 2 ^ n := by
  rw [Nat.pow_succ', mod_two_mul, mod_two_mul]
  have hx := Nat.mod_lt x (by decide : 0 < 2)
  have hy := Nat.mod_lt y (by decide : 0 < 2)
  omega

/-- The index J without its bits pos, .., pos + count - 1: the higher bits move down. -/
def unshift (pos count J : Nat) : Nat := J % 2 ^ pos + 2 ^ pos * (J / 2 ^ (pos + count))

/-! ## The product of the pairs' halves -/

/-- For each pair its half that the bits of j pick, the lowest bit first: the product of what they
read as. -/
def pairsVal : List (E × E) → Nat → K
  | [], _ => 1
  | p :: ps, j => ρ.val (if j % 2 == 1 then p.2 else p.1) * pairsVal ps (j / 2)

/-- One step of pairsAt, as an equation between functions. (Stated for the two last arguments at
once. Lean's kernel compares the arguments of one function from the last on, and it would try to
compute with r and r times a half before it looks at the lists.) -/
theorem pairsAt_cons_fun (p : E × E) (ps : List (E × E)) :
    pairsAt (p :: ps) =
      fun j r => pairsAt ps (j / 2) (mulE r (if j % 2 == 1 then p.2 else p.1)) := rfl

/-- One step of pairsAt. -/
theorem pairsAt_cons (p : E × E) (ps : List (E × E)) (j : Nat) (r : E) :
    pairsAt (p :: ps) j r = pairsAt ps (j / 2) (mulE r (if j % 2 == 1 then p.2 else p.1)) :=
  congrFun (congrFun (pairsAt_cons_fun p ps) j) r

/-- Without pairs, pairsAt returns what it was given. -/
theorem pairsAt_nil (j : Nat) (r : E) : pairsAt [] j r = r := rfl

/-- pairsAt reads as what it was given times the product of the pairs' halves. -/
theorem pairsAt_val (ps : List (E × E)) (j : Nat) (r : E) :
    ρ.val (pairsAt ps j r) = ρ.val r * pairsVal ρ ps j := by
  induction ps generalizing j r with
  | nil => rw [pairsAt_nil, pairsVal, mul_one]
  | cons p ps ih => rw [pairsAt_cons, ih, ρ.mul, pairsVal, mul_assoc]

/-- The product over two lists of pairs: the second list is picked by the higher bits of the
index. -/
theorem pairsVal_append (a b : List (E × E)) (j : Nat) :
    pairsVal ρ (a ++ b) j = pairsVal ρ a j * pairsVal ρ b (j / 2 ^ a.length) := by
  induction a generalizing j with
  | nil => simp [pairsVal]
  | cons p a ih =>
    simp only [List.cons_append, pairsVal, ih, List.length_cons, Nat.pow_succ',
      Nat.div_div_eq_div_mul]
    ring

/-- Only the bits of j below the number of pairs count. -/
theorem pairsVal_mod (a : List (E × E)) (j : Nat) :
    pairsVal ρ a (j % 2 ^ a.length) = pairsVal ρ a j := by
  induction a generalizing j with
  | nil => simp [pairsVal]
  | cons p a ih =>
    have h1 : j % 2 ^ (a.length + 1) % 2 = j % 2 := by
      rw [Nat.pow_succ', mod_two_mul]
      omega
    have h2 : j % 2 ^ (a.length + 1) / 2 = j / 2 % 2 ^ a.length := by
      rw [Nat.pow_succ', mod_two_mul]
      have := Nat.mod_lt j (by decide : 0 < 2)
      omega
    simp only [pairsVal, List.length_cons, h1, h2, ih]

/-- choicePairs n value has n pairs. -/
theorem choicePairs_length (n value : Nat) : (choicePairs n value).length = n := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih => simp [choicePairs, ih]

/-- Pairs that pick bits read as 1 where the index has these bits, and as 0 elsewhere. -/
theorem pairsVal_choice (n value j : Nat) :
    pairsVal ρ (choicePairs n value) j = if j % 2 ^ n = value % 2 ^ n then 1 else 0 := by
  induction n generalizing value j with
  | zero => simp [choicePairs, pairsVal, Nat.mod_one]
  | succ n ih =>
    simp only [choicePairs, pairsVal, ih, mod_pow_succ_eq_iff]
    have hj := Nat.mod_two_eq_zero_or_one j
    have hv := Nat.mod_two_eq_zero_or_one value
    rcases hj with hj | hj <;> rcases hv with hv | hv <;>
      simp [hj, hv, ρ.zero, ρ.one]

/-! ## An index without some of its bits -/

/-- The low bits of the index stay. -/
theorem unshift_mod (pos count J : Nat) : unshift pos count J % 2 ^ pos = J % 2 ^ pos := by
  unfold unshift
  rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- The bits above the ones that are taken out move down. -/
theorem unshift_div (pos count J : Nat) :
    unshift pos count J / 2 ^ pos = J / 2 ^ (pos + count) := by
  unfold unshift
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add]

/-- Bit d of unshift pos count J is bit d of J if d is below pos, else bit d + count of J. -/
theorem unshift_bit (pos count J d : Nat) :
    unshift pos count J / 2 ^ d % 2 = J / 2 ^ (if pos ≤ d then d + count else d) % 2 := by
  by_cases h : pos ≤ d
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [if_pos h, Nat.pow_add, ← Nat.div_div_eq_div_mul, unshift_div, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    congr 3
    omega
  · rw [if_neg h]
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le h)
    unfold unshift
    have h1 : 2 ^ (d + e + 1) = 2 ^ d * (2 * 2 ^ e) := by
      rw [Nat.add_assoc, Nat.pow_add, Nat.add_comm e 1, Nat.pow_add, Nat.pow_one]
    rw [h1, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.mod_mul_right_div_self, Nat.mul_assoc, Nat.add_mul_mod_self_left, mod_two_mul]
    omega

/-! ## The entries of a tensor -/

/-- What the written-out factor reads as at index j; 1 if there is none. -/
def Tensor.denseVal (v : Tensor) (j : Nat) : K :=
  if v.denseVars.isEmpty then 1
  else ρ.val (v.values.getD (v.first + denseIndex v.denseVars 0 j) zeroE)

/-- An entry reads as the scalar times the pairs' halves times the written-out factor. -/
theorem Tensor.entry_val (v : Tensor) (j : Nat) :
    ρ.val (v.entry j) = ρ.val v.scalar * pairsVal ρ v.pairs j * v.denseVal ρ j := by
  unfold Tensor.entry Tensor.denseVal
  by_cases h : v.denseVars.isEmpty = true
  · simp only [h, if_true, pairsAt_val, mul_one]
  · simp only [h, Bool.false_eq_true, if_false, ρ.mul, pairsAt_val]

/-- Every entry of x times a tensor reads as the entry times x. -/
theorem Tensor.entry_scale (v : Tensor) (x : E) (j : Nat) :
    ρ.val ((v.scale x).entry j) = ρ.val (v.entry j) * ρ.val x := by
  simp only [Tensor.entry_val, Tensor.scale, Tensor.denseVal, ρ.mul]
  ring

/-- If pos is at most the number of pairs: with choicePairs count value put in before pair number
pos, the product is 0 unless the index has these bits from bit pos on, and otherwise the old pairs'
product at the index without them. -/
theorem pairsVal_insert (ps : List (E × E)) (pos count value J : Nat) (h : pos ≤ ps.length) :
    pairsVal ρ (ps.take pos ++ choicePairs count value ++ ps.drop pos) J =
      (if J / 2 ^ pos % 2 ^ count = value % 2 ^ count then 1 else 0) *
        pairsVal ρ ps (unshift pos count J) := by
  have hl : (ps.take pos).length = pos := by rw [List.length_take, Nat.min_eq_left h]
  have e : pairsVal ρ ps (unshift pos count J) =
      pairsVal ρ (ps.take pos) J * pairsVal ρ (ps.drop pos) (J / 2 ^ (pos + count)) := by
    have hm : pairsVal ρ (ps.take pos) (unshift pos count J) = pairsVal ρ (ps.take pos) J := by
      have a := pairsVal_mod ρ (ps.take pos) (unshift pos count J)
      have b := pairsVal_mod ρ (ps.take pos) J
      rw [hl] at a b
      rw [← a, ← b, unshift_mod]
    conv_lhs => rw [← List.take_append_drop pos ps]
    rw [pairsVal_append, hl, unshift_div, hm]
  rw [e, pairsVal_append, pairsVal_append, List.length_append, hl, choicePairs_length,
    pairsVal_choice]
  ring

/-- The index within the written-out factor does not change if variables are put in. -/
theorem denseIndex_insert (dv : List Nat) (pos count i J : Nat) :
    denseIndex (dv.map fun d => if pos ≤ d then d + count else d) i J =
      denseIndex dv i (unshift pos count J) := by
  induction dv generalizing i with
  | nil => rfl
  | cons d dv ih => simp only [List.map_cons, denseIndex, ih, unshift_bit]

/-- If pos is at most the number of variables: an entry of v.insertChoice pos count value reads as 0
unless the bits pos, .., pos + count - 1 of the index are the low count bits of value; otherwise it
reads as the entry of v at the index without these bits (unshift). -/
theorem Tensor.entry_insertChoice (v : Tensor) (pos count value J : Nat) (h : pos ≤ v.vars) :
    ρ.val ((v.insertChoice pos count value).entry J) =
      (if J / 2 ^ pos % 2 ^ count = value % 2 ^ count then 1 else 0) *
        ρ.val (v.entry (unshift pos count J)) := by
  simp only [Tensor.entry_val, Tensor.insertChoice, Tensor.denseVal, List.isEmpty_map,
    pairsVal_insert ρ v.pairs pos count value J h, denseIndex_insert]
  ring

/-! ## An index with bits put in -/

/-- The index e with the low count bits of value put in before bit pos: the higher bits of e move
up. -/
def shiftIn (pos count value e : Nat) : Nat :=
  e % 2 ^ pos + (value % 2 ^ count) * 2 ^ pos + (e / 2 ^ pos) * 2 ^ (pos + count)

/-- The index with the bits put in: the low bits, and above them the bits put in and the higher
bits. -/
theorem shiftIn_form (pos count value e : Nat) :
    shiftIn pos count value e =
      e % 2 ^ pos + 2 ^ pos * (value % 2 ^ count + e / 2 ^ pos * 2 ^ count) := by
  unfold shiftIn
  rw [Nat.pow_add]
  ring

/-- Above the low bits come the inserted bits and then the higher bits. -/
theorem shiftIn_div (pos count value e : Nat) :
    shiftIn pos count value e / 2 ^ pos = value % 2 ^ count + e / 2 ^ pos * 2 ^ count := by
  rw [shiftIn_form, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add]

/-- The low bits stay. -/
theorem shiftIn_mod (pos count value e : Nat) :
    shiftIn pos count value e % 2 ^ pos = e % 2 ^ pos := by
  rw [shiftIn_form, Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- Bits that were put in and are taken out again leave the index as it was. -/
theorem unshift_shiftIn (pos count value e : Nat) :
    unshift pos count (shiftIn pos count value e) = e := by
  unfold unshift
  rw [shiftIn_mod, Nat.pow_add, ← Nat.div_div_eq_div_mul, shiftIn_div,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add]
  exact Nat.mod_add_div e (2 ^ pos)

/-- An index J is e with the bits put in exactly if J has these bits and is e without them. -/
theorem shiftIn_eq_iff (pos count value e J : Nat) :
    shiftIn pos count value e = J ↔
      J / 2 ^ pos % 2 ^ count = value % 2 ^ count ∧ unshift pos count J = e := by
  constructor
  · rintro rfl
    refine ⟨?_, unshift_shiftIn pos count value e⟩
    rw [shiftIn_div, Nat.add_mul_mod_self_right, Nat.mod_mod]
  · rintro ⟨h1, rfl⟩
    rw [shiftIn_form, unshift_mod, unshift_div, ← h1, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    have a1 := Nat.mod_add_div J (2 ^ pos)
    have a2 := Nat.mod_add_div (J / 2 ^ pos) (2 ^ count)
    rw [Nat.mul_comm (J / 2 ^ pos / 2 ^ count), a2, a1]

/-! ## The entries of a form -/

/-- The sum of the tensors' entries at an index, as Form.entry adds it up. -/
theorem foldl_tensors (l : List Tensor) (j : Nat) (a : E) :
    ρ.val (l.foldl (fun r v => addE r (v.entry j)) a) =
      ρ.val a + (l.map fun v => ρ.val (v.entry j)).sum :=
  Model.foldl_adds ρ.val (fun (r : E) (v : Tensor) => addE r (v.entry j))
    (fun v : Tensor => ρ.val (v.entry j)) (fun (r : E) (v : Tensor) => ρ.add r (v.entry j)) l a

/-- The sum of the single entries at an index, as Form.entry adds it up. -/
theorem foldl_entries (l : List (Nat × E)) (j : Nat) (a : E) :
    ρ.val (l.foldl (fun r e => if e.1 == j then addE r e.2 else r) a) =
      ρ.val a + (l.map fun e => if e.1 = j then ρ.val e.2 else 0).sum := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    by_cases h : e.1 = j
    · simp only [h, beq_self_eq_true, if_true, ρ.add]
      ring
    · have h' : (e.1 == j) = false := by simp [h]
      simp only [h, h', Bool.false_eq_true, if_false, zero_add]

/-- An entry of a form reads as the sum of the tensors' entries and of the single entries at that
index. -/
theorem Form.entry_val (f : Form) (j : Nat) :
    ρ.val (f.entry j) = (f.tensors.map fun v => ρ.val (v.entry j)).sum +
      (f.entries.map fun e => if e.1 = j then ρ.val e.2 else 0).sum := by
  unfold Form.entry
  simp only [foldl_entries, foldl_tensors, ρ.zero, zero_add]

/-- Every entry of the form without parts reads as 0. -/
theorem Form.entry_empty (j : Nat) : ρ.val (({} : Form).entry j) = 0 := by
  simp [Form.entry_val]

/-- An entry of a form plus a tensor reads as the sum of the two entries. -/
theorem Form.entry_add (f : Form) (v : Tensor) (j : Nat) :
    ρ.val ((f.add v).entry j) = ρ.val (f.entry j) + ρ.val (v.entry j) := by
  simp only [Form.entry_val, Form.add, List.map_cons, List.sum_cons]
  ring

/-- A single entry more adds its coefficient at its index and nothing elsewhere. -/
theorem Form.entry_addEntry (f : Form) (index : Nat) (c : E) (j : Nat) :
    ρ.val ((f.addEntry index c).entry j) =
      ρ.val (f.entry j) + if index = j then ρ.val c else 0 := by
  simp only [Form.entry_val, Form.addEntry, List.map_cons, List.sum_cons]
  ring

/-- Every entry of x times a form reads as the entry times x. -/
theorem Form.entry_scale (f : Form) (x : E) (j : Nat) :
    ρ.val ((f.scale x).entry j) = ρ.val (f.entry j) * ρ.val x := by
  simp only [Form.entry_val, Form.scale, List.map_map, add_mul, ← List.sum_map_mul_right]
  congr 2
  · apply List.map_congr_left
    intro v _
    simp [Tensor.entry_scale]
  · apply List.map_congr_left
    intro e _
    by_cases h : e.1 = j <;> simp [h, ρ.mul]

/-- An entry of the sum of two forms reads as the sum of the two entries. -/
theorem Form.entry_plus (f other : Form) (j : Nat) :
    ρ.val ((f.plus other).entry j) = ρ.val (f.entry j) + ρ.val (other.entry j) := by
  simp only [Form.entry_val, Form.plus, List.map_append, List.sum_append]
  ring

/-- An entry of f.addForm other x reads as the entry of f plus the entry of other times x. -/
theorem Form.entry_addForm (f other : Form) (x : E) (j : Nat) :
    ρ.val ((f.addForm other x).entry j) = ρ.val (f.entry j) + ρ.val (other.entry j) * ρ.val x := by
  rw [Form.addForm, Form.entry_plus, Form.entry_scale]

/-- Tensor.entry_insertChoice for a form, if pos is at most the number of variables of each of its
tensors. -/
theorem Form.entry_insertChoice (f : Form) (pos count value J : Nat)
    (h : ∀ v ∈ f.tensors, pos ≤ v.vars) :
    ρ.val ((f.insertChoice pos count value).entry J) =
      (if J / 2 ^ pos % 2 ^ count = value % 2 ^ count then 1 else 0) *
        ρ.val (f.entry (unshift pos count J)) := by
  simp only [Form.entry_val, Form.insertChoice, List.map_map, mul_add, ← List.sum_map_mul_left]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro v hv
    exact Tensor.entry_insertChoice ρ v pos count value J (h v hv)
  · congr 2
    funext e
    have hs := shiftIn_eq_iff pos count value e.1 J
    unfold shiftIn at hs
    by_cases h1 : J / 2 ^ pos % 2 ^ count = value % 2 ^ count
    · by_cases h2 : unshift pos count J = e.1
      · simp [hs.2 ⟨h1, h2⟩, h1, h2]
      · have h3 : ¬ (e.1 = unshift pos count J) := fun x => h2 x.symm
        have h4 := fun x => h2 (hs.1 x).2
        simp only [Function.comp, if_neg h4, if_neg h3, mul_zero]
    · have h4 := fun x => h1 (hs.1 x).1
      simp only [Function.comp, if_neg h4, if_neg h1, zero_mul]

end OnBytes

#print axioms OnBytes.Tensor.entry_insertChoice
#print axioms OnBytes.Form.entry_addForm
#print axioms OnBytes.Form.entry_insertChoice
