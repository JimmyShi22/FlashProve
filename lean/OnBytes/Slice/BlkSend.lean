-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSend.lean: the program's sample row, read in the field.

After a prover has sent an oracle message, the verifier draws a seed, a point z and a factor beta,
and the prover answers with the value of a linear form on the whole message. The program builds the
left side of that equation as a row (OnBytes/Iop/Send.lean: `Send.form`). This file gives the row's
coefficient on every entry of the message's two tables, for every shape of a message.

The pad is the last places of the last row of the mask table (of the main table, if the message has
no mask rows): one place or three for each answer (`Send.pad`).

The result. On an entry that is no place of the pad the coefficient is the weight of the point at
the entry's vertex on the message's cube. On a place of the pad it is beta times the place's basis
element if the place belongs to the answer that is asked for, and 0 if it belongs to another one.
In this closed form it is proved for one answer whose pad is one place. For all shapes what the pad
changes is left as a sum over its places.

Main definitions: `tableW` (the weight that a table's entry has under z), `padW` (what a place of
the pad has in place of it).
Main theorems: `coefAt_form` (all shapes: the weight, plus the change at each place of the pad that
is at the entry), `coefAt_form_other` (0 on every other oracle message), `form_parts` (what the
row is made of), `pad_one` and `coefAt_form_one` (one answer whose pad is one place),
`tableW_eq_eqW` (the weight as the library's weight at the entry's vertex on the whole cube),
`rowFits_form`, `maskFits_form` (the row can be carried to a group's tables).

Not claimed. Nothing on the run of the block SEND. Nothing on how the entries of a message are named
in the library's sample.
-/
import OnBytes.Iop.Send
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.BlkRow
import OnBytes.Slice.BlkTens

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The row, written out -/

/-- The equality vector on one of the two tables of a message, as `Send.form` makes it. -/
def sendTensor (codes : Codes) (s : OracleShape) (z : List E) (part : Part) : Tensor :=
  match part with
  | .main => Tensor.eq (z.take (Send.cube codes s).mainBits)
      (Send.front z (Send.cube codes s) (Send.cube codes s).mainBits false)
  | .mask => Tensor.eq (z.take (Send.cube codes s).maskBits)
      (Send.front z (Send.cube codes s) (Send.cube codes s).maskBits true)

/-- One step of the loop over the places of the pad. -/
def padStep (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ) (r : Row)
    (p : PadPlace) : Row :=
  r.addUnit o p.part p.index
    (subE (if p.answer == answer then mulE seed.beta p.basis else zeroE)
      ((sendTensor codes s seed.z p.part).entry p.index))

/-- `Send.form`, written out with the names above. -/
theorem form_eq (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ) :
    Send.form codes s o seed answer = (Send.pad codes s).map fun places =>
      let row0 := places.foldl (padStep codes s o seed answer) { kind := .sample }
      let row1 := if (Send.cube codes s).hasMain then
        row0.add o .main (sendTensor codes s seed.z .main) else row0
      if (Send.cube codes s).hasMask then row1.add o .mask (sendTensor codes s seed.z .mask)
      else row1 := by
  have hT : ∀ part : Part, (if part == .main then sendTensor codes s seed.z .main
      else sendTensor codes s seed.z .mask) = sendTensor codes s seed.z part := fun part => by
    cases part <;> rfl
  unfold Send.form
  cases Send.pad codes s with
  | none => rfl
  | some places =>
    have hstep : padStep codes s o seed answer = fun r p =>
        r.addUnit o p.part p.index
          (subE (if p.answer == answer then mulE seed.beta p.basis else zeroE)
            ((if p.part == .main then sendTensor codes s seed.z .main
              else sendTensor codes s seed.z .mask).entry p.index)) :=
      funext fun r => funext fun p => by
        unfold padStep
        rw [hT]
    rw [hstep]
    rfl

/-! ## The coefficient of the row -/

/-- The weight that entry i of a table has under the point z. -/
def tableW (codes : Codes) (s : OracleShape) (z : List E) (part : Part) (i : ℕ) : GE :=
  readE ((sendTensor codes s z part).entry i)

/-- What a place of the pad has in place of its weight: beta times its basis element if it
belongs to the answer that is asked for, else 0. -/
def padW (seed : SampleSeed) (answer : ℕ) (p : PadPlace) : GE :=
  if p.answer == answer then readE seed.beta * readE p.basis else 0

/-- True if the message has rows of this kind. -/
def hasPart (c : SampleCube) : Part → Bool
  | .main => c.hasMain
  | .mask => c.hasMask

/-- What the places of the pad that are at entry i of a table change there. -/
def padSum (codes : Codes) (s : OracleShape) (seed : SampleSeed) (answer : ℕ)
    (places : List PadPlace) (part : Part) (i : ℕ) : GE :=
  (places.map fun p => if p.part == part && p.index == i then
    padW seed answer p - tableW codes s seed.z p.part p.index else 0).sum

/-- The coefficient that one step of the loop over the pad writes. -/
theorem readE_padCoeff (codes : Codes) (s : OracleShape) (seed : SampleSeed) (answer : ℕ)
    (p : PadPlace) :
    readE (subE (if p.answer == answer then mulE seed.beta p.basis else zeroE)
      ((sendTensor codes s seed.z p.part).entry p.index)) =
      padW seed answer p - tableW codes s seed.z p.part p.index := by
  unfold padW tableW
  rw [readE_sub]
  by_cases h : (p.answer == answer) = true
  · rw [if_pos h, if_pos h, readE_mul]
  · rw [if_neg h, if_neg h, readE_zero]

/-- The loop over the places of the pad, from any row. -/
theorem coefAt_padFold (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (part : Part) (i : ℕ) : ∀ (places : List PadPlace) (r : Row),
    coefAt (places.foldl (padStep codes s o seed answer) r) o part i =
      coefAt r o part i + padSum codes s seed answer places part i
  | [], r => by
      unfold padSum
      rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | p :: places, r => by
      have hsum : padSum codes s seed answer (p :: places) part i =
          (if p.part == part && p.index == i then
            padW seed answer p - tableW codes s seed.z p.part p.index else 0) +
            padSum codes s seed answer places part i := by
        unfold padSum
        rw [List.map_cons, List.sum_cons]
      rw [List.foldl_cons, coefAt_padFold codes s o seed answer part i places, hsum]
      unfold padStep
      rw [coefAt_addUnit, readE_padCoeff, beq_self_eq_true, Bool.true_and, add_assoc]

/-- The row with which the loop begins has no coefficient. -/
theorem coefAt_sampleStart (o : ℕ) (part : Part) (i : ℕ) :
    coefAt { kind := .sample } o part i = 0 := by
  rw [coefAt_eq]
  simp [termsAt, unitsAt, runsAt, formsAt]

/-- The coefficient of the sample row, for every shape of a message: the weight of the entry, if
the message has the table, plus what the places of the pad on this entry change. -/
theorem coefAt_form (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) (part : Part) (i : ℕ) :
    ∃ places, Send.pad codes s = some places ∧
      coefAt row o part i =
        (if hasPart (Send.cube codes s) part then tableW codes s seed.z part i else 0) +
          padSum codes s seed answer places part i := by
  rw [form_eq] at h
  obtain ⟨places, hp, hrow⟩ := Option.map_eq_some_iff.1 h
  refine ⟨places, hp, ?_⟩
  have h0 := coefAt_padFold codes s o seed answer part i places { kind := .sample }
  rw [coefAt_sampleStart, zero_add] at h0
  rw [← hrow]
  unfold tableW
  cases part <;> cases hm : (Send.cube codes s).hasMain <;>
    cases hk : (Send.cube codes s).hasMask <;>
    simp [hasPart, hm, hk, coefAt_add, h0, add_comm]

/-- The loop over the places of the pad writes nothing on another oracle message. -/
theorem coefAt_padFold_other (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed)
    (answer o' : ℕ) (ho : o' ≠ o) (part : Part) (i : ℕ) : ∀ (places : List PadPlace) (r : Row),
    coefAt (places.foldl (padStep codes s o seed answer) r) o' part i = coefAt r o' part i
  | [], _ => rfl
  | p :: places, r => by
      have hb : (o == o') = false := beq_eq_false_iff_ne.2 fun e => ho e.symm
      rw [List.foldl_cons, coefAt_padFold_other codes s o seed answer o' ho part i places]
      unfold padStep
      rw [coefAt_addUnit, hb, Bool.false_and, Bool.false_and, if_neg Bool.false_ne_true, add_zero]

/-- The sample row of one oracle message is 0 on every other one. -/
theorem coefAt_form_other (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed)
    (answer : ℕ) (row : Row) (h : Send.form codes s o seed answer = some row) (o' : ℕ)
    (ho : o' ≠ o) (part : Part) (i : ℕ) : coefAt row o' part i = 0 := by
  rw [form_eq] at h
  obtain ⟨places, _, hrow⟩ := Option.map_eq_some_iff.1 h
  have hb : (o == o') = false := beq_eq_false_iff_ne.2 fun e => ho e.symm
  have h0 := coefAt_padFold_other codes s o seed answer o' ho part i places { kind := .sample }
  rw [coefAt_sampleStart] at h0
  rw [← hrow]
  cases hm : (Send.cube codes s).hasMain <;> cases hk : (Send.cube codes s).hasMask <;>
    simp [coefAt_add, h0, hb]

/-- The loop over the places of the pad keeps a row's kind and target. -/
theorem padFold_keeps (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ) :
    ∀ (places : List PadPlace) (r : Row),
      (places.foldl (padStep codes s o seed answer) r).kind = r.kind ∧
        (places.foldl (padStep codes s o seed answer) r).target = r.target
  | [], _ => ⟨rfl, rfl⟩
  | _ :: places, _ => padFold_keeps codes s o seed answer places _

/-- The sample row is marked as one, and its target is 0. -/
theorem form_kind (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) :
    row.kind = .sample ∧ row.target = zeroE := by
  rw [form_eq] at h
  obtain ⟨places, _, hrow⟩ := Option.map_eq_some_iff.1 h
  have h0 := padFold_keeps codes s o seed answer places { kind := .sample }
  rw [← hrow]
  cases hm : (Send.cube codes s).hasMain <;> cases hk : (Send.cube codes s).hasMask <;>
    exact h0

/-! ## The parts of the row -/

/-- The loop over the places of the pad adds single entries alone. -/
theorem padFold_parts (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ) :
    ∀ (places : List PadPlace) (r : Row),
      (places.foldl (padStep codes s o seed answer) r).terms = r.terms ∧
        (places.foldl (padStep codes s o seed answer) r).runs = r.runs ∧
        (places.foldl (padStep codes s o seed answer) r).forms = r.forms
  | [], _ => ⟨rfl, rfl, rfl⟩
  | _ :: places, _ => padFold_parts codes s o seed answer places _

/-- The sample row has one term for each table that the message has, no run and no form on a main
table. -/
theorem form_parts (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) :
    row.terms.toList =
        (if (Send.cube codes s).hasMain then [⟨o, .main, sendTensor codes s seed.z .main⟩]
          else []) ++
        (if (Send.cube codes s).hasMask then [⟨o, .mask, sendTensor codes s seed.z .mask⟩]
          else []) ∧
      row.runs = #[] ∧ row.forms = #[] := by
  rw [form_eq] at h
  obtain ⟨places, _, hrow⟩ := Option.map_eq_some_iff.1 h
  have h0 := padFold_parts codes s o seed answer places { kind := .sample }
  rw [← hrow]
  cases hm : (Send.cube codes s).hasMain <;> cases hk : (Send.cube codes s).hasMask <;>
    simp [Row.add, h0.1, h0.2.1, h0.2.2]

/-! ## One answer whose pad is one place -/

/-- The table that holds the pad: the mask table if the message has mask rows. -/
def padPart (c : SampleCube) : Part := if c.hasMask then .mask else .main

/-- The length of a message under the code of the rows that hold the pad. -/
def padLen (codes : Codes) (s : OracleShape) : ℕ :=
  if (Send.cube codes s).hasMask then (codes.mask.getD s.maskCode default).ell
  else (codes.base.getD s.code default).ell

/-- The index of the pad's one place: the last place of the last row of its table. -/
def padIndex (codes : Codes) (s : OracleShape) : ℕ :=
  ((if (Send.cube codes s).hasMask then s.maskRows else s.mainRows) - 1) +
    (padLen codes s - 1) *
      2 ^ (if (Send.cube codes s).hasMask then (Send.cube codes s).maskRowBits
        else (Send.cube codes s).mainRowBits)

/-- `Send.pad` with one answer, and rows over the extension field where the pad is. -/
theorem pad_cases (codes : Codes) (s : OracleShape) (h1 : s.answers = 1)
    (he : ((Send.cube codes s).hasMask || s.mainDeg == 3) = true) :
    Send.pad codes s = if padLen codes s < 1 then none
      else some [⟨padPart (Send.cube codes s), padIndex codes s, 0, thetaE 0⟩] := by
  unfold Send.pad padPart padIndex padLen
  simp only [h1, he, if_true, Nat.mul_one]
  split
  · rfl
  · simp [List.range_succ]

/-- With one answer, and rows over the extension field where the pad is, the pad is one place. -/
theorem pad_one (codes : Codes) (s : OracleShape) (h1 : s.answers = 1)
    (he : ((Send.cube codes s).hasMask || s.mainDeg == 3) = true) (hl : 1 ≤ padLen codes s) :
    Send.pad codes s =
      some [⟨padPart (Send.cube codes s), padIndex codes s, 0, thetaE 0⟩] := by
  rw [pad_cases codes s h1 he, if_neg (Nat.not_lt.2 hl)]

/-- The first basis element is 1. -/
theorem readE_theta_zero : readE (thetaE 0) = 1 := readE_one

/-- The coefficient of the sample row, with one answer whose pad is one place: beta on the pad, and
elsewhere the weight of the entry, if the message has the table. -/
theorem coefAt_form_one (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form codes s o seed 0 = some row) (h1 : s.answers = 1)
    (he : ((Send.cube codes s).hasMask || s.mainDeg == 3) = true)
    (hp : hasPart (Send.cube codes s) (padPart (Send.cube codes s)) = true)
    (part : Part) (i : ℕ) :
    coefAt row o part i =
      if part = padPart (Send.cube codes s) ∧ i = padIndex codes s then readE seed.beta
      else if hasPart (Send.cube codes s) part then tableW codes s seed.z part i else 0 := by
  obtain ⟨places, hpl, hc⟩ := coefAt_form codes s o seed 0 row h part i
  have hl : 1 ≤ padLen codes s := by
    by_contra hlt
    rw [pad_cases codes s h1 he, if_pos (Nat.lt_of_not_le hlt)] at hpl
    cases hpl
  rw [pad_one codes s h1 he hl] at hpl
  have hplaces : places = [⟨padPart (Send.cube codes s), padIndex codes s, 0, thetaE 0⟩] :=
    (Option.some.inj hpl).symm
  have hw : padW seed 0 ⟨padPart (Send.cube codes s), padIndex codes s, 0, thetaE 0⟩ =
      readE seed.beta := by
    show (if ((0 : ℕ) == 0) = true then readE seed.beta * readE (thetaE 0) else 0) = readE seed.beta
    have h00 : ((0 : ℕ) == 0) = true := rfl
    rw [if_pos h00, readE_theta_zero, mul_one]
  rw [hc, hplaces]
  unfold padSum
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hw]
  show (if hasPart (Send.cube codes s) part then tableW codes s seed.z part i else 0) +
    (if (padPart (Send.cube codes s) == part && padIndex codes s == i) = true then
      readE seed.beta -
        tableW codes s seed.z (padPart (Send.cube codes s)) (padIndex codes s) else 0) = _
  by_cases hh : part = padPart (Send.cube codes s) ∧ i = padIndex codes s
  · obtain ⟨e1, e2⟩ := hh
    have hb : (padPart (Send.cube codes s) == part && padIndex codes s == i) = true := by
      rw [e1, e2, beq_self_eq_true, beq_self_eq_true]
      rfl
    have hR : (if part = padPart (Send.cube codes s) ∧ i = padIndex codes s then readE seed.beta
        else if hasPart (Send.cube codes s) part then tableW codes s seed.z part i else 0) =
        readE seed.beta := if_pos ⟨e1, e2⟩
    have hL : (if hasPart (Send.cube codes s) part then tableW codes s seed.z part i else 0) =
        tableW codes s seed.z (padPart (Send.cube codes s)) (padIndex codes s) := by
      rw [e1, e2, hp, if_pos rfl]
    rw [hR, hL, hb, if_pos rfl]
    ring
  · have hb : (padPart (Send.cube codes s) == part && padIndex codes s == i) = false := by
      rw [Bool.and_eq_false_iff]
      by_cases e1 : part = padPart (Send.cube codes s)
      · exact Or.inr (beq_eq_false_iff_ne.2 fun e2 => hh ⟨e1, e2.symm⟩)
      · exact Or.inl (beq_eq_false_iff_ne.2 fun e => e1 e.symm)
    rw [if_neg hh, hb, if_neg Bool.false_ne_true, add_zero]

/-! ## The weight on the whole cube -/

/-- The loop of `Send.front`. -/
theorem readE_foldOneSub : ∀ (l : List E) (f : E),
    readE (l.foldl (fun f x => mulE f (subE oneE x)) f) =
      readE f * (l.map fun x => 1 - readE x).prod
  | [], f => by
      rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | x :: l, f => by
      rw [List.foldl_cons, readE_foldOneSub l, readE_mul, readE_sub, readE_one, List.map_cons,
        List.prod_cons, mul_assoc]

/-- More variables above an index that is too small to have a digit there: each gives the factor
1 - z. -/
theorem eqW_zeros (z : ℕ → GE) (i : ℕ) : ∀ (l : List E) (n : ℕ), i < 2 ^ n →
    (∀ t, t < l.length → z (n + t) = readL l t) →
    eqW (n + l.length) z i = eqW n z i * (l.map fun x => 1 - readE x).prod
  | [], n, _, _ => by
      rw [List.length_nil, Nat.add_zero, List.map_nil, List.prod_nil, mul_one]
  | x :: l, n, hi, hz => by
      have h1 : n + (x :: l).length = n + 1 + l.length := by
        rw [List.length_cons]
        omega
      have hi' : i < 2 ^ (n + 1) := by
        rw [pow_succ]
        omega
      have hz0 : z n = readE x := hz 0 (Nat.succ_pos _)
      have hz' : ∀ t, t < l.length → z (n + 1 + t) = readL l t := fun t ht => by
        have h2 := hz (t + 1) (Nat.succ_lt_succ ht)
        rw [readL_cons_succ] at h2
        rw [← h2]
        congr 1
        omega
      rw [h1, eqW_zeros z i l (n + 1) hi' hz', eqW_succ, Nat.testBit_lt_two_pow hi,
        if_neg Bool.false_ne_true, hz0, List.map_cons, List.prod_cons, mul_assoc]

/-- The top variable, at an index below 2^n. -/
theorem eqW_top_zero (n : ℕ) (z : ℕ → GE) (i : ℕ) (hi : i < 2 ^ n) :
    eqW (n + 1) z i = eqW n z i * (1 - z n) := by
  rw [eqW_succ, Nat.testBit_lt_two_pow hi, if_neg Bool.false_ne_true]

/-- The top variable, at 2^n plus an index below 2^n. -/
theorem eqW_top_one (n : ℕ) (z : ℕ → GE) (i : ℕ) (hi : i < 2 ^ n) :
    eqW (n + 1) z (2 ^ n + i) = eqW n z i * z n := by
  have hlow : eqW n z (2 ^ n + i) = eqW n z i := by
    rw [← eqW_mod n z (2 ^ n + i), Nat.add_mod_left, eqW_mod]
  rw [eqW_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hi, Bool.not_false, if_pos rfl,
    hlow]

/-- With one table the factor in front is 1. -/
theorem readE_front_single (z : List E) (c : SampleCube) (tb : ℕ) (mask : Bool)
    (hb : (c.hasMain && c.hasMask) = false) : readE (Send.front z c tb mask) = 1 := by
  unfold Send.front
  rw [hb, Bool.not_false, if_pos rfl, readE_one]

/-- With both tables, the factor in front times the weight on a table's own variables is the weight
on the whole cube: at the entry's index for the main table, and 2^(bits - 1) higher for the mask
table. -/
theorem front_mul_eqW (z : List E) (c : SampleCube) (tb : ℕ) (mask : Bool)
    (hb : (c.hasMain && c.hasMask) = true) (htb : tb + 1 ≤ c.bits) (hz : c.bits ≤ z.length)
    (i : ℕ) (hi : i < 2 ^ tb) :
    readE (Send.front z c tb mask) * eqW tb (readL z) i =
      eqW c.bits (readL z) ((if mask then 2 ^ (c.bits - 1) else 0) + i) := by
  have hlen : ((z.take (c.bits - 1)).drop tb).length = c.bits - 1 - tb := by
    rw [List.length_drop, List.length_take]
    omega
  have hmid : eqW (c.bits - 1) (readL z) i = eqW tb (readL z) i *
      (((z.take (c.bits - 1)).drop tb).map fun x => 1 - readE x).prod := by
    have h := eqW_zeros (readL z) i ((z.take (c.bits - 1)).drop tb) tb hi fun t ht => by
      rw [hlen] at ht
      rw [readL_drop, readL_take _ _ _ (by omega)]
    rw [hlen] at h
    rw [← h]
    congr 1
    omega
  have hi' : i < 2 ^ (c.bits - 1) :=
    Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
  have hbits : c.bits = c.bits - 1 + 1 := by omega
  have htop : readE (z.getD (c.bits - 1) zeroE) = readL z (c.bits - 1) := rfl
  unfold Send.front
  rw [hb, Bool.not_true, if_neg Bool.false_ne_true, readE_foldOneSub]
  cases mask
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, Nat.zero_add, readE_sub, readE_one,
      htop]
    conv_rhs => rw [hbits]
    rw [eqW_top_zero _ _ _ hi', hmid]
    ring
  · rw [if_pos rfl, if_pos rfl, htop]
    conv_rhs => rw [hbits]
    rw [Nat.add_sub_cancel, eqW_top_one _ _ _ hi', hmid]
    ring

/-- The index bits of one of the two tables. -/
def partBits (c : SampleCube) : Part → ℕ
  | .main => c.mainBits
  | .mask => c.maskBits

/-- The vertex of an entry on the message's cube, as a number: the entry's index in its table, and
2^(bits - 1) more for the mask table of a message that has both tables. -/
def cubeIdx (c : SampleCube) (part : Part) (i : ℕ) : ℕ :=
  (if c.hasMain && c.hasMask && part == .mask then 2 ^ (c.bits - 1) else 0) + i

/-- The weight of an entry: the factor in front, times the weight on the table's own variables. -/
theorem tableW_eq (codes : Codes) (s : OracleShape) (z : List E) (part : Part) (i : ℕ) :
    tableW codes s z part i =
      readE (Send.front z (Send.cube codes s) (partBits (Send.cube codes s) part) (part == .mask)) *
        eqW (min (partBits (Send.cube codes s) part) z.length) (readL z) i := by
  have key : ∀ (n : ℕ) (f : E), readE ((Tensor.eq (z.take n) f).entry i) =
      readE f * eqW (min n z.length) (readL z) i := fun n f => by
    rw [readE_eq, List.length_take]
    exact congrArg _ (eqW_congr _ _ _ _ fun t ht =>
      readL_take _ _ _ (Nat.lt_of_lt_of_le ht (Nat.min_le_left _ _)))
  cases part
  · exact key _ _
  · exact key _ _

/-- The cube has a main table if the message has main rows. -/
theorem cube_hasMain_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).hasMain = decide (0 < s.mainRows) := rfl

/-- The cube has a mask table if the message has mask rows. -/
theorem cube_hasMask_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).hasMask = decide (0 < s.maskRows) := rfl

/-- The bits that spell a main row. -/
theorem cube_mainRowBits_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).mainRowBits =
      if (Send.cube codes s).hasMain then ceilLog2 s.mainRows else 0 := rfl

/-- The bits that spell a mask row. -/
theorem cube_maskRowBits_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).maskRowBits =
      if (Send.cube codes s).hasMask then ceilLog2 s.maskRows else 0 := rfl

/-- The number of the cube's variables, as `Send.cube` sets it. -/
theorem cube_bits_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).bits =
      if (Send.cube codes s).hasMain && (Send.cube codes s).hasMask then
        max (Send.cube codes s).mainBits (Send.cube codes s).maskBits + 1
      else (Send.cube codes s).mainBits + (Send.cube codes s).maskBits := rfl

/-- The index bits of the main table, as `Send.cube` sets them. -/
theorem cube_mainBits_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).mainBits = if (Send.cube codes s).hasMain then
      (Send.cube codes s).mainRowBits + (codes.base.getD s.code default).logEll else 0 := rfl

/-- The index bits of the mask table, as `Send.cube` sets them. -/
theorem cube_maskBits_eq (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).maskBits = if (Send.cube codes s).hasMask then
      (Send.cube codes s).maskRowBits + (codes.mask.getD s.maskCode default).logEll else 0 := rfl

/-- A message with both tables has one variable more than the larger table. -/
theorem cube_bits_both (codes : Codes) (s : OracleShape)
    (h : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = true) :
    (Send.cube codes s).bits =
      max (Send.cube codes s).mainBits (Send.cube codes s).maskBits + 1 := by
  rw [cube_bits_eq, if_pos h]

/-- A message with one table has that table's variables. -/
theorem cube_bits_single (codes : Codes) (s : OracleShape)
    (h : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = false) (part : Part)
    (hp : hasPart (Send.cube codes s) part = true) :
    (Send.cube codes s).bits = partBits (Send.cube codes s) part := by
  have em : (Send.cube codes s).hasMain = false → (Send.cube codes s).mainBits = 0 := fun hm => by
    rw [cube_mainBits_eq, hm]
    rfl
  have ek : (Send.cube codes s).hasMask = false → (Send.cube codes s).maskBits = 0 := fun hk => by
    rw [cube_maskBits_eq, hk]
    rfl
  rw [cube_bits_eq, h, if_neg Bool.false_ne_true]
  cases part
  · have hm : (Send.cube codes s).hasMain = true := hp
    rw [hm, Bool.true_and] at h
    rw [ek h, Nat.add_zero]
    rfl
  · have hk : (Send.cube codes s).hasMask = true := hp
    rw [hk, Bool.and_true] at h
    rw [em h, Nat.zero_add]
    rfl

/-- The weight of an entry of a table is the library's weight of the point at the entry's vertex on
the message's cube, if the point has as many coordinates as the cube has variables, the message has
the table and the index is within it. -/
theorem tableW_eq_eqW (codes : Codes) (s : OracleShape) (z : List E) (part : Part) (i : ℕ)
    (hz : z.length = (Send.cube codes s).bits) (hp : hasPart (Send.cube codes s) part = true)
    (hi : i < 2 ^ partBits (Send.cube codes s) part) :
    tableW codes s z part i =
      eqW (Send.cube codes s).bits (readL z) (cubeIdx (Send.cube codes s) part i) := by
  rw [tableW_eq]
  unfold cubeIdx
  by_cases hb : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = true
  · have hbits := cube_bits_both codes s hb
    have hle : partBits (Send.cube codes s) part + 1 ≤ (Send.cube codes s).bits := by
      rw [hbits]
      cases part
      · exact Nat.succ_le_succ (Nat.le_max_left _ _)
      · exact Nat.succ_le_succ (Nat.le_max_right _ _)
    have hmin : min (partBits (Send.cube codes s) part) z.length =
        partBits (Send.cube codes s) part := by
      rw [hz]
      omega
    rw [hmin, front_mul_eqW z _ _ _ hb hle (Nat.le_of_eq hz.symm) i hi, hb, Bool.true_and]
  · have hb' : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = false :=
      Bool.eq_false_iff.2 hb
    have hbits := cube_bits_single codes s hb' part hp
    rw [readE_front_single _ _ _ _ hb', one_mul, hz, hbits, Nat.min_self, hb', Bool.false_and,
      if_neg Bool.false_ne_true, Nat.zero_add]

/-! ## The row fits the statement's tables -/

/-- The equality vector at a point has as many variables as the point has coordinates. -/
theorem vars_eqTensor (z : List E) (f : E) : (Tensor.eq z f).vars = z.length := by
  unfold Tensor.vars Tensor.eq
  exact List.length_map _

/-- A table has at most as many index bits as the cube has variables. -/
theorem partBits_le_bits (codes : Codes) (s : OracleShape) (part : Part) :
    partBits (Send.cube codes s) part ≤ (Send.cube codes s).bits := by
  by_cases hb : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = true
  · rw [cube_bits_both codes s hb]
    cases part
    · exact Nat.le_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.le_succ_of_le (Nat.le_max_right _ _)
  · rw [cube_bits_eq, if_neg hb]
    cases part
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left _ _

/-- The equality vector on a table has the table's index bits as its variables, if the point is
long enough. -/
theorem vars_sendTensor (codes : Codes) (s : OracleShape) (z : List E) (part : Part)
    (hz : (Send.cube codes s).bits ≤ z.length) :
    (sendTensor codes s z part).vars = partBits (Send.cube codes s) part := by
  have hle := partBits_le_bits codes s part
  cases part
  · show (Tensor.eq (z.take (Send.cube codes s).mainBits) _).vars = (Send.cube codes s).mainBits
    have hle' : (Send.cube codes s).mainBits ≤ (Send.cube codes s).bits := hle
    rw [vars_eqTensor, List.length_take]
    omega
  · show (Tensor.eq (z.take (Send.cube codes s).maskBits) _).vars = (Send.cube codes s).maskBits
    have hle' : (Send.cube codes s).maskBits ≤ (Send.cube codes s).bits := hle
    rw [vars_eqTensor, List.length_take]
    omega

/-- The sample row meets the conditions under which a row can be carried to a group's tables, if
the point has a coordinate for each variable of the cube and each table of the message has at least
as many index bits as the statement gives it row bits. -/
theorem rowFits_form (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) (S : Statement)
    (hz : (Send.cube codes s).bits ≤ seed.z.length)
    (hS : ∀ part, hasPart (Send.cube codes s) part = true →
      S.rowBits o part ≤ partBits (Send.cube codes s) part) : RowFits S row := by
  obtain ⟨ht, hr, hf⟩ := form_parts codes s o seed answer row h
  refine ⟨fun t hmem => ?_, fun w hw => ?_, fun f hmem => ?_⟩
  · rw [ht, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · by_cases hm : (Send.cube codes s).hasMain = true
      · rw [if_pos hm, List.mem_singleton] at hmem
        rw [hmem]
        show S.rowBits o .main ≤ (sendTensor codes s seed.z .main).vars
        rw [vars_sendTensor codes s seed.z .main hz]
        exact hS .main hm
      · rw [if_neg hm] at hmem
        exact absurd hmem List.not_mem_nil
    · by_cases hk : (Send.cube codes s).hasMask = true
      · rw [if_pos hk, List.mem_singleton] at hmem
        rw [hmem]
        show S.rowBits o .mask ≤ (sendTensor codes s seed.z .mask).vars
        rw [vars_sendTensor codes s seed.z .mask hz]
        exact hS .mask hk
      · rw [if_neg hk] at hmem
        exact absurd hmem List.not_mem_nil
  · rw [hr] at hw
    exact absurd hw List.not_mem_nil
  · rw [hf] at hmem
    exact absurd hmem List.not_mem_nil

/-- The sample row's vector on the mask table reaches over the whole of a group's places, if the
point has a coordinate for each variable of the cube and the mask table's index bits are at least
its row bits in the statement plus the group's place bits. -/
theorem maskFits_form (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) (S : Statement) (L : GroupLayout)
    (hz : (Send.cube codes s).bits ≤ seed.z.length)
    (hS : (Send.cube codes s).hasMask = true →
      S.rowBits o .mask + L.logEllZk ≤ (Send.cube codes s).maskBits) : MaskFits S L row := by
  obtain ⟨ht, _, _⟩ := form_parts codes s o seed answer row h
  intro t hmem hpart
  rw [ht, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · by_cases hm : (Send.cube codes s).hasMain = true
    · rw [if_pos hm, List.mem_singleton] at hmem
      rw [hmem] at hpart
      cases hpart
    · rw [if_neg hm] at hmem
      exact absurd hmem List.not_mem_nil
  · by_cases hk : (Send.cube codes s).hasMask = true
    · rw [if_pos hk, List.mem_singleton] at hmem
      rw [hmem]
      show S.rowBits o .mask + L.logEllZk ≤ (sendTensor codes s seed.z .mask).vars
      rw [vars_sendTensor codes s seed.z .mask hz]
      exact hS hk
    · rw [if_neg hk] at hmem
      exact absurd hmem List.not_mem_nil

/-- `MaskFits` does not look at a row's target. -/
theorem maskFits_target (S : Statement) (L : GroupLayout) (row : Row) (hr : MaskFits S L row)
    (y : E) : MaskFits S L { row with target := y } := hr

/-- The conditions of `RowFits` do not look at a row's target. -/
theorem rowFits_target (S : Statement) (row : Row) (hr : RowFits S row) (y : E) :
    RowFits S { row with target := y } := ⟨hr.terms, hr.runs, hr.forms⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.form_eq
#print axioms OnBytes.Slice.readE_padCoeff
#print axioms OnBytes.Slice.coefAt_padFold
#print axioms OnBytes.Slice.coefAt_sampleStart
#print axioms OnBytes.Slice.coefAt_form
#print axioms OnBytes.Slice.coefAt_padFold_other
#print axioms OnBytes.Slice.coefAt_form_other
#print axioms OnBytes.Slice.padFold_keeps
#print axioms OnBytes.Slice.form_kind
#print axioms OnBytes.Slice.padFold_parts
#print axioms OnBytes.Slice.form_parts
#print axioms OnBytes.Slice.pad_cases
#print axioms OnBytes.Slice.pad_one
#print axioms OnBytes.Slice.readE_theta_zero
#print axioms OnBytes.Slice.coefAt_form_one
#print axioms OnBytes.Slice.readE_foldOneSub
#print axioms OnBytes.Slice.eqW_zeros
#print axioms OnBytes.Slice.eqW_top_zero
#print axioms OnBytes.Slice.eqW_top_one
#print axioms OnBytes.Slice.readE_front_single
#print axioms OnBytes.Slice.front_mul_eqW
#print axioms OnBytes.Slice.tableW_eq
#print axioms OnBytes.Slice.cube_hasMain_eq
#print axioms OnBytes.Slice.cube_hasMask_eq
#print axioms OnBytes.Slice.cube_mainRowBits_eq
#print axioms OnBytes.Slice.cube_maskRowBits_eq
#print axioms OnBytes.Slice.cube_bits_eq
#print axioms OnBytes.Slice.cube_mainBits_eq
#print axioms OnBytes.Slice.cube_maskBits_eq
#print axioms OnBytes.Slice.cube_bits_both
#print axioms OnBytes.Slice.cube_bits_single
#print axioms OnBytes.Slice.tableW_eq_eqW
#print axioms OnBytes.Slice.vars_eqTensor
#print axioms OnBytes.Slice.partBits_le_bits
#print axioms OnBytes.Slice.vars_sendTensor
#print axioms OnBytes.Slice.rowFits_form
#print axioms OnBytes.Slice.maskFits_form
#print axioms OnBytes.Slice.maskFits_target
#print axioms OnBytes.Slice.rowFits_target
