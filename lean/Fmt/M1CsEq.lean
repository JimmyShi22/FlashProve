-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1CsEq.lean: the first toy (a product test), the code switch: the fast form that the decision
runs (Fmt/M1Cs.lean: `csStep`) is its meaning (`csStepLit`: the text's rows written out, then their
sum under the powers of theta): for all arguments, no hypothesis.

Both functions compute the linear claim on the new oracle message that the verifier holds after a
code switch, a step of the toy's proximity test; this file proves that an optimised function equals
the plain one. Theorems and proofs; a few definitions to state them with. Core Lean, no Mathlib.
A row (`GRow`, Fmt/M1Types.lean) is a linear equation on the message behind a sent oracle message:
coefficient vectors c (on the main table) and d (on the mask table) and a target t. A weight is the
power of theta under which a row is added. A stretch is a run of consecutive indices of a table.

What the two are. `csStepLit` makes, for every drawn position, three rows written out at the length
of the new oracle message's tables (the second and the third on the mask table alone), which on the
mask table are 0 outside one or two stretches, and adds row after row under the next power of theta
(`sumRows`, of the vector arithmetic of Fmt/M1Types.lean). `csStep` adds a draw's three rows in one
pass: on the main table the old main code's generator row under the weight; on the mask table one
list from the index 0 on, of five stretches. Tests (#guard) in Fmt/M1Cs.lean compare the two at tiny
sizes.

Why it holds without a hypothesis on the inputs. The arithmetic is on words: a sum or a product is
reduced modulo p, an input need not be. Two things could make the two forms differ.
(1) Adding 0 is not the identity on an entry with a word from p on. But every entry of the sum so
far is itself the result of an addition (after the first two rows already), so its words are below p
(`Inv`).
(2) A row of `csStepLit` holds "x + 0" where `csStep` has x. But that entry is then multiplied by
the weight, and a product may have a factor reduced first (`mulEF_addE_zero`, `mulEF_zero_addE`).
The weight after the first two rows is (1 · theta) · theta in `csStepLit` and theta · theta in
`csStep`: one value (`weight_two`). Where a table is too short for the five stretches, both forms
are cut alike.

Main names:
  `Spec.csStep_eq` (the statement), `csStep_eq` (its proof): for all arguments,
    csStep f old new s sample xs theta col = csStepLit f old new s sample xs theta col.
  `Can f l`: all entries of l have their words below p.
  `Inv f nM nD S`: the two tables of the sum's state S have the lengths nM and nD, and both satisfy
    `Can`.
  `cPart`, `dPart`: if the table so far satisfies `Can` (`hC`), a draw's three rows, added one after
    the other, give what the one pass gives: `cPart` on the main table, `dPart` on the mask table.
  `draw_step`, `inv_draw`: one draw, from a state with `Inv` (`h`): the two forms agree, and `Inv`
    holds again.
  `rowsOf`, `fastOf`, `all_draws`: all draws, from a state with `Inv`; a drawn position without a
    column gives "none" in both (a column: `Col`, Fmt/M1Types.lean).
  `stepL f u w r`: u + w r on lists: what that arithmetic's `axpy` is (`axpy_stepL`: by definition).

Limits: this file does not say that `csStepLit` is what the programs (the C++ implementation that
comes with this Lean code) compute: it follows their description; this file's sources include no
value of theirs on this block; what has been compared: the head of Fmt/M1Cs.lean. It says nothing on
soundness, nothing on time.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1Cs

set_option autoImplicit false

namespace Fmt.M1.CsEq

/-! ## The field: what adding 0 and multiplying by 0 do -/

theorem red_self (f : Fld) (a : UInt64) (h : f.ok a = true) : f.red a.toNat = a := by
  have h1 : a.toNat < f.p := of_decide_eq_true h
  unfold Fld.red
  rw [Nat.mod_eq_of_lt h1]
  exact UInt64.ofNat_toNat

theorem add_zero' (f : Fld) (a : UInt64) (h : f.ok a = true) : f.add a 0 = a := by
  unfold Fld.add
  exact red_self f a h

theorem okE_iff (f : Fld) (e : E) :
    f.okE e = true ↔ f.ok e.1 = true ∧ f.ok e.2.1 = true ∧ f.ok e.2.2 = true := by
  unfold Fld.okE
  simp only [Bool.and_eq_true, and_assoc]

/-- adding 0 to an element whose three words are below p gives it back -/
theorem addE_zero (f : Fld) (e : E) (h : f.okE e = true) : f.addE e Fld.zeroE = e := by
  obtain ⟨h1, h2, h3⟩ := (okE_iff f e).1 h
  unfold Fld.addE Fld.zeroE
  exact Prod.ext (add_zero' f _ h1) (Prod.ext (add_zero' f _ h2) (add_zero' f _ h3))

theorem okE_addE (f : Fld) (a b : E) : f.okE (f.addE a b) = true :=
  (okE_iff f _).2 ⟨Fld.ok_add f _ _, Fld.ok_add f _ _, Fld.ok_add f _ _⟩

theorem red_zero (f : Fld) : f.red 0 = 0 := by
  unfold Fld.red
  rw [Nat.zero_mod]
  rfl

theorem mulEF_zero (f : Fld) (w : E) : f.mulEF w Fld.zeroE = Fld.zeroE := by
  unfold Fld.mulEF Fld.zeroE
  simp [red_zero]

/-- a factor may be reduced first -/
theorem mulEF_addE_zero (f : Fld) (w x : E) : f.mulEF w (f.addE x Fld.zeroE) = f.mulEF w x := by
  unfold Fld.mulEF Fld.addE Fld.zeroE Fld.add
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod, Nat.mul_mod]

theorem mulEF_zero_addE (f : Fld) (w x : E) : f.mulEF w (f.addE Fld.zeroE x) = f.mulEF w x := by
  unfold Fld.mulEF Fld.addE Fld.zeroE Fld.add
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod, Nat.mul_mod]

theorem mulEF_ofF (f : Fld) (w : E) (p : UInt64) : f.mulEF w (Fld.ofF p) = f.scaleE p w :=
  (mulEF_eq f w _).trans (mulE_ofF' f w p)

theorem addE_zero_zero (f : Fld) : f.addE Fld.zeroE Fld.zeroE = Fld.zeroE :=
  addE_zero f _ (by cases f <;> rfl)

/-- The weight after two rows: (1 · x) · x is x · x. -/
theorem weight_two (f : Fld) (x : E) : f.mulE (f.mulE Fld.oneE x) x = f.mulE x x := by
  rw [← mulEF_eq f, ← mulEF_eq f, ← mulEF_eq f]
  unfold Fld.mulEF Fld.oneE
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod, Nat.mul_mod]

/-! ## Lists, entry by entry -/

/-- the entry at i; 0 beyond the end -/
def at0 (l : List E) (i : Nat) : E := l.getD i Fld.zeroE

theorem at0_ge (l : List E) (i : Nat) (h : l.length ≤ i) : at0 l i = Fld.zeroE := by
  unfold at0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem at0_lt (l : List E) (i : Nat) (h : i < l.length) : at0 l i = l[i] := by
  unfold at0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem ext_at0 (l l' : List E) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → at0 l i = at0 l' i) : l = l' := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  rw [← at0_lt l i h1, ← at0_lt l' i h2]
  exact h i h1

theorem at0_map (g : E → E) (l : List E) (i : Nat) (h : i < l.length) :
    at0 (l.map g) i = g (at0 l i) := by
  rw [at0_lt _ _ (by rw [List.length_map]; exact h), at0_lt _ _ h, List.getElem_map]

theorem at0_mapU (g : UInt64 → E) (l : List UInt64) (i : Nat) (h : i < l.length) :
    at0 (l.map g) i = g l[i] := by
  rw [at0_lt _ _ (by rw [List.length_map]; exact h), List.getElem_map]

theorem at0_append (l l' : List E) (i : Nat) :
    at0 (l ++ l') i = if i < l.length then at0 l i else at0 l' (i - l.length) := by
  unfold at0
  simp only [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left h]
  · rename_i h
    rw [List.getElem?_append_right (Nat.le_of_not_lt h)]

theorem length_padL (n : Nat) (u : List E) : (padL n u).length = max u.length n := by
  unfold padL
  rw [List.length_append, List.length_replicate]
  omega

theorem at0_padL (n : Nat) (u : List E) (i : Nat) : at0 (padL n u) i = at0 u i := by
  unfold padL
  rw [at0_append]
  split
  · rfl
  · rename_i h
    rw [at0_ge u i (Nat.le_of_not_lt h)]
    unfold at0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

theorem length_addL (f : Fld) (u v : List E) : (addL f u v).length = max u.length v.length := by
  unfold addL
  rw [List.length_zipWith, length_padL, length_padL]
  omega

theorem at0_addL (f : Fld) (u v : List E) (i : Nat) (h : i < max u.length v.length) :
    at0 (addL f u v) i = f.addE (at0 u i) (at0 v i) := by
  have h1 : i < (padL v.length u).length := by rw [length_padL]; exact h
  have h2 : i < (padL u.length v).length := by rw [length_padL]; omega
  rw [at0_lt _ _ (by rw [length_addL]; exact h)]
  unfold addL
  rw [List.getElem_zipWith, ← at0_lt _ _ h1, ← at0_lt _ _ h2, at0_padL, at0_padL]

theorem length_layAt (n o : Nat) (w : List E) : (layAt n o w).toList.length = n := by
  unfold layAt
  simp

theorem at0_layAt (n o : Nat) (w : List E) (i : Nat) (h : i < n) :
    at0 (layAt n o w).toList i = if o ≤ i then at0 w (i - o) else Fld.zeroE := by
  rw [at0_lt _ _ (by rw [length_layAt]; exact h)]
  unfold layAt at0
  simp

theorem length_addPre (f : Fld) : ∀ a b : List E, (addPre f a b).length = a.length
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => by
      show (addPre f as bs).length + 1 = as.length + 1
      rw [length_addPre f as bs]

theorem at0_addPre (f : Fld) :
    ∀ (a b : List E) (i : Nat), i < a.length →
      at0 (addPre f a b) i = if i < b.length then f.addE (at0 a i) (at0 b i) else at0 a i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _ => rfl
  | a :: as, b :: bs, 0, _ => rfl
  | a :: as, b :: bs, i + 1, h => by
      have ih := at0_addPre f as bs i (Nat.lt_of_succ_lt_succ h)
      show at0 (addPre f as bs) i =
        if i + 1 < bs.length + 1 then f.addE (at0 as i) (at0 bs i) else at0 as i
      rw [ih]
      by_cases hb : i < bs.length
      · rw [if_pos hb, if_pos (Nat.succ_lt_succ hb)]
      · rw [if_neg hb, if_neg (fun h' => hb (Nat.lt_of_succ_lt_succ h'))]


/-! ## One row added under a weight, entry by entry -/

/-- all entries have their words below p -/
def Can (f : Fld) (l : List E) : Prop := ∀ i, f.okE (at0 l i) = true

theorem okE_zero (f : Fld) : f.okE Fld.zeroE = true := by cases f <;> rfl

theorem can_addL (f : Fld) (u v : List E) : Can f (addL f u v) := by
  intro i
  by_cases h : i < max u.length v.length
  · rw [at0_addL f u v i h]
    exact okE_addE f _ _
  · rw [at0_ge _ _ (by rw [length_addL]; omega)]
    exact okE_zero f

theorem can_addPre (f : Fld) (a b : List E) (h : Can f a) : Can f (addPre f a b) := by
  intro i
  by_cases hi : i < a.length
  · rw [at0_addPre f a b i hi]
    split
    · exact okE_addE f _ _
    · exact h i
  · rw [at0_ge _ _ (by rw [length_addPre]; omega)]
    exact okE_zero f

/-- u + w r, on lists -/
def stepL (f : Fld) (u : List E) (w : E) (r : List E) : List E := addL f u (r.map (f.mulEF w))

theorem length_stepL (f : Fld) (u : List E) (w : E) (r : List E) :
    (stepL f u w r).length = max u.length r.length := by
  unfold stepL
  rw [length_addL, List.length_map]

theorem at0_mulMap (f : Fld) (w : E) (r : List E) (i : Nat) :
    at0 (r.map (f.mulEF w)) i = f.mulEF w (at0 r i) := by
  by_cases h : i < r.length
  · exact at0_map _ r i h
  · rw [at0_ge _ _ (by rw [List.length_map]; omega), at0_ge r i (by omega), mulEF_zero]

theorem at0_stepL (f : Fld) (u : List E) (w : E) (r : List E)
    (i : Nat) (h : i < max u.length r.length) :
    at0 (stepL f u w r) i = f.addE (at0 u i) (f.mulEF w (at0 r i)) := by
  unfold stepL
  rw [at0_addL f _ _ i (by rw [List.length_map]; exact h), at0_mulMap]

theorem can_stepL (f : Fld) (u : List E) (w : E) (r : List E) : Can f (stepL f u w r) :=
  can_addL f _ _

/-- elements of the base field under a weight -/
def sc (f : Fld) (w : E) (l : List UInt64) : List E := l.map fun p => f.scaleE p w

theorem length_sc (f : Fld) (w : E) (l : List UInt64) : (sc f w l).length = l.length :=
  List.length_map _

theorem mulEF_at0_ofF (f : Fld) (w : E) (l : List UInt64) (i : Nat) :
    f.mulEF w (at0 (l.map Fld.ofF) i) = at0 (sc f w l) i := by
  by_cases h : i < l.length
  · rw [at0_mapU _ _ _ h, mulEF_ofF]
    unfold sc
    rw [at0_mapU _ _ _ h]
  · rw [at0_ge _ _ (by rw [List.length_map]; omega),
      mulEF_zero, at0_ge _ _ (by rw [length_sc]; omega)]

/-- a row that stands on two stretches which do not meet, under a weight -/
theorem mul_row (f : Fld) (w : E) (gm gt : List UInt64) (a o i : Nat) (h : a + gm.length ≤ o) :
    f.mulEF w (f.addE (if a ≤ i then at0 (gm.map Fld.ofF) (i - a) else Fld.zeroE)
          (if o ≤ i then at0 (gt.map Fld.ofF) (i - o) else Fld.zeroE)) =
      if i < o then (if a ≤ i then at0 (sc f w gm) (i - a) else Fld.zeroE)
      else at0 (sc f w gt) (i - o) := by
  by_cases hi : i < o
  · rw [if_neg (by omega : ¬ o ≤ i), if_pos hi, mulEF_addE_zero]
    split
    · exact mulEF_at0_ofF f w gm _
    · exact mulEF_zero f w
  · rw [if_pos (by omega : o ≤ i), if_neg hi, if_pos (by omega : a ≤ i),
      at0_ge (gm.map Fld.ofF) (i - a) (by rw [List.length_map]; omega), mulEF_zero_addE]
    exact mulEF_at0_ofF f w gt _

theorem at0_five (l1 l2 l3 l4 l5 : List E) (i : Nat) :
    at0 (l1 ++ l2 ++ l3 ++ l4 ++ l5) i =
      if i < l1.length then at0 l1 i
      else if i < l1.length + l2.length then at0 l2 (i - l1.length)
      else if i < l1.length + l2.length + l3.length then at0 l3 (i - (l1.length + l2.length))
      else if i < l1.length + l2.length + l3.length + l4.length then
        at0 l4 (i - (l1.length + l2.length + l3.length))
      else at0 l5 (i - (l1.length + l2.length + l3.length + l4.length)) := by
  simp only [at0_append, List.length_append]
  by_cases h1 : i < l1.length
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos h1, if_pos h1]
  · by_cases h2 : i < l1.length + l2.length
    · rw [if_pos (by omega), if_pos (by omega), if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · by_cases h3 : i < l1.length + l2.length + l3.length
      · rw [if_pos (by omega), if_pos h3, if_neg h2, if_neg h1, if_neg h2, if_pos h3]
      · by_cases h4 : i < l1.length + l2.length + l3.length + l4.length
        · rw [if_pos h4, if_neg h3, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
        · rw [if_neg h4, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- The main table's part of a draw: if all entries of c have their words below p (`hC`), the three
rows added one after the other give `addPre f c (sc f w0 gmC)`. -/
theorem cPart (f : Fld) (c : List E) (hC : Can f c) (w0 w1 w2 : E) (gmC : List UInt64) :
    stepL f (stepL f (stepL f c w0 (layAt c.length 0 (gmC.map Fld.ofF)).toList) w1 []) w2 [] =
      addPre f c (sc f w0 gmC) := by
  have l1 : (stepL f c w0 (layAt c.length 0 (gmC.map Fld.ofF)).toList).length = c.length := by
    rw [length_stepL, length_layAt]; omega
  have l2 : (stepL f (stepL f c w0 (layAt c.length 0 (gmC.map Fld.ofF)).toList) w1 []).length =
      c.length := by
    rw [length_stepL, l1]; exact Nat.max_eq_left (Nat.zero_le _)
  have l3 : (stepL f (stepL f (stepL f c w0 (layAt c.length 0 (gmC.map Fld.ofF)).toList) w1 []) w2
        []).length = c.length := by
    rw [length_stepL, l2]; exact Nat.max_eq_left (Nat.zero_le _)
  refine ext_at0 _ _ (by rw [l3, length_addPre]) fun i hi => ?_
  rw [l3] at hi
  rw [at0_stepL f _ _ _ i (by rw [l2]; exact Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)),
    at0_stepL f _ _ _ i (by rw [l1]; exact Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)),
    at0_stepL f _ _ _ i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)), at0_layAt _ _ _ i hi,
    if_pos (Nat.zero_le i), Nat.sub_zero, mulEF_at0_ofF, at0_ge [] i (Nat.zero_le _), mulEF_zero,
    mulEF_zero, addE_zero f _ (okE_addE f _ _), addE_zero f _ (okE_addE f _ _),
    at0_addPre f c _ i hi, length_sc]
  split
  · rfl
  · rename_i h
    rw [at0_ge (sc f w0 gmC) i (by rw [length_sc]; omega), addE_zero f _ (hC i)]

theorem a3X (f : Fld) (d X : E) :
    f.addE (f.addE (f.addE d X) Fld.zeroE) Fld.zeroE = f.addE d X := by
  rw [addE_zero f _ (okE_addE f _ _), addE_zero f _ (okE_addE f _ _)]

theorem a3Y (f : Fld) (d Y : E) (h : f.okE d = true) :
    f.addE (f.addE (f.addE d Fld.zeroE) Y) Fld.zeroE = f.addE d Y := by
  rw [addE_zero f d h, addE_zero f _ (okE_addE f _ _)]

theorem a3Z (f : Fld) (d Z : E) (h : f.okE d = true) :
    f.addE (f.addE (f.addE d Fld.zeroE) Fld.zeroE) Z = f.addE d Z := by
  rw [addE_zero f d h, addE_zero f d h]

theorem a30 (f : Fld) (d : E) (h : f.okE d = true) :
    f.addE (f.addE (f.addE d Fld.zeroE) Fld.zeroE) Fld.zeroE = d := by
  rw [addE_zero f d h, addE_zero f d h, addE_zero f d h]

theorem mul_one_row (f : Fld) (w : E) (g : List UInt64) (o i : Nat) :
    f.mulEF w (if o ≤ i then at0 (g.map Fld.ofF) (i - o) else Fld.zeroE) =
      if o ≤ i then at0 (sc f w g) (i - o) else Fld.zeroE := by
  split
  · exact mulEF_at0_ofF f w g _
  · exact mulEF_zero f w

/-- The mask table's part of a draw: the three rows stand on five stretches that do not meet. If all
entries of d have their words below p (`hC`), the three rows added one after the other give d with
one list of five parts added onto its front (`addPre`). -/
theorem dPart (f : Fld) (d : List E) (hC : Can f d) (w0 w1 w2 : E) (gm gtC gt : List UInt64) :
    stepL f (stepL f (stepL f d w0 (layAt d.length (2 * gm.length) (gtC.map Fld.ofF)).toList) w1
          (addL f (layAt d.length 0 (gm.map Fld.ofF)).toList
            (layAt d.length (2 * gm.length + gtC.length) (gt.map Fld.ofF)).toList))
        w2 (addL f (layAt d.length gm.length (gm.map Fld.ofF)).toList
          (layAt d.length (2 * gm.length + gtC.length + gt.length) (gt.map Fld.ofF)).toList) =
      addPre f d (sc f w1 gm ++ sc f w2 gm ++ sc f w0 gtC ++ sc f w1 gt ++ sc f w2 gt) := by
  have lr2 : (addL f (layAt d.length 0 (gm.map Fld.ofF)).toList
        (layAt d.length (2 * gm.length + gtC.length) (gt.map Fld.ofF)).toList).length =
      d.length := by
    rw [length_addL, length_layAt, length_layAt]; exact Nat.max_self _
  have lr3 : (addL f (layAt d.length gm.length (gm.map Fld.ofF)).toList
        (layAt d.length (2 * gm.length + gtC.length + gt.length) (gt.map Fld.ofF)).toList).length =
      d.length := by
    rw [length_addL, length_layAt, length_layAt]; exact Nat.max_self _
  have l1 : (stepL f d w0 (layAt d.length (2 * gm.length) (gtC.map Fld.ofF)).toList).length =
      d.length := by
    rw [length_stepL, length_layAt]; exact Nat.max_self _
  have l2 : (stepL f (stepL f d w0 (layAt d.length (2 * gm.length) (gtC.map Fld.ofF)).toList) w1
        (addL f (layAt d.length 0 (gm.map Fld.ofF)).toList
          (layAt d.length (2 * gm.length + gtC.length) (gt.map Fld.ofF)).toList)).length =
      d.length := by
    rw [length_stepL, l1, lr2]; exact Nat.max_self _
  refine ext_at0 _ _
    (by rw [length_stepL, l2, lr3, length_addPre]; exact Nat.max_self _) fun i hi => ?_
  rw [length_stepL, l2, lr3, Nat.max_self] at hi
  rw [at0_stepL f _ _ _ i (by rw [l2, lr3, Nat.max_self]; exact hi),
    at0_stepL f _ _ _ i (by rw [l1, lr2, Nat.max_self]; exact hi),
    at0_stepL f _ _ _ i (by rw [length_layAt, Nat.max_self]; exact hi),
    at0_addL f _ _ i (by rw [length_layAt, length_layAt, Nat.max_self]; exact hi),
    at0_addL f _ _ i (by rw [length_layAt, length_layAt, Nat.max_self]; exact hi),
    at0_layAt _ _ _ i hi, at0_layAt _ _ _ i hi, at0_layAt _ _ _ i hi, at0_layAt _ _ _ i hi,
    at0_layAt _ _ _ i hi, mul_one_row, mul_row f w1 gm gt 0 _ i (by omega),
    mul_row f w2 gm gt gm.length _ i (by omega), at0_addPre f d _ i hi, at0_five]
  simp only [List.length_append, length_sc, Nat.sub_zero]
  have hd := hC i
  by_cases hA : i < gm.length
  · have c1 : ¬ 2 * gm.length ≤ i := by omega
    have c2 : i < 2 * gm.length + gtC.length := by omega
    have c3 : 0 ≤ i := Nat.zero_le i
    have c4 : i < 2 * gm.length + gtC.length + gt.length := by omega
    have c5 : ¬ gm.length ≤ i := by omega
    have c6 : i < gm.length + gm.length + gtC.length + gt.length + gt.length := by omega
    simp only [c1, c2, c3, c4, c5, c6, hA, ↓reduceIte]
    exact a3Y f _ _ hd
  · by_cases hB : i < gm.length + gm.length
    · have c1 : ¬ 2 * gm.length ≤ i := by omega
      have c2 : i < 2 * gm.length + gtC.length := by omega
      have c3 : 0 ≤ i := Nat.zero_le i
      have c4 : i < 2 * gm.length + gtC.length + gt.length := by omega
      have c5 : gm.length ≤ i := by omega
      have c6 : i < gm.length + gm.length + gtC.length + gt.length + gt.length := by omega
      simp only [c1, c2, c3, c4, c5, c6, hA, hB, ↓reduceIte]
      rw [at0_ge (sc f w1 gm) i (by rw [length_sc]; omega)]
      exact a3Z f _ _ hd
    · by_cases hCc : i < gm.length + gm.length + gtC.length
      · have c1 : 2 * gm.length ≤ i := by omega
        have c2 : i < 2 * gm.length + gtC.length := by omega
        have c3 : 0 ≤ i := Nat.zero_le i
        have c4 : i < 2 * gm.length + gtC.length + gt.length := by omega
        have c5 : gm.length ≤ i := by omega
        have c6 : i < gm.length + gm.length + gtC.length + gt.length + gt.length := by omega
        have e : i - 2 * gm.length = i - (gm.length + gm.length) := by omega
        simp only [c1, c2, c3, c4, c5, c6, hA, hB, hCc, ↓reduceIte]
        rw [at0_ge (sc f w1 gm) i (by rw [length_sc]; omega),
          at0_ge (sc f w2 gm) (i - gm.length) (by rw [length_sc]; omega), e]
        exact a3X f _ _
      · by_cases hD : i < gm.length + gm.length + gtC.length + gt.length
        · have c1 : 2 * gm.length ≤ i := by omega
          have c2 : ¬ i < 2 * gm.length + gtC.length := by omega
          have c4 : i < 2 * gm.length + gtC.length + gt.length := by omega
          have c5 : gm.length ≤ i := by omega
          have c6 : i < gm.length + gm.length + gtC.length + gt.length + gt.length := by omega
          have e : i - (2 * gm.length + gtC.length) = i - (gm.length + gm.length + gtC.length) := by
            omega
          simp only [c1, c2, c4, c5, c6, hA, hB, hCc, hD, ↓reduceIte]
          rw [at0_ge (sc f w0 gtC) (i - 2 * gm.length) (by rw [length_sc]; omega),
            at0_ge (sc f w2 gm) (i - gm.length) (by rw [length_sc]; omega), e]
          exact a3Y f _ _ hd
        · have c1 : 2 * gm.length ≤ i := by omega
          have c2 : ¬ i < 2 * gm.length + gtC.length := by omega
          have c4 : ¬ i < 2 * gm.length + gtC.length + gt.length := by omega
          have e : i - (2 * gm.length + gtC.length + gt.length) =
              i - (gm.length + gm.length + gtC.length + gt.length) := by omega
          simp only [c1, c2, c4, hA, hB, hCc, hD, ↓reduceIte]
          rw [at0_ge (sc f w0 gtC) (i - 2 * gm.length) (by rw [length_sc]; omega),
            at0_ge (sc f w1 gt) (i - (2 * gm.length + gtC.length)) (by rw [length_sc]; omega), e]
          by_cases hE : i < gm.length + gm.length + gtC.length + gt.length + gt.length
          · rw [if_pos hE]
            exact a3Z f _ _ hd
          · rw [if_neg hE, at0_ge (sc f w2 gt) _ (by rw [length_sc]; omega)]
            exact a30 f _ hd

/-! ## The sum of rows as a fold; one draw -/

/-- one row more under the present weight; then the next weight: the step of sumRows -/
def stF (f : Fld) (x : E) (s : GRow × E) (R : GRow) : GRow × E :=
  (⟨axpy f s.1.c s.2 R.c, axpy f s.1.d s.2 R.d, f.addE s.1.t (f.mulE s.2 R.t)⟩, f.mulE s.2 x)

theorem sumRows_fold (f : Fld) (x : E) (rows : List GRow) :
    sumRows f x rows = (rows.foldl (stF f x) (⟨#[], #[], Fld.zeroE⟩, Fld.oneE)).1 := rfl

theorem axpy_stepL (f : Fld) (u : Array E) (w : E) (v : Array E) :
    axpy f u w v = (stepL f u.toList w v.toList).toArray := rfl

/-- the state of the sum as lists; and back -/
def toSt (S : GRow × E) : List E × List E × E × E := (S.1.c.toList, S.1.d.toList, S.1.t, S.2)
def ofSt (a : List E × List E × E × E) : GRow × E :=
  (⟨a.1.toArray, a.2.1.toArray, a.2.2.1⟩, a.2.2.2)

theorem ofSt_toSt (S : GRow × E) : ofSt (toSt S) = S := rfl
theorem toSt_ofSt (a : List E × List E × E × E) : toSt (ofSt a) = a := rfl

/-- the two tables have their lengths, and all entries have their words below p -/
def Inv (f : Fld) (nM nD : Nat) (S : GRow × E) : Prop :=
  S.1.c.toList.length = nM ∧ S.1.d.toList.length = nD ∧ Can f S.1.c.toList ∧ Can f S.1.d.toList

theorem length_powers (z : UInt64) : ∀ (n : Nat) (s : UInt64), (powers z n s).length = n
  | 0, _ => rfl
  | n + 1, s => by
      show (powers z n _).length + 1 = n + 1
      rw [length_powers z n]

theorem length_genM (C : Code) (x : Nat) : (genM C x).length = C.l := length_powers _ _ _
theorem length_genT (C : Code) (x : Nat) : (genT C x).length = C.r := length_powers _ _ _

/-- One draw, from a state of which `Inv` holds (`h`): the three rows added one after the other are
the one pass (`addDraw`). -/
theorem draw_step (f : Fld) (old : Stage) (nM nD : Nat) (theta : E) (s : SRow) (x : Nat) (cl : Col)
    (S : GRow × E) (h : Inv f nM nD S) :
    (drawRows f old nM nD s x cl).foldl (stF f theta) S =
      ofSt (addDraw f old theta s x cl (toSt S)) := by
  obtain ⟨hc, hd, cc, cd⟩ := h
  subst hc hd
  have e1 := length_genM old.Z (cp old.Z x)
  have e2 := length_genT old.C x
  have e3 := length_genT old.Z (cp old.Z x)
  have C1 :=
    cPart f S.1.c.toList cc S.2 (f.mulE S.2 theta) (f.mulE (f.mulE S.2 theta) theta) (genM old.C x)
  have D1 := dPart f S.1.d.toList cd S.2 (f.mulE S.2 theta) (f.mulE (f.mulE S.2 theta) theta)
    (genM old.Z (cp old.Z x)) (genT old.C x) (genT old.Z (cp old.Z x))
  rw [e1, e2, e3] at D1
  refine Prod.ext ?_ rfl
  show GRow.mk _ _ _ = GRow.mk _ _ _
  congr 1
  · exact congrArg List.toArray C1
  · exact congrArg List.toArray D1

theorem inv_draw (f : Fld) (old : Stage) (nM nD : Nat) (theta : E) (s : SRow) (x : Nat) (cl : Col)
    (S : GRow × E) (h : Inv f nM nD S) :
    Inv f nM nD (ofSt (addDraw f old theta s x cl (toSt S))) := by
  obtain ⟨hc, hd, cc, cd⟩ := h
  exact ⟨(length_addPre f _ _).trans hc, (length_addPre f _ _).trans hd,
    can_addPre f _ _ cc, can_addPre f _ _ cd⟩

/-! ## All draws -/

/-- the draws' rows, in the order drawn; none if a drawn position has no column -/
def rowsOf (f : Fld) (old : Stage) (nM nD : Nat) (s : SRow)
    (col : Nat → Option Col) (xs : List Nat) : Option (List GRow) :=
  xs.foldr (fun x (acc : Option (List GRow)) =>
    match acc, col x with
    | some rs, some cl => some (drawRows f old nM nD s x cl ++ rs)
    | _, _ => none) (some [])

/-- the one pass over the draws -/
def fastOf (f : Fld) (old : Stage) (theta : E) (s : SRow) (col : Nat → Option Col)
    (a : Option (List E × List E × E × E)) (xs : List Nat) :
    Option (List E × List E × E × E) :=
  xs.foldl (fun (acc : Option (List E × List E × E × E)) x =>
    match acc, col x with
    | some st, some cl => some (addDraw f old theta s x cl st)
    | _, _ => none) a

theorem fastOf_none (f : Fld) (old : Stage) (theta : E) (s : SRow) (col : Nat → Option Col) :
    ∀ xs, fastOf f old theta s col none xs = none
  | [] => rfl
  | _ :: xs => fastOf_none f old theta s col xs

theorem all_draws (f : Fld) (old : Stage) (nM nD : Nat) (theta : E)
    (s : SRow) (col : Nat → Option Col) :
    ∀ (xs : List Nat) (S : GRow × E), Inv f nM nD S →
      (rowsOf f old nM nD s col xs).map (fun rs => rs.foldl (stF f theta) S) =
        (fastOf f old theta s col (some (toSt S)) xs).map ofSt
  | [], _, _ => rfl
  | x :: xs, S, h => by
      cases hx : col x with
      | none =>
          have e1 : rowsOf f old nM nD s col (x :: xs) = none := by
            show (match rowsOf f old nM nD s col xs, col x with
              | some rs, some cl => some (drawRows f old nM nD s x cl ++ rs)
              | _, _ => none) = none
            rw [hx]
            cases rowsOf f old nM nD s col xs <;> rfl
          have e2 : fastOf f old theta s col (some (toSt S)) (x :: xs) = none := by
            show fastOf f old theta s col (match some (toSt S), col x with
              | some st, some cl => some (addDraw f old theta s x cl st)
              | _, _ => none) xs = none
            rw [hx]
            exact fastOf_none f old theta s col xs
          rw [e1, e2]
          rfl
      | some cl =>
          have e1 : rowsOf f old nM nD s col (x :: xs) =
              (rowsOf f old nM nD s col xs).map fun rs => drawRows f old nM nD s x cl ++ rs := by
            show (match rowsOf f old nM nD s col xs, col x with
              | some rs, some cl => some (drawRows f old nM nD s x cl ++ rs)
              | _, _ => none) = _
            rw [hx]
            cases rowsOf f old nM nD s col xs <;> rfl
          have e2 : fastOf f old theta s col (some (toSt S)) (x :: xs) =
              fastOf f old theta s col (some (addDraw f old theta s x cl (toSt S))) xs := by
            show fastOf f old theta s col (match some (toSt S), col x with
              | some st, some cl => some (addDraw f old theta s x cl st)
              | _, _ => none) xs = _
            rw [hx]
          have ih := all_draws f old nM nD theta s col xs
            (ofSt (addDraw f old theta s x cl (toSt S))) (inv_draw f old nM nD theta s x cl S h)
          rw [e1, e2, Option.map_map, ← toSt_ofSt (addDraw f old theta s x cl (toSt S)), ← ih]
          congr 1
          funext rs
          show (drawRows f old nM nD s x cl ++ rs).foldl (stF f theta) S = _
          rw [List.foldl_append, draw_step f old nM nD theta s x cl S h]

/-! ## The whole -/

/-- the carried claim as a row on the new oracle message; the sample row at the tables' lengths -/
def carriedR (f : Fld) (old new : Stage) (s : SRow) : GRow :=
  ⟨layAt (2 ^ new.k * new.C.l) 0 (fitL Fld.zeroE old.C.l s.c.toList),
    addV f (layAt (2 ^ new.h * new.Z.l) 0 (fitL Fld.zeroE old.Z.l s.d0.toList))
      (layAt (2 ^ new.h * new.Z.l) old.Z.l (fitL Fld.zeroE old.Z.l s.d1.toList)),
    s.t⟩
def smpR (new : Stage) (sample : GRow) : GRow :=
  ⟨layAt (2 ^ new.k * new.C.l) 0 sample.c.toList,
    layAt (2 ^ new.h * new.Z.l) 0 sample.d.toList,
    sample.t⟩

/-- the sum's state after these two rows -/
def S2 (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (theta : E) : GRow × E :=
  [carriedR f old new s, smpR new sample].foldl (stF f theta) (⟨#[], #[], Fld.zeroE⟩, Fld.oneE)

theorem csRows_eq (f : Fld) (old new : Stage) (s : SRow) (sample : GRow)
    (xs : List Nat) (col : Nat → Option Col) :
    csRows f old new s sample xs col =
      (rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col xs).map fun rs =>
        carriedR f old new s :: smpR new sample :: rs := rfl

theorem inv_S2 (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (theta : E) :
    Inv f (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) (S2 f old new s sample theta) := by
  refine ⟨?_, ?_, can_stepL f _ _ _, can_stepL f _ _ _⟩
  · show (stepL f (stepL f [] Fld.oneE (layAt (2 ^ new.k * new.C.l) 0 _).toList) _
        (layAt (2 ^ new.k * new.C.l) 0 _).toList).length = _
    rw [length_stepL, length_stepL, length_layAt, length_layAt, List.length_nil]
    omega
  · show (stepL f
        (stepL f [] Fld.oneE
          (addL f (layAt (2 ^ new.h * new.Z.l) 0 _).toList
            (layAt (2 ^ new.h * new.Z.l) old.Z.l _).toList))
        _ (layAt (2 ^ new.h * new.Z.l) 0 _).toList).length = _
    rw [length_stepL, length_stepL, length_addL, length_layAt, length_layAt,
      length_layAt, List.length_nil]
    omega

theorem toSt_S2 (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (theta : E) :
    toSt (S2 f old new s sample theta) =
      ((S2 f old new s sample theta).1.c.toList,
        (S2 f old new s sample theta).1.d.toList,
        (S2 f old new s sample theta).1.t,
        f.mulE theta theta) := by
  show (_, _, _, f.mulE (f.mulE Fld.oneE theta) theta) = _
  rw [weight_two]

def Spec.csStep_eq : Prop :=
  ∀ (f : Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List Nat)
      (theta : E) (col : Nat → Option Col),
    csStep f old new s sample xs theta col = csStepLit f old new s sample xs theta col

/-- The fast code switch is its meaning: `csStep` = `csStepLit`, for all arguments. -/
theorem csStep_eq : Spec.csStep_eq := by
  intro f old new s sample xs theta col
  have hL : csStepLit f old new s sample xs theta col =
      ((rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col xs).map fun rs =>
          rs.foldl (stF f theta) (S2 f old new s sample theta)).map Prod.fst := by
    unfold csStepLit
    rw [csRows_eq, Option.map_map, Option.map_map]
    rfl
  have hF : csStep f old new s sample xs theta col =
      ((fastOf f old theta s col (some (toSt (S2 f old new s sample theta))) xs).map ofSt).map
        Prod.fst := by
    rw [toSt_S2, Option.map_map]
    rfl
  rw [hL, hF, all_draws f old _ _ theta s col xs _ (inv_S2 f old new s sample theta)]

end Fmt.M1.CsEq
