--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3CallerLaidApart.lean: UNDER THE PROGRAMS' OWN TEST ON A LAYOUT
(reqLayoutOk, OnBytes/Iop/ReqRows.lean) NO ENTRY OF AN ORACLE MESSAGE's TABLE HOLDS TWO ELEMENTS:
two elements of arrays of one link, in one message, at one place of its table, are one element of
one array. Statements and proofs, on public data alone.

Why. Whoever makes a tuple of messages with prescribed symbols (msgOf,
Johnson/Desc/First/Att/K05MsgOnto.lean) needs that two symbol addresses with one seat hold one value
(SymsSit's clause "apart"). The test on a layout has the clause for it: laidOk's second conjunct:
"no entry of the table holds two elements": no two blocks of the arrays in one message meet in rows
and in places. The theorems of this library that unfold the test draw its other clauses (a block
lies in its table; the blocks of a matrix cover it): this one was unfolded by none.

Main names.
  laidIn_inj   a block lays two elements that it holds at two places.
  laidIn_in   where a block is as large in the table as in its matrix, it lays an element that it
    holds inside its own stretch of rows and of places.
  meets_of_point   two blocks whose stretches have a row and a place in common meet.
  one_of_pairwise, one_of_flat   in a list of lists whose members, laid in a row, do not meet in
    pairs: two members that meet are one member of one list.
  tableApart_of_message   the clause, out of the test on one message's arrays.
  laidPlace_apart   THE STATEMENT.

It adds no strength beyond the test's own clause. No definition is made. Called: pairwise_of_noPair
(Johnson/Desc/First/Look/K3CallerLaid.lean); message_of_layout, block_of_message
(Johnson/Goal/Meaning/LaidInside.lean); the number of an element in its block and its laws: elemNo,
laidIn_eq, holds_parts, elem_of (Johnson/Road/K4/K4PinsBlocks.lean).

Limits. One link and one message: that two seats with one number of a message name one message of
one link (a link's own messages against the kept ones) is not said here. That the test has said yes
at a description's own letters: pub_layoutOk (Johnson/IMR/LayoutOkPub.lean), not called here.
Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3CallerLaid
import Johnson.Goal.Meaning.LaidInside
import Johnson.Road.K4.K4PinsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open OnBytes.Road.K4 (elemNo laidIn_eq holds_parts elem_of)

/-! ## An element's number in its block: K4's elemNo -/

/-- **A block lays two elements that it holds at two places.** -/
theorem laidIn_inj {b : LaidBlock} {i c i' c' : ℕ} (h : laidHolds b i c = true)
    (h' : laidHolds b i' c' = true) (e : laidIn b i c = laidIn b i' c') : i = i' ∧ c = c' := by
  rw [laidIn_eq, laidIn_eq] at e
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  have ex : elemNo b i c = elemNo b i' c' :=
    calc elemNo b i c
        = 2 ^ b.placeBits * (elemNo b i c / 2 ^ b.placeBits) + elemNo b i c % 2 ^ b.placeBits :=
          (Nat.div_add_mod _ _).symm
      _ = 2 ^ b.placeBits * (elemNo b i' c' / 2 ^ b.placeBits) +
            elemNo b i' c' % 2 ^ b.placeBits := by
          rw [Nat.add_left_cancel e1, Nat.add_left_cancel e2]
      _ = elemNo b i' c' := Nat.div_add_mod _ _
  obtain ⟨a1, a2, a3, a4⟩ := holds_parts h
  obtain ⟨b1, b2, b3, b4⟩ := holds_parts h'
  obtain ⟨-, ui, uc⟩ := elem_of a2 a4
  obtain ⟨-, vi, vc⟩ := elem_of b2 b4
  rw [ex, vi] at ui
  rw [ex, vc] at uc
  omega

/-- **A block lays an element that it holds inside its own stretch of rows and of places.** -/
theorem laidIn_in {b : LaidBlock} {i c : ℕ} (h : laidHolds b i c = true)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) :
    (b.firstRow ≤ (laidIn b i c).1 ∧ (laidIn b i c).1 < b.firstRow + 2 ^ b.rowBits) ∧
      b.firstPlace ≤ (laidIn b i c).2 ∧ (laidIn b i c).2 < b.firstPlace + 2 ^ b.placeBits := by
  rw [laidIn_eq]
  obtain ⟨-, a2, -, a4⟩ := holds_parts h
  have hx : elemNo b i c < 2 ^ b.placeBits * 2 ^ b.rowBits := by
    rw [← Nat.pow_add, Nat.add_comm, hs]
    exact (elem_of a2 a4).1
  exact ⟨⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.div_lt_of_lt_mul hx) _⟩,
    Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _⟩

/-! ## Blocks that meet -/

/-- Two blocks whose stretches have a row and a place in common meet, in the test's own words. -/
theorem meets_of_point {x y : LaidBlock} {R P : ℕ}
    (hx : (x.firstRow ≤ R ∧ R < x.firstRow + 2 ^ x.rowBits) ∧
      x.firstPlace ≤ P ∧ P < x.firstPlace + 2 ^ x.placeBits)
    (hy : (y.firstRow ≤ R ∧ R < y.firstRow + 2 ^ y.rowBits) ∧
      y.firstPlace ≤ P ∧ P < y.firstPlace + 2 ^ y.placeBits) :
    (laidMeet x.firstRow x.rowBits y.firstRow y.rowBits &&
      laidMeet x.firstPlace x.placeBits y.firstPlace y.placeBits) = true := by
  simp only [laidMeet, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Nat.lt_of_le_of_lt hx.1.1 hy.1.2, Nat.lt_of_le_of_lt hy.1.1 hx.1.2⟩,
    Nat.lt_of_le_of_lt hx.2.1 hy.2.2, Nat.lt_of_le_of_lt hy.2.1 hx.2.2⟩

/-- In a list whose members do not meet in pairs, two members that meet are one. -/
theorem one_of_pairwise {β : Type} (r : β → β → Bool) : ∀ (l : List β),
    (l.Pairwise fun x y => r x y = false) → ∀ x ∈ l, ∀ y ∈ l, r x y = true → r y x = true → x = y
  | [], _, x, hx, _, _, _, _ => by cases hx
  | z :: t, hp, x, hx, y, hy, h1, h2 => by
    obtain ⟨hz, ht⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · rfl
      · rw [hz y hy'] at h1
        cases h1
    · rcases List.mem_cons.1 hy with rfl | hy'
      · rw [hz x hx'] at h2
        cases h2
      · exact one_of_pairwise r t ht x hx' y hy' h1 h2

/-- In a list of lists whose members, laid in a row, do not meet in pairs: two members that meet are
one member of one list. -/
theorem one_of_flat {α β : Type} (f : α → List β) (r : β → β → Bool) : ∀ (l : List α),
    ((l.flatMap f).Pairwise fun x y => r x y = false) → ∀ a ∈ l, ∀ a' ∈ l, ∀ x ∈ f a,
      ∀ y ∈ f a', r x y = true → r y x = true → a = a' ∧ x = y
  | [], _, a, ha, _, _, _, _, _, _, _, _ => by cases ha
  | z :: t, hp, a, ha, a', ha', x, hx, y, hy, h1, h2 => by
    rw [List.flatMap_cons, List.pairwise_append] at hp
    obtain ⟨hz, ht, hc⟩ := hp
    rcases List.mem_cons.1 ha with rfl | ha1
    · rcases List.mem_cons.1 ha' with rfl | ha2
      · exact ⟨rfl, one_of_pairwise r _ hz x hx y hy h1 h2⟩
      · rw [hc x hx y (List.mem_flatMap.2 ⟨a', ha2, hy⟩)] at h1
        cases h1
    · rcases List.mem_cons.1 ha' with rfl | ha2
      · rw [hc y hy x (List.mem_flatMap.2 ⟨a, ha1, hx⟩)] at h2
        cases h2
      · exact one_of_flat f r t ht a ha1 a' ha2 x hx y hy h1 h2

/-! ## The clause, out of the test -/

/-- **The test on one message's arrays: no two of their blocks meet in rows and in places.** -/
theorem tableApart_of_message {codes : Codes} {o : OracleShape} {inIt : List ReqArray}
    (h : reqMessageLayoutOk codes o inIt = true) {A : ReqArray} (hA : A ∈ inIt) :
    (inIt.flatMap (·.blocks)).Pairwise fun x y =>
      (laidMeet x.firstRow x.rowBits y.firstRow y.rowBits &&
        laidMeet x.firstPlace x.placeBits y.firstPlace y.placeBits) = false := by
  unfold reqMessageLayoutOk at h
  have hne : inIt.isEmpty = false := by
    cases inIt with
    | nil => cases hA
    | cons _ _ => rfl
  rw [hne, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rw [Bool.and_eq_true] at h
    have h1 := h.1
    unfold laidOk at h1
    rw [Bool.and_eq_true] at h1
    exact pairwise_of_noPair _ _ h1.2
  · cases h

/-- **Two elements of arrays of one link, in one message, at one place of its table, are one element
of one array.** -/
theorem laidPlace_apart {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n n' : String} {a a' : ReqArray}
    (ha : OnBytes.reqArray layout l n = some a) (ha' : OnBytes.reqArray layout l n' = some a')
    (hm : a.message = a'.message) {r c r' c' : ℕ} {p : ℕ × ℕ}
    (h : laidPlace a.blocks r c = some p) (h' : laidPlace a'.blocks r' c' = some p) :
    n = n' ∧ r = r' ∧ c = c' := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨as', hl', hf'⟩ := Option.bind_eq_some_iff.1 ha'
  obtain rfl : as = as' := Option.some.inj (hl.symm.trans hl')
  have hA : a ∈ as := List.mem_of_find?_eq_some hf
  have hA' : a' ∈ as := List.mem_of_find?_eq_some hf'
  have hn : a.name = n := by simpa using List.find?_some hf
  have hn' : a'.name = n' := by simpa using List.find?_some hf'
  obtain ⟨m, -, hM⟩ := Meaning.message_of_layout ok hl hA
  have iA : a ∈ as.filter fun x => x.message == a.message :=
    List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩
  have iA' : a' ∈ as.filter fun x => x.message == a.message :=
    List.mem_filter.2 ⟨hA', by rw [hm]; exact beq_self_eq_true _⟩
  obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨b', hb', eb'⟩ := Option.map_eq_some_iff.1 h'
  have mb : b ∈ a.blocks := List.mem_of_find?_eq_some hb
  have mb' : b' ∈ a'.blocks := List.mem_of_find?_eq_some hb'
  have hh : laidHolds b r c = true := List.find?_some (p := fun β => laidHolds β r c) hb
  have hh' : laidHolds b' r' c' = true := List.find?_some (p := fun β => laidHolds β r' c') hb'
  have size : ∀ {A : ReqArray} {β : LaidBlock},
      A ∈ (as.filter fun x => x.message == a.message) → β ∈ A.blocks →
      β.rowBits + β.placeBits = β.bitsI + β.bitsC := fun {A β} h1 h2 => by
    obtain ⟨_, _, _, hk, _⟩ := Meaning.block_of_message hM h1 h2
    unfold laidBlockOk at hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.1.1.1.1.1.1.1.1
  have q := laidIn_in hh (size iA mb)
  have q' := laidIn_in hh' (size iA' mb')
  rw [eb] at q
  rw [eb'] at q'
  obtain ⟨e1, e2⟩ := one_of_flat (·.blocks) _ _ (tableApart_of_message hM iA) a iA a' iA' b mb b'
    mb' (meets_of_point q q') (meets_of_point q' q)
  subst e1
  subst e2
  obtain ⟨e3, e4⟩ := laidIn_inj hh hh' (eb.trans eb'.symm)
  exact ⟨hn.symm.trans hn', e3, e4⟩

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.laidIn_inj
#print axioms VerifiableInference.Desc.First.Look.laidIn_in
#print axioms VerifiableInference.Desc.First.Look.meets_of_point
#print axioms VerifiableInference.Desc.First.Look.one_of_pairwise
#print axioms VerifiableInference.Desc.First.Look.one_of_flat
#print axioms VerifiableInference.Desc.First.Look.tableApart_of_message
#print axioms VerifiableInference.Desc.First.Look.laidPlace_apart
