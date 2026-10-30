-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorFits.lean: "THE ROW FITS", CUT: the five clauses of the adding of
a row that read the new row's own summands (rowRestB, Johnson/Desc/Ground/Shape/Ground.lean: the
last five of the eight clauses of Ground.addRowP), at the very row that K9.asRow makes of the one
equation: FOUR OF THEM FOLLOW FROM TWO TESTS ON SIZES; THE FIFTH IS A TEST ON VALUES AND STAYS.
General laws; nothing is evaluated.

  `Keeps S S'`: the codes, the groups and each message's shape are the same. `takeN_keeps`: the
    taking of mask entries keeps them. `bits_keeps`, `there_keeps`: so the tables' bits and "the
    table is there" are the same.
  `termsRow_forms`: where termsRow returns: the row's terms, single entries and runs are as they
    were; each new form lies on the message that the present link reads for a term's array, and fits
    that message's main table (blocksForm_gives, DoorGives.lean).
  `allTerms_all`: what holds of every term of a listed array and one of its virtual rows holds of
    every term that K9.allTerms returns.
  `seatB`: A TEST ON SIZES: a term's message is a member of the group and has a main table.
    `seatsB L F S G`: the same over the listed arrays that have a virtual row.
  `maskB f S G n`: A TEST ON SIZES: where there are coefficients on masks: the mask message is a
    member of the group, has a mask table, and entry n - 1 is inside it.
  `padB S g row`: THE TEST ON VALUES: the row has no coefficient on a pad (the eighth clause).
  **`fits_pays`**: seatsB and maskB accept at the statement in front, the group is there, and padB
    accepts at every row that asRow makes: then rowRestB accepts at every such row: the premise
    hFits of door_returns (DoorRow.lean).

Limits. padB STAYS A PREMISE AT THE ROW THAT IS MADE. That the tests accept at the protocol's sizes
is not shown. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorGives
import Johnson.Desc.First.Batch.Shape.DoorRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (LaidBlock ReqLayout)
open VerifiableInference.Desc.Ground (rowL ok has takeMaskP)
open VerifiableInference.Desc.Ground.Sh (rowRestB)

/-! ## 1 What the taking of mask entries keeps -/

/-- The codes, the groups and each message's shape are the same. -/
def Keeps (S S' : Statement) : Prop :=
  S'.codes = S.codes ∧ S'.groups = S.groups ∧
    ∀ o : Nat, (S'.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)

theorem Keeps.refl (S : Statement) : Keeps S S := ⟨rfl, rfl, fun _ => rfl⟩

theorem Keeps.trans {A B C : Statement} (h1 : Keeps A B) (h2 : Keeps B C) : Keeps A C :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun o => (h2.2.2 o).trans (h1.2.2 o)⟩

variable {X : Type}

theorem takeMask_keeps (d : St X) (o : Nat) (y : Nat × St X) (h : takeMaskP d o = some y) :
    Keeps d.st y.2.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨rfl, rfl, fun o' => ?_⟩
    show ((d.st.oracles.modify o _)[o']?).map (·.shape) = _
    rw [Array.getElem?_modify]
    split
    · rename_i e
      subst e
      cases d.st.oracles[o]? <;> rfl
    · rfl
  · exact nomatch h

theorem takeN_keeps (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat) (y : List Nat × St X),
    takeN o n d acc = .ok y → Keeps d.st y.2.st
  | 0, d, acc, y, h => by
    obtain rfl : (acc.reverse, d) = y := Except.ok.inj h
    exact Keeps.refl _
  | n + 1, d, acc, y, h => by
    have h' : (there "K9.mask-entry-free" (takeMaskP d o) >>= fun x =>
      takeN o n x.2 (x.1 :: acc)) = .ok y := h
    obtain ⟨x, hx, hy⟩ := (ans_bind _ _ _).1 h'
    exact (takeMask_keeps d o x ((there_ok _ _ _).1 hx)).trans (takeN_keeps o n x.2 _ y hy)

theorem bits_keeps {S S' : Statement} (h : Keeps S S') (o : Nat) (p : Part) :
    S'.rowBits o p = S.rowBits o p ∧ S'.placeBits o p = S.placeBits o p := by
  obtain ⟨h1, -, h3⟩ := h
  have e := h3 o
  unfold Statement.rowBits Statement.placeBits
  rw [h1]
  cases a : S'.oracles[o]? with
  | none =>
    cases b : S.oracles[o]? with
    | none => exact ⟨rfl, rfl⟩
    | some y => rw [a, b] at e; exact nomatch e
  | some x =>
    cases b : S.oracles[o]? with
    | none => rw [a, b] at e; exact nomatch e
    | some y =>
      rw [a, b] at e
      have e' : x.shape = y.shape := Option.some.inj e
      simp only
      rw [e']
      exact ⟨rfl, rfl⟩

theorem table_keeps {S S' : Statement} (h : Keeps S S') (o : Nat) (p : Part) :
    S'.tableBits o p = S.tableBits o p := by
  unfold Statement.tableBits
  rw [(bits_keeps h o p).1, (bits_keeps h o p).2]

theorem there_keeps {S S' : Statement} (h : Keeps S S') (o : Nat) (p : Part) :
    Own.tableThere S' o p = Own.tableThere S o p := by
  have e := h.2.2 o
  unfold Own.tableThere
  cases a : S'.oracles[o]? with
  | none =>
    cases b : S.oracles[o]? with
    | none => rfl
    | some y => rw [a, b] at e; exact nomatch e
  | some x =>
    cases b : S.oracles[o]? with
    | none => rw [a, b] at e; exact nomatch e
    | some y =>
      rw [a, b] at e
      have e' : x.shape = y.shape := Option.some.inj e
      show decide (0 < x.shape.rows p) = decide (0 < y.shape.rows p)
      rw [e']

/-! ## 2 The row that termsRow makes -/

/-- The message that the present link reads for a term's array. -/
def msgOf (layout : ReqLayout) (f : ReqFrame) (born : Nat) (array : String) : Option Nat :=
  ((layout.link[born]?).bind fun arrays => arrays.find? fun a => a.name == array).bind fun a =>
    messageNow f born a.message

theorem termsRow_forms (layout : ReqLayout) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), termsRow layout f S ts row = .ok row' →
      row'.terms = row.terms ∧ row'.units = row.units ∧ row'.runs = row.runs ∧
        ∀ x ∈ row'.forms, x ∈ row.forms ∨ ∃ t ∈ ts, msgOf layout f t.born t.array = some x.oracle ∧
          Own.formFits x.c (S.tableBits x.oracle .main) = true
  | [], row, row', h => by
    obtain rfl : row = row' := Except.ok.inj h
    exact ⟨rfl, rfl, rfl, fun x hx => Or.inl hx⟩
  | t :: ts, row, row', h => by
    unfold termsRow at h
    simp only [ans_bind, there_ok] at h
    obtain ⟨a, ha, o, ho, c, hc, h⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := termsRow_forms layout f S ts (row.addForm o c) row' h
    refine ⟨e1, e2, e3, fun x hx => ?_⟩
    rcases e4 x hx with hx | ⟨t', ht', hm, hf⟩
    · have hx' : x ∈ row.forms.push ⟨o, c⟩ := hx
      rcases Array.mem_push.1 hx' with hx' | rfl
      · exact Or.inl hx'
      · refine Or.inr ⟨t, List.mem_cons_self, ?_, blocksForm_gives _ _ _ _ _ _ c hc⟩
        unfold msgOf
        rw [ha]
        exact ho
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hm, hf⟩

/-! ## 3 The terms' seats -/

theorem allTerms_all (L : LinkCtx) (F : Fork) (Q : ReqTerm → Prop)
    (hQ : ∀ ti ∈ List.range L.list.nt.size, ∀ r ∈ (F.trees.getD ti {}).rows, ∀ t,
      TermAt (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2 (F.trees.getD ti {}) r t →
        Q t)
    (terms : Array ReqTerm) (h : allTerms L F = .ok terms) : ∀ t ∈ terms, Q t := by
  unfold allTerms at h
  refine foldlM_keeps _ (fun A : Array ReqTerm => ∀ t ∈ A, Q t) _ _ _
    (fun t ht => absurd ht (by simp)) (fun ti hti A A' hA hs => ?_) h
  simp only [ans_bind, need_ok, exists_const] at hs
  obtain ⟨-, hs⟩ := hs
  rw [← Array.foldlM_toList] at hs
  refine foldlM_keeps _ (fun A : Array ReqTerm => ∀ t ∈ A, Q t) _ _ _ hA
    (fun r hr B B' hB hq => ?_) hs
  exact rowTerms_of _ _ _ r _ (hQ ti hti r (Array.mem_toList_iff.1 hr)) B B' hB hq

/-- **A test on sizes**: a term's message is a member of the group and has a main table. -/
def seatB (layout : ReqLayout) (f : ReqFrame) (S : Statement) (G : Group) (born : Nat)
    (array : String) : Bool :=
  match msgOf layout f born array with
  | none => false
  | some o => G.members.contains o && Own.tableThere S o .main

/-- The same over the listed arrays that have a virtual row. -/
def seatsB (L : LinkCtx) (F : Fork) (S : Statement) (G : Group) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    (F.trees.getD ti {}).rows.isEmpty ||
      seatB L.check.rows.layout L.check.frame S G (L.arrayOf.getD ti (0, "")).1
        (L.arrayOf.getD ti (0, "")).2

theorem seats_all (L : LinkCtx) (F : Fork) (S : Statement) (G : Group)
    (hb : seatsB L F S G = true) (terms : Array ReqTerm) (h : allTerms L F = .ok terms) :
    ∀ t ∈ terms, seatB L.check.rows.layout L.check.frame S G t.born t.array = true := by
  refine allTerms_all L F _ (fun ti hti r hr t ht => ?_) terms h
  unfold seatsB at hb
  have b1 := List.all_eq_true.1 hb ti hti
  rw [Bool.or_eq_true] at b1
  rcases b1 with b1 | b1
  · exfalso
    have : (F.trees.getD ti {}).rows = #[] := by simpa using b1
    rw [this] at hr
    exact absurd hr (by simp)
  · rw [ht.1, ht.2.1]
    exact b1

/-! ## 4 The row fits -/

/-- **A test on sizes**: the mask message's seat. n: the number of coefficients on masks. -/
def maskB (f : ReqFrame) (S : Statement) (G : Group) (n : Nat) : Bool :=
  n == 0 ||
    match maskAt f with
    | none => false
    | some o =>
      G.members.contains o && Own.tableThere S o .mask && decide (n - 1 < 2 ^ S.tableBits o .mask)

/-- **THE TEST ON VALUES**: no coefficient on a pad. -/
def padB (S : Statement) (g : Nat) (row : OnBytes.Row) : Bool :=
  has S.groups[g]? fun G =>
    G.members.all fun o =>
      ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        Own.allZero (row.coefficient o q.1 q.2)

/-- rowRestB, clause by clause, where the group is there. -/
theorem rest_of {S : Statement} {g : Nat} {row : OnBytes.Row} {G : Group}
    (hG : S.groups[g]? = some G)
    (c4 : (row.terms.all fun t =>
      Own.tensorInOrder t.v && Own.placeFits S G t.oracle t.part t.v.vars 0) = true)
    (c5 : (row.units.all fun u =>
      Own.placeFits S G u.oracle u.part (S.tableBits u.oracle u.part) u.index) = true)
    (c6 : (row.runs.all fun w =>
      Own.coeffsInside w.coeffs && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
        Own.placeFits S G w.oracle w.part (S.tableBits w.oracle w.part)
          (w.first + w.step * (w.coeffs.size - 1))) = true)
    (c7 : (row.forms.all fun f =>
      Own.placeFits S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
        Own.formFits f.c (S.tableBits f.oracle .main)) = true)
    (c8 : padB S g row = true) : rowRestB S g row = true := by
  unfold padB at c8
  unfold rowRestB rowL ok
  rw [hG] at c8 ⊢
  simp only [List.drop, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨c4, c5, c6, c7, c8⟩

theorem all_empty {α : Type} (a : Array α) (p : α → Bool) (h : a = #[]) : a.all p = true := by
  subst h
  simp

theorem place_of {S : Statement} {G : Group} {o : Nat} {p : Part} {i : Nat}
    (h1 : G.members.contains o = true) (h2 : Own.tableThere S o p = true)
    (h3 : i < 2 ^ S.tableBits o p) : Own.placeFits S G o p (S.tableBits o p) i = true := by
  unfold Own.placeFits
  rw [h1, h2, beq_self_eq_true, decide_eq_true h3]
  rfl

/-- **THE PREMISE hFits OF door_returns (DoorRow.lean), BROUGHT TO TWO TESTS ON SIZES AND THE ONE
TEST ON VALUES.** -/
theorem fits_pays (L : LinkCtx) (F : Fork) (d : St X) (G : Group)
    (hG : d.st.groups[L.check.group]? = some G)
    (b1 : seatsB L { F with doorShutF := true } d.st G = true)
    (b2 : maskB L.check.frame d.st G F.ns = true)
    (hPad : ∀ q F' y, equation L F = .ok (q, F') →
      asRow L.check.rows L.check.frame q d = .ok y → padB y.2.st L.check.group y.1 = true)
    (q : Equation) (F' : Fork) (y : OnBytes.Row × St X) (hq : equation L F = .ok (q, F'))
    (hy : asRow L.check.rows L.check.frame q d = .ok y) :
    rowRestB y.2.st L.check.group y.1 = true := by
  have c8 := hPad q F' y hq hy
  have hs := equation_size L F F' q hq
  obtain ⟨-, -, -, terms, mc, ht, -, eq⟩ := (equation_iff L F F' q).1 hq
  have et : q.terms = terms := by rw [eq]
  have hseat := seats_all L _ d.st G b1 terms ht
  obtain ⟨row, hr, hc⟩ := (asRow_iff _ _ _ _ _).1 hy
  obtain ⟨e1, e2, e3, e4⟩ := termsRow_forms _ _ _ _ _ _ hr
  have forms_ok : ∀ (S' : Statement), Keeps d.st S' → ∀ x ∈ row.forms,
      (Own.placeFits S' G x.oracle .main (S'.tableBits x.oracle .main) 0 &&
        Own.formFits x.c (S'.tableBits x.oracle .main)) = true := by
    intro S' K x hx
    rcases e4 x hx with hx | ⟨t, htm, hm, hf⟩
    · exact absurd hx (by simp)
    · have hs' := hseat t (by rw [← et]; exact Array.mem_toList_iff.1 htm)
      unfold seatB at hs'
      rw [hm] at hs'
      simp only [Bool.and_eq_true] at hs'
      rw [Bool.and_eq_true]
      refine ⟨place_of hs'.1 (by rw [there_keeps K]; exact hs'.2) (Nat.two_pow_pos _), ?_⟩
      rw [table_keeps K]
      exact hf
  rcases hc with ⟨-, rfl⟩ | ⟨he, m, x, hm, hx, -, rfl⟩
  · refine rest_of hG ?_ ?_ ?_ ?_ c8
    · exact all_empty _ _ e1
    · exact all_empty _ _ e2
    · exact all_empty _ _ e3
    · exact Array.all_eq_true'.2 fun z hz => forms_ok d.st (Keeps.refl _) z hz
  · have K := takeN_keeps m _ d [] x hx
    have hG' : x.2.st.groups[L.check.group]? = some G := by
      rw [K.2.1]
      exact hG
    have hn : F.ns ≠ 0 := by
      rw [empty_iff, hs] at he
      simpa using he
    unfold maskB at b2
    rw [Bool.or_eq_true] at b2
    rcases b2 with b2 | b2
    · exact absurd (by simpa using b2) hn
    · rw [hm] at b2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at b2
      obtain ⟨⟨m1, m2⟩, m3⟩ := b2
      refine rest_of hG' ?_ ?_ ?_ ?_ c8
      · exact all_empty _ _ e1
      · exact all_empty _ _ e2
      · show ((row.runs.push ⟨m, .mask, 0, 1, .own q.onMasks⟩).all _) = true
        rw [e3]
        refine Array.all_eq_true'.2 fun w hw => ?_
        rcases Array.mem_push.1 hw with hw | rfl
        · exact absurd hw (by simp)
        · show (true && decide (0 < q.onMasks.size) && decide (1 ≤ 1) &&
            Own.placeFits x.2.st G m .mask (x.2.st.tableBits m .mask)
              (0 + 1 * (q.onMasks.size - 1))) = true
          rw [hs, decide_eq_true (Nat.pos_of_ne_zero hn),
            place_of m1 (by rw [there_keeps K]; exact m2)
              (by rw [table_keeps K, Nat.zero_add, Nat.one_mul]; exact m3)]
          rfl
      · exact Array.all_eq_true'.2 fun z hz => forms_ok x.2.st K z hz

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.fits_pays
#print axioms VerifiableInference.Desc.K9.Shape.termsRow_forms
#print axioms VerifiableInference.Desc.K9.Shape.seats_all
#print axioms VerifiableInference.Desc.K9.Shape.rest_of
#print axioms VerifiableInference.Desc.K9.Shape.takeN_keeps
#print axioms VerifiableInference.Desc.K9.Shape.table_keeps
#print axioms VerifiableInference.Desc.K9.Shape.there_keeps
