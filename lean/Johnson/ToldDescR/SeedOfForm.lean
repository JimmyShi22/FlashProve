-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SeedOfForm.lean: no soundness is claimed.
Kind-free (every sender's tie owes it): off the row that the program's Send.form made (OnBytes/Iop/Send.lean), with whatever target, a seed can be read back: Desc.seedOf (Johnson/Desc/SmpRows.lean) answers: the third clause of the test smpHeld.
  pad_head          where the shape has an answer, the program's pad has a first place, and it lies in the mask table if the message has one, else in the main table
  fold_units        the laying of the pad's entries adds one unit a place
  **seedOf_form**   Send.form codes s o seed i = some row · the message has a row · the shape has an answer ⇒ (Desc.seedOf codes s { row with target := y }).isSome = true
No premise on the point's length, on the factor or on the codes is spent; i is any answer's number.
Nearest kin (not compared in this file; not machine-checked): seedReadsBack (Johnson/Desc/K1/Law/SeedReadsBack.lean): the like of kind K1's own sample row; with form_eq (Johnson/Desc/K1/Law/FormEq.lean) it gives this sentence under form_eq's three premises (every code's message length a power of two · the shape fits the codes · the pad fits). Here these three are not asked: that Send.form answers is enough.
  seedOf_none_of_no_answer   the second clause is needed: at a shape without an answer nothing is read back, off any row
Does not show. That what is read back is the seed (cut to the cube's coordinates). No member. Nothing on soundness.
-/
import Johnson.ToldDescR.FormOn
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K1

/-- Where the shape has an answer, the program's pad has a first place. -/
theorem pad_head {codes : Codes} {s : OracleShape} {places : List PadPlace}
    (h : Send.pad codes s = some places) (ha : 0 < s.answers) :
    ∃ p l, places = p :: l ∧
      p.part = if (Send.cube codes s).hasMask then Part.mask else Part.main := by
  unfold Send.pad at h
  dsimp only at h
  generalize hE : (if ((Send.cube codes s).hasMask || s.mainDeg == 3) = true then 1 else 3) = each
    at h
  have he : 0 < each := by
    rw [← hE]
    split <;> decide
  generalize (if (Send.cube codes s).hasMask = true then (codes.mask.getD s.maskCode default).ell
    else (codes.base.getD s.code default).ell) = len at h
  generalize (if (Send.cube codes s).hasMask = true then s.maskRows else s.mainRows) = rows at h
  generalize (if (Send.cube codes s).hasMask = true then (Send.cube codes s).maskRowBits
    else (Send.cube codes s).mainRowBits) = rb at h
  by_cases hl : len < each * s.answers
  · rw [if_pos hl] at h
    cases h
  · rw [if_neg hl] at h
    injection h with h
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 ha)
    obtain ⟨e, he'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 he)
    rw [hn, he'] at h
    simp only [List.range_succ_eq_map, List.flatMap_cons, List.map_cons, List.cons_append] at h
    exact ⟨_, _, h.symm, rfl⟩

/-- The laying of the pad's entries adds one unit a place. -/
theorem fold_units (o : Nat) (c : PadPlace → E) : ∀ (l : List PadPlace) (r : OnBytes.Row),
    (l.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index (c p)) r).units.size =
      r.units.size + l.length
  | [], _ => rfl
  | x :: l, r => by
    rw [List.foldl_cons, fold_units o c l, List.length_cons]
    show (r.units.push _).size + l.length = _
    rw [Array.size_push]
    omega

/-- **Off the program's sample row a seed can be read back.** -/
theorem seedOf_form {codes : Codes} {s : OracleShape} {o : Nat} {seed : SampleSeed} {i : Nat}
    {row : OnBytes.Row} (y : E) (h : Send.form codes s o seed i = some row)
    (hs : 0 < s.mainRows + s.maskRows) (ha : 0 < s.answers) :
    (VerifiableInference.Desc.seedOf codes s { row with target := y }).isSome = true := by
  obtain ⟨z, β⟩ := seed
  unfold Send.form at h
  simp only [ten_main, ten_mask, cube_hasMain, cube_hasMask, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨places, hpl, rfl⟩ := h
  obtain ⟨p, l, rfl, hpp⟩ := pad_head hpl ha
  rw [cube_hasMask] at hpp
  obtain ⟨p1, -, -, -⟩ := foldP_parts o (fun p =>
    subE (if p.answer == i then mulE β p.basis else zeroE)
      ((if p.part == .main then (Msg.of codes s).ten z .main
        else (Msg.of codes s).ten z .mask).entry p.index)) (p :: l) { kind := .sample }
  have hu := fold_units o (fun p =>
    subE (if p.answer == i then mulE β p.basis else zeroE)
      ((if p.part == .main then (Msg.of codes s).ten z .main
        else (Msg.of codes s).ten z .mask).entry p.index)) (p :: l) { kind := .sample }
  have hu0 : 0 < ((p :: l).foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index
      (subE (if p.answer == i then mulE β p.basis else zeroE)
        ((if p.part == .main then (Msg.of codes s).ten z .main
          else (Msg.of codes s).ten z .mask).entry p.index))) { kind := .sample }).units.size := by
    rw [hu, List.length_cons]
    omega
  generalize ((p :: l).foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index
      (subE (if p.answer == i then mulE β p.basis else zeroE)
        ((if p.part == .main then (Msg.of codes s).ten z .main
          else (Msg.of codes s).ten z .mask).entry p.index))) { kind := .sample }) = row0
    at p1 hu0 ⊢
  obtain ⟨u, hu1⟩ : ∃ u, row0.units[0]? = some u := ⟨_, Array.getElem?_eq_getElem hu0⟩
  have hne : ¬ ((Msg.of codes s).K = 0 ∧ (Msg.of codes s).Kzk = 0) := by
    rintro ⟨a, b⟩
    have a' : s.mainRows = 0 := a
    have b' : s.maskRows = 0 := b
    omega
  unfold VerifiableInference.Desc.seedOf
  simp only [hpl, cube_hasMain, cube_hasMask, Option.bind_eq_bind, Option.bind_some,
    List.head?_cons, Option.pure_def]
  cases hK : ((Msg.of codes s).K != 0) <;> cases hZ : ((Msg.of codes s).Kzk != 0)
  · exfalso
    exact hne ⟨by simpa using hK, by simpa using hZ⟩
  all_goals
    simp only [hZ, if_true, if_false, Bool.false_eq_true, Row.add, p1, Array.toList_push,
      Bool.and_true, Bool.and_false] at hpp ⊢
    simp [hpp, hu1]
    try (split <;> simp)

/-- THE SECOND CLAUSE IS NEEDED: at a shape without an answer nothing is read back, off any row. -/
theorem seedOf_none_of_no_answer (codes : Codes) (s : OracleShape) (r : OnBytes.Row)
    (ha : s.answers = 0) : VerifiableInference.Desc.seedOf codes s r = none := by
  have hp : Send.pad codes s = some [] := by
    unfold Send.pad
    simp [ha]
  unfold VerifiableInference.Desc.seedOf
  simp only [hp, Option.bind_eq_bind, Option.bind_some, List.head?_nil, Option.bind_none]
  simp

end ToldDesc

#print axioms ToldDesc.seedOf_none_of_no_answer
#print axioms ToldDesc.pad_head
#print axioms ToldDesc.seedOf_form
