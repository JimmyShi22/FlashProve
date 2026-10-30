-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanFitsB.lean: `PlanFits` (PartFitsReached.lean: seven sentences on
public data alone) AS A TEST WITH CODE: `planFitsB d ms own m t n ns : Bool`, and: its yes gives
`PlanFits`. So at closed data the premise is a closed Bool: for the kernel, an evaluation, or a test
at the door.

What is said.
  `shapesB`: over the links of the request's shape and each link's messages. `membersB`: over the
    numbers below n. `maskB`. `planFitsB`: these with the two tests of the programs, "an answer" and
    "room".
  `planFits_of_B`: **planFitsB d ms own m t n ns = true → PlanFits d ms own m t n ns.**

Limits. One direction. It has run at no data. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.PartFitsReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (FoldData)

/-- "shapes", with code. -/
def shapesB (d : FoldData) (m t n : ℕ) : Bool :=
  d.sent.shape.link.zipIdx.all fun L => L.1.messages.zipIdx.all fun x =>
    match whereD d m t L.2 x.2 with
    | some o => decide (o < n) && decide (d.M[o]? = some x.1.shape)
    | none => true

/-- "members", with code. -/
def membersB (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (List.range n).all fun o =>
    match d.M[o]?, d.L.places[o]? with
    | some sh, some x =>
      !own.contains x ||
        match ms.find? fun y => decide (seatOf y = x) with
        | some y => decide ((y.1.l.get y.2).1 = sh)
        | none => true
    | _, _ => true

/-- "mask", with code. -/
def maskB (d : FoldData) (m t n : ℕ) : Bool :=
  match maskD d m t with
  | some o =>
    decide (o < n) && (d.M[o]?).any fun sh =>
      decide (sh.maskRows = 1) && decide (sh.maskCode = d.sent.shape.maskCode) &&
        decide (sh.answers = d.sent.shape.answers)
  | none => true

/-- **The seven, with code.** -/
def planFitsB (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (m t n ns : ℕ) : Bool :=
  d.sent.codes.lengthsOk && reqLayoutOk d.sent.codes d.sent.shape d.sent.layout &&
    shapesB d m t n && membersB d ms own n && maskB d m t n &&
    decide (1 ≤ d.sent.shape.answers) &&
    decide (ns + d.sent.shape.answers ≤
      (d.sent.codes.mask.getD d.sent.shape.maskCode default).ell)

/-- **ITS YES GIVES `PlanFits`.** -/
theorem planFits_of_B {d : FoldData} {ms : List Mem} {own : List (ℕ × ℕ)} {m t n ns : ℕ}
    (h : planFitsB d ms own m t n ns = true) : PlanFits d ms own m t n ns := by
  unfold planFitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, h6, h7⟩
  · intro born j o msg hw hm
    obtain ⟨L, hL, hj⟩ := Option.bind_eq_some_iff.1 hm
    have a1 := List.all_eq_true.1 h3 (L, born) (List.mem_zipIdx_iff_getElem?.2 hL)
    have a2 := List.all_eq_true.1 a1 (msg, j) (List.mem_zipIdx_iff_getElem?.2 hj)
    simp only [hw, Bool.and_eq_true, decide_eq_true_eq] at a2
    exact a2
  · intro o x y sh ho hM hP hx hy
    have a1 := List.all_eq_true.1 h4 o (List.mem_range.2 ho)
    simp only [hM, hP, hy, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at a1
    rcases a1 with a1 | a1
    · have : own.contains x = true := by simpa using hx
      rw [this] at a1
      cases a1
    · exact a1
  · intro o ho
    unfold maskB at h5
    simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at h5
    obtain ⟨b1, b2⟩ := h5
    cases hM : d.M[o]? with
    | none =>
      rw [hM] at b2
      cases b2
    | some sh =>
      rw [hM, Option.any_some] at b2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at b2
      exact ⟨b1, sh, rfl, b2.1.1, b2.1.2, b2.2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planFits_of_B
