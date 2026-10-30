-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/TailMeans.lean: THEOREMS: WHAT A YES GIVES, for the tail of kind K10
behind the closing of the head's link (Johnson/Desc/First/Close/TailHead.lean: `countsHead`,
`leftHead`, `tailHead`, `tailHeadBlock`). No block imports this file, and no byte of a text turns.

What is said (each an "if and only if", but the last two, which are equations).
  `countsHead_iff`: **the four named counts**: the record stands inside the head's link, at some a,
    and: K10.tail.head: its sub-proof is opened · K10.tail.claims: as many claims were added as the
    plan counts · K10.tail.weights: there is one mark for each claim of the plan, and every mark is
    set (`weightsOut_iff`) · K10.tail.folds: there is one mark for each matrix of the smallness
    test, and every mark is set (`foldsOut_iff`).
  `leftHead_iff`: what the head's sub-proof left for its row: the record stands inside the head's
    link, and it is that link's `wo`.
  `back_iff`: the link's frame's three tests W3, W4, W5 (Johnson/Desc/First/Walk/Quiet.lean:
    `back`), taken apart: the last challenge was drawn and the link is closed; `samePlan` says yes
    (NOT taken apart: the frame's own); where the link's public record says that a row is left, the
    sub-proof has left what it is made of; and what is handed on.
  `tailHead_iff`: **just when the tail says yes, and what record it hands on**: a link with its fork
    is open (N); the four counts; W3 to W5; then, where the public record says that no row is left:
    the record as it leaves the link; where one is left: the pending row's text says yes (what THAT
    gives: Johnson/Desc/First/Pend/RowMeans.lean), the row is laid at the END of the pile, the
    statement's oracle messages are those that the row's text hands back, and the record leaves the
    link.
  `tailHead_head`: so at a yes the record stands inside the head's link with its sub-proof opened,
    and the link's context and fork are that link's own.
  `tailHeadBlock_decide`, `tailHeadBlock_shape`: the block decides by `tailHead` alone, whatever
    rounds and columns it is shown; it has no round, names no oracle message, states no run; it
    stands at K10's place.

WHAT THE TESTS READ. The verifier's own book-keeping in the carried record (where it stands; opened;
the number of claims added; the marks of weights handed out and of fold sums called; handed; done)
against the plan's numbers (planClaimsF, NM, the link's public record). NO TEST READS A VALUE THAT
WAS SENT OR DRAWN.

THEY ADD NO SECOND, INDEPENDENT EYE: the right sides are the texts read aloud.

Limits. `samePlan` (W4), `S.leaveLink?` and `pendingKept` are named, not taken apart: the frame's
and the record's own. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.TailHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LinkPub clearWith weightsOut foldsOut back samePlan pendingKept)

/-! ## 0 Steps of a text that can refuse -/

theorem need_iff (n : String) (b : Bool) : need n b = .ok () ↔ b = true := by
  cases b <;> simp [need]

theorem need_bind_iff {α : Type} (n : String) (b : Bool) (k : Unit → Except String α) (x : α) :
    (need n b >>= k) = .ok x ↔ b = true ∧ k () = .ok x := by
  cases b <;> simp [need, bind, Except.bind]

theorem bind_iff {α β : Type} (x : Except String α) (f : α → Except String β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

/-! ## 1 The counts -/

theorem weightsOut_iff (F : Fork) :
    weightsOut F = true ↔ F.kapMapF.size = F.planClaimsF ∧ ∀ b ∈ F.kapMapF, b = true := by
  simp only [weightsOut, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem, id]

theorem foldsOut_iff (tl : HTailF2) :
    foldsOut tl = true ↔ tl.foldTakenF.size = tl.NM ∧ ∀ b ∈ tl.foldTakenF, b = true := by
  simp only [foldsOut, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem, id]

/-- **The four named counts.** -/
theorem countsHead_iff (s : S) :
    countsHead s = .ok () ↔
      ∃ a, s.here = .head a ∧
        a.opened = true ∧
        a.F.nClaim = a.F.planClaimsF ∧
        (a.F.kapMapF.size = a.F.planClaimsF ∧ ∀ b ∈ a.F.kapMapF, b = true) ∧
        (a.tl.foldTakenF.size = a.tl.NM ∧ ∀ b ∈ a.tl.foldTakenF, b = true) := by
  unfold countsHead
  cases h : s.here with
  | head a =>
    simp only [need_bind_iff, need_iff, beq_iff_eq, weightsOut_iff, foldsOut_iff, Here.head.injEq,
      exists_eq_left']
  | between => simp
  | lay a => simp
  | att a => simp
  | fin a => simp
  | mem a => simp

theorem leftHead_iff (s : S) (w : WsForkOut) :
    leftHead s = some w ↔ ∃ a, s.here = .head a ∧ a.wo = some w := by
  unfold leftHead
  cases h : s.here <;> simp

/-! ## 2 The frame's three tests -/

theorem back_iff (X : LinkPub) (o : Option WsForkOut) (C : LinkCtx) (F : Fork)
    (x : ChainCheck × Option WsForkOut) :
    back X o C F = .ok x ↔
      (C.handed = true ∧ C.done = true) ∧ samePlan X F C.list = true ∧
        ((X.fv = true ∧ ∃ w, o = some w ∧ x = (C.check, some w)) ∨
          (X.fv = false ∧ x = (C.check, none))) := by
  unfold back
  cases h1 : C.handed <;> cases h2 : C.done <;> cases h3 : samePlan X F C.list <;>
    cases h4 : X.fv <;> cases o <;> simp [eq_comm]

/-! ## 3 The tail -/

/-- **Just when the tail says yes, and what it hands on.** -/
theorem tailHead_iff (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (s s' : S) :
    tailHead X lay lin s = .ok s' ↔
      ∃ C F, s.link? = some C ∧ s.fork? = some F ∧ countsHead s = .ok () ∧
        (C.handed = true ∧ C.done = true) ∧ samePlan X F C.list = true ∧
        ((X.fv = false ∧ s.leaveLink? = .ok s') ∨
          (X.fv = true ∧ ∃ w r os, leftHead s = some w ∧
            Pend.pendingRowO lay s.out.indexMasks w X.NCL lin s.st.oracles = .ok (r, os) ∧
            ({ s with out := pendingKept s.out r, st := { s.st with oracles := os } } :
              S).leaveLink? = .ok s')) := by
  unfold tailHead clearWith
  constructor
  · intro h
    split at h
    · rename_i C F hC hF
      obtain ⟨u, hc, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨x, hb, h⟩ := (bind_iff _ _ _).1 h
      obtain ⟨a1, a2, a3⟩ := (back_iff X _ C F x).1 hb
      rcases a3 with ⟨f, w, hw, rfl⟩ | ⟨f, rfl⟩
      · refine ⟨C, F, hC, hF, hc, a1, a2, Or.inr ⟨f, w, ?_⟩⟩
        cases hr : Pend.pendingRowO lay s.out.indexMasks w X.NCL lin s.st.oracles with
        | error e =>
          simp only [hr] at h
          cases h
        | ok y =>
          obtain ⟨r, os⟩ := y
          simp only [hr] at h
          exact ⟨r, os, hw, rfl, h⟩
      · exact ⟨C, F, hC, hF, hc, a1, a2, Or.inl ⟨f, h⟩⟩
    · cases h
  · rintro ⟨C, F, hC, hF, hc, a1, a2, a3⟩
    simp only [hC, hF]
    refine (bind_iff _ _ _).2 ⟨(), hc, ?_⟩
    rcases a3 with ⟨f, h⟩ | ⟨f, w, r, os, hw, hr, h⟩
    · refine (bind_iff _ _ _).2 ⟨_, (back_iff X _ C F _).2 ⟨a1, a2, Or.inr ⟨f, rfl⟩⟩, ?_⟩
      exact h
    · refine (bind_iff _ _ _).2 ⟨_, (back_iff X _ C F _).2 ⟨a1, a2, Or.inl ⟨f, w, hw, rfl⟩⟩, ?_⟩
      simp only [hr]
      exact h

/-- At a yes the record stands inside the head's link, its sub-proof opened. -/
theorem tailHead_head {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s s' : S}
    (h : tailHead X lay lin s = .ok s') :
    ∃ a, s.here = .head a ∧ a.opened = true ∧ s.link? = some a.L ∧ s.fork? = some a.F := by
  obtain ⟨C, F, _, _, hc, _⟩ := (tailHead_iff X lay lin s s').1 h
  obtain ⟨a, ha, ho, _⟩ := (countsHead_iff s).1 hc
  exact ⟨a, ha, ho, by simp [S.link?, ha, ho], by simp [S.fork?, ha, ho]⟩

/-! ## 4 The block -/

theorem tailHeadBlock_decide {Cl : Type} (X : LinkPub) (lay : WsLay) (lin : Params.LinShape)
    (l piece : Nat) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (tailHeadBlock (Cl := Cl) X lay lin l piece).decide s rs gs = tailHead X lay lin s := rfl

theorem tailHeadBlock_shape {Cl : Type} (X : LinkPub) (lay : WsLay) (lin : Params.LinShape)
    (l piece : Nat) :
    (tailHeadBlock (Cl := Cl) X lay lin l piece).rounds = [] ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).oracles = [] ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).before = [] ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).claims = [] ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).after = [] ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).planOk = true ∧
      (tailHeadBlock (Cl := Cl) X lay lin l piece).place = ⟨1, some l, piece, .K10⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.weightsOut_iff
#print axioms VerifiableInference.Desc.First.Close.foldsOut_iff
#print axioms VerifiableInference.Desc.First.Close.countsHead_iff
#print axioms VerifiableInference.Desc.First.Close.leftHead_iff
#print axioms VerifiableInference.Desc.First.Close.back_iff
#print axioms VerifiableInference.Desc.First.Close.tailHead_iff
#print axioms VerifiableInference.Desc.First.Close.tailHead_head
#print axioms VerifiableInference.Desc.First.Close.tailHeadBlock_decide
#print axioms VerifiableInference.Desc.First.Close.tailHeadBlock_shape
