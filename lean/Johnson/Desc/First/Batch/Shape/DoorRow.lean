-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorRow.lean: THE DOOR (K9.door, Johnson/Desc/First/Batch/Text.lean)
ON THE SHAPE OF THE STATEMENT: the text asRow cut; one function on shapes for what the door does to
the statement, the book of trees and the number of roots (Ground.Sh.CoreSh,
Johnson/Desc/Ground/Shape/Core.lean); and the door's two laws. General laws; nothing is
evaluated.

  `termsRow_kind`: the terms laid as a row leave the row's kind.
  `maskAt f`: which oracle message holds the present link's one mask row: read off the frame of the
    calls: numbers alone.
  **`asRow_iff`**: asRow returns y just if termsRow returns a row, and either the equation has no
    coefficient on masks and the statement stays, or maskAt finds the message o, K9.takeN takes as
    many entries of o as there are coefficients, the first entry taken is 0 and the last is their
    number less one (no more is tested of them), and y is made of them.
  `doorS f n g a`: THE DOOR ON SHAPES: n: the number of coefficients on masks; g: the link's group:
    the entries are taken (takeNS, DoorMasks.lean), they are tested to start at 0 and end at n - 1,
    and one plain row is added to group g (addRowS).
  **`door_carries`**: the door returns o from d: then doorS returns the shape of o.d from the shape
    of d, at n := the ledger's number of slots.
  **`door_returns`**: the tests on numbers and marks (the number of indices is laid; eqB; termsB;
    doorB; doorS returns), the three tests on values of DoorParts.lean, AND TWO TESTS THAT ARE NOT
    CUT IN THIS FILE accept: then the door returns. The two: "the row is made" (termsRow returns at
    the equation's own terms) and "the row fits" (rowRestB: the last five of the eight clauses of
    Ground.addRowP, which read the new row's own summands; three of them read values: the terms' and
    the forms' pair at a written-out variable, and the coefficients on the pads). DoorMade.lean and
    DoorFits.lean cut them.

Limits. "THE ROW IS MADE" AND "THE ROW FITS" ARE ASKED AT THE VERY EQUATION AND ROW THAT THE TEXTS
MAKE: they are premises in the form "for every equation that K9.equation returns …": each mixes
tests on sizes with tests on values, and is not cut here. That any test accepts in an honest
prover's run is not shown. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorParts
import Johnson.Desc.First.Batch.Shape.DoorMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.Ground.Sh (CoreSh shD addRowS addRow_carries addRow_returns rowRestB)

/-! ## 1 asRow, cut -/

theorem termsRow_kind (layout : ReqLayout) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), termsRow layout f S ts row = .ok row' →
      row'.kind = row.kind
  | [], row, row', h => by
    obtain rfl : row = row' := Except.ok.inj h
    rfl
  | t :: ts, row, row', h => by
    unfold termsRow at h
    simp only [ans_bind, there_ok] at h
    obtain ⟨a, -, o, -, c, -, h⟩ := h
    exact termsRow_kind layout f S ts (row.addForm o c) row' h

/-- Which oracle message holds the present link's one mask row. -/
def maskAt (f : ReqFrame) : Option Nat :=
  let messages := (f.shape.link[f.link]?.map (·.messages)).getD []
  (messages.findIdx? fun x => x.shape.maskRows != 0).bind fun m =>
    if (messages[m]?.map (·.shape.maskRows)) == some 1 then messageNow f f.link m else none

/-- The entries taken start at 0 and end at their number less one. -/
def fromZero (l : List Nat) : Bool := l.head? == some 0 && l.getLast? == some (l.length - 1)

variable {X : Type}

theorem asRow_iff (R : ReqRows) (f : ReqFrame) (q : Equation) (d : St X)
    (y : OnBytes.Row × St X) :
    asRow R f q d = .ok y ↔
      ∃ row, termsRow R.layout f d.st q.terms.toList {} = .ok row ∧
        ((q.onMasks.isEmpty = true ∧ y = ({ row with target := subE zeroE q.constant }, d)) ∨
          (q.onMasks.isEmpty = false ∧ ∃ o x, maskAt f = some o ∧
            takeN o q.onMasks.size d [] = .ok x ∧ fromZero x.1 = true ∧
            y = ({ row.addRun o .mask 0 1 (.own q.onMasks) with
              target := subE zeroE q.constant }, x.2))) := by
  unfold asRow maskAt fromZero
  simp only [ans_bind]
  constructor
  · rintro ⟨row, hr, h⟩
    refine ⟨row, hr, ?_⟩
    cases he : q.onMasks.isEmpty with
    | true =>
      rw [he] at h
      exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
    | false =>
      rw [he] at h
      simp only [Bool.false_eq_true, if_false, ans_bind, there_ok, need_ok, exists_const] at h
      obtain ⟨m, hm, h1, o, ho, x, hx, h2, e⟩ := h
      refine Or.inr ⟨rfl, o, x, ?_, hx, h2, (Except.ok.inj e).symm⟩
      rw [hm]
      show (if _ then _ else _) = _
      rw [if_pos h1]
      exact ho
  · rintro ⟨row, hr, h⟩
    refine ⟨row, hr, ?_⟩
    rcases h with ⟨he, rfl⟩ | ⟨he, o, x, ho, hx, h2, rfl⟩
    · rw [he]
      rfl
    · rw [he]
      simp only [Bool.false_eq_true, if_false, ans_bind, there_ok, need_ok, exists_const]
      obtain ⟨m, hm, hm2⟩ := Option.bind_eq_some_iff.1 ho
      by_cases h1 : ((((f.shape.link[f.link]?.map (·.messages)).getD [])[m]?.map
          (·.shape.maskRows)) == some 1) = true
      · rw [if_pos h1] at hm2
        exact ⟨m, hm, h1, o, hm2, x, hx, h2, rfl⟩
      · rw [if_neg h1] at hm2
        exact nomatch hm2

/-! ## 2 The door on shapes -/

/-- **The door on the shape of statement, book and roots.** -/
def doorS (f : ReqFrame) (n g : Nat) (a : CoreSh) : Option CoreSh :=
  if n == 0 then addRowS a g .plain
  else
    (maskAt f).bind fun o => (takeNS o n a []).bind fun x =>
      if fromZero x.1 then addRowS x.2 g .plain else none

theorem empty_iff (A : Array E) : A.isEmpty = (A.size == 0) := by
  obtain ⟨l⟩ := A
  cases l <;> rfl

theorem door_carries (owed : RowsOwed) (laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (o : Out X) (h : door owed laid L F d = .ok o) :
    doorS L.check.frame F.ns L.check.group (shD d) = some (shD o.d) := by
  obtain ⟨n, q, F', y, d', -, hq, -, hy, hd, rfl⟩ := (door_iff _ _ _ _ _ _).1 h
  obtain ⟨row, hr, hc⟩ := (asRow_iff _ _ _ _ _).1 hy
  have hk : row.kind = .plain := termsRow_kind _ _ _ _ _ _ hr
  have hs := equation_size L F F' q hq
  unfold doorS
  rcases hc with ⟨he, rfl⟩ | ⟨he, m, x, hm', hx, hz, rfl⟩
  · rw [empty_iff, hs] at he
    rw [if_pos he]
    have c := addRow_carries d d' _ _ hd
    rw [show ({ row with target := subE zeroE q.constant } : OnBytes.Row).kind = .plain
      from hk] at c
    exact c
  · rw [empty_iff, hs] at he
    rw [if_neg (by rw [he]; exact Bool.false_ne_true), hm']
    have c1 := takeN_carries m _ d [] x hx
    rw [hs] at c1
    show (takeNS m F.ns (shD d) []).bind _ = _
    rw [c1]
    show (if fromZero x.1 = true then _ else _) = _
    rw [if_pos hz]
    have c := addRow_carries x.2 d' _ _ hd
    rw [show ({ row.addRun m .mask 0 1 (.own q.onMasks) with
      target := subE zeroE q.constant } : OnBytes.Row).kind = .plain from hk] at c
    exact c

/-- **THE DOOR RETURNS.** hMade, hFits: the two tests that this file does not cut. -/
theorem door_returns (owed : RowsOwed) (n : Nat) (L : LinkCtx) (F : Fork) (d : St X) (z : CoreSh)
    (b1 : eqB L F = true)
    (b2 : termsB L { F with doorShutF := true } = true)
    (b3 : doorB owed n L { F with doorShutF := true } = true)
    (b4 : doorS L.check.frame F.ns L.check.group (shD d) = some z)
    (v1 : outsideV L F = true) (v2 : termsV L { F with doorShutF := true } = true)
    (v3 : slotsV { F with doorShutF := true } = true)
    (hMade : ∀ q F', equation L F = .ok (q, F') →
      ∃ row, termsRow L.check.rows.layout L.check.frame d.st q.terms.toList {} = .ok row)
    (hFits : ∀ q F' y, equation L F = .ok (q, F') →
      asRow L.check.rows L.check.frame q d = .ok y →
      rowRestB y.2.st L.check.group y.1 = true) :
    ∃ o, door owed (some n) L F d = .ok o := by
  obtain ⟨q, hq, hs⟩ := equation_returns L F b1 b2 v1 v2 v3
  obtain ⟨row, hr⟩ := hMade q _ hq
  have hk : row.kind = .plain := termsRow_kind _ _ _ _ _ _ hr
  have key : ∃ y, asRow L.check.rows L.check.frame q d = .ok y ∧ y.1.kind = .plain ∧
      addRowS (shD y.2) L.check.group .plain = some z := by
    unfold doorS at b4
    by_cases h0 : (F.ns == 0) = true
    · rw [if_pos h0] at b4
      have he : q.onMasks.isEmpty = true := by rw [empty_iff, hs]; exact h0
      exact ⟨_, (asRow_iff _ _ _ _ _).2 ⟨row, hr, Or.inl ⟨he, rfl⟩⟩, hk, b4⟩
    · rw [if_neg h0] at b4
      have he : q.onMasks.isEmpty = false := by
        rw [empty_iff, hs]
        simpa using h0
      obtain ⟨m, hm', b5⟩ := Option.bind_eq_some_iff.1 b4
      obtain ⟨w, hw, b6⟩ := Option.bind_eq_some_iff.1 b5
      by_cases hz : fromZero w.1 = true
      · rw [if_pos hz] at b6
        obtain ⟨x, hx⟩ := takeN_returns m F.ns d [] w hw
        have c1 := takeN_carries m F.ns d [] x hx
        obtain rfl : w = (x.1, shD x.2) := Option.some.inj (hw.symm.trans c1)
        exact ⟨_, (asRow_iff _ _ _ _ _).2
          ⟨row, hr, Or.inr ⟨he, m, x, hm', by rw [hs]; exact hx, hz, rfl⟩⟩, hk, b6⟩
      · rw [if_neg hz] at b6
        exact nomatch b6
  obtain ⟨y, hy, hky, hz⟩ := key
  have hf := hFits q _ y hq hy
  obtain ⟨d', hd⟩ := addRow_returns y.2 L.check.group y.1 z (by rw [hky]; exact hz) hf
  exact ⟨{ owed := none, L := L, F := { F with doorShutF := true }, d := d' },
    (door_iff owed (some n) L F d _).2
      ⟨n, q, { F with doorShutF := true }, y, d', rfl, hq, b3, hy, hd, rfl⟩⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.door_returns
#print axioms VerifiableInference.Desc.K9.Shape.asRow_iff
#print axioms VerifiableInference.Desc.K9.Shape.door_carries
