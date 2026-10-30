-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/SeatOfLay.lean: the seat of the i-th message of a sending, made of the trees'
layout; it lies among the trees that the sending's first written round sends. One definition, six
theorems. Kind-free: no sub-protocol's text is read.

Why. A kind that sends messages and samples them takes, in its law, a function `seat` from the
members to (tree, tenant), with the premise that each member's tree is one that the stretch's first
written round sends: base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length. Here the seat is made
off the layout that the program's own `layTrees` gives, and that premise follows.

What is said. base: the number of trees in front of the sending.
  `seatOfLay base lay i`: (base + the i-th message's tree in the layout, its part there).
  `seatOfLay_in`: under `LayFits n lay`, for i < n: base ≤ (seatOfLay base lay i).1, and less base
    it is below the layout's number of trees.
  `seatOfLay_at`: so at the layout that `layTrees codes sent` gives, for every notice.
  `seated_place`: IT IS THE BOOK'S OWN SEAT: where a sending is `Seated B B' n n0 lay num src`
    (Johnson/Desc/Book/Seated.lean), the book behind places message n0 + i at
    `seatOfLay B.trees.size lay i`.
  `trees_along`: written rounds that go along declared rounds (`Along (RoundIs num)`,
    Johnson/Desc/Sound/Stretch.lean), one for one, send as many trees each as the declared round's
    entry counts roots.
  `hseat_of_lay_at`: the premise in the law's form, at n members of which the i-th is the notice
    number ix i, and any written round d₁ that sends as many trees as the layout has.
  `hseat_of_lay`: the case ix i = i.

Limits. (1) That base is the number of trees in the book in front of the sending, so that
`seated_place` speaks of the same seat, is the caller's. (2) That the declared first round's entry
counts just the layout's trees is the kind's own make: not shown here. (3) That `seatOfLay` is the
seat by which the table of joints reads these members is not shown. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Book.Seated
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (Along RoundIs)

/-- The seat of the i-th message of a sending: its tree, counted through the file, and its part. -/
def seatOfLay (base : Nat) (lay : TreeLay) (i : Nat) : Nat × Nat :=
  (base + lay.tree.getD i 0, lay.part.getD i 0)

/-- The seat's tree is one of the layout's, counted from base. -/
theorem seatOfLay_in {n : Nat} {lay : TreeLay} (h : LayFits n lay) (base i : Nat) (hi : i < n) :
    base ≤ (seatOfLay base lay i).1 ∧ (seatOfLay base lay i).1 - base < lay.shapes.size := by
  have h1 := (h i hi).1
  show base ≤ base + lay.tree.getD i 0 ∧ base + lay.tree.getD i 0 - base < lay.shapes.size
  omega

/-- At the program's own layout. -/
theorem seatOfLay_at {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) (base i : Nat) (hi : i < sent.size) :
    base ≤ (seatOfLay base lay i).1 ∧ (seatOfLay base lay i).1 - base < lay.shapes.size :=
  seatOfLay_in (layTrees_fits h) base i hi

/-- **It is the book's own seat.** -/
theorem seated_place {B B' : TreeBook} {n n0 : Nat} {lay : TreeLay} {num : Nat → Nat}
    {src : Nat → Fmt.Src} (h : Seated B B' n n0 lay num src) (i : Nat) (hi : i < n) :
    B'.place[n0 + i]? = some (seatOfLay B.trees.size lay i) :=
  h.new i hi

/-- Written rounds that go along declared rounds send as many trees as the entries count roots. -/
theorem trees_along {num : Fmt.TreeSource → Nat} : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    ds.length = rs.length → Along (RoundIs num) rs ds →
    ds.map (·.trees.length) = rs.map (·.entry.roots)
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl
  | r :: rs, d :: ds, hl, h => by
    have h' : RoundIs num r d ∧ Along (RoundIs num) rs ds := h
    have e : d.trees.length = r.entry.roots := h'.1.2.2.2.2.2
    rw [List.map_cons, List.map_cons, e, trees_along rs ds (Nat.succ.inj hl) h'.2]

/-- **The premise in the law's form**, where member i is the notice number ix i (the members may be
some of the notices alone: those that are sampled). -/
theorem hseat_of_lay_at {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) (base n : Nat) (ix : Fin n → Nat)
    (hix : ∀ i, ix i < sent.size) (d₁ : RDT) (hd : d₁.trees.length = lay.shapes.size) (i : Fin n) :
    base ≤ (seatOfLay base lay (ix i)).1 ∧
      (seatOfLay base lay (ix i)).1 - base < d₁.trees.length := by
  rw [hd]
  exact seatOfLay_at h base (ix i) (hix i)

/-- Where member i is the notice number i. -/
theorem hseat_of_lay {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) (base n : Nat) (hn : n ≤ sent.size) (d₁ : RDT)
    (hd : d₁.trees.length = lay.shapes.size) (i : Fin n) :
    base ≤ (seatOfLay base lay i).1 ∧ (seatOfLay base lay i).1 - base < d₁.trees.length :=
  hseat_of_lay_at h base n (fun i => i) (fun i => Nat.lt_of_lt_of_le i.isLt hn) d₁ hd i

end VerifiableInference.Desc.Book
