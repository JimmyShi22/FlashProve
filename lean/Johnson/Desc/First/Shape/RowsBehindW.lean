-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/RowsBehindW.lean: KIND K13's QUIET SUB-PROTOCOL BEHIND W's COMMITMENT
(K13.rowsB at the first chain's lens K13.atS: Johnson/Desc/K13/Kind.lean, AtS.lean: the request's
own group, the joinings, the row (Eval); no round) AS ONE STEP ON THE SHAPE OF THE STATE THAT THE
FIRST CHAIN CARRIES (Chain.lean). General laws; nothing is evaluated.
  `joinsS`, `joins_carries`: K13.joinAll on the core's shape (Ground.Sh.joinS,
    Johnson/Desc/Ground/Shape/Ground.lean).
  **`evalS`**, **`eval_carries`**: K13.rows (Johnson/Desc/K13/Text.lean) on shapes, line by line:
    W's number; a new group (newGroupS); the messages of the claim's masks join it, then W, then the
    split's message where the plan asks for a split (joinS); the fresh mask's number; the claim's
    point has as many coordinates as the plan's kCol; one plain row is added (addRowsS,
    Johnson/Desc/Ground/Shape/More.lean). Where the text returns, so does the text on shapes, with
    the shape of what is laid and the core's shape behind. It names no lens and no carried record.
  **`rowsBG p`**: the step: it reads what stands at the memory (the messages, the numbers handed on,
    what is laid: atEnd) and the core; it lays the core's STATEMENT alone (the lens writes neither
    the book of trees nor the number of roots), the debt of rows (K13.Honest.owedSh) and what is
    laid for the last chain.
  **`rowsB_carries`**: the strong form: behind a yes the step returns the shape behind. No premise
    on values. `rowsB_leaves`: a yes leaves the mark of failure and what goes out.
Beside it. Another house has the same text on shapes for the key file's chain (rowsS, rows_carries),
in a file that imports that chain's shapes; the two part in the type of the numbers handed on (a
list there) and in the test on the point's length (asked here). One of the two is to stay. (That
file's path is not given. A later search by whole words for these two namesfound
 no text of that kind; files that came into the
library later were not searched.)
Limits. "Returns" is not here: that the decision says yes where two tests on a narrower shape pass
is another house's law (rowsB_returns_shape). evalS's LAST LINE MIRRORS THE TEXT's IN PART: addRowsS
asks the group's guards alone (rowsG, addRowG); the text's addRowsP asks besides the clauses on the
row's summands (rowRestB: addRowG_eq, Johnson/Desc/Ground/Shape/Ground.lean), which the sealed
addRows_returns (More.lean) takes as a premise: SO NOTHING IN evalS OR rowsBG BARS A RETURN WHERE
THE DECISION REFUSES (by reading: no state is built at which the two part). The bare sub-protocol:
the guards of a seat, and W's commitment in front of it, are not in it. No state is shown at which
the step returns. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K13.Honest.ShapeM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh shD)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.K13.Honest (LaidSh claimSh4 laidSh owedSh)

/-- K13.joinAll on the core's shape. -/
def joinsS (g : Nat) : List Nat → CoreSh → Option CoreSh
  | [], a => some a
  | o :: l, a => (Ground.Sh.joinS a g o false).bind (joinsS g l)

theorem joins_carries {g : Nat} : ∀ (l : List Nat) (d d' : K13.St), K13.joinAll g l d = .ok d' →
    joinsS g l (shD d) = some (shD d')
  | [], d, d', hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    rfl
  | o :: l, d, d', hj => by
    simp only [K13.joinAll, K13.Law.bind_ok, K13.Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    show (Ground.Sh.joinS (shD d) g o false).bind _ = _
    rw [Ground.Sh.join_carries d d₁ g o false h1, Option.bind_some]
    exact joins_carries l d₁ d' h2

/-- **K13.rows (Johnson/Desc/K13/Text.lean) on shapes, line by line**, but that the last line asks
nothing of the row's summands (see the head's Limits). c: the claim's shape. -/
def evalS (S : LinShape) (c : K13.Honest.ClaimSh) (ids : Array Nat) (a : CoreSh) :
    Option (LaidSh × CoreSh) :=
  (ids[0]?).bind fun w =>
  (Ground.Sh.newGroupS a S.w.code S.ownMaskCode).bind fun b =>
  (joinsS b.1 (listOfT (c.slots.map (·.1))) b.2).bind fun a₁ =>
  (Ground.Sh.joinS a₁ b.1 w false).bind fun a₂ =>
  (if S.ownSplitNeeded then ids[1]? else some noId).bind fun split =>
  (if S.ownSplitNeeded then Ground.Sh.joinS a₂ b.1 split false else some a₂).bind fun a₃ =>
  (if S.masksAhead then ids.back?.map some else some none).bind fun mask =>
  if c.point == S.kCol then
    (Ground.Sh.addRowsS a₃ b.1 [.plain]).map fun a₄ => (⟨w, split, b.1, mask, c⟩, a₄)
  else none

theorem eval_carries {S : LinShape} {claim : LinClaim} {ids : Array Nat} {d : K13.St}
    {o : LinFirst × K13.St} (h : K13.rows S claim ids d = .ok o) :
    evalS S (claimSh4 claim) ids (shD d) = some (laidSh o.1, shD o.2) := by
  simp only [rows_is, K13.Law.bind_ok, K13.Law.there_ok, K13.Law.pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, hsp, d₃, h3, mask, hmask, row, hrow, d₄, h4, rfl⟩ :=
      h
  obtain ⟨g, d₀⟩ := b
  have hN := Ground.Sh.newGroup_carries d d₀ S.w.code S.ownMaskCode g hb
  have hslots : (claimSh4 claim).slots.map (·.1) = claim.masks.toList.map (·.oracle) := by
    show (claim.masks.toList.map fun u => (u.oracle, u.part, u.index)).map (·.1) = _
    rw [List.map_map]
    rfl
  have hJ := joins_carries _ _ _ h1
  have hW := Ground.Sh.join_carries d₁ d₂ g w false h2
  have hA := Ground.Sh.addRows_carries d₃ d₄ g [row] h4
  have hk : (claim.psi.length == S.kCol) = true ∧ row.kind = .plain := by
    unfold linEvalRow at hrow
    by_cases hc : (claim.psi.length == S.kCol) = true
    · refine ⟨hc, ?_⟩
      simp only [hc, guard, if_true] at hrow
      obtain rfl := Option.some.inj hrow
      rfl
    · simp [hc, guard] at hrow
  have h3' : (if S.ownSplitNeeded then Ground.Sh.joinS (shD d₂) g split false
      else some (shD d₂)) = some (shD d₃) := by
    by_cases hs : S.ownSplitNeeded = true
    · rw [if_pos hs] at h3 ⊢
      exact Ground.Sh.join_carries d₂ d₃ g split false h3
    · rw [if_neg hs] at h3 ⊢
      rw [Option.some.inj h3]
  unfold evalS
  rw [hw, Option.bind_some, hN, Option.bind_some, hslots]
  show (joinsS g _ (shD d₀)).bind _ = _
  rw [hJ, Option.bind_some, hW, Option.bind_some, hsp, Option.bind_some, h3', Option.bind_some,
    hmask, Option.bind_some]
  have hp : ((claimSh4 claim).point == S.kCol) = true := hk.1
  rw [if_pos hp]
  have hA' : Ground.Sh.addRowsS (shD d₃) g [.plain] = some (shD d₄) := by
    rw [← hk.2]
    exact hA
  rw [hA']
  rfl

/-- **K13's quiet sub-protocol behind W's commitment (K13.rowsB at the first chain's lens), on the
chain's shape.** It reads what stands at the memory and the core; it lays the core's statement, the
debt of rows and what is laid for the last chain. -/
def rowsBG (p : K13.Where) (a : ChainSh) : Option ChainSh :=
  match a.atEnd with
  | some (msg, ids, some l) =>
    (evalS p.lin l.claim ids a.core).map fun o =>
      ((a.setCore ⟨o.2.st, a.core.book, a.core.roots⟩).setRowsOwed (owedSh a.rowsOwed)).setEnd
        (msg, ids, some o.1)
  | _ => none

/-- **"Carries", strong**: behind a yes the step returns the shape behind: no premise on values. -/
theorem rowsB_carries {p : K13.Where} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Unit) K13.atS p).decide s rs gs = .ok t) :
    rowsBG p (chainSh s) = some (chainSh t) := by
  obtain ⟨q, l, o, hp, hl, hrows, rfl⟩ := rowsB_ok K13.atS p h
  cases hs : s.here with
  | mem a =>
    simp only [K13.atS, hs] at hp
    obtain rfl := Option.some.inj hp
    have hl' : a.lin = some l := hl
    have hrows' : K13.rows p.lin l.claim a.ids ⟨s.st, s.book, s.roots, [], ()⟩ = .ok o := hrows
    have hE := eval_carries hrows'
    have howed : (if s.noneWaits = true then none else s.rowsOwed) = owedSh s.rowsOwed := by
      unfold S.noneWaits owedSh
      cases s.rowsOwed with
      | none => rfl
      | some r => rfl
    have hend : (chainSh s).atEnd = some (a.msg, a.ids, some (laidSh l)) := by
      show endSh s.here = _
      rw [hs]
      show some (a.msg, a.ids, a.lin.map laidSh) = _
      rw [hl']
      rfl
    have hset : K13.atS.set s
        { owed := if s.noneWaits = true then none else s.rowsOwed
          heard := s.out.reply
          indexMasks := s.out.indexMasks
          pile := s.out.pending
          msg := a.msg
          ids := a.ids
          lin := some o.1
          d := o.2 } =
        { s with
          st := o.2.st
          rowsOwed := owedSh s.rowsOwed
          here := .mem ⟨a.msg, a.ids, some o.1⟩ } := by
      simp only [K13.atS, hs, howed]
    have hsh : chainSh
        { s with
          st := o.2.st
          rowsOwed := owedSh s.rowsOwed
          here := .mem ⟨a.msg, a.ids, some o.1⟩ } =
        (((chainSh s).setCore ⟨(shD o.2).st, (chainSh s).core.book, (chainSh
            s).core.roots⟩).setRowsOwed
          (owedSh (chainSh s).rowsOwed)).setEnd (a.msg, a.ids, some (laidSh o.1)) := by
      obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
      subst hs
      rfl
    show rowsBG p (chainSh s) = some (chainSh (K13.atS.set s _))
    rw [hset, hsh]
    unfold rowsBG
    rw [hend]
    show (evalS p.lin (claimSh4 l.claim) a.ids (shD ⟨s.st, s.book, s.roots, [], ()⟩)).map _ = _
    rw [hE]
    rfl
  | between => simp [K13.atS, hs] at hp
  | lay a => simp [K13.atS, hs] at hp
  | att a => simp [K13.atS, hs] at hp
  | head a => simp [K13.atS, hs] at hp
  | fin a => simp [K13.atS, hs] at hp

/-- The quiet sub-protocol's yes leaves the mark of failure and what goes out. -/
theorem rowsB_leaves {p : K13.Where} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Unit) K13.atS p).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out := by
  obtain ⟨q, l, o, hp, hl, hrows, rfl⟩ := rowsB_ok K13.atS p h
  unfold K13.atS
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.joins_carries
#print axioms VerifiableInference.Desc.First.Shape.eval_carries
#print axioms VerifiableInference.Desc.First.Shape.rowsB_carries
#print axioms VerifiableInference.Desc.First.Shape.rowsB_leaves
#print axioms VerifiableInference.Desc.First.Shape.joinsS
#print axioms VerifiableInference.Desc.First.Shape.evalS
#print axioms VerifiableInference.Desc.First.Shape.rowsBG
