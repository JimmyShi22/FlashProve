-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorAtS.lean: the sub-protocol without a round "K9: the one equation"
(K9.oneEquation at the first chain's state, Johnson/Desc/First/Batch/Kind.lean and AtS.lean): what
its decision is, by the cut of DoorCut.lean; and WHICH COMPONENTS OF THE STATE's SHAPE (chainSh,
Johnson/Desc/First/Shape/Chain.lean) IT TURNS. General laws; nothing is evaluated.

  **`one_iff`**: the decision accepts from s to t just if the segment's part P is read off s,
    K9.door returns o at it, and t is s with the part laid back.
  `setLink_same`: laying the context that is there leaves the shape.
  **`one_turns`**: where the decision accepts from s to t: the shape of t is the shape of s with
    THREE components turned: the ledger's shape has the door shut · in the shape of statement, book
    and roots the statement is t's · no count of rows is owed. The link's context, the smallness
    test's structure, the tables, the calls' state, the book of trees, the number of roots and the
    pile stay.

Limits. ONE WAY, FROM AN ACCEPT. THE STATEMENT BEHIND IS NOT GIVEN HERE AS A FUNCTION OF THE SHAPE
IN FRONT: see DoorRow.lean and DoorMember.lean. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorCut
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

variable {Cl : Type}

theorem one_iff (p : Where) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t ↔
      ∃ P o, atS.get? s = some P ∧ door P.owed P.laid P.L P.F P.d = .ok o ∧
        t = atS.set s { P with owed := o.owed, L := o.L, F := o.F, d := o.d } := by
  show (do
    let P ← atS.part s
    let o ← door P.owed P.laid P.L P.F P.d
    pure (atS.set s { P with owed := o.owed, L := o.L, F := o.F, d := o.d }) :
      Except String S) = .ok t ↔ _
  unfold Lens.part
  simp only [ans_bind, there_ok]
  constructor
  · rintro ⟨P, hP, o, ho, e⟩
    exact ⟨P, o, hP, ho, (Except.ok.inj e).symm⟩
  · rintro ⟨P, o, hP, ho, rfl⟩
    exact ⟨P, hP, o, ho, rfl⟩

theorem setLink_same {a : ChainSh} {L : LinkSh} (h : a.link = some L) : a.setLink L = a := by
  have e : a.setLink L = a.layLink (a.link.map fun _ => L) := rfl
  rw [e, h]
  show a.layLink (some L) = a
  rw [← h]
  rfl

theorem part_reads {s : S} {P : Part} (h : atS.get? s = some P) :
    s.link? = some P.L ∧ s.fork? = some P.F := by
  have h' : (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← usedOf s
    pure ({ owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      Part) : Option Part) = some P := h
  cases hL : s.link? with
  | none => rw [hL] at h'; exact nomatch h'
  | some L =>
    cases hF : s.fork? with
    | none => rw [hL, hF] at h'; exact nomatch h'
    | some F =>
      cases ht : s.tl? with
      | none => rw [hL, hF, ht] at h'; exact nomatch h'
      | some tl =>
        cases hu : usedOf s with
        | none => rw [hL, hF, ht, hu] at h'; exact nomatch h'
        | some u =>
          rw [hL, hF, ht, hu] at h'
          obtain rfl := Option.some.inj h'
          exact ⟨rfl, rfl⟩

theorem one_turns (p : Where) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t) :
    ∃ F, s.fork? = some F ∧
      chainSh t = (((chainSh s).setLed (ledSh { F with doorShutF := true })).setCore
        (Ground.Sh.coreSh ⟨t.st, s.book, s.roots⟩)).setRowsOwed none := by
  obtain ⟨P, o, hP, ho, rfl⟩ := (one_iff p s t rs gs).1 h
  obtain ⟨n, q, F', y, d', -, hq, -, -, -, rfl⟩ := (door_iff _ _ _ _ _ _).1 ho
  obtain ⟨rfl, -⟩ := (equation_iff _ _ _ _).1 hq
  obtain ⟨hL, hF⟩ := part_reads hP
  refine ⟨P.F, hF, ?_⟩
  show chainSh { (s.putLink P.L).putFork { P.F with doorShutF := true } with
    st := d'.st, rowsOwed := none } = _
  have e : ∀ (z : S) (st' : Statement), chainSh { z with st := st', rowsOwed := none } =
      ((chainSh z).setCore (Ground.Sh.coreSh ⟨st', z.book, z.roots⟩)).setRowsOwed none :=
    fun _ _ => rfl
  have eb : ((s.putLink P.L).putFork { P.F with doorShutF := true }).book = s.book ∧
      ((s.putLink P.L).putFork { P.F with doorShutF := true }).roots = s.roots := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;> simp_all [S.putLink, S.putFork]
  rw [e, eb.1, eb.2, chainSh_putFork, chainSh_putLink,
    setLink_same (show (chainSh s).link = some (linkSh P.L) by
      show s.link?.map linkSh = _
      rw [hL]
      rfl)]
  rfl

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.one_iff
#print axioms VerifiableInference.Desc.K9.Shape.one_turns
#print axioms VerifiableInference.Desc.K9.Shape.setLink_same
#print axioms VerifiableInference.Desc.K9.Shape.part_reads
