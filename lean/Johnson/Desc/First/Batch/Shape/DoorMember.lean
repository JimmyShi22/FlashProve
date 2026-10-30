-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMember.lean: the sub-protocol without a round "K9: the one
equation" at the first chain's state: what it does to the shape of statement, book of trees and
number of roots (Ground.Sh.CoreSh), as a function of shapes; and when its decision accepts.
General laws; nothing is evaluated.

  `coreS s`: the shape of the state's statement, book and number of roots.
  `doorS_rest`: the door on shapes leaves the book's shape and the number of roots.
  **`one_core`**: the decision accepts from s to t: then, with L and F the link's context and the
    ledger of s: doorS L.check.frame F.ns L.check.group (coreS s) =
    some (coreS t).
  **`one_accepts`**: the segment's part P is read off s · the number of indices is laid · the tests
    on numbers and marks accept (eqB, termsB, doorB; doorS returns at coreS s) · the three tests on
    values accept (outsideV, termsV, slotsV) · "the row is made" and "the row fits" hold
    (DoorRow.lean): then the decision accepts.

Limits. Those of DoorRow.lean: one_accepts TAKES "the row is made" AND "the row fits" AS PREMISES,
uncut: they are cut in DoorMade.lean and DoorFits.lean and laid in in DoorChain.lean. termsB reads
three sizes of a virtual row that the ledger's shape does not hold yet. The bare sub-protocol: in a
seated chain it stands under the wrappers "no mark" and the comparison of the reply. That any test
accepts in an honest prover's run is not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorAtS
import Johnson.Desc.First.Batch.Shape.DoorRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh shD addRowS takeMaskS rowRestB)

/-- The shape of the state's statement, book and number of roots. -/
def coreS (s : S) : CoreSh := coreSh ⟨s.st, s.book, s.roots⟩

theorem addRowS_rest {a b : CoreSh} {g : Nat} {k : RowKind} (h : addRowS a g k = some b) :
    b.book = a.book ∧ b.roots = a.roots := by
  unfold addRowS at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · exact nomatch h

theorem takeMaskS_rest {a : CoreSh} {o : Nat} {y : Nat × CoreSh} (h : takeMaskS a o = some y) :
    y.2.book = a.book ∧ y.2.roots = a.roots := by
  unfold takeMaskS at h
  split at h
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · exact nomatch h

theorem takeNS_rest (o : Nat) : ∀ (n : Nat) (a : CoreSh) (acc : List Nat) (z : List Nat × CoreSh),
    takeNS o n a acc = some z → z.2.book = a.book ∧ z.2.roots = a.roots
  | 0, a, acc, z, h => by
    obtain rfl : (acc.reverse, a) = z := Option.some.inj h
    exact ⟨rfl, rfl⟩
  | n + 1, a, acc, z, h => by
    have h' : (takeMaskS a o).bind (fun x => takeNS o n x.2 (x.1 :: acc)) = some z := h
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨e1, e2⟩ := takeMaskS_rest hw
    obtain ⟨e3, e4⟩ := takeNS_rest o n w.2 (w.1 :: acc) z hz
    exact ⟨e3.trans e1, e4.trans e2⟩

theorem doorS_rest {f : ReqFrame} {n g : Nat} {a b : CoreSh} (h : doorS f n g a = some b) :
    b.book = a.book ∧ b.roots = a.roots := by
  unfold doorS at h
  split at h
  · exact addRowS_rest h
  · obtain ⟨o, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain ⟨e1, e2⟩ := takeNS_rest o n a [] x hx
      obtain ⟨e3, e4⟩ := addRowS_rest h
      exact ⟨e3.trans e1, e4.trans e2⟩
    · exact nomatch h

variable {Cl : Type}

theorem part_d {s : S} {P : Part} (h : atS.get? s = some P) : shD P.d = coreS s := by
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
          rfl

theorem set_core (s : S) (Q : Part) : coreS (atS.set s Q) =
    CoreSh.mk (Ground.Sh.stSh Q.d.st) (Ground.Sh.bookSh s.book) s.roots := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [coreS, atS, S.putLink, S.putFork, coreSh]

theorem one_core (p : Where) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t) :
    ∃ L F, s.link? = some L ∧ s.fork? = some F ∧
      doorS L.check.frame F.ns L.check.group (coreS s) = some (coreS t) := by
  obtain ⟨P, o, hP, ho, rfl⟩ := (one_iff p s t rs gs).1 h
  obtain ⟨hL, hF⟩ := part_reads hP
  have ed := part_d hP
  have c := door_carries P.owed P.laid P.L P.F P.d o ho
  rw [ed] at c
  refine ⟨P.L, P.F, hL, hF, ?_⟩
  rw [c]
  obtain ⟨e1, e2⟩ := doorS_rest c
  congr 1
  rw [set_core]
  show shD o.d = CoreSh.mk (Ground.Sh.stSh o.d.st) (Ground.Sh.bookSh s.book) s.roots
  have e1' : (shD o.d).book = Ground.Sh.bookSh s.book := e1
  have e2' : (shD o.d).roots = s.roots := e2
  rw [← e1', ← e2']
  rfl

theorem one_accepts (p : Where) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (P : Part) (n : Nat) (z : CoreSh) (hP : atS.get? s = some P) (hl : P.laid = some n)
    (b1 : eqB P.L P.F = true)
    (b2 : termsB P.L { P.F with doorShutF := true } = true)
    (b3 : doorB P.owed n P.L { P.F with doorShutF := true } = true)
    (b4 : doorS P.L.check.frame P.F.ns P.L.check.group (coreS s) = some z)
    (v1 : outsideV P.L P.F = true) (v2 : termsV P.L { P.F with doorShutF := true } = true)
    (v3 : slotsV { P.F with doorShutF := true } = true)
    (hMade : ∀ q F', equation P.L P.F = .ok (q, F') →
      ∃ row, termsRow P.L.check.rows.layout P.L.check.frame P.d.st q.terms.toList {} = .ok row)
    (hFits : ∀ q F' y, equation P.L P.F = .ok (q, F') →
      asRow P.L.check.rows P.L.check.frame q P.d = .ok y →
      rowRestB y.2.st P.L.check.group y.1 = true) :
    ∃ t, (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t := by
  have ed := part_d hP
  obtain ⟨o, ho⟩ := door_returns P.owed n P.L P.F P.d z b1 b2 b3
    (by rw [ed]; exact b4) v1 v2 v3 hMade hFits
  exact ⟨_, (one_iff p s _ rs gs).2 ⟨P, o, hP, by rw [hl]; exact ho, rfl⟩⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.doorS_rest
#print axioms VerifiableInference.Desc.K9.Shape.one_core
#print axioms VerifiableInference.Desc.K9.Shape.one_accepts
#print axioms VerifiableInference.Desc.K9.Shape.coreS
#print axioms VerifiableInference.Desc.K9.Shape.addRowS_rest
#print axioms VerifiableInference.Desc.K9.Shape.takeMaskS_rest
#print axioms VerifiableInference.Desc.K9.Shape.takeNS_rest
#print axioms VerifiableInference.Desc.K9.Shape.part_d
#print axioms VerifiableInference.Desc.K9.Shape.set_core
