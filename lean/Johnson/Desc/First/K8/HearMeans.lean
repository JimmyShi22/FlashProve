-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/HearMeans.lean: THE SMALLNESS TEST, ITS FIRST HALF: WHAT EACH TEST OF THE
KIND'S OWN TEXT CHECKS, IN PLAIN LOGIC.

The kind's text (Johnson/Desc/First/K8/Hear.lean) and its seat at the first chain's carried record
(Johnson/Desc/First/K8/AtS.lean) are programs: their tests are Boolean. Here each test has a
proposition that says what it checks, with a proof that the test says yes just where the
proposition holds. No block imports this file.
  `decide_iff`: AT ANY SEAT: the decision says yes on one round, and hands on st', if and only if
    the eight tests hold and st' is what the seat lays. `decide_one`: it says yes on one round
    alone.
  `planOk_iff`: the seven tests on the plan alone.
  `closed_atS`, `nothingOwed_atS`, `drawn_atS`: the seat's readings (a), (b), (c) at the carried
    record.
  `MeansAtS p s r s'`: what a yes means at the carried record, in one proposition: a link is open,
    with the smallness test's record tl; (a) tl's list of tables is closed; (b) no
    count of batched rows is owed; (c) tl's field for the matrix is empty and no draw is counted;
    (d) (e) (f) tl's number of matrices, their columns and rows and its number of combinations are
    the place's; (t) the closed list's tables have the place's shapes; and s' is s with the round's
    entries and the first columns laid into tl.
  `decide_atS_iff`: **the decision at the carried record says yes if and only if `MeansAtS`.**
Definitions, statements and proofs.
Limits. What the fields that are read MEAN (that the list which is closed is the right one) is not
said: each proposition speaks of the record's fields as they
lie. Nothing on the round's entries: that there are columns x tau of them, each -1, 0 or 1, is
asked by the frame (Block.step, roundsFit), in front of the decision.

-/
import Johnson.Desc.First.K8.LawAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- **The decision, at any seat, both ways.** -/
theorem decide_iff {S Cl : Type} (seat : Seat S) (p : Par) (st st' : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st [r] gs = .ok st' ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st r.drawn.trits.toArray (firstColumns p) = .ok st') := by
  constructor
  · intro h
    obtain ⟨r', e, c1, c2, c3, c4, c5, c7, c6, c8, hl⟩ := decide_ok seat p st st' [r] gs h
    obtain rfl : r = r' := by simpa using e
    exact ⟨c1, c2, c3, c4, c5, c7, c6, c8, hl⟩
  · rintro ⟨c1, c2, c3, c4, c5, c7, c6, c8, hl⟩
    simp [approximateRangeProofDrawKind, c1, c2, c3, c4, c5, c6, c7, c8, hl]

/-- It says yes on one round alone. -/
theorem decide_one {S Cl : Type} (seat : Seat S) (p : Par) (st st' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st rs gs = .ok st') : ∃ r, rs = [r] := by
  obtain ⟨r, e, _⟩ := decide_ok seat p st st' rs gs h
  exact ⟨r, e⟩

/-- The tests on the plan alone. -/
theorem planOk_iff {S Cl : Type} (seat : Seat S) (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk = true ↔
      (p.ks ≠ [] ∧ columns p ≠ 0 ∧ p.tau ≠ 0 ∧ p.matsIn ≠ [] ∧ p.readsIn ≠ [] ∧
        p.ms.length = p.ks.length ∧ ∀ a ∈ p.asks, a.2.1 ≠ 0 ∧ a.2.2 ≠ 0) := by
  simp [approximateRangeProofDrawKind, and_assoc]

/-- (a) at the carried record. -/
theorem closed_atS (s : S) :
    atS.closed s = true ↔ ∃ tl, s.tl? = some tl ∧ tl.funClosed = true := by
  simp only [atS]
  cases s.tl? <;> simp

/-- (b) at the carried record. -/
theorem nothingOwed_atS (s : S) :
    atS.nothingOwed s = true ↔ (s.rowsOwed = none ∨ s.rowsOwed = some 0) := by
  simp only [atS, S.closeOk, S.noneWaits]
  cases s.rowsOwed <;> simp

/-- (c) at the carried record. -/
theorem drawn_atS (s : S) :
    atS.drawn s = false ↔ ∃ tl, s.tl? = some tl ∧ tl.cfF.size = 0 ∧ tl.foldDrawn = 0 := by
  simp only [atS]
  cases s.tl? <;> simp [Array.isEmpty]

/-- What a yes means at the carried record. -/
def MeansAtS (p : Par) (s : S) (r : Fmt.RoundView) (s' : S) : Prop :=
  ∃ tl : HTailF2, s.tl? = some tl ∧ tl.funClosed = true ∧
    (s.rowsOwed = none ∨ s.rowsOwed = some 0) ∧ (tl.cfF.size = 0 ∧ tl.foldDrawn = 0) ∧
    tl.NM = p.ks.length ∧ tl.mats.toList.map (·.k) = p.ks ∧ tl.mats.toList.map (·.m) = p.ms ∧
    tl.tau = p.tau ∧ (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p ∧
    s' = s.putTl { tl with cfF := r.drawn.trits.toArray, cfFirst := firstColumns p }

/-- **The decision at the carried record says yes if and only if `MeansAtS`.** -/
theorem decide_atS_iff {Cl : Type} (p : Par) (s s' : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' ↔ MeansAtS p s r s' := by
  rw [decide_iff]
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c7, c6, c8, hl⟩
    obtain ⟨tl, ht, e⟩ := atS_lay s s' _ _ hl
    obtain ⟨t1, e1, a1⟩ := (closed_atS s).1 c1
    obtain ⟨t3, e3, a3⟩ := (drawn_atS s).1 c3
    rw [ht] at e1 e3
    obtain rfl : tl = t1 := Option.some.inj e1
    obtain rfl : tl = t3 := Option.some.inj e3
    exact ⟨tl, ht, a1, (nothingOwed_atS s).1 c2, a3, by simpa [atS, ht] using c4,
      by simpa [atS, ht] using c5, by simpa [atS, ht] using c7, by simpa [atS, ht] using c6,
      by simpa [atS, ht] using c8, e⟩
  · rintro ⟨tl, ht, a1, a2, a3, a4, a5, a7, a6, a8, e⟩
    refine ⟨(closed_atS s).2 ⟨tl, ht, a1⟩, (nothingOwed_atS s).2 a2, (drawn_atS s).2 ⟨tl, ht, a3⟩,
      by simpa [atS, ht] using a4, by simpa [atS, ht] using a5, by simpa [atS, ht] using a7,
      by simpa [atS, ht] using a6, by simpa [atS, ht] using a8, ?_⟩
    simp [atS, ht, e]

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.decide_iff
#print axioms VerifiableInference.Desc.First.K8.decide_one
#print axioms VerifiableInference.Desc.First.K8.planOk_iff
#print axioms VerifiableInference.Desc.First.K8.closed_atS
#print axioms VerifiableInference.Desc.First.K8.nothingOwed_atS
#print axioms VerifiableInference.Desc.First.K8.drawn_atS
#print axioms VerifiableInference.Desc.First.K8.decide_atS_iff
