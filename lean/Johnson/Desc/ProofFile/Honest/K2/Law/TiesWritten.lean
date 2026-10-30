-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TiesWritten.lean: the kind "the code switch" (K2): THE PUBLIC
TIES BETWEEN THE KIND's PLACES AND THE SEGMENTS' PUBLIC DATA, AS TESTS WITH CODE, THEIR YES AT THE
WRITTEN PLACES BY LEAN's KERNEL, AND SO AT THE LIBRARY's HEAD: they pay the premises hS, hSz, hSent,
hfind and hF of `copy_of_tests` (Honest/K2/Law/CopyOfTests.lean, which this file does not import).
PUBLIC DATA ALONE. Definitions; statements with their proofs.

  `sizesSame`, `sizesSame_eq`   two switches' sizes, field by field
  `leadsInto`    the segment whose number is the place's link has the place's sizes, its first
                 sending is the place's `switchSent`, its fold's row variables are the place's
  `frontNames`   TWO NUMBERINGS HELD AGAINST EACH OTHER: the member of p's list `front` whose number
                 is n behind all messages of the segments in front of p₀ (the closing's count of
                 stretches) names p₀'s part and its message n (the order of sending)
  `placesApart`  no two places of a list are one place
  `drop_head`, `seg_split`, `find_of_apart`   tools on lists
  `leadsInto_gives`, `frontNames_gives`   what their yes gives
  `switchLinksW`, `leadsW`, `frontNamesW`, `apartW`   THE CLOSED FACTS, at the written places and
                 segments
  `leadsW_can_fail`, `frontNamesW_can_fail`, `frontNamesW_number_can_fail`   controls: the link bent
                 by one; the place's name bent; the count bent by one message
  `fencesW`      none of the fenced facts is empty: the tests are asked at 24 and 23 places and at
                 300 pairs
  `switchTies_at_head`   THE END: under the head, at two places of the lot with p₀.link < p.link

Kin: `placesW_one` (Honest/K2/Law/PublicAtWritten.lean): just one written place at each of 23 named
places: less than `apartW`. `sentMeetsW` (Honest/K2/Law/SwitchNumsWritten.lean): the place's
`switchSent` against the written plan's sending: another list than the segments'.

Limits. The closed facts are by Lean's kernel, replayed by no independent checker. They are on the
written places and segments; `places_at_head` and `segments_at_head`
(Honest/K2/Law/PlacesWritten.lean) carry them to the library's head. Nothing on a book, on a run's
coins, on data or on challenges. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Sizes)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The tests -/

/-- Two switches' sizes, field by field. -/
def sizesSame (A B : Sizes) : Bool :=
  decide (A.codes = B.codes) && decide (A.code = B.code) && decide (A.maskCode = B.maskCode) &&
    decide (A.kept = B.kept) && decide (A.target = B.target)

theorem sizesSame_eq {A B : Sizes} (h : sizesSame A B = true) : A = B := by
  unfold sizesSame at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases A
  cases B
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- The switch at the place leads into the segment whose number is its link. -/
def leadsInto (segs : List SegmentPub) (p₀ : SwitchPlace) : Bool :=
  (segs[p₀.link]?).any fun S =>
    sizesSame S.sizes p₀.sizes && decide (S.sent.headD #[] = switchSent p₀.sizes p₀.others) &&
      decide (S.foldVars = p₀.foldVars)

/-- **TWO NUMBERINGS HELD AGAINST EACH OTHER.** -/
def frontNames (segs : List SegmentPub) (p₀ p : SwitchPlace) : Bool :=
  (List.range (switchSent p₀.sizes p₀.others).size).all fun n =>
    (p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + n]?).any fun x =>
      x.1 == ⟨p₀.place, 0⟩ && x.2.1 == n

def placesApart (ps : List SwitchPlace) : Bool := decide (ps.map (·.place)).Nodup

/-! ## 2 Tools, and what the tests' yes gives -/

theorem drop_head {α : Type} : ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a →
    l.drop i = a :: l.drop (i + 1)
  | [], _, _, h => by simp at h
  | x :: l, 0, a, h => by
    have e : x = a := by simpa using h
    rw [e]
    rfl
  | x :: l, i + 1, a, h => by
    have h' : l[i]? = some a := by simpa using h
    simpa using drop_head h'

theorem seg_split {α : Type} {l : List α} {a b : Nat} {x : α} (h : l[a]? = some x) (hab : a < b) :
    (l.take b).drop a = x :: (l.take b).drop (a + 1) :=
  drop_head (by rw [List.getElem?_take_of_lt hab, h])

theorem find_of_apart : ∀ {ps : List SwitchPlace}, (ps.map (·.place)).Nodup →
    ∀ {p₀ : SwitchPlace}, p₀ ∈ ps →
      (ps.find? fun q => (⟨q.place, 0⟩ : Addr) == ⟨p₀.place, 0⟩) = some p₀
  | [], _, _, hp => by cases hp
  | q :: rest, hn, p₀, hp => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hp with e | hr
    · rw [e, List.find?_cons_of_pos (by simp)]
    · have hne : q.place ≠ p₀.place := fun e => hn.1 (e ▸ List.mem_map_of_mem hr)
      rw [List.find?_cons_of_neg (by simpa [Addr.mk.injEq] using hne)]
      exact find_of_apart hn.2 hr

theorem leadsInto_gives {segs : List SegmentPub} {p₀ : SwitchPlace}
    (h : leadsInto segs p₀ = true) :
    ∃ S, segs[p₀.link]? = some S ∧ S.sizes = p₀.sizes ∧
      S.sent.headD #[] = switchSent p₀.sizes p₀.others ∧ S.foldVars = p₀.foldVars := by
  unfold leadsInto at h
  cases hS : segs[p₀.link]? with
  | none =>
    rw [hS] at h
    simp only [Option.any_none, Bool.false_eq_true] at h
  | some S =>
    rw [hS] at h
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨S, rfl, sizesSame_eq h.1.1, h.1.2, h.2⟩

theorem frontNames_gives {segs : List SegmentPub} {p₀ p : SwitchPlace}
    (h : frontNames segs p₀ p = true) {n : Nat} (hn : n < (switchSent p₀.sizes p₀.others).size) :
    ∃ ct, p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + n]? =
      some (⟨p₀.place, 0⟩, n, ct) := by
  unfold frontNames at h
  have hx := List.all_eq_true.1 h n (List.mem_range.2 hn)
  cases hf : p.front[0 + ((segs.take p₀.link).map (·.messages)).sum + n]? with
  | none =>
    rw [hf] at hx
    simp only [Option.any_none, Bool.false_eq_true] at hx
  | some x =>
    rw [hf] at hx
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hx
    obtain ⟨a, m, ct⟩ := x
    simp only at hx
    rw [hx.1, hx.2]
    exact ⟨ct, rfl⟩

/-! ## 3 The closed facts -/

theorem switchLinksW : (placesW.all fun p => decide (p.link ≤ segsW.length)) = true := by
  decide +kernel

theorem leadsW :
    (placesW.all fun p₀ => decide (segsW.length ≤ p₀.link) || leadsInto segsW p₀) = true := by
  decide +kernel

theorem frontNamesW :
    (placesW.all fun p => placesW.all fun p₀ =>
      decide (p.link ≤ p₀.link) || frontNames segsW p₀ p) = true := by
  decide +kernel

theorem apartW : placesApart placesW = true := by decide +kernel

/-- A control: at a place whose link is bent by one the first test says no, at each written place
that leads into a segment. -/
theorem leadsW_can_fail :
    (placesW.all fun p₀ => decide (segsW.length ≤ p₀.link + 1) ||
      !leadsInto segsW { p₀ with link := p₀.link + 1 }) = true := by
  decide +kernel

/-- A control: with p₀'s place bent into p's the second test says no, at each pair: AND EVERY
LOOK-UP ANSWERS THERE: so the no comes of the name that the member bears, not of a lacking
member. -/
theorem frontNamesW_can_fail :
    (placesW.all fun p => placesW.all fun p₀ =>
      decide (p.link ≤ p₀.link) ||
        (!frontNames segsW { p₀ with place := p.place } p &&
          (List.range (switchSent p₀.sizes p₀.others).size).all fun n =>
            (p.front[0 + ((segsW.take p₀.link).map (·.messages)).sum + n]?).isSome)) = true := by
  decide +kernel

/-- A control on the second clause, the message's number: with one message more counted in the first
segment every look-up lands one member further: the first then bears p₀'s name and the number 1,
where the test wants 0: so the test says no, at each pair, AND THE NO COMES OF THE NUMBER. -/
theorem frontNamesW_number_can_fail :
    (placesW.all fun p => placesW.all fun p₀ =>
      decide (p.link ≤ p₀.link) ||
        (!frontNames
            (segsW.modifyHead fun Sg => { Sg with sent := Sg.sent ++ [#[default]] }) p₀ p &&
          (p.front[0 + ((segsW.take p₀.link).map (·.messages)).sum + 1]?).any fun x =>
            x.1 == ⟨p₀.place, 0⟩ && x.2.1 == 1)) = true := by
  decide +kernel

/-- **NONE OF THE FENCED FACTS ABOVE IS EMPTY**: the counts of the places and of the pairs at which
the fence says no, so that the test behind it is asked. -/
theorem fencesW :
    placesW.length = 25 ∧ segsW.length = 25 ∧
      (placesW.filter fun p₀ => decide (p₀.link < segsW.length)).length = 24 ∧
      (placesW.filter fun p₀ => decide (p₀.link + 1 < segsW.length)).length = 23 ∧
      (placesW.map fun p =>
        (placesW.filter fun p₀ => decide (p₀.link < p.link)).length).sum = 300 := by
  decide +kernel

/-! ## 4 At the library's head -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **THE END.** -/
theorem switchTies_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hl : p₀.link < p.link) :
    (∃ Sg rest, (segmentsOf Zp Bs.G₀)[p₀.link]? = some Sg ∧
      ((segmentsOf Zp Bs.G₀).take p.link).drop p₀.link = Sg :: rest ∧
      Sg.sizes = p₀.sizes ∧ Sg.sent.headD #[] = switchSent p₀.sizes p₀.others ∧
      Sg.foldVars = p₀.foldVars) ∧
    ((switchPlaces Zp Bs.G₀).find? fun q => (⟨q.place, 0⟩ : Addr) == ⟨p₀.place, 0⟩) = some p₀ ∧
    ∀ n, n < (switchSent p₀.sizes p₀.others).size →
      ∃ ct, p.front[0 + (((segmentsOf Zp Bs.G₀).take p₀.link).map (·.messages)).sum + n]? =
        some (⟨p₀.place, 0⟩, n, ct) := by
  rw [places_at_head h O] at hp₀ hp ⊢
  rw [segments_at_head h O]
  have hle : p.link ≤ segsW.length := of_decide_eq_true (List.all_eq_true.1 switchLinksW p hp)
  have h1 := List.all_eq_true.1 leadsW p₀ hp₀
  rw [Bool.or_eq_true] at h1
  have h1' : leadsInto segsW p₀ = true := by
    rcases h1 with e | e
    · exact absurd (of_decide_eq_true e) (by omega)
    · exact e
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 frontNamesW p hp) p₀ hp₀
  rw [Bool.or_eq_true] at h2
  have h2' : frontNames segsW p₀ p = true := by
    rcases h2 with e | e
    · exact absurd (of_decide_eq_true e) (by omega)
    · exact e
  obtain ⟨Sg, hSg, e1, e2, e3⟩ := leadsInto_gives h1'
  exact ⟨⟨Sg, _, hSg, seg_split hSg hl, e1, e2, e3⟩,
    find_of_apart (of_decide_eq_true apartW) hp₀, fun n hn => frontNames_gives h2' hn⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.sizesSame
#print axioms ProofFile.Honest.K2.Law.sizesSame_eq
#print axioms ProofFile.Honest.K2.Law.leadsInto
#print axioms ProofFile.Honest.K2.Law.frontNames
#print axioms ProofFile.Honest.K2.Law.placesApart
#print axioms ProofFile.Honest.K2.Law.drop_head
#print axioms ProofFile.Honest.K2.Law.seg_split
#print axioms ProofFile.Honest.K2.Law.find_of_apart
#print axioms ProofFile.Honest.K2.Law.leadsInto_gives
#print axioms ProofFile.Honest.K2.Law.frontNames_gives
#print axioms ProofFile.Honest.K2.Law.switchLinksW
#print axioms ProofFile.Honest.K2.Law.leadsW
#print axioms ProofFile.Honest.K2.Law.frontNamesW
#print axioms ProofFile.Honest.K2.Law.apartW
#print axioms ProofFile.Honest.K2.Law.leadsW_can_fail
#print axioms ProofFile.Honest.K2.Law.frontNamesW_can_fail
#print axioms ProofFile.Honest.K2.Law.frontNamesW_number_can_fail
#print axioms ProofFile.Honest.K2.Law.fencesW
#print axioms ProofFile.Honest.K2.Law.switchTies_at_head
