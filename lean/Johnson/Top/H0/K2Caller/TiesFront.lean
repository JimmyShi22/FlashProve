-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TiesFront.lean: the code switch: THE FRONT SIDE OF ITS TIES TO THE
TABLE OF JOINTS: t1 (from the table's promise in front to the law's «on») and t4 (from the law's
relation in front to the items that the switch's row closes: carry, pinKept, «no mark»), in the form
of the fields t1 and t4 of Tw/K2C/TiedForm.lean's TiesAt. Rules over a letter Mg, with what is asked
of Mg's fields BY NAME; and the heart of «carry» at the made sentence (CarryK2.lean).
  ins_cases    what the switch's row closes: an item of insQ is carry m, pinKept m or «no mark»
  t4_front     THE FIELD t4, at every witness w with Laid z a w (a letter: meant: «w is what the
               table's extractor lays at a»): from fC («the law's relation in front gives Mg.carry
               m») and fP («… with Laid gives Mg.pin at every kept seat»)
  carry_front  fC's HEART: the library's relation at a typed reading fa' of (the verifier's state,
               the oracles), where fa' is CarryK2.lean's faAt at that state's front and frame, gives
               carryRow
  carryK2_front  so, where Mg.carry m is carryK2 … m: fC
  on_parts     what the table's promise holds at a verifier's state without a mark: the public
               items' Bools, «shown» and «no collision» at every sampled seat whose pin is open,
               pubP
  kept_sampled  a kept seat is a sampled seat wherever pinKept is open
  t1_front     THE FIELD t1: from two things by name: the way in lets in (hIn) · the Bool and the
               Prop of ONE public item q₀ that is open at the border, with «shown» and «no
               collision» at the kept seats, give the law's «on» at what the way in lets in (hOn)
LIMITS. RULES OVER LETTERS: NOTHING IS PAID HERE BUT carry_front. fP IS A PREMISE: that each kept
member's pin holds of the witness in front is not derived: it wants (a) that the slot of the made
open word IS the kept member's own committed word, (b) that the library's decoder at the typed
structure r (SwRow) is the table's at the seat, (c) that the table's extractor lays what is decoded:
none is typed. hfa (the law's reading is faAt) is to hold by the make of inX and strs: not shown.
hIn and hOn are premises on Mg, N and the door; that q₀ and pinKept are open at the border: two
tests on the table. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryK2
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H Cb Iop IOR
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Pub onAt openSets pubSets start
  sampledIn)
open VerifiableInference.Desc.First.K2Hands

section
variable {P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (k m : ℕ)

/-- What the switch's row closes. -/
theorem ins_cases (hins : (rowQ links ps k).ins = [.carry m, .pinKept m])
    (hctx : (rowQ links ps k).ctx = []) (i : Item) (hi : insQ links ps k i) :
    i = .carry m ∨ i = .pinKept m ∨ i = .unmarked := by
  unfold insQ at hi
  rw [hins, hctx] at hi
  simpa using hi

/-- **The field t4.** -/
theorem t4_front (hins : (rowQ links ps k).ins = [.carry m, .pinKept m])
    (hctx : (rowQ links ps k).ctx = [])
    (o : P → First.S × F.E.Str → Prop) (R Laid : P → First.S × F.E.Str → W → Prop)
    (t1 : ∀ z a, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → o z a)
    (fC : ∀ z a w, o z a → R z a w → Mg.carry m (z, a.1) (strsOf F a.2) w)
    (fP : ∀ z a w, o z a → R z a w → Laid z a w →
      ∀ x ∈ N.keptOf m, Mg.pin x.1 x.2 (z, a.1) (strsOf F a.2) w)
    (z : P) (a : First.S × F.E.Str) (w : W)
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hm : ¬ a.1.failed ≠ none) (hR : R z a w)
    (hL : Laid z a w) :
    relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k) a w := by
  intro i hi
  rcases ins_cases links ps k m hins hctx i hi with rfl | rfl | rfl
  · exact fC z a w (t1 z a ha hm) hR
  · exact fP z a w (t1 z a ha hm) hR hL
  · exact not_not.1 hm

/-- A kept seat is a sampled seat wherever pinKept is open. -/
theorem kept_sampled (O : List Item) (hO : Item.pinKept m ∈ O) (x : ℕ × ℕ) (hx : x ∈ N.keptOf m) :
    x ∈ sampledIn N O :=
  List.mem_flatMap.2 ⟨.pinKept m, hO, hx⟩

/-- **What the table's promise holds at a verifier's state without a mark.** -/
theorem on_parts (z : P) (a : First.S × F.E.Str)
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hm : ¬ a.1.failed ≠ none) :
    (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pub q (z, a.1) = true) ∧
      (∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.shown x.1 x.2 (strsOf F a.2) ∧ Mg.noColl x.1 x.2 (z, a.1) (strsOf F a.2)) ∧
      ∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (z, a.1) := by
  obtain ⟨-, h⟩ := ha
  rcases h with h | ⟨hb, -, hs, hp⟩
  · exact absurd h hm
  · refine ⟨fun q hq => ?_, hs, hp⟩
    simp only [Bool.and_eq_true] at hb
    have hh := hb.1.2
    unfold VerifiableInference.Desc.First.pubHeld at hh
    exact List.all_eq_true.1 hh q (List.mem_append_left _ hq)

/-- **The field t1.** -/
theorem t1_front (enter : First.S → Except String First.S) (on : First.S × F.E.Str → Prop)
    (q₀ : Pub) (hq : q₀ ∈ (pubSets Mg.more links ps)[k]?.getD [])
    (hO : Item.pinKept m ∈ (openSets links ps (start links))[k]?.getD [])
    (hIn : ∀ (z : P) (a : First.S × F.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → ∃ t, enter a.1 = .ok t)
    (hOn : ∀ (z : P) (a : First.S × F.E.Str) t, enter a.1 = .ok t → Mg.pub q₀ (z, a.1) = true →
      Mg.pubP q₀ (z, a.1) →
      (∀ x ∈ N.keptOf m, Mg.shown x.1 x.2 (strsOf F a.2) ∧
        Mg.noColl x.1 x.2 (z, a.1) (strsOf F a.2)) → on (t, a.2))
    (z : P) (a : First.S × F.E.Str)
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hm : ¬ a.1.failed ≠ none) :
    ∃ t, enter a.1 = .ok t ∧ on (t, a.2) := by
  obtain ⟨t, ht⟩ := hIn z a ha hm
  obtain ⟨h1, h2, h3⟩ := on_parts N Mg links ps k z a ha hm
  exact ⟨t, ht, hOn z a t ht (h1 q₀ hq) (h3 q₀ hq)
    fun x hx => h2 x (kept_sampled N m _ hO x hx)⟩

end

section
variable (r : SwRow) (H : r.OK) {Y Yf : Type} (p : K2.P2) (orc : Y → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp) (rd : Yf → Y)
  (fa' : First.S × Yf → (vecD (plainD r H)).tgt.X × (vecD (plainD r H)).tgt.Ex.Str)
  (on : First.S × Yf → Prop)

/-- **The heart of «carry».** -/
theorem carry_front
    (hfront : ∀ a, on a → ∃ fx W₀, K2.frontAt p a.1 = some fx ∧ K2.frameAt fx = some W₀)
    (hfa : ∀ a fx W₀, on a → K2.frontAt p a.1 = some fx → K2.frameAt fx = some W₀ →
      fa' a = faAt r H p orc smp (a.1, fx, W₀) (rd a.2))
    (a : First.S × Yf) (ha : on a) (u : (vecD (plainD r H)).tgt.W)
    (h : ((vecD (plainD r H)).tgt.S.over (vecD (plainD r H)).tgt.A).relR (fa' a) u) :
    carryRow r H p orc smp a.1 (rd a.2) := by
  obtain ⟨fx, W₀, h1, h2⟩ := hfront a ha
  rw [hfa a fx W₀ ha h1 h2] at h
  refine ⟨fx, W₀, h1, h2, carryOf_of _ _ _ h ?_ rfl⟩
  funext i
  exact ((plain_none r H).false i).elim

/-- **fC where Mg.carry is the made sentence.** -/
theorem carryK2_front {P W : Type} (h : r.ok = true) (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2)
    (door : ℕ → First.S → Option First.S)
    (smpA : ∀ (r : SwRow) (H : r.OK), _root_.Tw.K2.Front → SwitchFrame →
      (vecD (plainD r H)).held.Smp) (m : ℕ) (hr : rowAt m = some r)
    (fa' : First.S × Yf → (vecD (plainD r (r.ok_says h))).tgt.X ×
      (vecD (plainD r (r.ok_says h))).tgt.Ex.Str)
    (hfront : ∀ a, on a → ∃ fx W₀, K2.frontAt (pAt m) a.1 = some fx ∧ K2.frameAt fx = some W₀)
    (hfa : ∀ a fx W₀, on a → K2.frontAt (pAt m) a.1 = some fx → K2.frameAt fx = some W₀ →
      fa' a = faAt r (r.ok_says h) (pAt m) orc (smpA r (r.ok_says h)) (a.1, fx, W₀) (rd a.2))
    (z : P) (s t : First.S) (y : Yf) (w : W) (hd : door m s = some t) (ha : on (t, y))
    (u : (vecD (plainD r (r.ok_says h))).tgt.W)
    (hu : ((vecD (plainD r (r.ok_says h))).tgt.S.over (vecD (plainD r (r.ok_says h))).tgt.A).relR
      (fa' (t, y)) u) :
    carryK2 rowAt pAt door orc smpA m (z, s) (rd y) w := by
  unfold carryK2
  simp only [hr, hd]
  exact ⟨h, carry_front r (r.ok_says h) (pAt m) orc (smpA r (r.ok_says h)) rd fa' on hfront hfa
    (t, y) ha u hu⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.t1_front
#print axioms VerifiableInference.Desc.First.K2Caller.carryK2_front

#print axioms VerifiableInference.Desc.First.K2Caller.t4_front
#print axioms VerifiableInference.Desc.First.K2Caller.carry_front
