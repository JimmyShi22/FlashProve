-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6GivenOfLeft.lean.
WHAT IT IS NOT. Every statement on a state is CONDITIONAL: that the two public sentences hold at any
state is a premise. No state is shown at which they do. The test keysFitB is evaluated nowhere in
this file (at the goals' scope: Law/K6KeysInScope.lean). Nothing on soundness, on completeness or on
hiding.
WHAT IT IS. WHEN THE OUTPUT HEAD's LETTERS ARE READ AT A STATE: when given (Kinds/HeadFrame.lean)
returns. The library has that behind an accept of the head's decision alone; here it is had IN FRONT
of that decision. given asks three things: the lookup's points are laid; a token was heard; each
call's key point has the coordinates that the head's text asks and ends as the lookup's point does.
  pointLast_append  the last n coordinates of a point laid behind another.
  test_of_pointsOk  the third test, as given types it, from the sentence PointsOk
                    (Kinds/HeadInLaw.lean): the way back of Law/FromGiven.lean's pointsOk_of_test.
  keysFitB          a test with code on public numbers: the shape of the lookup on the calls against
                    the head's sizes.
  pointsOk_of_raw   CONDITIONAL: that test; what was heard has the lookup's own make (a call's key
                    point is a tail of the second point, then the first point): PointsOk.
  given_of_parts    CONDITIONAL on the three: given returns: the way back of given_ok.
  left_raw          CONDITIONAL on the sentence "what the lookup on the calls left"
                    (First/Look/K3LeftItem.lean): the key points' make and lengths.
  letters_of_left   CONDITIONAL: that sentence; "a token is heard, below the vocabulary's size"
                    (tokenHeardB, Stored/FillK6K7.lean); keysFitB: given's three tests pass. Of
                    tokenHeardB the first half alone is spent: no end holds "below the size".
  given_of_left     MAIN. CONDITIONAL on the same: given returns.
LETTERS. g in the tops' ends stands under "there is", pinned by given's equation.
CALLED: Att.P.last_append (First/Att/K05Merged.lean: its lastCoords has the text of Point.last),
Came.calls_length, Came.calls_keys (Law/FromGiven.lean), Came.call_get (Law/Call.lean), the fields
zx, zkRaw, zkLen of K3Left (Top/H/K3LeftStatement.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.Kinds.Law.K6LeftSays
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Stored.FillK6K7
import Johnson.Desc.First.Att.K05Merged

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork Forest.Shape Forest.Heard)
open VerifiableInference.OnPublicFiles (k3LeftItem)
open VerifiableInference.Desc.First (S)
open Norm (lt ls)

/-- The last n coordinates of a point behind another are the last n of the second, where it has so
many. -/
theorem pointLast_append (a z : Point) (n : Nat) (hn : n ≤ z.size) :
    (a ++ z).last n = z.last n := by
  exact VerifiableInference.Desc.First.Att.P.last_append a hn

section Sized

variable [Sizes]

/-- The converse of pointsOk_of_test (Law/FromGiven.lean): PointsOk gives given's third test, as it
is typed there. -/
theorem test_of_pointsOk (floor : Nat) (zx : Point) (zk : Nat → Point)
    (h : PointsOk floor zx zk) :
    ((fromLookup floor zx zk).calls.zipIdx.all fun c =>
      (zk c.2).size == lJ floor c.1.2 + Norm.lt &&
        (zk c.2).last (Norm.ls + Norm.lt) == zx.last (Norm.ls + Norm.lt)) = true := by
  rw [List.all_eq_true]
  rintro ⟨x, i⟩ hx
  rw [List.mem_zipIdx_iff_getElem?] at hx
  dsimp only at hx
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hx
  have hi : i < 6 := by
    rw [Came.calls_length] at hlt
    exact hlt
  have hk : x.2 = callKeys i := by
    have e := Came.calls_keys floor zx zk hi
    rw [List.getD_eq_getElem?_getD, hx] at e
    exact e
  obtain ⟨p1, p2⟩ := h i (callKeys i) (Came.call_get hi)
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hk]
  exact ⟨p1, p2⟩

/-- **A TEST WITH CODE ON PUBLIC NUMBERS**: the lookup's shape h3 against the head's sizes and the
least logarithm of a call's number of keys: six calls at least; the lookup's first point has ls + lt
coordinates at least; call c's key point has as many coordinates as the head's text asks. -/
def keysFitB (floor : Nat) (h3 : Forest.Shape) : Bool :=
  Decidable.decide (6 ≤ h3.NC) && Decidable.decide (ls + lt ≤ h3.dT) &&
    (List.range 6).all fun c => ((h3.calls[c]?).map (·.n)).getD 0 == lJ floor (callKeys c) + lt

/-- From how the lookup makes its key points, at numbers that pass the test: PointsOk. CONDITIONAL.
-/
theorem pointsOk_of_raw (floor : Nat) (h3 : Forest.Shape) (g : Forest.Heard)
    (hfit : keysFitB floor h3 = true) (hzx : g.zx.size = h3.dT)
    (hraw : ∀ c, c < h3.NC →
      g.zk.getD c #[] = g.zy.extract (h3.rK - h3.iota.getD c 0) g.zy.size ++ g.zx)
    (hlen : ∀ c, c < h3.NC → (g.zk.getD c #[]).size = ((h3.calls[c]?).map (·.n)).getD 0) :
    PointsOk floor g.zx fun c => g.zk.getD c #[] := by
  unfold keysFitB at hfit
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hfit
  obtain ⟨⟨h6, hd⟩, hn⟩ := hfit
  intro c keys hc
  have hc6 : c < 6 := by
    by_contra hge
    have hnone : callList[c]? = none := List.getElem?_eq_none (by
      have : callList.length = 6 := rfl
      omega)
    rw [hnone] at hc
    cases hc
  have hk : keys = callKeys c := by
    rw [Came.call_get hc6] at hc
    exact (Option.some.inj hc).symm
  subst hk
  have hcN : c < h3.NC := by omega
  show (g.zk.getD c #[]).size = _ ∧ Point.last (g.zk.getD c #[]) (ls + lt) = _
  refine ⟨by rw [hlen c hcN, hn c hc6], ?_⟩
  rw [hraw c hcN]
  exact pointLast_append _ _ _ (by rw [hzx]; exact hd)

end Sized

/-- The converse of given_ok (Law/FromGiven.lean): WHERE THE THREE TESTS PASS, given RETURNS. -/
theorem given_of_parts {St : Type} (p : Par) (L : Seat St) (s : St) (z : Point × (Nat → Point))
    (y : Nat) (hz : L.lookup s = some z) (hy : Reply.token L.toSeat s = some y)
    (hP : @PointsOk p.sizes p.floor z.1 z.2) : ∃ g : Given, given p L s = .ok g := by
  have ht := @test_of_pointsOk p.sizes p.floor z.1 z.2 hP
  unfold given
  simp only [hz, hy, named, need, bind, Except.bind, pure, Except.pure, ht, if_true]
  exact ⟨_, rfl⟩

/-- What the sentence "what the lookup on the calls left" says of the key points, as machine words:
two fields that Law/K6LeftSays.lean's LeftSays has (zx, zkLen), and the one that it has not (how a
key point is made). -/
theorem left_raw (p : First.Look.P) (s : S) (L : k3LeftItem p s) :
    ∃ h3 g, p.shape = some h3 ∧ s.lookHeard? = some g ∧ g.zx.size = h3.dT ∧
      (∀ c, c < h3.NC →
        g.zk.getD c #[] = g.zy.extract (h3.rK - h3.iota.getD c 0) g.zy.size ++ g.zx) ∧
      ∀ c, c < h3.NC → (g.zk.getD c #[]).size = ((h3.calls[c]?).map (·.n)).getD 0 := by
  obtain ⟨⟨h3, hs, hL⟩, _⟩ := L
  obtain ⟨F, F', g, rs, _, _, K, hg, _⟩ := hL
  exact ⟨h3, g, hs, hg, K.zx, fun c hc => (K.zkRaw c hc).2, K.zkLen⟩

/-- **given's THREE TESTS PASS AT A STATE AT WHICH THE TWO PUBLIC SENTENCES HOLD**: "what the lookup
on the calls left", and "a token is heard, below the vocabulary's size". CONDITIONAL: on these two
and on the test on public numbers. z, y: pinned by the state's two readers. -/
theorem letters_of_left (W : OnBytes.Model.Verify.Public) {p3 : First.Look.P} {h3 : Forest.Shape}
    {s : S} (L : k3LeftItem p3 s) (hs : p3.shape = some h3)
    (hfit : @keysFitB (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor h3 = true)
    (ht : tokenHeardB W.hS (readsOf W) s = true) :
    ∃ (z : Point × (Nat → Point)) (y : Nat), (seatAt W.hS (readsOf W)).lookup s = some z ∧
      Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y ∧
      @PointsOk (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor z.1 z.2 := by
  obtain ⟨h3', g, hs', hg, hzx, hraw, hlen⟩ := left_raw p3 s L
  obtain rfl : h3' = h3 := Option.some.inj (hs'.symm.trans hs)
  have hP := @pointsOk_of_raw (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor h3' g
    hfit hzx hraw hlen
  have hz : (seatAt W.hS (readsOf W)).lookup s = some (g.zx, fun c => g.zk.getD c #[]) := by
    show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
    rw [hg]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y := by
    unfold tokenHeardB at ht
    cases hy : Reply.token (seatAt W.hS (readsOf W)).toSeat s with
    | some y => exact ⟨y, rfl⟩
    | none =>
      rw [hy] at ht
      cases ht
  exact ⟨_, y, hz, hy, hP⟩

/-- **THE HEAD's LETTERS ARE READ AT SUCH A STATE.** CONDITIONAL: as the last. -/
theorem given_of_left (W : OnBytes.Model.Verify.Public) {p3 : First.Look.P} {h3 : Forest.Shape}
    {s : S} (L : k3LeftItem p3 s) (hs : p3.shape = some h3)
    (hfit : @keysFitB (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor h3 = true)
    (ht : tokenHeardB W.hS (readsOf W) s = true) :
    ∃ g : Given, given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g := by
  obtain ⟨z, y, hz, hy, hP⟩ := letters_of_left W L hs hfit ht
  exact given_of_parts _ _ s z y hz hy hP

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.pointLast_append
#print axioms VerifiableInference.Desc.Kinds.Head.Law.test_of_pointsOk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.pointsOk_of_raw
#print axioms VerifiableInference.Desc.Kinds.Head.Law.given_of_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.left_raw
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_of_left
#print axioms VerifiableInference.Desc.Kinds.Head.Law.given_of_left
