-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchArmsB.lean: THE CODE SWITCH AT THE HEAD's PLACE AND AT THE PLACE
BEHIND THE LAST SEGMENT (kind K2): "RETURNS" FROM THREE TESTS WITH CODE EACH: ONE ON THE CHAIN's
SHAPE WITH THE ROWS' MAKES BESIDE IT, ONE ON VALUES OF THE STATE, ONE ON THE TWO ROUNDS AND THE
COLUMNS. General laws; nothing is evaluated.

What it is for. The laws head_returns_sent and finish_returns_sent
(Johnson/Desc/K2/Honest/Returns/ArmsSent.lean) lead from HeadPlain and FinPlain, nine fields each,
to a yes of the kind's own decision. The seventh field is the call of the switch at the place's own
front (CallPlain), which SwitchCallB.lean has sorted at a general front.

  1 `armR p y b r₁ r₂ gs`: what both places ask of the rounds and the groups of columns: the
    positions lie in the plan's range · the call's test (callR) at the columns laid flat · no column
    is left · as many groups of columns as trees read.
  2 `headFrontS` | `headFront_S`: the head's front, off the chain's shape. **`headB p x`**: the
    head's link is entered, and the frame has the segment's group · the kind stands at the head ·
    the group's number is the plan's · no count of rows waits · callB. **`headR`**: armR at that
    front.
    `headOnesV s`: onesV at the rows that the head's own frame carries.
    **`headPlain_of_B`**, **`head_returns_B`**: headB p (chainF s), headOnesV s and headR p
    (chainF s) r₁ r₂ gs accept: then decideWith sendByL8 p s [r₁, r₂] gs returns.
  3 `finFrontS` | `finFront_S`, **`finB`**, **`finR`**, `finOnesV`, **`finPlain_of_B`**,
    **`finish_returns_B`**: the like at the place behind the last segment: the finish is entered and
    has laid its group.

Limits. One way. NO STATE IS SHOWN AT WHICH THE TESTS ACCEPT. At these two places the new group was
made by an earlier step: so its three clauses (it is there; no test has begun; no member) are asked
on the shape, inside callB. No law here carries the tests on values from what the chain's steps lay.
The kind's own decision: the quiet steps around it are not treated, and no member of a chain is
named. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SwitchCallB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.Ground.Sh (stSh)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat headFrontOf finFrontOf)
open VerifiableInference.Desc.K2.Honest.Returns (CallPlain HeadPlain FinPlain sendingAt inFront
  sentAt leftAfter head_returns_sent finish_returns_sent)
open _root_.Tw.K2 (Front sendByL8)

/-! ## 1 What both places ask of the rounds and the groups of columns -/

/-- The test on the two rounds and the groups of columns, at a front. -/
def armR (p : P2) (y : FrontS) (b : Ground.Sh.BookSh) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : Bool :=
  match y.a.codes.base[y.rows.code]? with
  | some c =>
    decide (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) && callR p y b r₁ r₂ (flat p gs) &&
      (leftAfterS (Positions.ofDraws c.logN r₂.drawn.poss) b (treesOfS b y.rows)
        (flat p gs)).isEmpty &&
      decide (gs.length = p.read.length)
  | none => false

/-- What armR gives at a front, beside the call's test. -/
theorem arm_of_R {p : P2} {x : Front} {B : TreeBook} {roots : Nat} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {c : Code}
    (e : x.st.codes.base[x.f.rows.code]? = some c)
    (h : armR p (frontS x) (Ground.Sh.bookSh B) r₁ r₂ gs = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) ∧
      callR p (frontS x) (Ground.Sh.bookSh B) r₁ r₂ (flat p gs) = true ∧
      leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) B
        (K2.Honest.Returns.treesOf
          (inFront (par9 p) x B (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ (flat p gs)))
        (flat p gs) = [] ∧
      gs.length = p.read.length := by
  unfold armR at h
  split at h
  · rename_i c' e'
    obtain rfl : c = c' := Option.some.inj (e.symm.trans e')
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, ?_, h4⟩
    rw [leftAfter_sh, ← trees_sh]
    exact h3
  · cases h

/-! ## 2 The head's place -/

/-- The head's front, off the chain's shape. hd: the shape of the head's own fields. -/
def headFrontS (x : ChainF) (hd : HeadSh) (T : SwitchTarget) : FrontS :=
  ⟨x.1.core.st, x.2, hd.fr.rows, hd.fr.group, T, linkOthers x.1.check.frame⟩

theorem headFront_S (s : S) (a : HeadOwn) (T : SwitchTarget) :
    frontS (headFrontOf s a T) = headFrontS (chainF s) (headSh a) T := rfl

/-- **The test on the plan's numbers and the chain's shape, at the head's place.** -/
def headB (p : P2) (x : ChainF) : Bool :=
  match x.1.head, x.1.check.frame.groups[x.1.check.frame.link]? with
  | some hd, some Q =>
    decide (p.stands = .head) && decide (hd.fr.group = p.grp) && waitsB x.1.rowsOwed &&
      callB p (headFrontS x hd Q.target) x.1.core.book
  | _, _ => false

/-- **The test on the two rounds and the columns, at the head's place.** -/
def headR (p : P2) (x : ChainF) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match x.1.head, x.1.check.frame.groups[x.1.check.frame.link]? with
  | some hd, some Q => armR p (headFrontS x hd Q.target) x.1.core.book r₁ r₂ gs
  | _, _ => false

/-- **The test on values of the state, at the head's place**: onesV at the rows that the head's own
frame carries. -/
def headOnesV (s : S) : Bool :=
  match s.here with
  | .head a => onesV s.st a.fr.rows
  | _ => false

/-- **The three tests give the premises.** -/
theorem headPlain_of_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : headB p (chainF s) = true) (hV : headOnesV s = true)
    (hR : headR p (chainF s) r₁ r₂ gs = true) :
    ∃ a Q c G, HeadPlain p s r₁ r₂ gs a Q c G := by
  unfold headOnesV at hV
  split at hV
  · rename_i a hh
    have hhd : (chainF s).1.head = some (headSh a) := by
      show headOf s.here = _
      rw [hh]
      rfl
    unfold headB at hB
    unfold headR at hR
    rw [hhd] at hB hR
    cases e2 : (chainF s).1.check.frame.groups[(chainF s).1.check.frame.link]? with
    | none =>
      rw [e2] at hB
      cases hB
    | some Q =>
      rw [e2] at hB hR
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
      obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hB
      have b4' : callB p (frontS (headFrontOf s a Q.target)) (Ground.Sh.bookSh s.book) = true := b4
      have hR' : armR p (frontS (headFrontOf s a Q.target)) (Ground.Sh.bookSh s.book) r₁ r₂ gs =
          true := hR
      have hc : ∃ c, (headFrontOf s a Q.target).st.codes.base[
          (headFrontOf s a Q.target).f.rows.code]? = some c := by
        unfold callB at b4'
        split at b4'
        · rename_i c e
          exact ⟨c, e⟩
        · cases b4'
      obtain ⟨c, ec⟩ := hc
      obtain ⟨r1, r2, r3, r4⟩ := arm_of_R (roots := s.roots) ec hR'
      obtain ⟨c', G, ec', H⟩ := callPlain_of_B (roots := s.roots) b4' hV r2
      obtain rfl : c = c' := Option.some.inj (ec.symm.trans ec')
      exact ⟨a, Q, c, G, b1, r1, hh, b2, e2, b3, H, r3, r4⟩
  · cases hV

/-- **The three tests accept: the kind's own decision says yes at the head's place.** -/
theorem head_returns_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : headB p (chainF s) = true) (hV : headOnesV s = true)
    (hR : headR p (chainF s) r₁ r₂ gs = true) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨a, Q, c, G, H⟩ := headPlain_of_B hB hV hR
  exact head_returns_sent H

/-! ## 3 The place behind the last segment -/

/-- The finish's front, off the chain's shape. a: the shape of the finish's own fields. -/
def finFrontS (x : ChainF) (a : FinSh) (Q : ReqGroup) : FrontS :=
  ⟨x.1.core.st, x.2, a.fr.rows, a.fr.group, Q.target,
    #[foldMaskNotice (a.fr.blank.foldShape a.fr.link {})]⟩

theorem finFront_S (s : S) (a : FinOwn) (Q : ReqGroup) :
    frontS (finFrontOf s a Q) = finFrontS (chainF s) (finSh a) Q := rfl

/-- **The test on the plan's numbers and the chain's shape, behind the last segment.** -/
def finB (p : P2) (x : ChainF) : Bool :=
  match x.1.fin with
  | some a =>
    match a.G with
    | some Q =>
      decide (p.stands = .finish) && decide (a.fr.group = p.grp) && waitsB x.1.rowsOwed &&
        callB p (finFrontS x a Q) x.1.core.book
    | none => false
  | none => false

/-- **The test on the two rounds and the columns, behind the last segment.** -/
def finR (p : P2) (x : ChainF) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match x.1.fin with
  | some a =>
    match a.G with
    | some Q => armR p (finFrontS x a Q) x.1.core.book r₁ r₂ gs
    | none => false
  | none => false

/-- **The test on values of the state, behind the last segment**: onesV at the rows that the
finish's own frame carries. -/
def finOnesV (s : S) : Bool :=
  match s.here with
  | .fin a => onesV s.st a.fr.rows
  | _ => false

/-- **The three tests give the premises.** -/
theorem finPlain_of_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : finB p (chainF s) = true) (hV : finOnesV s = true)
    (hR : finR p (chainF s) r₁ r₂ gs = true) :
    ∃ a Q c G, FinPlain p s r₁ r₂ gs a Q c G := by
  unfold finOnesV at hV
  split at hV
  · rename_i a hh
    have hfin : (chainF s).1.fin = some (finSh a) := by
      show finOf s.here = _
      rw [hh]
      rfl
    unfold finB at hB
    unfold finR at hR
    rw [hfin] at hB hR
    cases e2 : a.G with
    | none =>
      have e2' : (finSh a).G = none := e2
      simp only [e2'] at hB
      cases hB
    | some Q =>
      have e2' : (finSh a).G = some Q := e2
      simp only [e2'] at hB hR
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
      obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hB
      have b4' : callB p (frontS (finFrontOf s a Q)) (Ground.Sh.bookSh s.book) = true := b4
      have hR' : armR p (frontS (finFrontOf s a Q)) (Ground.Sh.bookSh s.book) r₁ r₂ gs = true := hR
      have hc : ∃ c, (finFrontOf s a Q).st.codes.base[(finFrontOf s a Q).f.rows.code]? =
          some c := by
        unfold callB at b4'
        split at b4'
        · rename_i c e
          exact ⟨c, e⟩
        · cases b4'
      obtain ⟨c, ec⟩ := hc
      obtain ⟨r1, r2, r3, r4⟩ := arm_of_R (roots := s.roots) ec hR'
      obtain ⟨c', G, ec', H⟩ := callPlain_of_B (roots := s.roots) b4' hV r2
      obtain rfl : c = c' := Option.some.inj (ec.symm.trans ec')
      exact ⟨a, Q, c, G, b1, r1, hh, b2, e2, b3, H, r3, r4⟩
  · cases hV

/-- **The three tests accept: the kind's own decision says yes behind the last segment.** -/
theorem finish_returns_B {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hB : finB p (chainF s) = true) (hV : finOnesV s = true)
    (hR : finR p (chainF s) r₁ r₂ gs = true) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨a, Q, c, G, H⟩ := finPlain_of_B hB hV hR
  exact finish_returns_sent H

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.arm_of_R
#print axioms VerifiableInference.Desc.First.Shape.headFront_S
#print axioms VerifiableInference.Desc.First.Shape.headPlain_of_B
#print axioms VerifiableInference.Desc.First.Shape.head_returns_B
#print axioms VerifiableInference.Desc.First.Shape.finFront_S
#print axioms VerifiableInference.Desc.First.Shape.finPlain_of_B
#print axioms VerifiableInference.Desc.First.Shape.finish_returns_B
