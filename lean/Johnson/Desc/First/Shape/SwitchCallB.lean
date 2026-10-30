-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchCallB.lean: THE CALL OF THE CODE SWITCH AT A GENERAL FRONT (kind K2):
ITS PREMISES (CallPlain, Johnson/Desc/K2/Honest/Returns/ArmsSent.lean: fifteen fields) FROM THREE
TESTS WITH CODE: ONE ON SHAPES AND THE PLAN, ONE ON VALUES OF THE STATE, ONE ON THE TWO ROUNDS AND
THE COLUMNS. General laws; nothing is evaluated.

What it is for. At the head's place and at the place behind the last segment the kind's decision
calls the switch at the place's own front. This file sorts the call's premises by what they read,
once, at a general front; SwitchArmsB.lean lays the two places' fronts into it.

  1 `FrontS`, `frontS`: what the tests read of a front: the statement's shape, the makes of its
    rows, the make of the carried single rows, the new group's number, the target, what is announced
    beside the target's own messages. `sendingAt_S`: the sending's public numbers hang on these.
  2 `frontPlainB_split`: the clause on the positions' range, taken out of frontPlainB
    (SwitchFrontPlain.lean).
  3 **`callB p y b`**: ON THE PLAN's NUMBERS, y : FrontS AND THE BOOK's SHAPE b: the old main code
    is there · the first round's entry fits what is announced · the sending's tests on the plan · as
    many messages as places in the book · as many trees as roots · ReadFits but "opens" (readFitsB)
    · FrontPlain but "the ones" and the positions' range (frontPlainB at no position).
  4 **`callR p y b r₁ r₂ cols`**: ON THE ROUNDS AND THE COLUMNS: round 1 fits its entry, draws as
    many elements as the seeds take, holds no value, no position, no trit · no seed's factor is
    spelt by three words 0 · round 2 holds the answers · the seven conditions of the round "LOC" ·
    the trees open at the columns (allOpenB) · the listed positions lie in the old main code's
    range.
  5 **`callPlain_of_B`**: callB p (frontS x) (bookSh B), onesV x.st x.f.rows (SwitchFrontFits.lean)
    and callR p (frontS x) (bookSh B) r₁ r₂ cols accept: then CallPlain p x B roots r₁ r₂ cols c G
    at the old main code c and the group G under the front's number.

Limits. One way. No front is shown at which the tests accept. No law here carries onesV from what a
chain's steps lay. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K2.Honest.Returns.ArmsSent
import Johnson.Desc.First.Shape.SwitchLinkB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (StSh stSh)
open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K2.Honest.Returns (CallPlain sendingAt inFront sentAt)
open _root_.Tw.K2 (Front Col switchNotices)

/-! ## 1 What the tests read of a front -/

/-- What the tests read of a front. -/
structure FrontS where
  /-- the statement's shape -/
  a : StSh
  /-- the makes of the statement's rows -/
  F : FormsSh
  /-- the make of the carried single rows -/
  rows : SingleSh
  /-- the new group's number -/
  group : Nat
  /-- the target -/
  T : SwitchTarget
  /-- what is announced beside the target's own messages -/
  others : Array OracleNotice

def frontS (x : Front) : FrontS :=
  ⟨stSh x.st, formsOf x.st, singleSh x.f.rows, x.f.group, x.T, x.others⟩

theorem sendingAt_S (p : P2) (x : Front) :
    sendingAt p x = sendingS p (frontS x).a.codes (frontS x).T (frontS x).others := rfl

/-! ## 2 The positions' range, taken out -/

theorem frontPlainB_split (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) (grp : Nat)
    (poss : List Nat) (c : Code) :
    frontPlainB a F old T grp poss c =
      (frontPlainB a F old T grp [] c && inRangeB a old poss c) := by
  have e : inRangeB a old [] c = true := rfl
  unfold frontPlainB
  rw [e]
  cases inRangeB a old poss c <;> simp

/-! ## 3 On shapes and the plan -/

/-- **The call's test on the plan's numbers and on shapes.** -/
def callB (p : P2) (y : FrontS) (b : Ground.Sh.BookSh) : Bool :=
  match y.a.codes.base[y.rows.code]? with
  | some c =>
    planOk1 none (switchNotices y.T y.others) (par9 p).eSeed &&
      K1.planOkOwn (sendingS p y.a.codes y.T y.others) &&
      decide (y.a.oracles.length = b.place.length) &&
      decide (((layTrees (sendingS p y.a.codes y.T y.others).codes
        (sendingS p y.a.codes y.T y.others).sent).getD {}).shapes.size = (par9 p).eSeed.roots) &&
      readFitsB y.a b y.rows && frontPlainB y.a y.F y.rows y.T y.group [] c
  | none => false

/-! ## 4 On the rounds and the columns -/

/-- **The call's test on the two rounds and the columns.** -/
def callR (p : P2) (y : FrontS) (b : Ground.Sh.BookSh) (r₁ r₂ : Fmt.RoundView) (cols : List Col) : Bool :=
  match y.a.codes.base[y.rows.code]? with
  | some c =>
    _root_.Desc.Plain.fits (par9 p).eSeed r₁ &&
      decide ((r₁.drawn.elems.map E.ofTriple).length =
        (sendingS p y.a.codes y.T y.others).seeds *
          ((sendingS p y.a.codes y.T y.others).coordinates + 1)) &&
      r₁.vals.isEmpty && r₁.drawn.poss.isEmpty && r₁.drawn.trits.isEmpty &&
      ((K1.seedsOf (sendingS p y.a.codes y.T y.others) r₁).all fun z => !isZeroE z.2) &&
      decide ((K1.answersIn (K1.cutTo (sendingS p y.a.codes y.T y.others) r₂)).length =
        (sendingS p y.a.codes y.T y.others).answers) &&
      locB (par9 p) (sendingS p y.a.codes y.T y.others).answers c.logN r₂ &&
      allOpenB y.a b (par9 p).firstTree (Positions.ofDraws c.logN r₂.drawn.poss)
        (treesOfS b y.rows) cols &&
      inRangeB y.a y.rows r₂.drawn.poss c
  | none => false

/-! ## 5 The premises -/

/-- **The three tests give the call's premises.** -/
theorem callPlain_of_B {p : P2} {x : Front} {B : TreeBook} {roots : Nat} {r₁ r₂ : Fmt.RoundView}
    {cols : List Col} (hB : callB p (frontS x) (Ground.Sh.bookSh B) = true)
    (hV : onesV x.st x.f.rows = true)
    (hR : callR p (frontS x) (Ground.Sh.bookSh B) r₁ r₂ cols = true) :
    ∃ c G, x.st.codes.base[x.f.rows.code]? = some c ∧ CallPlain p x B roots r₁ r₂ cols c G := by
  unfold callB at hB
  split at hB
  · rename_i c e5
    unfold callR at hR
    split at hR
    · rename_i c' f5
      obtain rfl : c = c' := Option.some.inj (e5.symm.trans f5)
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
        Bool.not_eq_true'] at hB hR
      obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hR
      have hfp : frontPlainB (stSh x.st) (formsOf x.st) (singleSh x.f.rows) x.T x.f.group
          r₂.drawn.poss c = true := by
        rw [frontPlainB_split, Bool.and_eq_true]
        exact ⟨b6, a10⟩
      obtain ⟨G, -, hF⟩ := frontPlain_of_B hfp hV
      have hRd : K2.Honest.Returns.ReadFits
          (inFront (par9 p) x B (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols)
          (Positions.ofDraws c.logN r₂.drawn.poss) := by
        rw [readFits_iffB, Bool.and_eq_true]
        exact ⟨b5, a9⟩
      refine ⟨c, G, e5,
        { entry := b1, fits₁ := a1, plan := b2, step := ?_, draw := a2, vals := a3, poss := a4
          trits := a5, factor := a6, answers := a7, trees := b4, oldCode := e5, loc := a8
          reads := hRd, front := hF }⟩
      rw [← Ground.Sh.orc_size, ← Ground.Sh.place_size]
      exact b3
    · cases hR
  · cases hB

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sendingAt_S
#print axioms VerifiableInference.Desc.First.Shape.frontPlainB_split
#print axioms VerifiableInference.Desc.First.Shape.callPlain_of_B
