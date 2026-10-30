-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CarryTests.lean: the premises of `carryExact_from_front` that name no words, as tests with code.

What is defined. Tests that return true or false, of the public parameters Zp, a link's number, the first chain's state
t₀ in front of a closing and the closing's rounds rs. They are meant to be evaluated at a state of a run.
  `shapedB`, `shapedAllB`   the rounds have the kind's shape (`Shaped`, `ShapedAll`,
                   Johnson/Desc/K10/Honest/YesFree.lean)
  `lenB`            the main code's message length is 2 ^ logEll of the group's layout
  `behind`          the state behind the step of the lifted closing (`K9.closing`), at first tree 0 and no columns: in
                   front of "the segment is shut"
  `notInHeadB`      at the head's sort the state does not stand in the head
  `doorAt`, `frontOf`   what the library's way in returns behind the closing, and the front there
  `judgedFree`, `judgedAt`   eleven lines, each a name with its test: six that read of the public parameters the
                   closing's numbers P alone, five that read more
  `controlsFree`, `controlsAt`   nine controls: the same tests at bent data: each is meant to say no
  `judgedBehind`    four of the lines again, at a state behind the closing that is handed in: it feeds no theorem
  `parAt`, `sheet`   the closing's numbers as the lot makes them (Johnson/Desc/ProofFile/Lot/K9.lean); all lines at a
                   link

What is proved.
  `shaped_of`, `shapedAll_of`, `len_of`, `notInHead_of`   a yes of a test gives the premise
  `closing_step_is`   the lifted block's step, at 2 + k rounds of the kind's shape, returns what its decision returns at
                   the rounds without their digests, and takes no column

  **`carryExact_of_tests`**   where eight of the tests say yes, `carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean)
                   holds at the state behind the lifted closing's step, if the premises on the words hold

Limits. THE PREMISES ON THE WORDS ARE NO TESTS: that every row that the group's proximity test takes in (`runRows`)
holds of the witness's words, that the witness's table at the fresh mask's message pairs with the hiding polynomial's
coefficients, that "FOLD epsilon" shows that polynomial's sum and that the rounds "FOLD round" show the honest round
polynomials stay a premise (hW) of `carryExact_of_tests`. Three of the eleven lines feed no theorem: "the public
parameters have a switch into group n + 1", "the closing's group is n", "the front's new group is n + 1": they ask
whether n names a place that is there and belongs to this closing, which the sentence itself does not ask. `behind` is
the step of the lifted block alone, at `Cl := Unit`: the two more wrappers that stand around it in the first chain
(AtS.lean), the claims' retyping, the place's name and a block of the kind "frame" that the makers may join behind the
member are not laid: that the description's own member returns the same state is not shown. That the group's number is
the link's is taken, and tested by one line. A test's yes at one state says nothing of another. No
control is proved to say no. Two lines have no control: the one on the head, and "the way
in returns"; where the next switch stands at a link the way in returns at every state, so that line then says what "the
lifted closing's step returns" says. That a test's no refutes its premise is proved of `closeBaseB` alone
(`closeBaseB_iff`, BaseB.lean). `carryExact_of_tests` is applied nowhere: that its premises can be met together is not
shown. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.CarryWords
import Johnson.Desc.K10.Honest.AtS
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs.Tests
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase closeBaseB closeBase_of Shaped ShapedAll
  shapedAll_noDigest groups_nil rounds_fit)
open ProofFile.Honest.K10.Values (keptLen)

/-! ## 1 The tests -/

/-- The round shows n elements of the extension field, and drew one element, no position and no matrix entry. -/
def shapedB (n : Nat) (r : Fmt.RoundView) : Bool :=
  (r.vals.all fun g => match g with
    | .e _ => true
    | _ => false) && r.vals.length == n && r.drawn.elems.length == 1 && r.drawn.poss.isEmpty &&
    r.drawn.trits.isEmpty

/-- "BAT", "FOLD epsilon", then rounds "FOLD round". -/
def shapedAllB : List Fmt.RoundView → Bool
  | rB :: rE :: rR => shapedB 0 rB && shapedB 1 rE && rR.all (shapedB 2)
  | _ => false

/-- The main code's message length is 2 ^ logEll of the group's layout. -/
def lenB (s : Rec) : Bool :=
  match s.st.groups[s.frame.group]? with
  | some G => 2 ^ (Own.layoutOf s.st G).logEll == (s.st.codes.base.getD s.frame.shape.code default).ell
  | none => false

/-- The state behind the lifted closing's step, at no columns. -/
def behind (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) : Option First.S :=
  ((K9.closing (Cl := Unit) P).step 0 t₀ rs []).toOption.map (·.1)

/-- At the head's sort the state does not stand in the head. -/
def notInHeadB (Zp : ProofFile.Pub) (n : Nat) (s : First.S) : Bool :=
  match (ProofFile.pAtK2 Zp n).stands, s.here with
  | .head, .head _ => false
  | _, _ => true

/-- What the way in returns behind the closing. -/
def doorAt (Zp : ProofFile.Pub) (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) : Option First.S :=
  (behind P t₀ rs).bind (doorZ Zp n)

/-- The front there. -/
def frontOf (Zp : ProofFile.Pub) (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) :
    Option _root_.Tw.K2.Front :=
  (doorAt Zp n P t₀ rs).bind (First.K2.frontAt (ProofFile.pAtK2 Zp n))

/-- **The judged lines that read of the public parameters the closing's numbers P alone**: each line's name with its
test. n: the number of the group that the closing closes. t₀: the first chain's state in front of the block `K9.closing
P`, the second of the three of `K9.closeOf`: behind the one equation. rs: that block's rounds. -/
def judgedFree (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) : List (String × Bool) :=
  [("CloseBase's test says yes at the state in front", closeBaseB P (K9.recOf t₀)),
   ("there are 2 + k rounds", rs.length == 2 + P.k),
   ("the rounds have the kind's shape", shapedAllB rs),
   ("the main code's message length is 2 ^ logEll of the group's layout", lenB (K9.recOf t₀)),
   ("the lifted closing's step returns", (behind P t₀ rs).isSome),
   ("the closing's group is n", (K9.recOf t₀).frame.group == n)]

/-- **The judged lines that read the public parameters** Zp. -/
def judgedAt (Zp : ProofFile.Pub) (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) :
    List (String × Bool) :=
  [("the public parameters have a switch into group n + 1", (ProofFile.pAtK2? Zp n).isSome),
   ("the next switch does not stand at the head, or the state behind the closing does not stand in the head",
     ((behind P t₀ rs).map (notInHeadB Zp n)).getD false),
   ("the way in returns at the state behind the closing", (doorAt Zp n P t₀ rs).isSome),
   ("the front returns at the state behind the closing", (frontOf Zp n P t₀ rs).isSome),
   ("the front's new group is n + 1", ((frontOf Zp n P t₀ rs).map fun fx => fx.f.group == n + 1).getD false)]

/-- **The controls that read of the public parameters the closing's numbers P alone**: the same tests at bent data: each
is meant to say no. -/
def controlsFree (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) : List (String × Bool) :=
  [("CloseBase's test at a frame without a mask",
     closeBaseB P { K9.recOf t₀ with frame := { (K9.recOf t₀).frame with mask := none } }),
   ("2 + k rounds, at one round fewer", (rs.drop 1).length == 2 + P.k),
   ("the kind's shape, at the rounds in the other order", shapedAllB rs.reverse),
   ("the main code's message length, at a code's number that is not there",
     lenB { K9.recOf t₀ with frame := { (K9.recOf t₀).frame with
       shape := { (K9.recOf t₀).frame.shape with code := (K9.recOf t₀).st.codes.base.size } } }),
   ("the step returns, at one round fewer", (behind P t₀ (rs.drop 1)).isSome),
   ("the closing's group is n + 1", (K9.recOf t₀).frame.group == n + 1)]

/-- **The controls that read the public parameters**: each is meant to say no. -/
def controlsAt (Zp : ProofFile.Pub) (n : Nat) (P : Par) (t₀ : First.S) (rs : List Fmt.RoundView) :
    List (String × Bool) :=
  [("a switch into group n + 1000001", (ProofFile.pAtK2? Zp (n + 1000000)).isSome),
   ("the front returns, at the state in front of the closing",
     ((doorZ Zp n t₀).bind (First.K2.frontAt (ProofFile.pAtK2 Zp n))).isSome),
   ("the front's new group is n", ((frontOf Zp n P t₀ rs).map fun fx => fx.f.group == n).getD false)]

/-- **Four of the lines again, at a state s₁ that is handed in**: for the state behind the closing that a description's
own member returns, which may differ from `behind`. -/
def judgedBehind (Zp : ProofFile.Pub) (n : Nat) (s₁ : First.S) : List (String × Bool) :=
  [("AT THE STATE HANDED IN: the next switch does not stand at the head, or the state does not stand in the head",
     notInHeadB Zp n s₁),
   ("AT THE STATE HANDED IN: the way in returns", (doorZ Zp n s₁).isSome),
   ("AT THE STATE HANDED IN: the front returns",
     ((doorZ Zp n s₁).bind (First.K2.frontAt (ProofFile.pAtK2 Zp n))).isSome),
   ("AT THE STATE HANDED IN: the front's new group is n + 1",
     (((doorZ Zp n s₁).bind (First.K2.frontAt (ProofFile.pAtK2 Zp n))).map fun fx => fx.f.group == n + 1).getD false)]

/-- The closing's numbers at the link l, as the lot makes them of the public parameters. -/
def parAt (Zp : ProofFile.Pub) (l : Nat) : Option Par :=
  (ProofFile.k9Where (ProofFile.k9Stretches Zp) l).bind (ProofFile.k10Par Zp (ProofFile.k9Stretches Zp))

/-- **The whole sheet at the link l**: the judged lines, then the controls, each control's name marked. The group's
number is taken to be the link's: the line "the closing's group is n" tests it. One line alone where the lot has no
numbers for a closing at l. -/
def sheet (Zp : ProofFile.Pub) (l : Nat) (t₀ : First.S) (rs : List Fmt.RoundView) : List (String × Bool) :=
  match parAt Zp l with
  | some P =>
    (s!"the lot has the closing's numbers at the link n = {l}", true) ::
      (judgedFree l P t₀ rs ++ judgedAt Zp l P t₀ rs ++
        (controlsFree l P t₀ rs ++ controlsAt Zp l P t₀ rs).map fun x =>
          ("CONTROL, MEANT TO SAY false: " ++ x.1, x.2))
  | none => [(s!"the lot has the closing's numbers at the link n = {l}", false)]

/-! ## 2 What a yes gives -/

theorem shaped_of {n : Nat} {r : Fmt.RoundView} (h : shapedB n r = true) : Shaped n r := by
  unfold shapedB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, h4, h5⟩
  · have key : ∀ l : List Fmt.ItemValue, (l.all fun g => match g with
              | .e _ => true
              | _ => false) = true → ∃ xs : List Fmt.Ext, l = xs.map Fmt.ItemValue.e := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨[], rfl⟩
      | cons g l ih =>
        intro hl
        rw [List.all_cons, Bool.and_eq_true] at hl
        obtain ⟨xs, rfl⟩ := ih hl.2
        cases g with
        | e x => exact ⟨x :: xs, rfl⟩
        | _ => exact absurd hl.1 (by simp)
    obtain ⟨xs, hx⟩ := key _ h1
    refine ⟨xs, hx, ?_⟩
    rw [hx, List.length_map] at h2
    exact h2
  · match he : r.drawn.elems, h3 with
    | [t], _ => exact ⟨t, rfl⟩

theorem shapedAll_of : ∀ {rs : List Fmt.RoundView}, shapedAllB rs = true → ShapedAll rs
  | [], h => by cases h
  | [_], h => by cases h
  | _ :: _ :: rR, h => by
    unfold shapedAllB at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨shaped_of h.1.1, shaped_of h.1.2, fun r hr => shaped_of (h.2 r hr)⟩

theorem len_of {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (h : lenB s = true) :
    2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell := by
  unfold lenB at h
  rw [H.there] at h
  have hc : (D.S1 s).codes = s.st.codes := (extends_begun s.st s.frame.group D.G).codes
  rw [hc]
  exact beq_iff_eq.1 h

/-- **The lifted block's step, at 2 + k rounds of the kind's shape, returns what its decision returns at the rounds
without their digests**, and takes no column. -/
theorem closing_step_is {Cl : Type} (P : Par) (ft : Nat) (t s' : First.S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hl : rs.length = 2 + P.k) (hs : ShapedAll rs)
    (h : (K9.closing (Cl := Cl) P).decide t (rs.map noDigest) [] = .ok s') :
    (K9.closing (Cl := Cl) P).step ft t rs cols = .ok (s', 0) := by
  have g : groupsOf ft (K9.closing (Cl := Cl) P).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (First.Close.entries P) _
  have f : roundsFit (K9.closing (Cl := Cl) P).rounds rs = true := rounds_fit (Cl := Cl) P rs hl hs
  unfold Block.step
  rw [f, g]
  show ((K9.closing (Cl := Cl) P).decide t (rs.map noDigest) []).bind _ = _
  rw [h]
  rfl

theorem notInHead_of {Zp : ProofFile.Pub} {n : Nat} {s : First.S} (h : notInHeadB Zp n s = true) :
    (ProofFile.pAtK2 Zp n).stands = .head → ∀ x, s.here ≠ .head x := by
  intro hp x hx
  unfold notInHeadB at h
  rw [hp, hx] at h
  cases h

/-- **What a yes of the tests gives.** Where the tests on the state in front, on the rounds and on the way in say yes,
`carryExact` holds at the state s₁ behind the lifted closing's step, if the premises on the words hold: for the data D
of `CloseBase`, the rounds without their digests and the row that the batching returns there are coefficients W and a
point γ with: every row that the group's proximity test takes in (`runRows`) holds of the witness's words in front of
the closing; the witness's table at the fresh mask's message pairs with W; "FOLD epsilon" shows the sum of W's
polynomial; the rounds "FOLD round" show the honest round polynomials. -/
theorem carryExact_of_tests {Q Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat) (z : Q)
    (t₀ : First.S) (y : Strs) (v : Wit Cells Tok MsgT) (P : Par) (rs : List Fmt.RoundView)
    (h1 : closeBaseB P (K9.recOf t₀) = true) (h2 : (rs.length == 2 + P.k) = true)
    (h3 : shapedAllB rs = true) (h4 : lenB (K9.recOf t₀) = true)
    {s₁ t : First.S} {fx : _root_.Tw.K2.Front} (h5 : behind P t₀ rs = some s₁)
    (h6 : notInHeadB Zp n s₁ = true) (h7 : doorZ Zp n s₁ = some t)
    (h8 : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx)
    (hW : ∀ (D : BaseData) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (row : GroupRow),
      CloseBase P (K9.recOf t₀) D → rs.map noDigest = rB :: rE :: rR →
      Own.batch (D.S1 (K9.recOf t₀)) (K9.recOf t₀).frame.group
        ⟨Own.layoutOf (K9.recOf t₀).st D.G, runRows (K9.recOf t₀).st D.G⟩ (drawnOf rB) = some row →
      ∃ (W : HIdx (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) → GE)
        (γ : HPt (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g))),
        AllSay rdE (K9.recOf t₀).st (runRows (K9.recOf t₀).st D.G).toList
          (wordsFirst arr t₀.st t₀.book v) ∧
        Pairs (stageB D (K9.recOf t₀)) (stageB D (K9.recOf t₀)).Z.l W
          (freshB D (K9.recOf t₀) (wordsFirst arr t₀.st t₀.book v)) ∧
        readE ((sentOf rE).getD 0 zeroE) =
          hMu (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) W ∧
        Shows ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g) rR
          (foldQK (stageB D (K9.recOf t₀)) (vecG (stageB D (K9.recOf t₀)) row)
            (msgOf (stageB D (K9.recOf t₀)) (tablesOf (D.S1 (K9.recOf t₀))
              (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr t₀.st t₀.book v))) W
            (readE (drawnOf rE))
            (keptVal (keptLen (D.S1 (K9.recOf t₀))) (tablesOf (D.S1 (K9.recOf t₀))
              (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr t₀.st t₀.book v)).kept row.kept)
            γ) γ) :
    carryExact Zp arr n (z, s₁) y v := by
  obtain ⟨D, H⟩ := closeBase_of h1
  have hl : rs.length = 2 + P.k := beq_iff_eq.1 h2
  have hs : ShapedAll rs := shapedAll_of h3
  obtain ⟨rB, rE, rR, hr⟩ : ∃ rB rE rR, rs.map noDigest = rB :: rE :: rR := by
    match rs, hs with
    | a :: b :: c, _ => exact ⟨_, _, _, rfl⟩
  have hl' : (rB :: rE :: rR).length = 2 + P.k := by rw [← hr, List.length_map, hl]
  have hs' : ShapedAll (rB :: rE :: rR) := hr ▸ shapedAll_noDigest hs
  obtain ⟨row, hrow, hdec⟩ := closing_leaves (Cl := Unit) H rB rE rR [] hl' hs'
  have hstep := closing_step_is (Cl := Unit) P 0 t₀ _ rs [] hl hs (hr ▸ hdec)
  unfold behind at h5
  rw [hstep] at h5
  cases Option.some.inj h5
  obtain ⟨W, γ, w1, w2, w3, w4⟩ := hW D rB rE rR row H hr hrow
  exact carryExact_from_front (Cl := Unit) Zp arr n z t₀ y v H rB rE rR [] hl' hs' hrow _ rfl
    (notInHead_of h6) h7 h8 (len_of H h4) w1 W γ w2 w3 w4

end ProofFile.Honest.K10.LeftIs.Tests

#print axioms ProofFile.Honest.K10.LeftIs.Tests.shapedB
#print axioms ProofFile.Honest.K10.LeftIs.Tests.shapedAllB
#print axioms ProofFile.Honest.K10.LeftIs.Tests.lenB
#print axioms ProofFile.Honest.K10.LeftIs.Tests.behind
#print axioms ProofFile.Honest.K10.LeftIs.Tests.notInHeadB
#print axioms ProofFile.Honest.K10.LeftIs.Tests.doorAt
#print axioms ProofFile.Honest.K10.LeftIs.Tests.frontOf
#print axioms ProofFile.Honest.K10.LeftIs.Tests.judgedFree
#print axioms ProofFile.Honest.K10.LeftIs.Tests.judgedAt
#print axioms ProofFile.Honest.K10.LeftIs.Tests.controlsFree
#print axioms ProofFile.Honest.K10.LeftIs.Tests.controlsAt
#print axioms ProofFile.Honest.K10.LeftIs.Tests.judgedBehind
#print axioms ProofFile.Honest.K10.LeftIs.Tests.parAt
#print axioms ProofFile.Honest.K10.LeftIs.Tests.sheet
#print axioms ProofFile.Honest.K10.LeftIs.Tests.shaped_of
#print axioms ProofFile.Honest.K10.LeftIs.Tests.shapedAll_of
#print axioms ProofFile.Honest.K10.LeftIs.Tests.len_of
#print axioms ProofFile.Honest.K10.LeftIs.Tests.closing_step_is
#print axioms ProofFile.Honest.K10.LeftIs.Tests.notInHead_of
#print axioms ProofFile.Honest.K10.LeftIs.Tests.carryExact_of_tests
