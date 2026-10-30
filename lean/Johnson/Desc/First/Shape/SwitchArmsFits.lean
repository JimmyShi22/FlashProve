-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchArmsFits.lean: THE CODE SWITCH AT THE HEAD's PLACE AND AT THE PLACE
BEHIND THE LAST SEGMENT (kind K2): ROUNDS AND COLUMNS THAT FIT THE KIND's DECLARED ROUNDS MEET THE
TEST ON ROUNDS AND COLUMNS (headR, finR: SwitchArmsB.lean), UNDER THE TEST ON SHAPES AND ONE MORE
TEST ON THE PLAN AND THE SHAPE. General laws; nothing is evaluated.

What it is for. A block's step asks two tests on form in front of its decision (Block.Fits,
Johnson/Top/H0/StepLaws/StepLaws.lean). SwitchLinkFits.lean and SwitchLinkFactor.lean lead from
these to the test on rounds and columns at a segment's first place. Here the like, once at a general
front, then at the two other places.

  1 `callB_entry`: callB's clause on the first round's entry.
  2 **`armP p y b`**: THE FURTHER TEST ON THE PLAN's NUMBERS AND SHAPES, at a front: linkP's six
    clauses (SwitchLinkFits.lean): round 1 draws as many elements as the seeds take · round 2 holds
    as many answers as the sending takes · the positions' range is the old main code's · a position
    is drawn · treesShapeB at the trees that are opened · the plan's list of trees read is the list
    of these trees, each by its number in the chain, its depth and its width.
  3 **`armR_of_fits`**: roundsFit (K2.rounds p) [R₁, R₂], the columns' test, callB p y b and armP
    p y b: then armR p y b (noDigest R₁) (noDigest R₂) accepts at the groups that the step shows.
    `armR_of_Fits`: the same at a block with the kind's declared rounds.
  4 `headP`, **`headR_of_Fits`**; `finP`, **`finR_of_Fits`**: at the two places: Block.Fits, headB
    and headP (finB and finP): then the rounds are two and headR (finR) accepts at them, shown
    without the sealed digest, and at the groups that the step shows.

By opens_of_cols, k2_fit, groups_k2, answersIn_len and regroup_length (SwitchLinkFits.lean), and by
rounds_give_shown and nonZero_of_entry (Johnson/Desc/K2/Honest/Returns/DrawFits.lean, DrawTies.lean)
for "no seed's factor is spelt by three words 0".

Limits. No plan and shape are shown at which the tests accept. "Not 0" is said of words, as the
kind's text says it. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SwitchArmsB
import Johnson.Desc.First.Shape.SwitchLinkFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 par9 flat)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (switchNotices)

/-! ## 1 The entry -/

/-- callB's clause on the first round's entry. -/
theorem callB_entry {p : P2} {y : FrontS} {b : Ground.Sh.BookSh} (h : callB p y b = true) :
    planOk1 none (switchNotices y.T y.others) (par9 p).eSeed = true := by
  unfold callB at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1.1
  · cases h

/-! ## 2 The further test on the plan and shapes -/

/-- **The further test on the plan's numbers and shapes, at a front.** -/
def armP (p : P2) (y : FrontS) (b : Ground.Sh.BookSh) : Bool :=
  match y.a.codes.base[y.rows.code]? with
  | some c =>
    decide (p.seeds = (sendingS p y.a.codes y.T y.others).seeds *
        ((sendingS p y.a.codes y.T y.others).coordinates + 1)) &&
      decide (p.answers = (sendingS p y.a.codes y.T y.others).answers) &&
      decide (p.logN = c.logN) && decide (0 < p.positions) &&
      treesShapeB y.a b c.logN (treesOfS b y.rows) &&
      readsOfS b p.firstTree (treesOfS b y.rows) == some p.read
  | none => false

/-! ## 3 Rounds and columns that fit, at a front -/

/-- **Rounds and columns that fit meet the test on rounds and columns, at a front.** -/
theorem armR_of_fits {p : P2} {y : FrontS} {b : Ground.Sh.BookSh} {ft : Nat} {R₁ R₂ : Fmt.RoundView}
    {cols : List Col} (hf : roundsFit (First.K2.rounds p) [R₁, R₂] = true)
    (hc : (cols.take ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id).length).map
        (fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id)
    (hB : callB p y b = true) (hP : armP p y b = true) :
    armR p y b (noDigest R₁) (noDigest R₂)
      (regroup ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).map (·.length))
        (cols.take ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id).length)) =
      true := by
  obtain ⟨_, _, e, a1, a2, a3, a4, b1, b2, b3, b4, b5⟩ := k2_fit hf
  obtain ⟨rfl, rfl⟩ : R₁ = _ ∧ R₂ = _ := by
    have := List.cons.inj e
    exact ⟨this.1, (List.cons.inj this.2).1⟩
  have he := callB_entry hB
  unfold armP at hP
  unfold armR callR
  split at hP
  · rename_i c e5
    rw [e5]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hP
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hP
    rw [groups_k2] at hc ⊢
    have hr : ∀ q ∈ R₂.drawn.poss, q < 2 ^ c.logN := p3 ▸ b5
    obtain ⟨o1, o2⟩ := opens_of_cols _ _ p.firstTree c.logN R₂.drawn.poss hr
      (fun k => p.firstTree + k - ft) _ p.read _ p6 p5 hc
    have hv : R₂.vals.length = p.answers := by
      have := congrArg List.length b1
      rwa [List.length_map, List.length_replicate] at this
    have hz := (K2.Honest.Returns.rounds_give_shown p _ R₁ R₂ p1
      (K2.Honest.Returns.nonZero_of_entry p _ _ (sendingS_sent p _ _ _) he) hf).2.2.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
      Bool.not_eq_true']
    refine ⟨⟨⟨b5, ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, a1⟩, a3⟩, a4⟩, hz⟩, ?_⟩, ?_⟩, o1⟩, ?_⟩⟩, o2⟩, ?_⟩
    · show (R₁.drawn.elems.length == p.seeds && R₁.drawn.poss.length == 0 &&
        R₁.drawn.trits.length == 0) = true
      rw [a2, a3, a4]
      simp
    · show (R₁.drawn.elems.map E.ofTriple).length = _
      rw [List.length_map, a2, p1]
    · show ((R₂.vals.take _).filterMap _).length = _
      rw [← p2]
      have et : R₂.vals.take p.answers = R₂.vals := by rw [← hv, List.take_length]
      rw [et]
      exact answersIn_len _ _ b1
    · show (!("LOC" != "LOC") && !((0 : Nat) != 0) && ((0 : Nat) == 0) &&
          !(R₂.vals.length - _ != 0) &&
        (R₂.drawn.elems.length == 0 && R₂.drawn.poss.length == p.positions &&
          R₂.drawn.trits.length == 0) &&
        (p.logN == c.logN && decide (0 < p.positions)) && R₂.drawn.elems.isEmpty) = true
      rw [← p2, hv, b2, b3, b4, p3]
      simp [p4]
    · unfold inRangeB
      rw [List.all_eq_true]
      intro v hv'
      have hm : v ∈ listOfT R₂.drawn.poss := by simpa [Positions.ofDraws] using hv'
      rw [listOfT_eq] at hm
      have hq := hr v ((Fmt.listOf_mem _ _).1 hm)
      have eg : y.a.codes.base.getD y.rows.code default = c := by
        rw [Array.getD_eq_getD_getElem?, e5]
        rfl
      rw [eg]
      exact decide_eq_true hq
    · rw [regroup_length, List.length_map, List.length_map]
  · cases hP

/-- The same at a block with the kind's declared rounds. -/
theorem armR_of_Fits {Cl : Type} {blk : Block S Cl} {p : P2} {y : FrontS} {b : Ground.Sh.BookSh}
    {ft : Nat} {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hB : callB p y b = true) (hP : armP p y b = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧
      armR p y b (noDigest R₁) (noDigest R₂) (blk.shown ft rs cols) = true := by
  obtain ⟨h1, h2⟩ := hF
  rw [hb] at h1
  obtain ⟨R₁, R₂, rfl, -⟩ := k2_fit h1
  refine ⟨R₁, R₂, rfl, ?_⟩
  unfold Block.want at h2
  unfold Block.shown Block.want
  rw [hb] at h2 ⊢
  exact armR_of_fits h1 (beq_iff_eq.1 h2) hB hP

/-! ## 4 The two places -/

/-- **The further test on the plan and the shape, at the head's place.** -/
def headP (p : P2) (x : ChainF) : Bool :=
  match x.1.head, x.1.check.frame.groups[x.1.check.frame.link]? with
  | some hd, some Q => armP p (headFrontS x hd Q.target) x.1.core.book
  | _, _ => false

/-- **Rounds and columns that fit meet headR.** -/
theorem headR_of_Fits {Cl : Type} {blk : Block S Cl} {p : P2} {x : ChainF} {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hB : headB p x = true) (hP : headP p x = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧
      headR p x (noDigest R₁) (noDigest R₂) (blk.shown ft rs cols) = true := by
  unfold headB at hB
  unfold headP at hP
  unfold headR
  split at hB
  · rename_i hd Q e1 e2
    rw [e1, e2] at hP
    simp only [Bool.and_eq_true] at hB
    exact armR_of_Fits hb hF hB.2 hP
  · cases hB

/-- **The further test on the plan and the shape, behind the last segment.** -/
def finP (p : P2) (x : ChainF) : Bool :=
  match x.1.fin with
  | some a =>
    match a.G with
    | some Q => armP p (finFrontS x a Q) x.1.core.book
    | none => false
  | none => false

/-- **Rounds and columns that fit meet finR.** -/
theorem finR_of_Fits {Cl : Type} {blk : Block S Cl} {p : P2} {x : ChainF} {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hB : finB p x = true) (hP : finP p x = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧
      finR p x (noDigest R₁) (noDigest R₂) (blk.shown ft rs cols) = true := by
  unfold finB at hB
  unfold finP at hP
  unfold finR
  split at hB
  · rename_i a e1
    rw [e1] at hP
    dsimp only at hP
    split at hB
    · rename_i Q e2
      rw [e2] at hP
      simp only [Bool.and_eq_true] at hB
      exact armR_of_Fits hb hF hB.2 hP
    · cases hB
  · cases hB

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.callB_entry
#print axioms VerifiableInference.Desc.First.Shape.armR_of_fits
#print axioms VerifiableInference.Desc.First.Shape.armR_of_Fits
#print axioms VerifiableInference.Desc.First.Shape.headR_of_Fits
#print axioms VerifiableInference.Desc.First.Shape.finR_of_Fits
