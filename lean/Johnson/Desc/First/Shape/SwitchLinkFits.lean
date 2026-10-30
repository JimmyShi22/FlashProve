-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchLinkFits.lean: THE CODE SWITCH AT A SEGMENT's FIRST PLACE (kind K2):
ROUNDS AND COLUMNS THAT FIT THE KIND's DECLARED ROUNDS MEET THE TEST ON ROUNDS AND COLUMNS (linkR,
SwitchLinkB.lean), BUT FOR ONE CLAUSE, WHICH IS LEFT TO SwitchLinkFactor.lean, AND UNDER ONE MORE
TEST ON THE PLAN AND THE SHAPE. General laws; nothing is evaluated.

What it is for. A block's step asks two tests on form in front of its decision (Block.Fits,
Johnson/Top/H0/StepLaws/StepLaws.lean): the rounds fit the declared rounds (roundsFit,
Johnson/Desc/Block.lean); the next columns are, in key, position and width, those that are read.
linkR asks thirteen clauses of the two rounds and the groups of columns that the decision is shown.

  1 `answersIn_len`, **`k2_fit`**: what rounds that fit the kind's two declared rounds (K2.rounds p,
    Johnson/Top/H0/Tw/K2C/Kind.lean) give.
  2 `readOfS`, `readsOfS`, `treesShapeB`, **`linkP p x`**: THE FURTHER TEST ON THE PLAN's NUMBERS
    AND THE SHAPE: round 1 draws as many elements as the seeds take · round 2 holds as many answers
    as the sending takes · the positions' range is the old main code's · a position is drawn · each
    tree that is opened is in the book; its sampled parts belong to the same groups, and to one
    group at most where it holds a message without a sample (leafOkS); such a tree has not been
    opened before; it is not longer than the positions' range (treesShapeB) · THE PLAN's LIST OF
    TREES READ IS THE LIST OF THE TREES THAT HOLD THE OLD MESSAGES, each by its number in the chain,
    its depth and its width.
    `factorV p x r₁`: the clause that is left: no seed's factor is spelt by three words 0.
  3 `ownAtS_of`, `colsStand_of`, `regroup_length`, **`opens_of_cols`**: columns that are those read,
    laid into groups and flat again: the trees open at them, and none is left.
  4 `groups_k2`, **`linkR_of_fits`**: roundsFit (K2.rounds p) [R₁, R₂], the columns' test, linkP p x
    and factorV p x (noDigest R₁): then linkR p x (noDigest R₁) (noDigest R₂) accepts at the groups
    that the step shows. **`linkR_of_Fits`**: the same at a block with these declared rounds, in
    the words of Block.Fits and Block.shown.

WHICH CLAUSES FALL TO WHAT. To roundsFit alone: range · fits₁ · vals · poss · trits · groups. To
roundsFit with a clause of linkP: draw · answers · loc · inRange. To the columns' test with
linkP: the trees open · no column is left. NOT DRAWN HERE: no seed's factor is 0: it falls to
roundsFit too, with clauses of linkB and linkP: SwitchLinkFactor.lean.

Limits. No plan and shape are shown at which linkP accepts. The number in the label of the chain's
first own tree, which the step's test on columns takes, plays no part: the groups that a decision is
shown hold no key. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SwitchLinkB
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground.Sh (StSh)
open VerifiableInference.Desc.First.K2 (P2 par9 flat)

/-! ## 1 Rounds that fit the kind's two declared rounds -/

/-- Items that are all answers. -/
theorem answersIn_len : ∀ (l : List Fmt.ItemValue) (n : Nat),
    l.map itemOf = List.replicate n .answer →
    (l.filterMap fun | .answer x => some (E.ofTriple x) | _ => none).length = n
  | [], n, h => by
    cases n with
    | zero => rfl
    | succ n => cases h
  | g :: l, n, h => by
    cases n with
    | zero => cases h
    | succ n =>
      rw [List.map_cons, List.replicate_succ] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      cases g with
      | answer x =>
        rw [List.filterMap_cons]
        show (_ :: _).length = _
        rw [List.length_cons, answersIn_len l n h2]
      | f _ => cases h1
      | e _ => cases h1
      | word _ => cases h1
      | root _ => cases h1

/-- **Rounds that fit the kind's declared rounds.** -/
theorem k2_fit {p : P2} {rs : List Fmt.RoundView} (h : roundsFit (First.K2.rounds p) rs = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧ R₁.vals = [] ∧ R₁.drawn.elems.length = p.seeds ∧
      R₁.drawn.poss = [] ∧ R₁.drawn.trits = [] ∧
      R₂.vals.map itemOf = List.replicate p.answers .answer ∧ R₂.drawn.elems = [] ∧
      R₂.drawn.poss.length = p.positions ∧ R₂.drawn.trits = [] ∧
      ∀ q ∈ R₂.drawn.poss, q < 2 ^ p.logN := by
  unfold First.K2.rounds at h
  match rs, h with
  | [R₁, R₂], h =>
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, -⟩, -⟩, ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, -⟩, -⟩, -⟩ := h
    refine ⟨R₁, R₂, rfl, ?_, a2, List.eq_nil_of_length_eq_zero a3,
      List.eq_nil_of_length_eq_zero a4, ?_, List.eq_nil_of_length_eq_zero b2, b3,
      List.eq_nil_of_length_eq_zero b4, b5⟩
    · have : R₁.vals.map itemOf = [] := by
        rw [a1]
        simp [Fmt.DeclaredRound.items, Fmt.Entry.cut]
      exact List.map_eq_nil_iff.1 this
    · rw [b1]
      simp [Fmt.DeclaredRound.items, Fmt.Entry.cut]
  | [], h => cases h
  | [_], h => simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [roundsFit] at h

/-! ## 2 The further test on the plan and the shape -/

/-- A tree of the book as the plan's list of trees read names it: its number in the chain, its
depth, its width. The number is the tree's own less firstTree, cut off at 0: a tree numbered below
firstTree reads as 0. -/
def readOfS (b : Ground.Sh.BookSh) (firstTree t : Nat) : Option (Nat × Nat × Nat) :=
  (b.trees[t]?).map fun T =>
    (T.number - firstTree, T.shape.logN, T.shape.mainWidth + T.shape.maskWidth)

def readsOfS (b : Ground.Sh.BookSh) (firstTree : Nat) : List Nat → Option (List (Nat × Nat × Nat))
  | [] => some []
  | t :: ts => (readOfS b firstTree t).bind fun r => (readsOfS b firstTree ts).map (r :: ·)

/-- AllOpen's four clauses at a tree that read no column. -/
def treesShapeB (a : StSh) (b : Ground.Sh.BookSh) (logN : Nat) (ts : List Nat) : Bool :=
  ts.all fun t =>
    match b.trees[t]? with
    | some T => leafOkS a T && (!T.oneList || T.lists == 0) && decide (T.shape.logN ≤ logN)
    | none => false

/-- **The further test on the plan's numbers and the shape.** -/
def linkP (p : P2) (x : ChainF) : Bool :=
  match x.1.check.frame.groups[x.1.check.frame.link]?,
    x.1.core.st.codes.base[x.1.check.frame.rows.code]? with
  | some Q, some c =>
    decide (p.seeds =
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).seeds *
          ((sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).coordinates + 1)) &&
      decide (p.answers =
        (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)).answers) &&
      decide (p.logN = c.logN) && decide (0 < p.positions) &&
      treesShapeB
        (withGroupS x.1.core.st x.1.check.frame.shape.code x.1.check.frame.shape.maskCode)
        x.1.core.book c.logN (treesOfS x.1.core.book x.1.check.frame.rows) &&
      readsOfS x.1.core.book p.firstTree (treesOfS x.1.core.book x.1.check.frame.rows) ==
        some p.read
  | _, _ => false

/-- **The clause that is left**: no seed's factor is spelt by three words 0. -/
def factorV (p : P2) (x : ChainF) (r₁ : Fmt.RoundView) : Bool :=
  match x.1.check.frame.groups[x.1.check.frame.link]? with
  | some Q =>
    (K1.seedsOf (sendingS p x.1.core.st.codes Q.target (linkOthers x.1.check.frame)) r₁).all
      fun z => !isZeroE z.2
  | none => false

/-! ## 3 The columns -/

/-- The list at which a tree of the book is opened, under positions in the range. -/
theorem ownAtS_of {b : Ground.Sh.BookSh} {t logN : Nat} {poss : List Nat} {T : Ground.Sh.TreeSh}
    (hT : b.trees[t]? = some T) (hr : ∀ q ∈ poss, q < 2 ^ logN) :
    ownAtS (Positions.ofDraws logN poss) b t =
      (Fmt.listOf (poss.map (· % 2 ^ T.shape.logN))).toArray := by
  unfold ownAtS
  rw [hT]
  dsimp only
  split
  · rename_i he
    have he' : T.shape.logN = logN := beq_iff_eq.1 he
    show (listOfT poss).toArray = _
    rw [listOfT_eq, he']
    congr 2
    conv_lhs => rw [← List.map_id poss]
    exact List.map_congr_left fun q hq => (Nat.mod_eq_of_lt (hr q hq)).symm
  · show (listOfT (poss.toArray.map (· % 2 ^ T.shape.logN)).toList).toArray = _
    rw [listOfT_eq, Array.toList_map]

/-- Columns whose positions and widths are as asked stand, under whatever key they are laid. -/
theorem colsStand_of (k k' W : Nat) : ∀ (l : List Col) (xs : List Nat),
    l.map (fun c => (c.1, c.2.1, c.2.2.length)) = xs.map (fun x => (k', x, W)) →
    Own.colsStand k W (l.map fun c => (k, c.2.1, c.2.2)) xs = true
  | [], _, _ => rfl
  | _ :: _, [], h => by cases h
  | c :: l, x :: xs, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have ih := colsStand_of k k' W l xs h2
    unfold Own.colsStand at ih ⊢
    rw [List.map_cons, List.zip_cons_cons, List.all_cons, ih, Bool.and_true]
    have e1 : c.2.1 = x := congrArg (·.2.1) h1
    have e2 : c.2.2.length = W := congrArg (·.2.2) h1
    simp [e1, e2]

theorem regroup_length : ∀ (ns : List Nat) (cols : List Col), (regroup ns cols).length = ns.length
  | [], _ => rfl
  | n :: ns, cols => by
    unfold regroup
    rw [List.length_cons, List.length_cons, regroup_length ns]

/-- **Columns that are those read, laid into groups and flat again: the trees open at them, and none
is left.** key: under which key the columns came: it plays no part. -/
theorem opens_of_cols (a : StSh) (b : Ground.Sh.BookSh) (ft logN : Nat) (poss : List Nat)
    (hr : ∀ q ∈ poss, q < 2 ^ logN) (key : Nat → Nat) :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)) (got : List Col),
      readsOfS b ft ts = some rd → treesShapeB a b logN ts = true →
      got.map (fun c => (c.1, c.2.1, c.2.2.length)) =
        (rd.map fun r =>
          (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x => (key r.1, x, r.2.2)).flatMap id →
      allOpenB a b ft (Positions.ofDraws logN poss) ts
          ((rd.zip (regroup ((rd.map fun r =>
            (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x =>
              (key r.1, x, r.2.2)).map (·.length)) got)).flatMap
            fun x => x.2.map fun c => (x.1.1, c.1, c.2)) = true ∧
        leftAfterS (Positions.ofDraws logN poss) b ts
          ((rd.zip (regroup ((rd.map fun r =>
            (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x =>
              (key r.1, x, r.2.2)).map (·.length)) got)).flatMap
            fun x => x.2.map fun c => (x.1.1, c.1, c.2)) = []
  | [], rd, got, h1, _, _ => by
    obtain rfl : [] = rd := Option.some.inj h1
    exact ⟨rfl, rfl⟩
  | t :: ts, rd, got, h1, h2, h3 => by
    unfold readsOfS at h1
    obtain ⟨r, hr1, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨rd', hrd, rfl⟩ := Option.map_eq_some_iff.1 h1
    unfold readOfS at hr1
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hr1
    unfold treesShapeB at h2
    rw [List.all_cons, Bool.and_eq_true, hT] at h2
    obtain ⟨h2a, h2b⟩ := h2
    have hown := ownAtS_of (b := b) (t := t) hT hr
    simp only [List.map_cons, List.flatMap_cons, id, List.length_map] at h3 ⊢
    generalize hO : Fmt.listOf (poss.map (· % 2 ^ T.shape.logN)) = own at hown h3 ⊢
    have hlen : (own.map fun x =>
        (key (T.number - ft), x, T.shape.mainWidth + T.shape.maskWidth)).length = own.length :=
      List.length_map _
    have g1 : (got.take own.length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
        own.map fun x => (key (T.number - ft), x, T.shape.mainWidth + T.shape.maskWidth) := by
      rw [List.map_take, h3, List.take_left' hlen]
    have g2 : (got.drop own.length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
        (rd'.map fun r =>
          (Fmt.listOf (poss.map (· % 2 ^ r.2.1))).map fun x => (key r.1, x, r.2.2)).flatMap id := by
      rw [List.map_drop, h3, List.drop_left' hlen]
    have gl : (got.take own.length).length = own.length := by
      have := congrArg List.length g1
      rwa [List.length_map, List.length_map] at this
    obtain ⟨i1, i2⟩ := opens_of_cols a b ft logN poss hr key ts rd' (got.drop own.length) hrd h2b g2
    simp only [List.map_map] at i1 i2
    unfold regroup
    rw [List.zip_cons_cons, List.flatMap_cons]
    simp only [List.map_map]
    have hc : ((got.take own.length).map
        ((fun c : Nat × List UInt64 => (T.number - ft, c.1, c.2)) ∘ fun c : Col =>
          (c.2.1, c.2.2))).length = own.length := by rw [List.length_map, gl]
    have hs : (ownAtS (Positions.ofDraws logN poss) b t).size = own.length := by
      rw [hown, List.size_toArray]
    refine ⟨?_, ?_⟩
    · unfold allOpenB
      rw [hT, hs, List.take_left' hc, List.drop_left' hc, hown, Bool.and_eq_true]
      refine ⟨?_, i1⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2a ⊢
      refine ⟨⟨h2a, ?_⟩, colsStand_of _ _ _ _ _ g1⟩
      rw [List.length_append, hc]
      exact Nat.le_add_right _ _
    · unfold leftAfterS
      rw [hs, List.drop_left' hc]
      exact i2

/-! ## 4 Rounds and columns that fit -/

/-- What the kind's declared rounds read. -/
theorem groups_k2 (p : P2) (ft : Nat) (D₁ D₂ : Fmt.Drawn) :
    groupsOf ft (First.K2.rounds p) [D₁, D₂] =
      p.read.map fun r =>
        (Fmt.listOf (D₂.poss.map (· % 2 ^ r.2.1))).map fun x =>
          (p.firstTree + r.1 - ft, x, r.2.2) := by
  simp [groupsOf, First.K2.rounds, List.map_map, Function.comp_def]

/-- **Rounds and columns that fit meet the test on rounds and columns**, under the further test on
the plan and the shape, and where factorV accepts. -/
theorem linkR_of_fits {p : P2} {x : ChainF} {ft : Nat} {R₁ R₂ : Fmt.RoundView} {cols : List Col}
    (hf : roundsFit (First.K2.rounds p) [R₁, R₂] = true)
    (hc : (cols.take ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id).length).map
        (fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id)
    (hP : linkP p x = true) (hz : factorV p x (noDigest R₁) = true) :
    linkR p x (noDigest R₁) (noDigest R₂)
      (regroup ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).map (·.length))
        (cols.take ((groupsOf ft (First.K2.rounds p) [R₁.drawn, R₂.drawn]).flatMap id).length)) =
      true := by
  obtain ⟨_, _, e, a1, a2, a3, a4, b1, b2, b3, b4, b5⟩ := k2_fit hf
  obtain ⟨rfl, rfl⟩ : R₁ = _ ∧ R₂ = _ := by
    have := List.cons.inj e
    exact ⟨this.1, (List.cons.inj this.2).1⟩
  unfold linkP at hP
  unfold factorV at hz
  unfold linkR
  split at hP
  · rename_i Q c e2 e5
    rw [e2] at hz
    rw [e2, e5]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hP
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hP
    rw [groups_k2] at hc ⊢
    have hr : ∀ q ∈ R₂.drawn.poss, q < 2 ^ c.logN := p3 ▸ b5
    obtain ⟨o1, o2⟩ := opens_of_cols _ _ p.firstTree c.logN R₂.drawn.poss hr
      (fun k => p.firstTree + k - ft) _ p.read _ p6 p5 hc
    have hv : R₂.vals.length = p.answers := by
      have := congrArg List.length b1
      rwa [List.length_map, List.length_replicate] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b5, ?_⟩, ?_⟩, a1⟩, a3⟩, a4⟩, hz⟩, ?_⟩, ?_⟩, o1⟩, o2⟩, ?_⟩, ?_⟩
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
    · rw [regroup_length, List.length_map, List.length_map]
    · unfold inRangeB
      rw [List.all_eq_true]
      intro v hv'
      have hm : v ∈ listOfT R₂.drawn.poss := by simpa [Positions.ofDraws] using hv'
      rw [listOfT_eq] at hm
      have hq := hr v ((Fmt.listOf_mem _ _).1 hm)
      have eg : ((withGroupS x.1.core.st x.1.check.frame.shape.code
          x.1.check.frame.shape.maskCode).codes.base.getD x.1.check.frame.rows.code default) =
          c := by
        show x.1.core.st.codes.base.getD x.1.check.frame.rows.code default = c
        rw [Array.getD_eq_getD_getElem?, e5]
        rfl
      rw [eg]
      exact decide_eq_true hq
  · cases hP

/-- **The same at a block with the kind's declared rounds.** -/
theorem linkR_of_Fits {Cl : Type} {blk : Block S Cl} {p : P2} {x : ChainF} {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hP : linkP p x = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧ (factorV p x (noDigest R₁) = true →
      linkR p x (noDigest R₁) (noDigest R₂) (blk.shown ft rs cols) = true) := by
  obtain ⟨h1, h2⟩ := hF
  rw [hb] at h1
  obtain ⟨R₁, R₂, rfl, -⟩ := k2_fit h1
  refine ⟨R₁, R₂, rfl, fun hz => ?_⟩
  unfold Block.want at h2
  unfold Block.shown Block.want
  rw [hb] at h2 ⊢
  exact linkR_of_fits h1 (beq_iff_eq.1 h2) hP hz

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.answersIn_len
#print axioms VerifiableInference.Desc.First.Shape.k2_fit
#print axioms VerifiableInference.Desc.First.Shape.ownAtS_of
#print axioms VerifiableInference.Desc.First.Shape.colsStand_of
#print axioms VerifiableInference.Desc.First.Shape.regroup_length
#print axioms VerifiableInference.Desc.First.Shape.opens_of_cols
#print axioms VerifiableInference.Desc.First.Shape.groups_k2
#print axioms VerifiableInference.Desc.First.Shape.linkR_of_fits
#print axioms VerifiableInference.Desc.First.Shape.linkR_of_Fits
