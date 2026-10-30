-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/OnShape.lean: THE CLOSING OF A SEGMENT (K10): THOSE OF ITS GUARDS THAT
READ NO ROW's SUMMAND, AND ITS TURN OF THE STATEMENT, AS FUNCTIONS OF THE STATEMENT's SHAPE
(`StSh`, Johnson/Desc/Ground/Shape/Core.lean: another author's: what is left of a statement when
every field element, and every row's summands, are left out). Lemmas on the verifier's own text;
no honest side's frame in them; none of the library's goals.

NO TYPE OF A SHAPE IS LAID HERE. OVER `StSh`, NOT OVER THAT AUTHOR's `CoreSh` (statement, book,
roots): the kind's own record holds no book and no count of roots; `closeS_ground` is the tie:
where the turn yields, it is, on `CoreSh`, that author's two routines in a row, and book and roots
stay (one way: the two routines ask fewer guards). OF THE FRAME seven fields are read, none of
which holds a field element: shape (its two codes' numbers; the link's shape), groups (the link's
group: its k and h), next, link, moment, group, mask. SIX NUMBERS off these are the arguments of
`closeG` and `closeS` (code, maskCode, k, h, the group's number g, the mask's number m); the rest
stand as tests on the frame beside `closeG` (`closeShapeB_eq`) and as premises (`close_returnsS`).
"Nothing is owed" is of the record, not of the frame.

  `foldShapeFitsS`, `foldMaskFitsS`   the verifier's two tests on a fold's shape and on its fresh
                   mask (`Own.foldShapeFits`, `Own.foldMaskFits`, Johnson/Desc/Own/Fold.lean), off
                   the shape; with `foldShapeFitsS_eq`, `foldMaskFitsS_eq`
  `begun_sh`, `spentS`, `spent_sh`   the shapes of the statement behind the beginning of a test,
                   and behind the spending of a mask
  `closeG`       THE GUARDS ON THE STATEMENT's SHAPE: that author's `beginRunG`, `runCountS`,
                   `layoutS`, `spendG`, and the two above
  `closeS`       THE TURN: the shape behind, where the guards say yes; `closeS_isSome`;
                   `closeS_ground`
  `closeShapeB_eq`   the first test of Johnson/Desc/K10/Honest/Split.lean (`closeShapeB`) IS:
                   nothing is owed; the frame names the link's shape, the link's group and a mask;
                   the closing is due; and `closeG` of the statement's shape
  `close_carries`    each yes of the decision: `closeS` at the shape in front yields the shape
                   behind
  `close_returnsS`   where nothing is owed, the frame names these three, the closing is due,
                   `closeS` yields at the shape in front, the rounds have the kind's number and
                   shape, AND THE NAMED TEST `closeValsB` (the batching returns; the batched row
                   fits) says yes: the decision returns
  `Toy.turn_yields`, `Toy.turn_refuses`, `Toy.turn_once`, `Toy.turn_is`   Lean's kernel runs
                   guards and turn at a small shape

Limits. `closeValsB` reads the rows' summands and what "BAT" drew: it is no function of the shape.
WHAT A CALLER WHO WANTS THE WHOLE STATE's SHAPE WILL MISS HERE. (1) THE FRAME's SINGLE ROWS, which
the closing lays: of their shape nothing is said. From Johnson/Desc/K10/Honest/Returns.lean's
`rows_shape` six things could be had off the arguments and the shape in front (the two codes'
numbers, the layout, two masks, the fresh mask's number, the number of kept rows); the k
challenges and the lengths of the two vectors on the mask tables:
Johnson/Desc/K10/Honest/Rows.lean (`rows_make`), from the yes alone, over the library's two laws
on these lengths (First/Close/Law/CarriedRows.lean); beside it, not called, the library's
`closing_inv2` (Whole.lean); the make of the form on the main table and of the kept forms hangs on
the batched row (`forms_behind`, AtMakes.lean), so on the open and sample rows' forms, which
`StSh` leaves out on purpose. (2) The frame's other fields' and "owed"'s turn: `CloseKeeps`
(Johnson/Desc/K10/Honest/Keeps.lean), an equation. (3) The lift to the first chain's state:
`K10Turns`, same file. (4) The step: Step.lean, AtS.lean; that rounds which fit the block have the
kind's number and shape (the way back from `roundsFit`): Johnson/Desc/K10/Honest/Fits.lean. (5)
The whole at the shape of the first chain's state: Johnson/Desc/K10/Honest/AtChain.lean, under one
named premise; that premise paid: AtMakes.lean; the step on the pair of shape and makes:
AtPair.lean. Of the block's decision at the kind's own record. EVALUATED AT ONE SMALL SHAPE:
h = 0, no kept member, no sample row. It stands over two files of another author's
(Johnson/Desc/Ground/Shape/Core.lean, Ground.lean),
and over files of this folder. AtChain.lean, AtMakes.lean and
AtPair.lean STAND OVER THIS FILE AND OVER OTHER AUTHORS' FILES: a tree may hold this file without
them: what this head says of them is then said of no file of that tree. Nothing on soundness,
completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Split
import Johnson.Desc.K10.Honest.Keeps
import Johnson.Desc.Ground.Shape.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.Ground.Sh

/-- The verifier's test that a fold's shape fits the statement, off the statement's shape. -/
def foldShapeFitsS (a : StSh) (F : FoldShape) : Bool :=
  let L := F.layout
  let n := L.members.size
  match a.codes.base[F.code]?, a.codes.mask[F.maskCode]? with
  | some c, some zk =>
    decide (1 ≤ L.k) &&
    decide (L.h ≤ L.k) &&
    decide (zk.logN ≤ c.logN) &&
    decide (2 * L.k + 1 - L.h ≤ zk.ell) &&
    L.kept.size == n && L.mainFirst.size == n && L.maskFirst.size == n &&
    ((List.range n).all fun i =>
      match a.oracles[L.members.getD i noId]? with
      | none => false
      | some x =>
        let o := x.shape
        let folded := decide (0 < o.mainRows) && !L.kept.getD i false
        (o.mainRows == 0 || o.code == F.code) &&
        (o.maskRows == 0 || o.maskCode == F.maskCode) &&
        (match L.mainFirst.getD i none with
          | some f => folded && decide (f + o.mainRows ≤ 2 ^ L.k)
          | none => !folded) &&
        (match L.maskFirst.getD i none with
          | some f => decide (0 < o.maskRows) && decide (f + o.maskRows ≤ 2 ^ L.h)
          | none => o.maskRows == 0)) &&
    ((List.range n).any fun i =>
      match a.oracles[L.members.getD i noId]? with
      | none => false
      | some x => decide (0 < x.shape.mainRows) && !L.kept.getD i false)
  | _, _ => false

theorem foldShapeFitsS_eq (S : Statement) (F : FoldShape) :
    foldShapeFitsS (stSh S) F = Own.foldShapeFits S F := by
  unfold foldShapeFitsS Own.foldShapeFits
  simp only [orc_get]
  show (match S.codes.base[F.code]?, S.codes.mask[F.maskCode]? with
    | some c, some zk => _
    | _, _ => false) = _
  cases S.codes.base[F.code]? with
  | none => rfl
  | some c =>
    cases S.codes.mask[F.maskCode]? with
    | none => rfl
    | some zk =>
      dsimp only
      congr 1
      · congr 1
        congr 1
        funext i
        cases S.oracles[F.layout.members.getD i noId]? <;> rfl
      · congr 1
        funext i
        cases S.oracles[F.layout.members.getD i noId]? <;> rfl

/-- The verifier's test that an oracle message can be the fold's fresh mask, off the shape. -/
def foldMaskFitsS (a : StSh) (F : FoldShape) (fresh : Nat) : Bool :=
  match a.oracles[fresh]? with
  | none => false
  | some o =>
    o.shape.mainRows == 0 &&
    o.shape.maskRows == 2 ^ F.layout.h &&
    o.shape.maskCode == F.maskCode &&
    !o.sampled &&
    o.shape.answers == 0 &&
    !F.layout.members.contains fresh

theorem foldMaskFitsS_eq (S : Statement) (F : FoldShape) (fresh : Nat) :
    foldMaskFitsS (stSh S) F fresh = Own.foldMaskFits S F fresh := by
  unfold foldMaskFitsS Own.foldMaskFits
  rw [orc_get]
  cases S.oracles[fresh]? <;> rfl

/-- The shape of the statement behind the beginning of a test. -/
theorem begun_sh (S : Statement) (g : Nat) (G : Group) :
    stSh (Slice.begun S g G) = begunS (stSh S) g (grpSh G) := by
  rw [stSh_eq (S := Slice.begun S g G) (Slice.closeLedgers_codes _ _) (closeLedgers_sh _ _)
    (g := modAt (stSh S).groups g fun G => { G with inRun := true, kinds := [] }) (by
      show ((Slice.closeLedgers S G.members.toList).groups.modify g _).toList.map grpSh = _
      rw [Slice.ProxRun.closeLedgers_groups]
      exact map_modify _ _ _ grpSh _ fun _ => rfl)]
  rfl

/-- The statement's shape with a message marked as spent as a mask. -/
def spentS (a : StSh) (m : Nat) : StSh :=
  { a with oracles := modAt a.oracles m fun x => { x with spent := true } }

theorem spent_sh (S : Statement) (m : Nat) : stSh (spent S m) = spentS (stSh S) m :=
  stSh_eq rfl (map_modify _ _ _ orcSh _ fun _ => rfl) rfl

/-- **THE GUARDS ON THE STATEMENT's SHAPE.** code, maskCode: the request's two codes' numbers. k, h:
the two numbers of row variables of the request's group at the link. g: the group's number in the
statement. m: the mask's message. -/
def closeG (P : Par) (code maskCode k h g m : Nat) (a : StSh) : Bool :=
  beginRunG a g &&
  match a.groups[g]? with
  | none => false
  | some G =>
    let F :=
      ioppFoldShape { code := code, maskCode := maskCode, k := k, h := h } (layoutS a G)
    P.rows == runCountS a G &&
    (layoutS a G).k == k && (layoutS a G).h == h &&
    P.k == k &&
    foldShapeFitsS (begunS a g G) F && foldMaskFitsS (begunS a g G) F m &&
    spendG (begunS a g G) m

/-- **THE TURN OF THE STATEMENT's SHAPE**, where the guards say yes. -/
def closeS (P : Par) (code maskCode k h g m : Nat) (a : StSh) : Option StSh :=
  if closeG P code maskCode k h g m a then
    (a.groups[g]?).map fun G => spentS (begunS a g G) m
  else none

/-- The turn yields just where the guards say yes. -/
theorem closeS_isSome (P : Par) (code maskCode k h g m : Nat) (a : StSh) :
    (closeS P code maskCode k h g m a).isSome = closeG P code maskCode k h g m a := by
  unfold closeS
  cases hg : closeG P code maskCode k h g m a with
  | false => rfl
  | true =>
    rw [if_pos rfl]
    unfold closeG at hg
    cases hG : a.groups[g]? with
    | none => rw [hG] at hg; simp at hg
    | some G => rfl

/-- **WHERE THE TURN YIELDS IT IS THE OTHER AUTHOR's TWO ROUTINES IN A ROW**, on the shape of
statement, book and roots: the beginning of a test on the group, then the spending of the mask
(`beginRunS`, `spendS`, Johnson/Desc/Ground/Shape/Ground.lean): book and roots stay. -/
theorem closeS_ground {P : Par} {code maskCode k h g m : Nat} (a : CoreSh) {y : StSh}
    (hS : closeS P code maskCode k h g m a.st = some y) :
    (beginRunS a g).bind (fun z => spendS z.2 m) = some { a with st := y } := by
  unfold closeS at hS
  split at hS
  · rename_i hg
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hS
    unfold closeG at hg
    rw [hG] at hg
    simp only [Bool.and_eq_true] at hg
    unfold beginRunS
    rw [if_pos hg.1, hG]
    show spendS { a with st := begunS a.st g G } m = _
    unfold spendS
    rw [if_pos hg.2.2]
    rfl
  · cases hS

/-- The guards that read no row's summand, at given data, are: nothing owed, the closing is due,
and the guards on the statement's shape. -/
theorem shapeAtB_eq (P : Par) (s : Rec) (D : BaseData)
    (hG : s.st.groups[s.frame.group]? = some D.G) :
    shapeAtB P s D = (s.owed.isNone && decide (s.frame.next = .laterOrClose) &&
      s.frame.moment == reqMoments D.L &&
      closeG P s.frame.shape.code s.frame.shape.maskCode D.Gq.k D.Gq.h s.frame.group D.m
        (stSh s.st)) := by
  unfold shapeAtB closeG
  rw [grp_get, hG, beginRunG_eq]
  show _ = (_ && _ && _ && (_ && (P.rows == runCountS (stSh s.st) (grpSh D.G) &&
    (layoutS (stSh s.st) (grpSh D.G)).k == D.Gq.k &&
    (layoutS (stSh s.st) (grpSh D.G)).h == D.Gq.h &&
    P.k == D.Gq.k &&
    foldShapeFitsS (begunS (stSh s.st) s.frame.group (grpSh D.G)) _ &&
    foldMaskFitsS (begunS (stSh s.st) s.frame.group (grpSh D.G)) _ D.m &&
    spendG (begunS (stSh s.st) s.frame.group (grpSh D.G)) D.m)))
  rw [runCountS_eq, layoutS_eq, ← begun_sh, foldShapeFitsS_eq, foldMaskFitsS_eq, spendG_eq]
  simp only [BaseData.S1, BaseData.F, Bool.and_assoc]

/-- **THE FIRST TEST IS A TEST ON "OWED", ON SEVEN FIELDS OF THE FRAME AND ON THE STATEMENT's
SHAPE.** -/
theorem closeShapeB_eq (P : Par) (s : Rec) :
    closeShapeB P s =
      match s.frame.shape.link[s.frame.link]?, s.frame.groups[s.frame.link]?, s.frame.mask with
      | some L, some Gq, some m =>
        s.owed.isNone && decide (s.frame.next = .laterOrClose) && s.frame.moment == reqMoments L &&
          closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m (stSh s.st)
      | _, _, _ => false := by
  unfold closeShapeB baseData
  cases h1 : s.frame.shape.link[s.frame.link]? with
  | none => rfl
  | some L =>
    cases h2 : s.frame.groups[s.frame.link]? with
    | none => rfl
    | some Gq =>
      cases h3 : s.frame.mask with
      | none => rfl
      | some m =>
        cases h4 : s.st.groups[s.frame.group]? with
        | none =>
          show false = _
          have : closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m
              (stSh s.st) = false := by
            unfold closeG
            rw [grp_get, h4]
            simp
          show false = (_ && _ && _ && closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h
            s.frame.group m (stSh s.st))
          rw [this, Bool.and_false]
        | some G => exact shapeAtB_eq P s ⟨L, Gq, m, G⟩ h4

/-- **EACH YES OF THE DECISION CARRIES THE SHAPE**: the turn at the shape in front yields the
shape behind. -/
theorem close_carries {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ Gq m, s.frame.groups[s.frame.link]? = some Gq ∧ s.frame.mask = some m ∧
      closeS P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m (stSh s.st) =
        some (stSh s'.st) := by
  have hy := ((close_yes_split (Cl := Cl) P s rs gs).1 ⟨s', h⟩).2.2.1
  obtain ⟨L, Gq, G, m, rows, _, k2, k3, _, _, k6, k7, _, _, rfl⟩ := close_keeps h
  rw [closeShapeB_eq, k2, k3, k6] at hy
  have hg : closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m
      (stSh s.st) =
      true := by
    simp only [Bool.and_eq_true] at hy
    exact hy.2
  refine ⟨Gq, m, k3, k6, ?_⟩
  unfold closeS
  rw [if_pos hg, grp_get, k7]
  show some (spentS (begunS (stSh s.st) s.frame.group (grpSh G)) m) = _
  rw [← begun_sh, ← spent_sh]

/-- **WHERE THE TURN YIELDS, THE DECISION RETURNS**, under what is left: nothing owed; the frame
names the link's shape, the link's group and a mask; the closing is due; the rounds have the
kind's number and shape; and THE NAMED TEST `closeValsB`. -/
theorem close_returnsS {Cl : Type} {P : Par} {s : Rec} {L : Params.ReqLink} {Gq : ReqGroup}
    {m : Nat} {y : StSh} (h0 : s.owed = none) (h1 : s.frame.shape.link[s.frame.link]? = some L)
    (h2 : s.frame.groups[s.frame.link]? = some Gq) (h3 : s.frame.mask = some m)
    (h4 : s.frame.next = .laterOrClose) (h5 : s.frame.moment = reqMoments L)
    (hS : closeS P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m (stSh s.st) =
      some y)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) (hv : closeValsB s rs = true) :
    ∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s' := by
  refine (close_yes_split P s rs gs).2 ⟨hl, hs, ?_, hv⟩
  rw [closeShapeB_eq, h1, h2, h3]
  have hg : closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m
      (stSh s.st) =
      true := by
    unfold closeS at hS
    split at hS
    · assumption
    · cases hS
  show (s.owed.isNone && decide (s.frame.next = .laterOrClose) && s.frame.moment == reqMoments L &&
    closeG P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m (stSh s.st)) = true
  rw [hg, h0, h4, h5]
  simp

namespace Toy

/-- The turn at a place's parameters, at the shape of the small record of
Johnson/Desc/K10/Honest/FrontToy.lean, with what its frame names. -/
def turnAt (P : Par) : Option StSh :=
  s.frame.mask.bind fun m => (s.frame.groups[s.frame.link]?).bind fun Gq =>
    closeS P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m (stSh s.st)

/-- The turn once more, at a shape. -/
def turnFrom (a : StSh) : Option StSh :=
  s.frame.mask.bind fun m => (s.frame.groups[s.frame.link]?).bind fun Gq =>
    closeS P s.frame.shape.code s.frame.shape.maskCode Gq.k Gq.h s.frame.group m a

/-- LEAN's KERNEL RUNS THE GUARDS AND THE TURN ON THE SHAPE: they yield at the toy's parameters. -/
theorem turn_yields : (turnAt P).isSome = true := by decide +kernel

/-- They yield nothing at another count of rows, and at another number of rounds. -/
theorem turn_refuses : (turnAt { P with rows := 3 }).isSome = false ∧
    (turnAt { P with k := 1 }).isSome = false := by decide +kernel

/-- A REFUSAL THAT HANGS ON THE SHAPE (with `turn_yields`, which says that there is such a shape):
at the shape that the turn yields the turn yields nothing. Several clauses refuse there together:
the group is under test, it has no row left, the mask is spent. -/
theorem turn_once : (turnAt P).bind turnFrom = none := by decide +kernel

/-- What the turn yields is the shape of the statement behind each yes of the decision. -/
theorem turn_is (rs : List Fmt.RoundView) (s' : Rec)
    (h : ((kind (Cl := Unit)) P).decide s rs [] = .ok s') : turnAt P = some (stSh s'.st) := by
  obtain ⟨Gq, m, h1, h2, h3⟩ := close_carries h
  unfold turnAt
  rw [h2, h1]
  exact h3

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.Toy.turn_yields
#print axioms ProofFile.Honest.K10.YesFree.Toy.turn_refuses
#print axioms ProofFile.Honest.K10.YesFree.Toy.turn_once
#print axioms ProofFile.Honest.K10.YesFree.Toy.turn_is
#print axioms ProofFile.Honest.K10.YesFree.closeS_isSome
#print axioms ProofFile.Honest.K10.YesFree.closeS_ground
#print axioms ProofFile.Honest.K10.YesFree.closeShapeB_eq
#print axioms ProofFile.Honest.K10.YesFree.close_carries
#print axioms ProofFile.Honest.K10.YesFree.close_returnsS
#print axioms ProofFile.Honest.K10.YesFree.foldShapeFitsS_eq
#print axioms ProofFile.Honest.K10.YesFree.foldMaskFitsS_eq
