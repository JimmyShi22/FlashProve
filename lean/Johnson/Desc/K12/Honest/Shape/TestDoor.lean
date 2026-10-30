-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestDoor.lean: the door of a proximity test from the shape: the
front, the batching, the frame's question and the first fold of the description's own block
(`guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) accept in a row where one Bool on the shape of the
structure in front (`doorB`, on `TestSh`, Johnson/Desc/K12/Honest/Shape/Test.lean) is true, beside
four premises that are named below. Both cases of the first fold's mask. No prover, no coin, no
frame for an honest side.

  1  `frontLS`, `frontLS_eq`   the front's nineteen clauses on the shape are the library's list.
  2  `gpOkS_eq`, `labelsOkS_eq`   the guard on the group's trees and the one on their numbers, on
      the shape, are the library's `gpOk` and `labelsOk` (Johnson/Desc/K12/Law/FirstOk.lean,
      FirstCut.lean), also where the guard lets the mask come in by a receiving (`entered_some`,
      `entered_none`).
  3  `testFront_of`, `testFrontOwn_of`, `batOwes_of`, `frontOwes_of`   Bools on the shape give the
      premises of the laws on the door (Johnson/Prover/Link/FormFirst.lean, FormBat.lean,
      FormDoor.lean; Johnson/Desc/K12/Honest/OwnFoldFirst.lean).
  4  `doorB`, `door_of_shape`, `door_of_shape_own`   the door.

The four premises beside the Bool.
  · the first mark beside the shape: the statement is tidy (`stTidyB`,
    Johnson/Desc/Ground/Shape/Marks.lean). Of it the order of the statement alone is used. Its
    reader reads values at one spot, over the whole statement (a written-out variable's pair in a
    whole coefficient vector; Marks.lean says which): that is idle only where no row of any group
    has such a factor in such a vector.
  · the rows that the test takes in are plain (`PlainRow`): asked of these rows alone, not of the
    whole statement; `runRows_plain` gives it from the second mark. It fails at a test that takes
    in a row with a written-out factor (Marks.lean says where such rows are laid): of such a test
    these laws say nothing. `TestFront` (FormFirst.lean), which `testFront_of` concludes, asks less
    of these rows: that they are dense (`DenseRow`, OnBytes/Slice/BlkProxDense.lean); so that
    law's premise on the rows is stronger than its conclusion's clause. `TestFrontOwn` asks plain
    rows.
  · `claimsB t`: a named test on values: each row that lies open on the group passes all clauses of
    the adding once more, at the statement as it is. Three of these clauses read values.
  · the view's form: the batching's and the fold's rounds are of the declared form (`roundsFit`),
    and the declared rounds are cut as the frame cuts them (`batCut`, `foldCut` or `foldCutOwn`:
    tests on the plan).
  The first two have no field in `TestSh`: whoever cuts a block's decision into a function of a
  shape and named tests on values lays them beside the shape, as marks that are carried, or among
  the tests.
  The parameters cur, nxt, cutB, cutF, i, n are free in the laws: the caller supplies the plan's
  own.

Limits. The door alone: nothing on a switch, on the later stages or on the base case. Sufficient,
not necessary: `commonB` asks what the laws on the door ask (no kept member; at most 63 variables;
the layout's numbers are the stage's), not what the block asks. The laws speak of `decide` alone:
what the block asks of the plan alone (`planOk`) is not here. `batOwesB`, and so `doorB`, asks
`p.early`: both laws on the door stand under "the masks come early", also the one in which the
first fold receives its own mask. That `doorB` is true at a place of a file is an evaluation that
is not made here (small examples: TestDoorToy.lean, which is not in this library). Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.K12.Honest.OwnFoldDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (Clauses on has)

/-! ## 1 The front's nineteen clauses -/

theorem on_map {α β : Type} (x : Option α) (f : α → β) (p : β → Bool) :
    on (x.map f) p = on x fun a => p (f a) := by
  cases x <;> rfl

theorem treeOf (B : TreeBook) (o : Nat) :
    (((bookSh B).place[o]?).bind fun p => (bookSh B).trees[p.1]?) =
      ((B.place[o]?).bind fun p => B.trees[p.1]?).map treeSh := by
  rw [place_get]
  cases B.place[o]? with
  | none => rfl
  | some p => exact tree_get B p.1

/-- The front's clauses, on the shape. -/
def frontLS (c : CoreSh) (g : Nat) (mask : Option Nat) : Clauses :=
  let G := c.st.groups[g]?
  let each (f : Nat → OrcSh → Bool) : Bool :=
    on G fun G => G.members.all fun o => on c.st.oracles[o]? (f o)
  let m := mask.bind fun m => c.st.oracles[m]?
  [("front: the group is there", G.isSome),
   ("front: no test of it has begun", on G (!·.inRun)),
   ("front: a member", on G (!·.members.isEmpty)),
   ("front: as many kept marks as members", on G fun G => G.kept.length == G.members.length),
   ("front: the members rise", on G fun G => (List.range (G.members.length - 1)).all fun i =>
     decide (G.members.getD i 0 < G.members.getD (i + 1) 0)),
   ("front: every member is there", on G fun G =>
     G.members.all fun o => (c.st.oracles[o]?).isSome),
   ("front: every member is sampled", each fun _ y => y.sampled),
   ("front: every member knows the group", each fun _ y => y.groups.contains g),
   ("front: as many sample rows as answers", each fun _ y => y.rows == y.shape.answers),
   ("front: every member's pad is the public one", each fun _ y =>
     match Own.padMade c.st.codes y.shape with
     | none => false
     | some l => y.pad == l.map fun p => (p.part, p.index)),
   ("front: no open claim is a sample row", on G fun G => G.kinds.all fun k => k != .sample),
   ("front: the mask's message is there", mask.isNone || m.isSome),
   ("front: the mask's message is not sampled", on m (!·.sampled)),
   ("front: the mask's message counts no answer", on m (·.shape.answers == 0)),
   ("front: the mask's message is not spent", on m (!·.spent)),
   ("front: the mask's message is no member",
     on G fun G => on mask fun m => !G.members.contains m),
   ("front: statement and book are in step", c.st.oracles.length == c.book.place.length),
   ("front: each tree is in the book", on G fun G => (G.members ++ mask.toList).all fun o =>
     ((c.book.place[o]?).bind fun p => c.book.trees[p.1]?).isSome),
   ("front: a tree that is opened at one list only has not been opened", on G fun G =>
     (G.members ++ mask.toList).all fun o =>
       on ((c.book.place[o]?).bind fun p => c.book.trees[p.1]?) fun t =>
         !t.oneList || t.lists == 0)]

theorem frontLS_eq (S : Statement) (B : TreeBook) (r g : Nat) (mask : Option Nat) :
    frontLS (coreSh ⟨S, B, r⟩) g mask = frontL S B g mask := by
  unfold frontLS frontL coreSh
  dsimp only
  have hm : (mask.bind fun a => Option.map orcSh S.oracles[a]?) =
      (mask.bind fun m => S.oracles[m]?).map orcSh := by
    cases mask <;> rfl
  simp only [grp_get, orc_get, treeOf, hm, on_map, Option.isSome_map, orc_size, place_size]
  simp only [grpSh, orcSh, treeSh, stSh, Array.isEmpty_toList, Array.length_toList, getD_toList,
    Array.all_toList, List.all_map, Array.contains_toList, Function.comp_def]
  rfl

/-! ## 2 The guards on the group's trees -/

open H2K.First (Seat1 seatOf entered opensOf gpOf gpL gpAll gpOk labelsL labelsOk memL apartB oM oZ
  codeB keyAt logAt widthAt numAt)

def seatOfS (c : CoreSh) (id : Nat) : Option Seat1 :=
  (c.st.oracles[id]?).bind fun x => (c.book.place[id]?).bind fun q =>
    (c.book.trees[q.1]?).map fun T => ⟨id, x.shape, q.1, q.2, T.shape, T.number⟩

theorem seatOfS_eq (S : Statement) (B : TreeBook) (r id : Nat) :
    seatOfS (coreSh ⟨S, B, r⟩) id = seatOf S B id := by
  unfold seatOfS seatOf coreSh
  dsimp only
  rw [orc_get, place_get]
  cases S.oracles[id]? with
  | none => rfl
  | some x =>
    cases B.place[id]? with
    | none => rfl
    | some q =>
      show ((bookSh B).trees[q.1]?).map _ = (B.trees[q.1]?).map _
      rw [tree_get]
      cases B.trees[q.1]? <;> rfl

/-- The plain data of the guards, with the book as a shape. -/
structure PlainS where
  codes : Codes
  book : BookSh
  L : GroupLayout
  mems : List Seat1
  fresh : Seat1
  ts : List Nat
  opens : List (Fmt.Shape × Fmt.TreeSource)

def gpOfS (p : P12) (a : ThinSh) (s : Fmt.M1.Stage) (L : GroupLayout) : Option PlainS :=
  (stageAt p 0 s).bind fun cu => (maskThin p (ioppFoldShape cu L) a).bind fun e =>
    (L.members.toList.mapM (seatOfS e.2)).bind fun ms => (seatOfS e.2 e.1).map fun f =>
      ⟨e.2.st.codes, e.2.book, L, ms, f, Fmt.listOf ((ms.map (·.t)) ++ [f.t]), opensOf p s.k⟩

def keyAtS (F : Nat) (b : BookSh) (t : Nat) : Nat := ((b.trees[t]?).map (·.number)).getD 0 - F
def logAtS (b : BookSh) (t : Nat) : Nat := ((b.trees[t]?).map (·.shape.logN)).getD 0
def widthAtS (b : BookSh) (t : Nat) : Nat :=
  ((b.trees[t]?).map fun T => T.shape.mainWidth + T.shape.maskWidth).getD 0
def numAtS (b : BookSh) (t : Nat) : Nat := ((b.trees[t]?).map (·.number)).getD 0

theorem keyAtS_eq (F : Nat) (B : TreeBook) (t : Nat) : keyAtS F (bookSh B) t = keyAt F B t := by
  unfold keyAtS keyAt
  rw [tree_get]
  cases B.trees[t]? <;> rfl

theorem logAtS_eq (B : TreeBook) (t : Nat) : logAtS (bookSh B) t = logAt B t := by
  unfold logAtS logAt
  rw [tree_get]
  cases B.trees[t]? <;> rfl

theorem widthAtS_eq (B : TreeBook) (t : Nat) : widthAtS (bookSh B) t = widthAt B t := by
  unfold widthAtS widthAt
  rw [tree_get]
  cases B.trees[t]? <;> rfl

theorem numAtS_eq (B : TreeBook) (t : Nat) : numAtS (bookSh B) t = numAt B t := by
  unfold numAtS numAt
  rw [tree_get]
  cases B.trees[t]? <;> rfl

/-- The guards' clauses. kept: the number of the claim's kept forms. -/
def gpLS (p : P12) (a : Fmt.M1.Stage) (kept : Nat) (D : PlainS) : H2K.First.Clauses :=
  let K := D.codes
  let F := p.nums.firstTree
  (D.mems.zipIdx.flatMap fun x => memL K a D.L x.2 x.1) ++
  [("apartM", apartB (oM D.L) (·.sh.mainRows) D.mems), ("apartZ",
      apartB (oZ D.L) (·.sh.maskRows) D.mems),
   ("kept", D.L.kept.all (!·)),
   ("sizes", D.L.kept.size == D.L.members.size && D.L.mainFirst.size == D.L.members.size &&
      D.L.maskFirst.size == D.L.members.size),
   ("f:main", D.fresh.sh.mainRows == 0), ("f:mask", D.fresh.sh.maskRows == 2 ^ a.h),
   ("f:short", decide (D.fresh.tsh.logN ≤ a.C.a)), ("f:zshort", decide (a.Z.a ≤ D.fresh.tsh.logN)),
   ("f:codeZ", codeB K.mask[D.fresh.sh.maskCode]? a.Z),
   ("f:no member", !D.L.members.contains D.fresh.id),
   ("opens.n", D.opens.length == D.ts.length),
   ("opens.key", D.opens.map (·.1.tree - F) == D.ts.map (keyAtS F D.book)),
   ("opens.a", D.opens.map (·.1.a) == D.ts.map (logAtS D.book)),
   ("opens.W", D.opens.map (·.1.W) == D.ts.map (widthAtS D.book)),
   ("row.kept", kept == 0)]

/-- What the library's plain data is on shapes. -/
def plainSh (D : H2K.First.Plain) : PlainS :=
  ⟨D.st.codes, bookSh D.book, D.L, D.mems, D.fresh, D.ts, D.opens⟩

theorem gpLS_eq (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : H2K.First.Plain) :
    gpLS p a row.kept.size (plainSh D) = gpL p a row D := by
  unfold gpLS gpL plainSh
  dsimp only
  have e1 : keyAtS p.nums.firstTree (bookSh D.book) = keyAt p.nums.firstTree D.book :=
    funext (keyAtS_eq _ _)
  have e2 : logAtS (bookSh D.book) = logAt D.book := funext (logAtS_eq _)
  have e3 : widthAtS (bookSh D.book) = widthAt D.book := funext (widthAtS_eq _)
  have e4 : (row.kept.size == 0) = row.kept.isEmpty := by
    cases h : row.kept.isEmpty with
    | true => simpa using Array.isEmpty_iff_size_eq_zero.1 h
    | false =>
      cases h2 : (row.kept.size == 0) with
      | false => rfl
      | true =>
        rw [Array.isEmpty_iff_size_eq_zero.2 (by simpa using h2)] at h
        cases h
  rw [e1, e2, e3, e4]

theorem maskThin_came {p : P12} {F : FoldShape} {a : ThinSh} {i : Nat} (h : a.mask = some i) :
    maskThin p F a = some (i, a.core) := by
  unfold maskThin
  rw [h]

theorem maskThin_own {p : P12} {F : FoldShape} {a : ThinSh} (h : a.mask = none) :
    maskThin p F a = (recvS p.nums.firstTree a.core #[foldMaskNotice F]).bind fun x =>
      (x.1[0]?).map fun id => (id, x.2) := by
  unfold maskThin
  rw [h]

/-- The carried state at which the guard lets the mask come in. -/
def dIn (t : T12) : _root_.Desc.Plain.DState Unit := ⟨t.st, t.book, t.roots, [], ()⟩

theorem core_dIn (t : T12) : (thinSh t).core = shD (dIn t) := rfl

theorem entered_some {p : P12} {t : T12} {cu : IoppStage} {L : GroupLayout} {id : Nat}
    {S' : Statement} {B' : TreeBook} (h : entered p t cu L = some (id, S', B')) :
    ∃ r', maskThin p (ioppFoldShape cu L) (thinSh t) = some (id, coreSh ⟨S', B', r'⟩) := by
  unfold entered at h
  cases hm : t.mask with
  | some i0 =>
    rw [hm] at h
    cases h
    exact ⟨t.roots, maskThin_came hm⟩
  | none =>
    rw [hm] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨i0, hi, h⟩ := Option.map_eq_some_iff.1 h
    cases h
    refine ⟨x.2.roots, ?_⟩
    have c := recv_carries p.nums.firstTree (dIn t) x.2 _ x.1 hx
    rw [maskThin_own (a := thinSh t) hm, core_dIn, c, Option.bind_some]
    show (x.1[0]?).map _ = _
    rw [hi]
    rfl

theorem entered_none {p : P12} {t : T12} {cu : IoppStage} {L : GroupLayout}
    (h : entered p t cu L = none) : maskThin p (ioppFoldShape cu L) (thinSh t) = none := by
  unfold entered at h
  cases hm : t.mask with
  | some i0 =>
    rw [hm] at h
    cases h
  | none =>
    rw [hm] at h
    rw [maskThin_own (a := thinSh t) hm, core_dIn]
    cases hr : Ground.recvP p.nums.firstTree (dIn t) #[foldMaskNotice (ioppFoldShape cu L)] with
    | none =>
      cases hs : recvS p.nums.firstTree (shD (dIn t)) #[foldMaskNotice (ioppFoldShape cu L)] with
      | none => rfl
      | some y =>
        obtain ⟨x, hx⟩ := recv_returns p.nums.firstTree (dIn t) _ y hs
        rw [hr] at hx
        cases hx
    | some x =>
      have h' : (Ground.recvP p.nums.firstTree (dIn t)
          #[foldMaskNotice (ioppFoldShape cu L)]).bind (fun x =>
            (x.1[0]?).map fun id => (id, x.2.st, x.2.book)) = none := h
      rw [hr, Option.bind_some] at h'
      rw [recv_carries p.nums.firstTree (dIn t) x.2 _ x.1 hr, Option.bind_some]
      show (x.1[0]?).map _ = none
      cases hi : x.1[0]? with
      | none => rfl
      | some i0 =>
        rw [hi] at h'
        cases h'

theorem gpOfS_eq (p : P12) (t : T12) (s : Fmt.M1.Stage) (L : GroupLayout) :
    gpOfS p (thinSh t) s L = (gpOf p t s L).map plainSh := by
  unfold gpOfS gpOf
  cases stageAt p 0 s with
  | none => rfl
  | some cu =>
    rw [Option.bind_some, Option.bind_some]
    cases he : entered p t cu L with
    | none =>
      rw [entered_none he]
      rfl
    | some e =>
      obtain ⟨id, S', B'⟩ := e
      obtain ⟨r', hr'⟩ := entered_some he
      rw [hr', Option.bind_some, Option.bind_some]
      have ef : seatOfS (coreSh ⟨S', B', r'⟩) = seatOf S' B' := funext (seatOfS_eq S' B' r')
      dsimp only
      rw [ef]
      cases L.members.toList.mapM (seatOf S' B') with
      | none => rfl
      | some ms =>
        rw [Option.bind_some, Option.bind_some]
        cases seatOf S' B' id <;> rfl

/-- The thin shape off the rich one. -/
def thinOf (a : TestSh) : ThinSh :=
  ⟨a.core, a.g,
    match a.pass with
    | .nothing => .nothing
    | .claim c => .claim c.lay
    | .single r n =>
      .single (if r.masks == 2 then r.lay.members.push r.fresh else r.lay.members).toList n
    | .switched _ _ => .switched,
    a.mask⟩

theorem thinOf_eq (t : T12) : thinOf (testSh t) = thinSh t := by
  unfold thinOf testSh thinSh
  cases t.pass <;> rfl

def gpAllS (p : P12) (a : TestSh) : H2K.First.Clauses :=
  match p.nums.stages, a.pass with
  | s :: _, .claim c =>
    match gpOfS p (thinOf a) s c.lay with
    | some D => gpLS p s c.kept D
    | none => [("the plain data cannot be made: a member, the mask, a place or a tree is lacking",
        false)]
  | _, _ => [("no stage, or no claim passes", false)]

/-- **The guard on the group's trees, on the shape.** -/
def gpOkS (p : P12) (a : TestSh) : Bool := H2K.First.ok (gpAllS p a)

theorem gpOkS_eq (p : P12) (t : T12) : gpOkS p (testSh t) = gpOk p t := by
  unfold gpOkS gpOk gpAllS gpAll
  rw [thinOf_eq]
  cases p.nums.stages with
  | nil => rfl
  | cons s l =>
    have e : (testSh t).pass = passSh t.pass := rfl
    rw [e]
    cases ht : t.pass with
    | claim row L =>
      show H2K.First.ok (match gpOfS p (thinSh t) s L with
        | some D => gpLS p s row.kept.size D
        | none =>
          [("the plain data cannot be made: a member, the mask, a place or a tree is lacking",
            false)]) =
        H2K.First.ok (match gpOf p t s L with
        | some D => gpL p s row D
        | none =>
          [("the plain data cannot be made: a member, the mask, a place or a tree is lacking",
            false)])
      rw [gpOfS_eq]
      cases gpOf p t s L with
      | none => rfl
      | some D =>
        show H2K.First.ok (gpLS p s row.kept.size (plainSh D)) = _
        rw [gpLS_eq]
    | _ => rfl

def labelsLS (p : P12) (a : TestSh) : H2K.First.Clauses :=
  match p.nums.stages, a.pass with
  | s :: _, .claim c =>
    match gpOfS p (thinOf a) s c.lay with
    | some D => [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAtS D.book))]
    | none => [("the plain data cannot be made", false)]
  | _, _ => [("no stage, or no claim passes", false)]

def labelsOkS (p : P12) (a : TestSh) : Bool := H2K.First.ok (labelsLS p a)

theorem labelsOkS_eq (p : P12) (t : T12) : labelsOkS p (testSh t) = labelsOk p t := by
  unfold labelsOkS labelsOk labelsLS labelsL
  rw [thinOf_eq]
  cases p.nums.stages with
  | nil => rfl
  | cons s l =>
    have e : (testSh t).pass = passSh t.pass := rfl
    rw [e]
    cases ht : t.pass with
    | claim row L =>
      show H2K.First.ok (match gpOfS p (thinSh t) s L with
        | some D => [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAtS D.book))]
        | none => [("the plain data cannot be made", false)]) =
        H2K.First.ok (match gpOf p t s L with
        | some D => [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAt D.book))]
        | none => [("the plain data cannot be made", false)])
      rw [gpOfS_eq]
      cases gpOf p t s L with
      | none => rfl
      | some D =>
        show H2K.First.ok [("opens.tree",
          D.opens.map (·.1.tree) == D.ts.map (numAtS (bookSh D.book)))] = _
        rw [show numAtS (bookSh D.book) = numAt D.book from funext (numAtS_eq _)]
    | _ => rfl

/-! ## 3 What stands in front of the door, read off the shape -/

open Johnson.Prover.Link (TestFront BatOwes FrontOwes batT layoutOf_own)
open ProofFile.Honest.K12 (TestFrontOwn)

theorem runRows_plain {S : Statement} (hp : stPlainB S = true) {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) : ∀ r ∈ (runRows S G).toList, PlainRow r := by
  intro r hr
  unfold runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  rcases hr with (c | c) | c
  · exact plain_rows hp hG r c.1
  · rw [← Array.foldl_toList] at c
    rcases mem_samples S r _ _ c with c' | ⟨o, _, x, hx, hr''⟩
    · simp at c'
    · exact plain_samples hp hx r hr''
  · exact plain_rows hp hG r c.1

/-- The clauses that both cases of the first fold's mask share. -/
def commonB (p : P12) (cur nxt : Fmt.M1.Stage) (c : CoreSh) (g : Nat) (i n : Nat × Nat) : Bool :=
  has c.st.groups[g]? fun G =>
    decide (p.idx[0]? = some i) && decide (p.idx[1]? = some n) && decide (G.code = i.1) &&
    decide (G.maskCode = i.2) &&
    decide (c.st.codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩) &&
    decide (c.st.codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩) &&
    decide (c.st.codes.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩) &&
    decide (c.st.codes.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩) &&
    decide ((layoutS c.st G).k = cur.k) && decide ((layoutS c.st G).h = cur.h) &&
    (G.members.any fun o => (c.st.oracles[o]?).any fun x => decide (0 < x.shape.mainRows)) &&
    G.kept.all (!·) && K12.stageOk false cur && decide (nxt.Z.a ≤ nxt.C.a) &&
    decide (cur.k + ceilLog2 cur.C.l ≤ 63)

/-- The mask has come: its message can be the fold's fresh mask. -/
def cameB (cur : Fmt.M1.Stage) (c : CoreSh) (g : Nat) (i : Nat × Nat) (id : Nat) : Bool :=
  has c.st.groups[g]? fun G => has c.st.oracles[id]? fun o =>
    decide (o.shape.mainRows = 0) && decide (o.shape.maskRows = 2 ^ cur.h) &&
    decide (o.shape.maskCode = i.2) && !o.sampled && decide (o.shape.answers = 0) && !o.spent &&
    !G.members.contains id

structure Common (p : P12) (cur nxt : Fmt.M1.Stage) (t : T12) (G : Group) (i n : Nat × Nat) :
    Prop where
  group : t.st.groups[t.g]? = some G
  idx0 : p.idx[0]? = some i
  idx1 : p.idx[1]? = some n
  code : G.code = i.1
  maskCode : G.maskCode = i.2
  base : t.st.codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩
  maskC : t.st.codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩
  base1 : t.st.codes.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩
  mask1 : t.st.codes.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩
  layK : (layoutOf t.st G).k = cur.k
  layH : (layoutOf t.st G).h = cur.h
  main : ∃ j < G.members.size, ∃ x, t.st.oracles[G.members.getD j noId]? = some x ∧
    0 < x.shape.mainRows
  noKept : ∀ j, G.kept.getD j false = false
  stage : K12.stageOk false cur = true
  stage1 : nxt.Z.a ≤ nxt.C.a
  vars : cur.k + ceilLog2 cur.C.l ≤ 63

theorem common_of {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat}
    (h : commonB p cur nxt (testSh t).core t.g i n = true) : ∃ G, Common p cur nxt t G i n := by
  unfold commonB at h
  have e : (testSh t).core.st = stSh t.st := rfl
  rw [e, grp_get] at h
  cases hG : t.st.groups[t.g]? with
  | none =>
    rw [hG] at h
    cases h
  | some G =>
    rw [hG] at h
    simp only [has, Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
      a15⟩ := h
    rw [layoutS_eq, layoutOf_own hG] at a9 a10
    refine ⟨G, hG, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_, ?_, a13, a14, a15⟩
    · obtain ⟨o, ho, hx⟩ := List.any_eq_true.1 a11
      rw [orc_get] at hx
      have ho' : o ∈ G.members.toList := ho
      obtain ⟨j, hj, ej⟩ := List.getElem_of_mem ho'
      have hj' : j < G.members.size := by simpa using hj
      refine ⟨j, hj', ?_⟩
      have eg : G.members.getD j noId = o := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj']
        simpa using ej
      rw [eg]
      cases hxo : t.st.oracles[o]? with
      | none =>
        rw [hxo] at hx
        cases hx
      | some x =>
        rw [hxo] at hx
        exact ⟨x, rfl, by simpa [orcSh] using hx⟩
    · intro j
      have a12' : ∀ b ∈ G.kept.toList, (!b) = true := List.all_eq_true.1 a12
      rw [Array.getD_eq_getD_getElem?]
      cases hk : G.kept[j]? with
      | none => rfl
      | some b =>
        obtain ⟨hj, eb⟩ := Array.getElem?_eq_some_iff.1 hk
        have := a12' b (eb ▸ Array.getElem_mem_toList hj)
        simpa using this

theorem testFrontOwn_of {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat}
    (h : commonB p cur nxt (testSh t).core t.g i n = true) (hm : t.mask = none)
    (hs : (testSh t).core.st.oracles.length = (testSh t).core.book.place.length)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r) :
    ∃ G, TestFrontOwn p cur nxt t G i n := by
  obtain ⟨G, C⟩ := common_of h
  have hs' : (stSh t.st).oracles.length = (bookSh t.book).place.length := hs
  rw [orc_size, place_size] at hs'
  exact ⟨G, C.group, (tidy_of ht).inOrder, hp G C.group, C.idx0, C.idx1, C.code,
    C.maskCode, C.base, C.maskC, C.base1, C.mask1, C.layK, C.layH, C.main, C.noKept, hm, hs',
    C.stage, C.stage1, C.vars⟩

theorem testFront_of {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat} {id : Nat}
    (h : commonB p cur nxt (testSh t).core t.g i n = true) (hm : t.mask = some id)
    (hc : cameB cur (testSh t).core t.g i id = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r) :
    ∃ G, TestFront p cur nxt t G i n id := by
  obtain ⟨G, C⟩ := common_of h
  unfold cameB at hc
  have e : (testSh t).core.st = stSh t.st := rfl
  rw [e, grp_get, orc_get, C.group] at hc
  cases ho : t.st.oracles[id]? with
  | none =>
    rw [ho] at hc
    cases hc
  | some o =>
    rw [ho] at hc
    simp only [has, Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hc
    have b7' : id ∉ G.members := by
      intro hmem
      have : G.members.toList.contains id = true := by
        rw [Array.contains_toList]
        exact Array.contains_iff_mem.2 hmem
      rw [show (grpSh G).members = G.members.toList from rfl, this] at b7
      cases b7
    exact ⟨G, C.group, (tidy_of ht).inOrder,
      fun r hr => OnBytes.Slice.ProxRun.denseRow_of_plain (hp G C.group r hr), C.idx0, C.idx1,
      C.code, C.maskCode, C.base, C.maskC, C.base1, C.mask1, C.layK, C.layH, C.main, C.noKept, hm,
      ⟨o, ho, b1, b2, b3, b4, b5, b6, b7'⟩, C.stage, C.stage1, C.vars⟩

/-- The guard on the group's trees reads of the claim its layout and the number of kept forms. -/
theorem gpOkS_claim (p : P12) (c : CoreSh) (g : Nat) (m : Option Nat) (a b : ClaimSh)
    (h1 : a.lay = b.lay) (h2 : a.kept = b.kept) :
    gpOkS p ⟨c, g, .claim a, m⟩ = gpOkS p ⟨c, g, .claim b, m⟩ := by
  cases a
  cases b
  simp only at h1 h2
  subst h1 h2
  unfold gpOkS gpAllS
  cases p.nums.stages <;> rfl

theorem labelsOkS_claim (p : P12) (c : CoreSh) (g : Nat) (m : Option Nat) (a b : ClaimSh)
    (h1 : a.lay = b.lay) : labelsOkS p ⟨c, g, .claim a, m⟩ = labelsOkS p ⟨c, g, .claim b, m⟩ := by
  cases a
  cases b
  simp only at h1
  subst h1
  unfold labelsOkS labelsLS
  cases p.nums.stages <;> rfl

/-- What the batching's part asks beside `TestFront` or `TestFrontOwn` (`BatOwes`), on the shape.
cut: its declared round. -/
def batOwesB (p : P12) (cut : List Fmt.DeclaredRound) (a : TestSh) : Bool :=
  (match a.pass with
    | .nothing => true
    | _ => false) && p.early && codesFit p { codes := a.core.st.codes } &&
  (match beginRunS a.core a.g with
    | some x =>
      cut.all (fun d => d.entry.rows == x.1.2) &&
        gpOkS p ⟨x.2, a.g, .claim ⟨x.1.1, a.g, 0, 0, true, true⟩, a.mask⟩ &&
        labelsOkS p ⟨x.2, a.g, .claim ⟨x.1.1, a.g, 0, 0, true, true⟩, a.mask⟩
    | none => false)

theorem batOwes_of {p : P12} {cut : List Fmt.DeclaredRound} {t : T12} {G : Group}
    (h : batOwesB p cut (testSh t) = true) (hG : t.st.groups[t.g]? = some G) :
    BatOwes p cut t G := by
  unfold batOwesB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hpass : t.pass = .nothing := by
    have h1' : (match passSh t.pass with
      | .nothing => true
      | _ => false) = true := h1
    cases ht : t.pass with
    | nothing => rfl
    | _ =>
      rw [ht] at h1'
      cases h1'
  have e : (testSh t).core = shD (dIn t) := rfl
  rw [e] at h4
  cases hb : beginRunS (shD (dIn t)) (testSh t).g with
  | none =>
    rw [hb] at h4
    cases h4
  | some x =>
    rw [hb] at h4
    obtain ⟨⟨run, d'⟩, hP⟩ := beginRun_returns (dIn t) t.g x hb
    have c := beginRun_carries (dIn t) d' t.g run hP
    obtain rfl : x = ((run.layout, run.rows.size), shD d') :=
      Option.some.inj (hb.symm.trans c)
    have hP' := hP
    unfold Ground.beginRunP at hP'
    split at hP'
    · rename_i hok
      have hG' : (dIn t).st.groups[t.g]? = some G := hG
      rw [hG'] at hP'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hP')
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h4
      obtain ⟨⟨c1, c2⟩, c3⟩ := h4
      have hidle : G.inRun = false := by
        simp only [Ground.ok, Ground.beginRunL, hG', List.all_cons, List.all_nil, Ground.has,
          Option.map_some, Option.getD_some, Bool.and_eq_true, Bool.not_eq_true'] at hok
        exact hok.2.1
      refine ⟨hpass, h2, h3, hidle, c1, fun row hk => ?_⟩
      have ek : (claimSh row (layoutOf t.st G)).kept = 0 := by
        show row.kept.size = 0
        rw [hk]
        rfl
      have el : (claimSh row (layoutOf t.st G)).lay = Own.layoutOf t.st G :=
        (layoutOf_own hG).symm
      constructor
      · rw [← gpOkS_eq]
        exact (gpOkS_claim p _ t.g t.mask _ _ el ek).trans c2
      · rw [← labelsOkS_eq]
        exact (labelsOkS_claim p _ t.g t.mask _ _ el).trans c3
    · cases hP'

/-- What the front asks, on the shape. -/
def frontOwesB (p : P12) (a : TestSh) : Bool :=
  p.nums.free == a.core.roots && Ground.ok (frontLS a.core a.g a.mask) &&
    H2K.Pub.pubOk p a.core.st.codes

/-- **The front's named test on the rows that lie open**: each passes all clauses of the adding once
more, at the statement as it is. Three of its clauses read values. -/
def claimsB (t : T12) : Bool :=
  (t.st.groups[t.g]?).any fun G =>
    G.rows.toList.all fun row => Ground.ok (Ground.rowL t.st t.g row)

theorem frontOwes_of {p : P12} {t : T12} {G : Group} (h : frontOwesB p (testSh t) = true)
    (hv : claimsB t = true) (hG : t.st.groups[t.g]? = some G) : FrontOwes p t G := by
  unfold frontOwesB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' : Ground.ok (frontLS (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask) = true := h2
  rw [frontLS_eq] at h2'
  unfold claimsB at hv
  rw [hG] at hv
  have hv' : ∀ row ∈ G.rows.toList, Ground.ok (Ground.rowL t.st t.g row) = true :=
    List.all_eq_true.1 hv
  refine ⟨by simpa using h1, List.all_eq_true.1 h2', fun row hr => ?_, h3⟩
  obtain ⟨G', hG', hc⟩ := K9L.rowL_clauses t.st t.g row (hv' row hr)
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  exact hc

/-! ## 4 The door -/

open Johnson.Prover.Link (batCut foldCut foldT bat5_yes front5_yes group_batT fold5_yes
  foldFront_first drawnOf)
open ProofFile.Honest.K12 (foldCutOwn foldTOwn door_yes_own)

/-- **What the door asks of the structure's shape, as one Bool.** It is not all that the door asks
of the structure: `door_of_shape` and `door_of_shape_own` take `stTidyB`, plain rows and `claimsB`
beside it. cutB: the batching's declared round. i, n: the numbers of the first two stages' codes. -/
def doorB (p : P12) (cur nxt : Fmt.M1.Stage) (cutB : List Fmt.DeclaredRound) (i n : Nat × Nat)
    (a : TestSh) : Bool :=
  commonB p cur nxt a.core a.g i n && batOwesB p cutB a && frontOwesB p a &&
    match a.mask with
    | some id => cameB cur a.core a.g i id
    | none => a.core.st.oracles.length == a.core.book.place.length

/-- **The door from the shape, where the first fold receives its own mask**: the Bool on the
shape, the first mark, plain rows, the front's named test on the open rows, the two tests on the
plan's cut, and rounds of the declared form: then the front, the batching, the frame's question and
the first fold accept in a row. G: the group under test. row: what the batching makes of the rows
that the test takes in. -/
theorem door_of_shape_own {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat}
    {cutB cutF : List Fmt.DeclaredRound} (h : doorB p cur nxt cutB i n (testSh t) = true)
    (hm : t.mask = none) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (hB : batCut cutB = true) (hF : foldCutOwn cur.k cutF = true)
    (rsB rsF : List Fmt.RoundView) (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldTOwn p (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n
          (rsF.map noDigest)) := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFrontOwn_of h1 hm (by simpa using h4') ht hp
  obtain ⟨row, a0, a1, a2, a3, a4⟩ := door_yes_own H cutB cutF (batOwes_of h2 H.group)
    (frontOwes_of h3 hv H.group) hB hF rsB rsF fB fF
  exact ⟨G, row, H.group, a0, a1, a2, a3, a4⟩

/-- **The door from the shape, where the mask has come.** -/
theorem door_of_shape {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat} {id : Nat}
    {cutB cutF : List Fmt.DeclaredRound} (h : doorB p cur nxt cutB i n (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true) (hB : batCut cutB = true) (hF : foldCut cur.k cutF = true)
    (rsB rsF : List Fmt.RoundView) (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n id
          (rsF.map noDigest)) := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H cutB B hB rsB fB
  exact ⟨G, row, H.group, hr, front5_yes B.pass H.group (frontOwes_of h3 hv H.group), hb,
    group_batT H row, fold5_yes (foldFront_first H _ row hr) hF rsF fF⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.on_map
#print axioms ProofFile.Honest.Sh.treeOf
#print axioms ProofFile.Honest.Sh.frontLS_eq
#print axioms ProofFile.Honest.Sh.seatOfS_eq
#print axioms ProofFile.Honest.Sh.keyAtS_eq
#print axioms ProofFile.Honest.Sh.logAtS_eq
#print axioms ProofFile.Honest.Sh.widthAtS_eq
#print axioms ProofFile.Honest.Sh.numAtS_eq
#print axioms ProofFile.Honest.Sh.gpLS_eq
#print axioms ProofFile.Honest.Sh.maskThin_came
#print axioms ProofFile.Honest.Sh.maskThin_own
#print axioms ProofFile.Honest.Sh.core_dIn
#print axioms ProofFile.Honest.Sh.entered_some
#print axioms ProofFile.Honest.Sh.entered_none
#print axioms ProofFile.Honest.Sh.gpOfS_eq
#print axioms ProofFile.Honest.Sh.thinOf_eq
#print axioms ProofFile.Honest.Sh.gpOkS_eq
#print axioms ProofFile.Honest.Sh.labelsOkS_eq
#print axioms ProofFile.Honest.Sh.runRows_plain
#print axioms ProofFile.Honest.Sh.common_of
#print axioms ProofFile.Honest.Sh.testFrontOwn_of
#print axioms ProofFile.Honest.Sh.testFront_of
#print axioms ProofFile.Honest.Sh.gpOkS_claim
#print axioms ProofFile.Honest.Sh.labelsOkS_claim
#print axioms ProofFile.Honest.Sh.batOwes_of
#print axioms ProofFile.Honest.Sh.frontOwes_of
#print axioms ProofFile.Honest.Sh.door_of_shape_own
#print axioms ProofFile.Honest.Sh.door_of_shape
#print axioms ProofFile.Honest.Sh.frontLS
#print axioms ProofFile.Honest.Sh.seatOfS
#print axioms ProofFile.Honest.Sh.PlainS
#print axioms ProofFile.Honest.Sh.gpOfS
#print axioms ProofFile.Honest.Sh.keyAtS
#print axioms ProofFile.Honest.Sh.logAtS
#print axioms ProofFile.Honest.Sh.widthAtS
#print axioms ProofFile.Honest.Sh.numAtS
#print axioms ProofFile.Honest.Sh.gpLS
#print axioms ProofFile.Honest.Sh.plainSh
#print axioms ProofFile.Honest.Sh.dIn
#print axioms ProofFile.Honest.Sh.thinOf
#print axioms ProofFile.Honest.Sh.gpAllS
#print axioms ProofFile.Honest.Sh.gpOkS
#print axioms ProofFile.Honest.Sh.labelsLS
#print axioms ProofFile.Honest.Sh.labelsOkS
#print axioms ProofFile.Honest.Sh.commonB
#print axioms ProofFile.Honest.Sh.cameB
#print axioms ProofFile.Honest.Sh.Common
#print axioms ProofFile.Honest.Sh.batOwesB
#print axioms ProofFile.Honest.Sh.frontOwesB
#print axioms ProofFile.Honest.Sh.claimsB
#print axioms ProofFile.Honest.Sh.doorB
