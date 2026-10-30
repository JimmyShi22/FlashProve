-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Switch.lean: THE CODE SWITCH (the kind K2's own decision,
Johnson/Top/H0/Tw/K2C/Kind.lean: decideWith at the laid sending) ON THE FIRST CHAIN's SHAPE WITH
THE ROWS' MAKES BESIDE IT: THE UPDATE AS CODE, AND "CARRIES" FROM A YES ALONE. General laws;
nothing is evaluated.

This file has one half. The other, "returns" (a Bool on the pair, named tests on values, rounds and
columns that fit ⊢ the decision says yes), is not here.

Names. The kind stands in three dresses (p.stands): at a link's first place (.link), in the head's
link (.head), at the finish (.finish). "H:1", "H:2", "F:1" are members' names in the plan's table of
places: the head's link's first and second place, the finish's first.

  1 `onSt`, `closeLedgerG_sh`, `joinG_sh`, `addRowsG_sh`, `newGroupSt` | `newGroupG_st`: the text's
    four effects on the statement alone, each on the statement's shape and on the makes.
  2 `oldOraclesS`, `openOne_book`, `opened_book`, `readBookS` | `readOld_book`: each tree that
    holds a message asked for is counted once. After the like laws for the proximity test's own
    copy of this text (Johnson/Desc/K12/Honest/Shape/TestCore.lean).
  3 `joinsSt` | `joins_sh`, **`behindU`** | **`switchBehind_sh`**: the step behind the sending.
  4 `sendByL8_sh`: the sending that the switch calls (SendP.lean's sendP_sh through the library's
    two equivalences).
  5 **`switchEU`** | **`switchE_sh`**: what all three dresses share: the sending, then the step
    behind it. The number of drawn positions is the plan's (p.positions): the text's own test on
    the round says so.
  6 `linkOthers`, **`linkU`**, **`link_carries`**: p.stands = .link → decideWith sendByL8 p s rs gs
    = .ok s' → linkU p (chainF s) = some (chainF s').
  7 **`headU`**, `chainSh_headKept`, **`head_carries`**: the like at p.stands = .head: the first
    half of "H:2".

Limits. THE UPDATE ALONE: linkU and headU ask fewer tests than the decision: that the decision says
yes where they return is NOT shown here. The quiet step behind the head's switch, and the finish's
dress ("F:1"), are not here (SwitchEnds.lean has their updates). The bare decision: no member of
the proof file's list is named. No state is shown at which linkU returns. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Shape.SwitchRowsMk
import Johnson.Desc.First.Shape.ChainF
import Johnson.Desc.Ground.Shape.More
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.SendsOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (StSh CoreSh stSh shD joinS closeLedgerS addRowsS newGroupS
  countB countB_sh modAt)

local notation "bookS" => VerifiableInference.Desc.Ground.Sh.bookSh
local notation "BookS" => VerifiableInference.Desc.Ground.Sh.BookSh
open _root_.Tw.K2 (dOf closeLedgerG joinG addRowsG newGroupG SwIn SwOut switchBehind readOld
  openOne)

/-! ## 1 The four effects on the statement alone -/

/-- A routine on the core that reads and turns the statement alone, on the statement's shape. -/
def onSt (f : CoreSh → Option CoreSh) (a : StSh) : Option StSh :=
  (f ⟨a, bookS {}, 0⟩).map (·.st)

theorem closeLedgerG_sh {S S' : Statement} {o : Nat} (h : closeLedgerG S o = .ok S') :
    onSt (closeLedgerS · o) (stSh S) = some (stSh S') ∧ formsOf S' = formsOf S := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    refine ⟨?_, closeLedger_forms hd⟩
    show (closeLedgerS (shD (dOf S)) o).map (·.st) = _
    rw [Ground.Sh.closeLedger_carries _ _ _ hd]
    rfl
  · cases h

theorem joinG_sh {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S') :
    onSt (joinS · g o kept) (stSh S) = some (stSh S') ∧ formsOf S' = formsOf S := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    refine ⟨?_, join_forms hd⟩
    show (joinS (shD (dOf S)) g o kept).map (·.st) = _
    rw [Ground.Sh.join_carries _ _ _ _ _ hd]
    rfl
  · cases h

theorem addRowsG_sh {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') :
    onSt (addRowsS · g (rows.map (·.kind))) (stSh S) = some (stSh S') ∧
      formsOf S' = { formsOf S with
        groups := modAt (formsOf S).groups g (· ++ rows.map rowMk) } := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    refine ⟨?_, addRows_forms hd⟩
    show (addRowsS (shD (dOf S)) g (rows.map (·.kind))).map (·.st) = _
    rw [Ground.Sh.addRows_carries _ _ _ _ hd]
    rfl
  · cases h

/-- A new group, on the statement's shape. -/
def newGroupSt (a : StSh) (code maskCode : Nat) : Option (StSh × Nat) :=
  (newGroupS ⟨a, bookS {}, 0⟩ code maskCode).map fun y => (y.2.st, y.1)

theorem newGroupG_st {S S' : Statement} {code maskCode g : Nat}
    (h : newGroupG S code maskCode = .ok (S', g)) :
    newGroupSt (stSh S) code maskCode = some (stSh S', g) ∧
      formsOf S' = { formsOf S with groups := (formsOf S).groups ++ [[]] } := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    refine ⟨?_, newGroup_forms hd⟩
    unfold newGroupSt
    rw [show (⟨stSh S, bookS {}, 0⟩ : CoreSh) = shD (dOf S) from rfl,
      Ground.Sh.newGroup_carries _ _ _ _ _ hd]
    rfl
  · cases h

/-! ## 2 The book behind the reading of the old rows

After the like law for the proximity test's own copy of this text
(Johnson/Desc/K12/Honest/Shape/TestCore.lean: openOne_book, opened_book, readOld_book). -/

def oldOraclesS (old : SingleSh) : Array Nat :=
  if old.masks == 2 then old.layout.members.push old.fresh else old.layout.members

theorem openOne_book (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s s' : TreeBook × List _root_.Tw.K2.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : openOne S ft pos B0 t s = .ok s') : bookS s'.1 = countB (bookS s.1) t := by
  unfold openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact countB_sh _ _)
      | cases h
  · cases h

theorem opened_book (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (l : List Nat)
      (s s' : TreeBook × List _root_.Tw.K2.Col × Array (Nat × Array Nat × Array (Array F))),
      l.foldlM (fun s t => openOne S ft pos B0 t s) s = .ok s' →
      bookS s'.1 = l.foldl countB (bookS s.1)
  | [], s, s', h => by cases h; rfl
  | t :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := (K1.bind_ok _ _ _).1 h
    rw [opened_book S ft pos B0 l s1 s' h2, openOne_book S ft pos B0 t s s1 h1]
    rfl

/-- The book behind the reading, on shapes. -/
def readBookS (old : SingleSh) (b : BookS) : Option BookS :=
  ((oldOraclesS old).toList.mapM fun o => b.place[o]?).map fun ps =>
    (Fmt.listOf (ps.map (·.1))).foldl countB b

theorem readOld_book {i : SwIn} {pos : Positions} {B : TreeBook}
    {left : List _root_.Tw.K2.Col} {ys : Array E} (h : readOld i pos = .ok (B, left, ys)) :
    readBookS (singleSh i.old) (bookS i.book) = some (bookS B) := by
  obtain ⟨places, cols, opened, R⟩ := First.K2.readOld_inv h
  have h1 := R.hPlaces
  have h3 := R.hOpen
  unfold readBookS
  rw [Array.mapM_eq_mapM_toList] at h1
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h1
  rw [show oldOraclesS (singleSh i.old) = singleRowsOracles i.old from rfl]
  simp only [Ground.Sh.place_get]
  rw [hl]
  rw [OnBytes.listOfT_eq] at h3
  have := opened_book _ _ _ _ _ _ _ h3
  show some _ = some _
  rw [this]
  simp

/-! ## 3 The step behind the sending -/

/-- Several joinings in a row, on the statement's shape. -/
def joinsSt {ι : Type} (g : Nat) (who : ι → Nat) (kept : ι → Bool) (l : List ι) (a : StSh) :
    Option StSh :=
  l.foldlM (fun s p => onSt (joinS · g (who p) (kept p)) s) a

theorem joins_sh {ι : Type} (g : Nat) (who : ι → Nat) (kept : ι → Bool) :
    ∀ (l : List ι) (S S' : Statement),
      l.foldlM (fun S p => joinG S g (who p) (kept p)) S = .ok S' →
      joinsSt g who kept l (stSh S) = some (stSh S') ∧ formsOf S' = formsOf S
  | [], S, S', h => by
    cases h
    exact ⟨rfl, rfl⟩
  | p :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := (K1.bind_ok _ _ _).1 h
    obtain ⟨e1, e2⟩ := joinG_sh h1
    obtain ⟨g1, g2⟩ := joins_sh g who kept l S1 S' h2
    refine ⟨?_, g2.trans e2⟩
    unfold joinsSt
    rw [List.foldlM_cons, e1]
    exact g1

/-- **Tw.K2.switchBehind on shapes.** grp: the new group. ids: the sending's numbers. draws: how
many positions are drawn. -/
def behindU (grp : Nat) (old : SingleSh) (T : SwitchTarget) (ids : Array Nat) (draws : Nat)
    (a : CoreSh) (F : FormsSh) : Option (CoreSh × FormsSh) :=
  (readBookS old a.book).bind fun B =>
  (if 0 < T.shape.maskRows then onSt (closeLedgerS · (ids.getD 0 noId)) a.st
    else some a.st).bind fun s1 =>
  (onSt (joinS · grp (ids.getD 0 noId) false) s1).bind fun s2 =>
  (joinsSt grp (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain)
    ((ids.extract 1 (1 + T.kept.size)).zip T.kept).toList s2).bind fun s3 =>
  (swRowsS s3 F old T (ids.getD 0 noId) (ids.extract 1 (1 + T.kept.size)) draws).bind fun rows =>
  (onSt (addRowsS · grp (rows.map (·.kind))) s3).map fun s4 =>
    (⟨s4, B, a.roots⟩, { F with groups := modAt F.groups grp (· ++ rows) })

theorem switchBehind_sh {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) (roots : Nat) :
    behindU i.grp (singleSh i.old) i.T i.ids i.drawn.poss.length
        ⟨stSh i.st, bookS i.book, roots⟩ (formsOf i.st) =
      some (⟨stSh o.st, bookS o.book, roots⟩, formsOf o.st) := by
  obtain ⟨c, y, S1, S2, S3, rows, R⟩ := First.K2.switchBehind_inv h
  have hL : (if 0 < i.T.shape.maskRows then
        onSt (closeLedgerS · (i.ids.getD 0 noId)) (stSh i.st) else some (stSh i.st)) =
      some (stSh S1) ∧ formsOf S1 = formsOf i.st := by
    have hl := R.hLedger
    by_cases hm : 0 < i.T.shape.maskRows
    · rw [if_pos hm] at hl ⊢
      exact closeLedgerG_sh hl
    · rw [if_neg hm] at hl ⊢
      cases hl
      exact ⟨rfl, rfl⟩
  obtain ⟨j1, j2⟩ := joinG_sh R.hJoinG
  have hk := R.hJoinKept
  rw [← Array.foldlM_toList] at hk
  obtain ⟨k1, k2⟩ := joins_sh i.grp (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain)
    _ S2 S3 hk
  have hr := swRows_mk R.hRows
  rw [show (Positions.ofDraws c.logN i.drawn.poss).draws.size = i.drawn.poss.length from by
    simp [Positions.ofDraws], k2, j2, hL.2] at hr
  obtain ⟨a1, a2⟩ := addRowsG_sh R.hAdded
  unfold behindU
  dsimp only
  rw [readOld_book R.hRead, hL.1]
  show ((onSt (joinS · i.grp (i.ids.getD 0 noId) false) (stSh S1)).bind fun s2 => _) = _
  rw [j1]
  show ((joinsSt i.grp _ _ _ (stSh S2)).bind fun s3 => _) = _
  rw [k1]
  show ((swRowsS (stSh S3) _ _ _ _ _ _).bind fun rows => _) = _
  rw [hr]
  show ((onSt (addRowsS · i.grp ((rows.map rowMk).map (·.kind))) (stSh S3)).map fun s4 => _) = _
  rw [show (rows.map rowMk).map (·.kind) = rows.map (·.kind) from by
    rw [List.map_map]; rfl, a1, a2, k2, j2, hL.2]
  rfl

/-! ## 4 The sending that the switch calls -/

theorem sendByL8_sh {P : _root_.Tw.K2.Par9} {S : Statement} {B : TreeBook} {roots : Nat}
    {settled : Bool} {notices : Array OracleNotice} {rS rL : Fmt.RoundView} {y : _root_.Tw.K2.Sent}
    (h : _root_.Tw.K2.sendByL8 P S B roots settled notices rS rL = .ok y) :
    sendPS P.firstTree notices ⟨stSh S, bookS B, roots⟩ =
        some (y.ids, ⟨stSh y.st, bookS y.book, y.roots⟩) ∧
      formsOf y.st = sendPF P.firstTree notices ⟨stSh S, bookS B, roots⟩ (formsOf S) := by
  obtain ⟨ids, took, d, hs, rfl⟩ := (First.K2.sendByL8_iff P S B roots settled notices rS rL y).1 h
  obtain ⟨-, -, sd, an, hp⟩ := (First.K2.sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
  have e : ∀ d : _root_.Desc.Plain.DState Unit, shD d = ⟨stSh d.st, bookS d.book, d.roots⟩ :=
    fun _ => rfl
  have h1 := sendP_sh hp
  rw [e, e] at h1
  exact h1

/-! ## 5 What all three dresses share: the sending, then the step behind it -/

open VerifiableInference.Desc.First.K2 (P2 decideWith par9)
open OnBytes.Params (ReqMessage)

/-- **Tw.K2.switchE on shapes: the update alone.** grp: the new group. old: the carried single rows'
make. Returns the sending's numbers, the core and the makes behind. -/
def switchEU (p : P2) (grp : Nat) (old : SingleSh) (T : SwitchTarget)
    (others : Array OracleNotice) (a : CoreSh) (F : FormsSh) :
    Option (Array Nat × CoreSh × FormsSh) :=
  (sendPS p.firstTree (_root_.Tw.K2.switchNotices T others) a).bind fun y =>
    (behindU grp old T y.1 p.positions y.2
      (sendPF p.firstTree (_root_.Tw.K2.switchNotices T others) a F)).map fun z => (y.1, z.1, z.2)

theorem switchE_sh {p : P2} {s : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols : List _root_.Tw.K2.Col} {w : SwOut} {roots : Nat}
    (h : _root_.Tw.K2.switchE switchBehind (par9 p) _root_.Tw.K2.sendByL8 s x r₁ r₂ cols =
      .ok (w, roots)) :
    ∃ ids : Array Nat,
      switchEU p x.f.group (singleSh x.f.rows) x.T x.others ⟨stSh x.st, bookS s.book, s.roots⟩
          (formsOf x.st) = some (ids, ⟨stSh w.st, bookS w.book, roots⟩, formsOf w.st) ∧
        w.out.g = ids.getD 0 noId ∧ w.out.kept = ids.extract 1 (1 + x.T.kept.size) ∧
        w.out.others = ids.extract (1 + x.T.kept.size) ids.size := by
  obtain ⟨y, W⟩ := First.K2.switchE_inv h
  obtain ⟨y1, y2⟩ := sendByL8_sh W.hSend
  have hb := switchBehind_sh W.hBehind y.roots
  obtain ⟨c, yy, T1, T2, T3, rows, Bh⟩ := First.K2.switchBehind_inv W.hBehind
  have hloc : r₂.drawn.poss.length = p.positions := by
    have := Bh.hLoc
    simp only [First.K2.locOk, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.2.1.2
  refine ⟨y.ids, ?_, ?_, ?_, ?_⟩
  · unfold switchEU
    rw [show p.firstTree = (par9 p).firstTree from rfl, y1]
    show (behindU x.f.group (singleSh x.f.rows) x.T y.ids p.positions
      ⟨stSh y.st, bookS y.book, y.roots⟩ _).map _ = _
    rw [← y2, ← hloc]
    have hb' : behindU x.f.group (singleSh x.f.rows) x.T y.ids r₂.drawn.poss.length
        ⟨stSh y.st, bookS y.book, y.roots⟩ (formsOf y.st) =
        some (⟨stSh w.st, bookS w.book, y.roots⟩, formsOf w.st) := hb
    rw [hb', W.hRoots]
    rfl
  · rw [Bh.hOut]
    rfl
  · rw [Bh.hOut]
    rfl
  · rw [Bh.hOut]
    rfl

/-! ## 6 A segment's first place -/

/-- What the front announces beside the target's own messages. -/
def linkOthers (f : FrameSh) : Array OracleNotice :=
  ReqFrame.notices (f.blank.atMoment 0) ++ #[foldMaskNotice (f.blank.foldShape f.link {})]

/-- **The code switch at a segment's first place, on the chain's shape with the rows' makes beside
it: the update alone.** -/
def linkU (p : P2) (x : ChainF) : Option ChainF :=
  let f := x.1.check.frame
  (f.groups[f.link]?).bind fun G =>
  (newGroupSt x.1.core.st f.shape.code f.shape.maskCode).bind fun n =>
  (switchEU p n.2 f.rows G.target (linkOthers f) ⟨n.1, x.1.core.book, x.1.core.roots⟩
    { x.2 with groups := x.2.groups ++ [[]] }).bind fun z =>
  let ids := z.1.extract (1 + G.target.kept.size) z.1.size
  let own := f.blank.atMoment 0
  (ids[own.length]?).bind fun mask =>
  (joinsSt n.2 (fun q : ReqMessage × Nat => q.2) (fun q => decide (0 < q.1.life))
    (zipT own (ids.extract 0 own.length).toList) z.2.1.st).map fun s5 =>
    (((x.1.setCore ⟨s5, z.2.1.book, z.2.1.roots⟩).setRowsOwed none).setCheck
      { x.1.check with
        frame := { f with
          group := n.2, moment := 1, own := #[] ++ ids.extract 0 own.length, plain := 0
          keptBefore := z.1.extract 1 (1 + G.target.kept.size), mask := some mask
          atStart := f.atStart ++ ids.extract (own.length + 1) ids.size
          next := .laterOrClose }
        sent := #[] ++ ids.extract 0 own.length, inLink := true, moments := 1 }, z.2.2)

/-- **From a yes of the kind's own decision at a segment's first place: the update returns the
shape behind and the makes behind.** No premise on values. -/
theorem link_carries {p : P2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .link)
    (h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s') :
    linkU p (chainF s) = some (chainF s') := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, R⟩ := First.K2.link_inv hp h
  have hF := R.hFront
  unfold _root_.Tw.K2.firstFront at hF
  split at hF
  · cases hF
  · split at hF
    · cases hF
    · split at hF
      · rename_i L G hL hG
        dsimp only at hF
        split at hF
        · cases hF
        · rename_i S1 g hN
          cases hF
          obtain ⟨n1, n2⟩ := newGroupG_st hN
          obtain ⟨ids, e1, -, e3, e4⟩ := switchE_sh R.hSwitch
          have hB := R.hBehind
          unfold _root_.Tw.K2.firstBehind at hB
          dsimp only at hB
          split at hB
          · cases hB
          · split at hB
            · cases hB
            · rename_i mask hm
              split at hB
              · cases hB
              · split at hB
                · cases hB
                · rename_i S5 hj
                  cases hB
                  obtain ⟨j1, j2⟩ := joins_sh _ (fun q : ReqMessage × Nat => q.2)
                    (fun q => decide (0 < q.1.life)) _ _ _ hj
                  rw [e4] at hm j1
                  rw [n2] at e1
                  unfold linkU
                  dsimp only
                  rw [show (chainF s).1.check.frame.groups[(chainF s).1.check.frame.link]? =
                    some G from hG]
                  show ((newGroupSt (stSh s.st) s.check.frame.shape.code
                    s.check.frame.shape.maskCode).bind fun n => _) = _
                  rw [n1]
                  show ((switchEU p g (singleSh s.check.frame.rows) G.target _
                    ⟨stSh S1, bookS s.book, s.roots⟩ _).bind fun z => _) = _
                  have e1' : switchEU p g (singleSh s.check.frame.rows) G.target
                      (linkOthers (chainF s).1.check.frame) ⟨stSh S1, bookS s.book, s.roots⟩
                      { groups := (chainF s).2.groups ++ [[]], oracles := (chainF s).2.oracles } =
                      some (ids, ⟨stSh w.st, bookS w.book, roots⟩, formsOf w.st) := e1
                  rw [e1']
                  show (((ids.extract (1 + G.target.kept.size) ids.size)[
                    (s.check.frame.atMoment 0).length]?).bind fun mask => _) = _
                  rw [hm]
                  have j1' : joinsSt g (fun q : ReqMessage × Nat => q.2)
                      (fun q => decide (0 < q.1.life))
                      (zipT (s.check.frame.atMoment 0)
                        ((ids.extract (1 + G.target.kept.size) ids.size).extract 0
                          (s.check.frame.atMoment 0).length).toList) (stSh w.st) =
                      some (stSh S') := j1
                  show ((joinsSt g (fun q : ReqMessage × Nat => q.2)
                      (fun q => decide (0 < q.1.life))
                      (zipT (s.check.frame.atMoment 0)
                        ((ids.extract (1 + G.target.kept.size) ids.size).extract 0
                          (s.check.frame.atMoment 0).length).toList) (stSh w.st)).map
                      fun s5 => _) = _
                  rw [j1', R.hOut, ← j2, e3, e4]
                  rfl
      · cases hF
      · cases hF

/-! ## 7 The switch at the head's link (the first half of "H:2") -/

/-- **The code switch at the head's link: the update alone.** The link is entered; its group was
opened by the front at "H:1". -/
def headU (p : P2) (x : ChainF) : Option ChainF :=
  (x.1.head).bind fun hd =>
  (x.1.check.frame.groups[x.1.check.frame.link]?).bind fun G =>
  (switchEU p hd.fr.group hd.fr.rows G.target (linkOthers x.1.check.frame) x.1.core x.2).map
    fun z =>
      (((x.1.setCore z.2.1).setRowsOwed none).setHead
        { hd with
          kept := z.1.extract 1 (1 + G.target.kept.size)
          ids := z.1.extract (1 + G.target.kept.size) z.1.size }, z.2.2)

theorem chainSh_headKept (s : S) (a : HeadOwn) (hh : s.here = .head a) (st : Statement)
    (book : TreeBook) (roots : Nat) (kept ids : Array Nat) :
    chainSh { s with st := st, book := book, roots := roots, rowsOwed := none
                     here := .head { a with kept := kept, ids := ids } } =
      (((chainSh s).setCore ⟨stSh st, bookS book, roots⟩).setRowsOwed none).setHead
        { headSh a with kept := kept, ids := ids } := by
  obtain ⟨st0, book0, roots0, rowsOwed0, failed0, check0, out0, here0, req0⟩ := s
  cases hh
  rfl

theorem head_carries {p : P2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s') :
    headU p (chainF s) = some (chainF s') := by
  obtain ⟨r₁, r₂, a, G, w, roots, rfl, R⟩ := First.K2.head_inv hp h
  obtain ⟨ids, e1, -, e3, e4⟩ := switchE_sh R.hSwitch
  have hhd : (chainF s).1.head = some (headSh a) := by
    show headOf s.here = _
    rw [R.hHere]
    rfl
  unfold headU
  rw [hhd]
  show (((chainF s).1.check.frame.groups[(chainF s).1.check.frame.link]?).bind fun G => _) = _
  rw [show (chainF s).1.check.frame.groups[(chainF s).1.check.frame.link]? = some G from R.hGroup]
  show ((switchEU p a.fr.group (singleSh a.fr.rows) G.target
    (linkOthers (frameSh s.check.frame)) ⟨stSh s.st, bookS s.book, s.roots⟩
    (formsOf s.st)).map fun z => _) = _
  rw [show switchEU p a.fr.group (singleSh a.fr.rows) G.target
    (linkOthers (frameSh s.check.frame)) ⟨stSh s.st, bookS s.book, s.roots⟩ (formsOf s.st) = _
    from e1]
  show some _ = some _
  rw [R.hOut, e3, e4]
  unfold chainF
  rw [chainSh_headKept s a R.hHere]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.head_carries
#print axioms VerifiableInference.Desc.First.Shape.switchE_sh
#print axioms VerifiableInference.Desc.First.Shape.link_carries
#print axioms VerifiableInference.Desc.First.Shape.sendByL8_sh
#print axioms VerifiableInference.Desc.First.Shape.switchBehind_sh
#print axioms VerifiableInference.Desc.First.Shape.closeLedgerG_sh
#print axioms VerifiableInference.Desc.First.Shape.joinG_sh
#print axioms VerifiableInference.Desc.First.Shape.addRowsG_sh
#print axioms VerifiableInference.Desc.First.Shape.newGroupG_st
#print axioms VerifiableInference.Desc.First.Shape.readOld_book
#print axioms VerifiableInference.Desc.First.Shape.openOne_book
#print axioms VerifiableInference.Desc.First.Shape.opened_book
#print axioms VerifiableInference.Desc.First.Shape.joins_sh
#print axioms VerifiableInference.Desc.First.Shape.chainSh_headKept
