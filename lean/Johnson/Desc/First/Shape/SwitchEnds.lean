-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchEnds.lean: WHAT STANDS AROUND THE CODE SWITCH AT THE HEAD's LINK AND
AT THE FINISH, ON THE FIRST CHAIN's SHAPE WITH THE ROWS' MAKES BESIDE IT: THE UPDATES AS CODE, AND
"CARRIES" FROM A YES ALONE. General laws; nothing is evaluated. It goes on where Switch.lean ends
(whose head says what "H:2" and "F:1" name).

  1 `firstBehindU` | `firstBehind_sh`: Tw.K2.firstBehind: the fresh mask's number; the own messages
    join; the frame behind.
  2 **`headOpenU`** | **`headOpen_carries`**: K2.headOpenQ P s = .ok s' → headOpenU P (chainF s) =
    some (chainF s'): the quiet step behind the head's switch (the second half of "H:2"): what lay
    shut in the entered link (HeadSh.shut: six fields) is laid bare; the ledger is the plan's,
    empty; the context is the walk's front's (the library's front_iff).
  3 THE FINISH ("F:1"): **`finFrontU`** | `finFront_carries` (K2.finishFrontQ: a new group; the
    finish is entered) · **`finU`** | `switchE_pos` | `chainSh_finSw` | **`fin_carries`** (the
    switch at p.stands = .finish) · **`finBehindU`** | `finBehind_carries` (K2.finishBehindQ: the
    fresh mask's number).

All over the library's closed forms of a yes (headOpenQ_iff, finishFrontQ_iff, finishBehindQ_iff,
finish_inv).

Limits. THE UPDATES ALONE: each asks fewer tests than its text: that the text says yes where the
update returns is NOT shown here. headOpenQ tests values (the reply is an entry of the vocabulary;
the covered positions can be made of the request's words): none of that is here. The pieces are not
joined to the places' blocks ("H:2" is two decisions in a row, "F:1" three), and no member of the
proof file's list is named. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Switch
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Walk.FrameProps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (StSh CoreSh stSh joinS)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 HeadPar headOpenQ finishFrontQ
  finishBehindQ)
open OnBytes.Params (ReqMessage)
open Johnson.Desc.First.Walk (firstKept weightsAtZero emptySlots)

local notation "bookS" => VerifiableInference.Desc.Ground.Sh.bookSh

/-! ## 1 What stands behind a switch at a link -/

/-- Tw.K2.firstBehind on shapes. n: the number of plain scalars. -/
def firstBehindU (a : StSh) (f : FrameSh) (own : List ReqMessage) (kept others : Array Nat)
    (n : Nat) : Option (StSh × FrameSh × Array Nat) :=
  (others[own.length]?).bind fun mask =>
  (joinsSt f.group (fun q : ReqMessage × Nat => q.2) (fun q => decide (0 < q.1.life))
    (zipT own (others.extract 0 own.length).toList) a).map fun s5 =>
    (s5, { f with
        plain := n, keptBefore := kept, mask := some mask
        atStart := f.atStart ++ others.extract (own.length + 1) others.size
        own := f.own ++ others.extract 0 own.length, next := .laterOrClose },
      others.extract 0 own.length)

theorem firstBehind_sh {S S' : Statement} {x : _root_.Tw.K2.Front} {sw : Switched}
    {plain : List E} {f : ReqFrame} {mine : Array Nat}
    (h : _root_.Tw.K2.firstBehind S x sw plain = .ok (S', f, mine)) :
    firstBehindU (stSh S) (frameSh x.f) x.own sw.kept sw.others plain.length =
        some (stSh S', frameSh f, mine) ∧ formsOf S' = formsOf S := by
  unfold _root_.Tw.K2.firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i mask hm
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i S5 hj
          cases h
          obtain ⟨j1, j2⟩ := joins_sh _ (fun q : ReqMessage × Nat => q.2)
            (fun q => decide (0 < q.1.life)) _ _ _ hj
          refine ⟨?_, j2⟩
          unfold firstBehindU
          rw [hm]
          have j1' : joinsSt (frameSh x.f).group (fun q : ReqMessage × Nat => q.2)
              (fun q => decide (0 < q.1.life))
              (zipT x.own (sw.others.extract 0 x.own.length).toList) (stSh S) =
              some (stSh S') := j1
          show ((joinsSt (frameSh x.f).group (fun q : ReqMessage × Nat => q.2)
              (fun q => decide (0 < q.1.life))
              (zipT x.own (sw.others.extract 0 x.own.length).toList) (stSh S)).map
              fun s5 => _) = _
          rw [j1']
          rfl

/-! ## 2 The quiet step behind the head's switch (the second half of "H:2") -/

/-- **K2.headOpenQ on shapes: the update alone.** -/
def headOpenU (P : HeadPar) (x : ChainF) : Option ChainF :=
  (x.1.head).bind fun hd =>
  (hd.shut).bind fun sh =>
  (firstBehindU x.1.core.st hd.fr (x.1.check.frame.blank.atMoment 0) hd.kept hd.ids
    (if x.1.reply then 1 else 0)).map fun y =>
    let check : CheckSh :=
      { x.1.check with frame := y.2.1, sent := y.2.2, inLink := true, moments := 1 }
    (ChainSh.mk x.1.marked 3 (some sh.tl)
      (some (ledSh (emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns))) sh.tables
      x.1.rowsOwed ⟨y.1, x.1.core.book, x.1.core.roots⟩ x.1.reply x.1.indexMasks x.1.pile
      x.1.atEnd check
      (some (linkSh { check := check.blank, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp }))
      sh.look sh.lookHeard x.1.own (some { hd with shut := none }) x.1.att x.1.fin, x.2)

theorem headOpen_carries {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    headOpenU P (chainF s) = some (chainF s') := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, A⟩ := (First.K2.headOpenQ_iff P s s').1 h
  obtain ⟨e1, e2⟩ := firstBehind_sh A.behind
  obtain ⟨-, -, hL, hout⟩ := Johnson.Desc.First.Walk.Props.front_iff.1 A.front
  have ho := A.opens
  unfold S.openHead? S.openHead at ho
  rw [A.here] at ho
  simp only [A.fresh, Bool.false_eq_true, if_false] at ho
  obtain ⟨rfl, hm⟩ := (S.unmarked_ok _ _).1 ho
  have hb := A.opened
  cases hb
  have hhd : (chainF s).1.head = some (headSh a) := by
    show headOf s.here = _
    rw [A.here]
    rfl
  have hsh : (headSh a).shut = some ⟨tailSh a.tl, ledSh a.F, linkSh a.L,
      a.x.map fun x => heardAll x.g1, a.lookHeard.map heardAll,
      a.t.map fun t => t.funs.toList.map funSh⟩ := by
    unfold headSh
    simp [A.fresh]
  have hn : s.out.reply.toList.length = if (chainF s).1.reply then 1 else 0 := by
    show _ = if s.out.reply.isSome then 1 else 0
    rw [A.seat]
    rfl
  unfold headOpenU
  rw [hhd]
  show (((headSh a).shut).bind fun sh => _) = _
  rw [hsh]
  show ((firstBehindU (stSh s.st) (frameSh a.fr) (s.check.frame.atMoment 0) a.kept a.ids
    (if (chainF s).1.reply then 1 else 0)).map fun y => _) = _
  rw [← hn]
  have e1' : firstBehindU (stSh s.st) (frameSh a.fr) (s.check.frame.atMoment 0) a.kept a.ids
      s.out.reply.toList.length = some (stSh st, frameSh f, mine) := e1
  rw [e1', A.out', hL, hout]
  obtain ⟨st0, book0, roots0, rowsOwed0, failed0, check0, out0, here0, req0⟩ := s
  cases A.here
  show some _ = some _
  congr 1
  unfold chainF
  rw [e2]
  simp [chainSh, ChainSh.mk, hereNo, headOf, headSh, attOf, finOf, endSh, S.tl?, S.fork?,
    S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, ChainSh.marked, ChainSh.rowsOwed,
    ChainSh.core, ChainSh.reply, ChainSh.indexMasks, ChainSh.pile, ChainSh.atEnd, ChainSh.check,
    ChainSh.own, ChainSh.att, ChainSh.fin, firstKept, checkSh, linkSh, A.fresh,
    frameSh_blank, CheckSh.blank]
  exact ⟨rfl, rfl, rfl⟩

/-! ## 3 The finish ("F:1"): the quiet step in front, the switch, the quiet step behind -/

/-- A switch's record before any switch. -/
def swSh0 : SwSh := swSh default

/-- **K2.finishFrontQ on shapes: the update alone.** -/
def finFrontU (x : ChainF) : Option ChainF :=
  let f := x.1.check.frame
  (f.groups[f.link]?).bind fun G =>
  (newGroupSt x.1.core.st f.shape.code f.shape.maskCode).map fun n =>
    (((x.1.setCore ⟨n.1, x.1.core.book, x.1.core.roots⟩).setHere 5).layFin
      (some { G := some G, fr := { f with group := n.2, moment := 1, own := #[] }, sw := swSh0
              answers := none, stages := none, row := groupMk default, L := default, mask := none
              st := swSh0 }),
      { x.2 with groups := x.2.groups ++ [[]] })

theorem finFront_carries {s s' : S} (h : finishFrontQ s = .ok s') :
    finFrontU (chainF s) = some (chainF s') := by
  obtain ⟨G, x, s₁, a, A⟩ := (First.K2.finishFrontQ_iff s s').1 h
  have hF := A.front
  unfold _root_.Tw.K2.finishFront at hF
  split at hF
  · cases hF
  · split at hF
    · cases hF
    · rename_i G' hG'
      split at hF
      · cases hF
      · rename_i S1 g hN
        cases hF
        obtain ⟨n1, n2⟩ := newGroupG_st hN
        have he := A.enters
        unfold S.enterFin? S.enterFin at he
        rw [if_pos A.between] at he
        obtain ⟨rfl, hm⟩ := (S.unmarked_ok _ _).1 he
        have ha := A.entered
        cases ha
        unfold finFrontU
        dsimp only
        rw [show (chainF s).1.check.frame.groups[(chainF s).1.check.frame.link]? = some G
          from A.group]
        show ((newGroupSt (stSh s.st) s.check.frame.shape.code
          s.check.frame.shape.maskCode).map fun n => _) = _
        rw [n1, A.out]
        show some _ = some _
        congr 1
        unfold chainF
        rw [n2]
        have hb : s.here = .between := by
          have := A.between
          unfold S.atBetween at this
          cases hh : s.here <;> simp [hh] at this
          rfl
        obtain ⟨st0, book0, roots0, rowsOwed0, failed0, check0, out0, here0, req0⟩ := s
        cases hb
        rfl

/-- **The code switch at the finish: the update alone.** -/
def finU (p : P2) (x : ChainF) : Option ChainF :=
  (x.1.fin).bind fun a =>
  (a.G).bind fun G =>
  (switchEU p a.fr.group a.fr.rows G.target
    #[foldMaskNotice (a.fr.blank.foldShape a.fr.link {})] x.1.core x.2).map fun z =>
      (((x.1.setCore z.2.1).setRowsOwed none).setFin
        { a with sw :=
            { g := z.1.getD 0 noId, kept := z.1.extract 1 (1 + G.target.kept.size)
              others := z.1.extract (1 + G.target.kept.size) z.1.size
              logN := p.logN, draws := p.positions } }, z.2.2)

/-- The positions that a switch hands on: their range and number are the plan's. -/
theorem switchE_pos {p : P2} {s : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols : List _root_.Tw.K2.Col} {w : _root_.Tw.K2.SwOut} {roots : Nat}
    (h : _root_.Tw.K2.switchE _root_.Tw.K2.switchBehind (par9 p) _root_.Tw.K2.sendByL8 s x r₁ r₂
      cols = .ok (w, roots)) :
    w.out.positions.logN = p.logN ∧ w.out.positions.draws.size = p.positions := by
  obtain ⟨y, W⟩ := First.K2.switchE_inv h
  obtain ⟨c, yy, T1, T2, T3, rows, Bh⟩ := First.K2.switchBehind_inv W.hBehind
  have := Bh.hLoc
  simp only [First.K2.locOk, Bool.and_eq_true, beq_iff_eq] at this
  rw [Bh.hOut]
  have hq : r₂.drawn.poss.length = p.positions := this.1.1.2.1.2
  refine ⟨this.1.2.1.symm, ?_⟩
  show (Positions.ofDraws c.logN r₂.drawn.poss).draws.size = _
  rw [← hq]
  simp [Positions.ofDraws]

theorem chainSh_finSw (s : S) (a : FinOwn) (hh : s.here = .fin a) (G : ReqGroup)
    (hG : a.G = some G) (st : Statement) (book : TreeBook) (roots : Nat) (sw : Switched) :
    chainSh { s with st := st, book := book, roots := roots, rowsOwed := none
                     here := .fin { a with sw := sw } } =
      (((chainSh s).setCore ⟨stSh st, bookS book, roots⟩).setRowsOwed none).setFin
        { finSh a with G := some G, sw := swSh sw } := by
  obtain ⟨st0, book0, roots0, rowsOwed0, failed0, check0, out0, here0, req0⟩ := s
  cases hh
  obtain ⟨G0, fr0, sw0, an0, sg0, row0, L0, mask0, sw1⟩ := a
  cases hG
  rfl

theorem fin_carries {p : P2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .finish)
    (h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s') :
    finU p (chainF s) = some (chainF s') := by
  obtain ⟨r₁, r₂, a, G, w, roots, rfl, R⟩ := First.K2.finish_inv hp h
  obtain ⟨ids, e1, e2, e3, e4⟩ := switchE_sh R.hSwitch
  obtain ⟨q1, q2⟩ := switchE_pos R.hSwitch
  have hfin : (chainF s).1.fin = some (finSh a) := by
    show finOf s.here = _
    rw [R.hHere]
    rfl
  unfold finU
  rw [hfin]
  show (((finSh a).G).bind fun G => _) = _
  rw [show (finSh a).G = some G from R.hLaid]
  have e1' : switchEU p (finSh a).fr.group (finSh a).fr.rows G.target
      #[foldMaskNotice ((finSh a).fr.blank.foldShape (finSh a).fr.link {})] (chainF s).1.core
      (chainF s).2 = some (ids, ⟨stSh w.st, bookS w.book, roots⟩, formsOf w.st) := e1
  show ((switchEU p (finSh a).fr.group (finSh a).fr.rows G.target
      #[foldMaskNotice ((finSh a).fr.blank.foldShape (finSh a).fr.link {})] (chainF s).1.core
      (chainF s).2).map fun z => _) = _
  have hs : swSh w.out = ⟨ids.getD 0 noId, ids.extract 1 (1 + G.target.kept.size),
      ids.extract (1 + G.target.kept.size) ids.size, p.logN, p.positions⟩ := by
    unfold swSh
    rw [e2, e3, e4, q1, q2]
    rfl
  rw [e1', R.hOut]
  show some _ = some _
  unfold chainF
  rw [chainSh_finSw s a R.hHere G R.hLaid, hs]

/-- **K2.finishBehindQ on shapes.** -/
def finBehindU (x : ChainF) : Option ChainF :=
  (x.1.fin).bind fun a => (a.sw.others[0]?).map fun m => (x.1.setFin { a with mask := some m }, x.2)

theorem finBehind_carries {s s' : S} (h : finishBehindQ s = .ok s') :
    finBehindU (chainF s) = some (chainF s') := by
  obtain ⟨a, m, hh, hm, rfl⟩ := (First.K2.finishBehindQ_iff s s').1 h
  unfold finBehindU
  rw [show (chainF s).1.fin = some (finSh a) from by
    show finOf s.here = _
    rw [hh]
    rfl]
  show (((finSh a).sw.others[0]?).map fun m => _) = _
  rw [show (finSh a).sw.others[0]? = some m from hm]
  obtain ⟨st0, book0, roots0, rowsOwed0, failed0, check0, out0, here0, req0⟩ := s
  cases hh
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.finFront_carries
#print axioms VerifiableInference.Desc.First.Shape.switchE_pos
#print axioms VerifiableInference.Desc.First.Shape.fin_carries
#print axioms VerifiableInference.Desc.First.Shape.finBehind_carries
#print axioms VerifiableInference.Desc.First.Shape.firstBehind_sh
#print axioms VerifiableInference.Desc.First.Shape.headOpen_carries
#print axioms VerifiableInference.Desc.First.Shape.chainSh_finSw
