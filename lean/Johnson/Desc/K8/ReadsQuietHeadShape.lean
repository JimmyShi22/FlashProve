-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietHeadShape.lean: THE STEP WITHOUT A ROUND BEHIND THE SENDING OF THE READS,
AT THE HEAD's LINK (head, Johnson/Desc/K8/ReadsQuiet.lean), AS ONE STEP ON THE SHAPE OF THE STATE
THAT THE FIRST CHAIN CARRIES (Johnson/Desc/First/Shape/Chain.lean). General laws: nothing is
evaluated. The shape of the head's own fields sees the table of the tables (HeadSh.tab,
Johnson/Desc/First/Shape/HeadPart.lean), so the step lays it too.
  `headTabsAt`: THE TABLES THAT THE STEP MAKES AT A STATE: a function with code of the place's
    parameters and the state: of the covered positions (off the request's words and the heard reply)
    and what the head's own rounds heard, by the step's own maker (tables).
  `tabsSh`: what the chain's shape sees of the tables: the shapes of their parts; the table of the
    tables. `headG`: THE STEP: of the shape of the PLAN's record of the smallness test, what the
    shape sees of the tables that are made, and the state's shape. It reads where the chain stands,
    the shape of the link's context, the statement's shape and the shape of the head's own fields;
    it turns the shape of the smallness test's record, the tables' shapes, and the table of the
    tables.
  `chainSh_headLaid`: the two fields laid at the opened link, seen through the shape.
  **`head_sh`**: the block's decision, seen through the shape, IS the step at tabsSh of headTabsAt's
    tables. One equation, at every state; no premise.
Limits. THE STEP's SECOND ARGUMENT IS READ OFF THE STATE, NOT OFF ITS SHAPE: that headTabsAt
returns, and that what the shape sees of its tables hangs on the state's shape alone, is not shown
here. So this is no step on the shape alone. The covered positions' four tests read the request's
words and the heard reply. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.ReadsQuietShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-- **The tables that the step makes at a state**, at the head's link: of the covered positions (off
the request's words and the heard reply) and what the head's own rounds heard. Nothing where the
link is not opened, where one of these cannot be said or is not laid, or where the maker refuses. -/
def headTabsAt (P : PH) (s : S) : Option Head.Tables :=
  match s.here with
  | .head a =>
    if a.opened then
      (s.covered P.h.T P.h.V).toOption.bind fun cov => a.x.bind fun x =>
        (tables P.h P.L P.hp cov x).toOption
    else none
  | _ => none

/-- What the chain's shape sees of the head's tables: the shapes of the tables' parts; the table of
the tables. -/
def tabsSh (t : Head.Tables) : List FunSh × List (String × Nat × Nat) :=
  (t.funs.toList.map funSh, t.tab)

/-- **THE STEP ON THE CHAIN's SHAPE, at the head's link.** t: the shape of the plan's record of the
smallness test; made: what the shape sees of the tables that are made. -/
def headG (t : TailSh) (made : Option (List FunSh × List (String × Nat × Nat))) (a : ChainSh) :
    Option ChainSh :=
  if a.here != 3 then none else
  match made, a.link, a.head with
  | some m, some L, some h =>
    (closedSh t m.1 L a.core.st).map fun t' =>
      ((a.setTl t').layTables (some m.1)).setHead { h with tab := some m.2 }
  | _, _, _ => none

/-- The tables and the smallness test's record laid at the opened head's link, seen through the
shape. -/
theorem chainSh_headLaid (s : S) (a : First.HeadOwn) (hh : s.here = .head a)
    (ho : a.opened = true) (t : Head.Tables) (tl : HTailF2) :
    chainSh { s with here := .head { a with t := some t, tl := tl } } =
      (((chainSh s).setTl (tailSh tl)).layTables (some (t.funs.toList.map funSh))).setHead
        { headSh a with tab := some t.tab } := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .head a := hh
  simp [chainSh, ChainSh.mk, ChainSh.marked, ChainSh.here, ChainSh.tl, ChainSh.led,
    ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks,
    ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard,
    ChainSh.own, ChainSh.head, ChainSh.att, ChainSh.fin, endSh, hereNo, headOf, headSh, attOf,
        finOf,
    S.tl?, S.fork?,
    S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, ChainSh.setTl, ChainSh.layTables,
    ChainSh.setHead, ho]

/-- **The block's decision at the head's link is the step on the shape**, at the shapes of the
tables that are made at the state. -/
theorem head_sh (P : PH) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((head P).decide s rs gs).toOption.map chainSh) =
      headG (tailSh P.hp.tl) ((headTabsAt P s).map tabsSh) (chainSh s) := by
  unfold headG
  cases hh : s.here with
  | head a =>
    cases ho : a.opened with
    | false =>
      have h1 : ((chainSh s).here != 3) = true := by
        show (hereNo s.here != 3) = true
        rw [hh]
        simp only [hereNo, ho]
        rfl
      rw [if_pos h1]
      unfold head
      dsimp only
      rw [hh]
      dsimp only
      rw [ho]
      rfl
    | true =>
      have h1 : (chainSh s).here = 3 := by
        show hereNo s.here = 3
        rw [hh]
        simp only [hereNo, ho]
        rfl
      have h3 : (chainSh s).link = some (linkSh a.L) := by
        show s.link?.map linkSh = _
        unfold S.link?
        rw [hh]
        dsimp only
        rw [ho]
        rfl
      have h4 : (chainSh s).core.st = Ground.Sh.stSh s.st := rfl
      have h5 : (chainSh s).head = some (headSh a) := by
        show headOf s.here = _
        rw [hh]
        rfl
      obtain ⟨f, hf⟩ : ∃ f : Head.Tables → HTailF2 → S,
          f = fun t tl => { s with here := .head { a with t := some t, tl := tl } } := ⟨_, rfl⟩
      have key : ∀ t tl, chainSh (f t tl) =
          (((chainSh s).setTl (tailSh tl)).layTables (some (t.funs.toList.map funSh))).setHead
            { headSh a with tab := some t.tab } := fun t tl => by
        rw [hf]
        exact chainSh_headLaid s a hh ho t tl
      have hd : (head P).decide s rs gs = (do
          let cov ← under "reads: the covered positions cannot be said" (s.covered P.h.T P.h.V)
          let x ← (a.x.elim (.error "reads: what the head heard is not laid") .ok : Except String _)
          let t ← tables P.h P.L P.hp cov x
          let tl ← closed P.hp.tl t.funs a.L s.st
          pure (f t tl)) := by
        rw [hf]
        unfold head
        dsimp only
        rw [hh]
        dsimp only
        rw [ho]
        rfl
      have htb : headTabsAt P s = (s.covered P.h.T P.h.V).toOption.bind fun cov => a.x.bind fun x =>
          (tables P.h P.L P.hp cov x).toOption := by
        unfold headTabsAt
        rw [hh]
        dsimp only
        rw [ho]
        rfl
      rw [h1, h3, h4, h5, if_neg (by decide), hd, htb]
      cases s.covered P.h.T P.h.V with
      | error e => rfl
      | ok cov =>
        cases a.x with
        | none => rfl
        | some x =>
          have e1 : (do
              let cov ← under "reads: the covered positions cannot be said"
                (Except.ok cov : Except String Head.Covered)
              let x ← ((some x).elim (.error "reads: what the head heard is not laid") .ok :
                Except String _)
              let t ← tables P.h P.L P.hp cov x
              let tl ← closed P.hp.tl t.funs a.L s.st
              pure (f t tl) : Except String S) = (do
              let t ← tables P.h P.L P.hp cov x
              let tl ← closed P.hp.tl t.funs a.L s.st
              pure (f t tl)) := rfl
          have e2 : ((Except.ok cov : Except String Head.Covered).toOption.bind fun cov =>
              (some x).bind fun x => (tables P.h P.L P.hp cov x).toOption) =
              (tables P.h P.L P.hp cov x).toOption := rfl
          rw [e1, e2]
          cases tables P.h P.L P.hp cov x with
          | error e => rfl
          | ok t =>
            have hc := closed_sh P.hp.tl t.funs a.L s.st
            show ((do
              let tl ← closed P.hp.tl t.funs a.L s.st
              pure (f t tl) : Except String S).toOption.map chainSh) =
              (closedSh (tailSh P.hp.tl) (t.funs.toList.map funSh) (linkSh a.L)
                (Ground.Sh.stSh s.st)).map fun t' =>
                  (((chainSh s).setTl t').layTables (some (t.funs.toList.map funSh))).setHead
                    { headSh a with tab := some t.tab }
            rw [← hc]
            cases closed P.hp.tl t.funs a.L s.st with
            | error e => rfl
            | ok tl => exact congrArg some (key t tl)
  | _ =>
    have h1 : ((chainSh s).here != 3) = true := by
      show (hereNo s.here != 3) = true
      rw [hh]
      rfl
    rw [if_pos h1]
    unfold head
    dsimp only
    rw [hh]
    rfl

end VerifiableInference.Desc.K8.ReadsQuiet

#print axioms VerifiableInference.Desc.K8.ReadsQuiet.chainSh_headLaid
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.head_sh
