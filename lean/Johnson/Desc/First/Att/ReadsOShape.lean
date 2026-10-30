-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/ReadsOShape.lean: THE STEP WITHOUT A ROUND BEHIND THE SENDING OF THE READS,
AT AN ATTENTION LINK (readsAtSO, Johnson/Desc/First/Att/ReadsO.lean), AS ONE STEP ON THE SHAPE OF
THE STATE THAT THE FIRST CHAIN CARRIES (Johnson/Desc/First/Shape/Chain.lean). General laws: nothing
is evaluated.

  tabsAt          THE TABLES THAT THE STEP MAKES AT A STATE: a function with code of the plan and
                  the state: of what the link's own rounds heard, what the lookup returned and the
                  ledger, by the step's own two makers (ptsFrom, tablesP).
  attG            THE STEP: of the shapes of the tables that are made, and the state's shape. It
                  reads where the chain stands, the shape of the smallness test's record, the shape
                  of the link's context and the statement's shape; it turns the shape of the
                  smallness test's record and the tables' shapes.
  readsStepO_closed, readsStepO_none, chainSh_attLaid   the step on data behind its makers; where a
                  maker refuses; the two fields laid, seen through the shape.
  **att_sh**      the decision, seen through the shape, IS the step at the shapes of tabsAt's
                  tables: it says yes just where the step returns, and then the shape behind is what
                  the step returns. One equation, at every state; no premise.

Limits. THE STEP's FIRST ARGUMENT IS READ OFF THE STATE, NOT OFF ITS SHAPE: that tabsAt returns, and
that its tables' shapes hang on the state's shape alone, is not shown here. So this is no step on
the shape alone. Whether the two makers test a value is not said here. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Att.ReadsO
import Johnson.Desc.K8.ReadsQuietShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K8.ReadsQuiet (closed closedSh closed_sh closeSh)

/-- **The tables that the step makes at a state**: of what the link's own rounds heard, what the
lookup returned and the ledger. Nothing where one of these is not laid, where the chain stands in no
attention link, or where one of the two makers refuses. -/
def tabsAt (A : Attention.Plan) (s : First.S) : Option Attention.Tables :=
  match s.here with
  | .att a =>
    s.heard5?.bind fun h => a.g.bind fun g =>
      (P.ptsFrom (P.parCOf A).geo g.zk h a.F).bind fun p =>
        (P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
          (P.lookOfO (P.parCOf A).geo.lmb g) p).map tabsBack
  | _ => none

/-- **THE STEP ON THE CHAIN's SHAPE, at an attention link.** funs: the shapes of the tables that are
made. -/
def attG (funs : Option (List FunSh)) (a : ChainSh) : Option ChainSh :=
  if a.here != 2 then none else
  match funs, a.tl, a.link with
  | some fs, some t, some L =>
    (closedSh t fs L a.core.st).map fun t' => (a.setTl t').layTables (some fs)
  | _, _, _ => none

/-- The step on data behind its two makers: the list is closed and the tests are asked. -/
theorem readsStepO_closed (c : P.ParC) (zk : Array (Array E)) (look : P.LookIn) (h : P.Heard)
    (tl : HTailF2) (L : LinkCtx) (S : Statement) (F : Fork) {p : P.Pts} {t : P.TablesP}
    (hp : P.ptsFrom c.geo zk h F = some p) (ht : P.tablesP c.geo c.mats c.nW look p = some t) :
    (readsStepO c zk look h tl L S F).toOption =
      (closed tl (tabsBack t).funs L S).toOption.map fun tl' => (tabsBack t, tl', F.next) := by
  unfold readsStepO closed
  rw [hp]
  show ((do
    need "A.reads.open" (!tl.funClosed)
    let t ← named "A.reads.tables" (P.tablesP c.geo c.mats c.nW look p)
    let tl' ← K8.Order.close tl (tabsBack t).funs
    K8.Order.front tl' L S
    pure (tabsBack t, tl', F.next) : Except String _).toOption) = _
  rw [ht]
  cases hc : tl.funClosed with
  | true =>
    have e : K8.Order.close tl (tabsBack t).funs =
        .error "the smallness test: the list of tables was closed already" := by
      unfold K8.Order.close
      rw [hc]
      rfl
    rw [e]
    rfl
  | false =>
    show ((do
      let tl' ← K8.Order.close tl (tabsBack t).funs
      K8.Order.front tl' L S
      pure (tabsBack t, tl', F.next) : Except String _).toOption) = _
    cases K8.Order.close tl (tabsBack t).funs with
    | error e => rfl
    | ok tl' =>
      show ((do
        K8.Order.front tl' L S
        pure (tabsBack t, tl', F.next) : Except String _).toOption) =
        ((do K8.Order.front tl' L S; pure tl' : Except String HTailF2).toOption.map fun tl' =>
          (tabsBack t, tl', F.next))
      cases K8.Order.front tl' L S <;> rfl

/-- Where a maker refuses the step on data refuses. -/
theorem readsStepO_none (c : P.ParC) (zk : Array (Array E)) (look : P.LookIn) (h : P.Heard)
    (tl : HTailF2) (L : LinkCtx) (S : Statement) (F : Fork)
    (hn : ((P.ptsFrom c.geo zk h F).bind fun p => P.tablesP c.geo c.mats c.nW look p) = none) :
    (readsStepO c zk look h tl L S F).toOption = none := by
  unfold readsStepO
  cases tl.funClosed with
  | true => rfl
  | false =>
    cases hp : P.ptsFrom c.geo zk h F with
    | none => rfl
    | some p =>
      rw [hp] at hn
      have ht : P.tablesP c.geo c.mats c.nW look p = none := hn
      show ((do
        let t ← named "A.reads.tables" (P.tablesP c.geo c.mats c.nW look p)
        let tl' ← K8.Order.close tl (tabsBack t).funs
        K8.Order.front tl' L S
        pure (tabsBack t, tl', F.next) : Except String _).toOption) = none
      rw [ht]
      rfl

/-- The tables and the smallness test's record laid at an attention link, seen through the shape. -/
theorem chainSh_attLaid (s : First.S) (a : First.AttOwn) (hh : s.here = .att a)
    (t : Attention.Tables) (tl : HTailF2) :
    chainSh { s with here := .att { a with t := some t, tl := tl } } =
      ((chainSh s).setTl (tailSh tl)).layTables (some (t.funs.toList.map funSh)) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .att a := hh
  rfl

/-- **The decision at an attention link is the step on the shape**, at the shapes of the tables that
are made at the state: it says yes just where the step returns, and then the state's shape behind is
what the step returns. -/
theorem att_sh (A : Attention.Plan) (s : First.S) :
    ((readsAtSO A s).toOption.map chainSh) =
      attG ((tabsAt A s).map fun t => t.funs.toList.map funSh) (chainSh s) := by
  unfold attG
  cases hh : s.here with
  | att a =>
    have h1 : (chainSh s).here = 2 := by
      show hereNo s.here = 2
      rw [hh]
      rfl
    have h2 : (chainSh s).tl = some (tailSh a.tl) := by
      show s.tl?.map tailSh = _
      unfold First.S.tl?
      rw [hh]
      rfl
    have h3 : (chainSh s).link = some (linkSh a.L) := by
      show s.link?.map linkSh = _
      unfold First.S.link?
      rw [hh]
      rfl
    have h4 : (chainSh s).core.st = Ground.Sh.stSh s.st := rfl
    have h5 : s.heard5? = a.heard5 := by
      unfold First.S.heard5?
      rw [hh]
    obtain ⟨f, hf⟩ : ∃ f : Attention.Tables → HTailF2 → First.S,
        f = fun t tl => { s with here := .att { a with t := some t, tl := tl } } := ⟨_, rfl⟩
    have key : ∀ t tl, chainSh (f t tl) =
        ((chainSh s).setTl (tailSh tl)).layTables (some (t.funs.toList.map funSh)) := fun t tl => by
      rw [hf]
      exact chainSh_attLaid s a hh t tl
    have hd : readsAtSO A s = (do
        let h ← named "A.reads.heard" a.heard5
        let g ← named "A.reads.look" a.g
        let r ← readsStepO (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L s.st a.F
        pure (f r.1 r.2.1)) := by
      rw [hf]
      unfold readsAtSO
      dsimp only
      rw [hh, h5]
    have htb : tabsAt A s = a.heard5.bind fun h => a.g.bind fun g =>
        (P.ptsFrom (P.parCOf A).geo g.zk h a.F).bind fun p =>
          (P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
            (P.lookOfO (P.parCOf A).geo.lmb g) p).map tabsBack := by
      unfold tabsAt
      rw [hh, h5]
    rw [h1, h2, h3, h4, if_neg (by decide), hd, htb]
    cases a.heard5 with
    | none => rfl
    | some h =>
      cases a.g with
      | none => rfl
      | some g =>
        show (((readsStepO (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L s.st
          a.F).bind fun r => (pure (f r.1 r.2.1) : Except String First.S)).toOption.map chainSh) = _
        simp only [Option.bind_some]
        cases hp : P.ptsFrom (P.parCOf A).geo g.zk h a.F with
        | none =>
          have e := readsStepO_none (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L
            s.st a.F (by rw [hp]; rfl)
          cases hr : readsStepO (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L
              s.st a.F with
          | error _ => rfl
          | ok r =>
            rw [hr] at e
            cases e
        | some p =>
          simp only [Option.bind_some]
          cases ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
              (P.lookOfO (P.parCOf A).geo.lmb g) p with
          | none =>
            have e := readsStepO_none (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl
              a.L s.st a.F (by rw [hp]; exact ht)
            cases hr : readsStepO (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L
                s.st a.F with
            | error _ => rfl
            | ok r =>
              rw [hr] at e
              cases e
          | some t =>
            have e := readsStepO_closed (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl
              a.L s.st a.F hp ht
            have hc := closed_sh a.tl (tabsBack t).funs a.L s.st
            show _ = (closedSh (tailSh a.tl) ((tabsBack t).funs.toList.map funSh) (linkSh a.L)
              (Ground.Sh.stSh s.st)).map fun t' =>
                ((chainSh s).setTl t').layTables (some ((tabsBack t).funs.toList.map funSh))
            rw [← hc]
            cases hr : readsStepO (P.parCOf A) g.zk (P.lookOfO (P.parCOf A).geo.lmb g) h a.tl a.L
                s.st a.F with
            | error x =>
              rw [hr] at e
              cases hcl : closed a.tl (tabsBack t).funs a.L s.st with
              | error _ => rfl
              | ok tl' =>
                rw [hcl] at e
                cases e
            | ok r =>
              rw [hr] at e
              cases hcl : closed a.tl (tabsBack t).funs a.L s.st with
              | error _ =>
                rw [hcl] at e
                cases e
              | ok tl' =>
                rw [hcl] at e
                obtain rfl : r = (tabsBack t, tl', a.F.next) := Option.some.inj e
                exact congrArg some (key (tabsBack t) tl')
  | _ =>
    have h1 : ((chainSh s).here != 2) = true := by
      show (hereNo s.here != 2) = true
      rw [hh]
      simp only [hereNo]
      first | rfl | (split <;> rfl)
    rw [if_pos h1]
    unfold readsAtSO
    dsimp only
    rw [hh]
    rfl

end VerifiableInference.Desc.First.Att

#print axioms VerifiableInference.Desc.First.Att.readsStepO_closed
#print axioms VerifiableInference.Desc.First.Att.readsStepO_none
#print axioms VerifiableInference.Desc.First.Att.chainSh_attLaid
#print axioms VerifiableInference.Desc.First.Att.att_sh
