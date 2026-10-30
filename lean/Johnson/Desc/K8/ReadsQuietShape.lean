-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietShape.lean: THE STEP WITHOUT A ROUND BEHIND THE SENDING OF THE READS, AT A
LAYERS' LINK (layers, Johnson/Desc/K8/ReadsQuiet.lean), AS ONE STEP ON THE SHAPE OF THE STATE THAT
THE FIRST CHAIN CARRIES (Johnson/Desc/First/Shape/Chain.lean). General laws: nothing is evaluated.

  closeSh, close_sh     the list of tables is closed (Order.close,
                  Johnson/Desc/First/K8/Order.lean), on the shape of the smallness test's record.
  closedSh, closed_sh   the list is closed and the three tests in front of the draw are asked
                  (closed), on shapes: over the law on these tests (front_sh,
                  Johnson/Desc/K8/Honest/OrderShape.lean).
  layersG         THE STEP: of the shape of the PLAN's record of the smallness test at the link, and
                  the state's shape. It reads where the chain stands, the tables' shapes, the shape
                  of the link's context and the statement's shape; it turns the shape of the
                  smallness test's record alone.
  **layers_sh**   the block's decision, seen through the shape, IS the step: it says yes just where
                  the step returns, and then the shape behind is what the step returns. One
                  equation, at every state; no premise.

By layers_sh the decision's verdict is a function of the shape of the plan's record and of the
state's shape: so it reads no field element.
Limits. The head's link's step and an attention link's are not here (ReadsQuietHeadShape.lean;
Johnson/Desc/First/Att/ReadsOShape.lean). The block's test on the plan (planned) is not treated.
Under which name the decision refuses is not said. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Desc.K8.Honest.OrderShape
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Order.close Order.front)
open VerifiableInference.Desc.First.K8.Honest (frontB front_sh)
open VerifiableInference.Desc.First.Shape

/-- The list of tables is closed, on the shape of the smallness test's record. -/
def closeSh (t : TailSh) (funs : List FunSh) : Option TailSh :=
  if t.funClosed then none else some { t with funClosed := true, funs := funs }

theorem close_sh (tl : HTailF2) (funs : Array HFun) :
    ((Order.close tl funs).toOption.map tailSh) = closeSh (tailSh tl) (funs.toList.map funSh) := by
  unfold Order.close closeSh
  have e : (tailSh tl).funClosed = tl.funClosed := rfl
  rw [e]
  cases tl.funClosed <;> rfl

/-- closed (the list is closed; then the three tests in front of the draw), on shapes. -/
def closedSh (t : TailSh) (funs : List FunSh) (L : LinkSh) (st : Ground.Sh.StSh) :
    Option TailSh :=
  (closeSh t funs).bind fun t' => if frontB t' L st then some t' else none

theorem closed_sh (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (st : Statement) :
    ((closed tl funs L st).toOption.map tailSh) =
      closedSh (tailSh tl) (funs.toList.map funSh) (linkSh L) (Ground.Sh.stSh st) := by
  unfold closed closedSh
  rw [← close_sh]
  cases hc : Order.close tl funs with
  | error e => rfl
  | ok tl' =>
    show ((do Order.front tl' L st; pure tl' : Except String HTailF2).toOption.map tailSh) =
      if frontB (tailSh tl') (linkSh L) (Ground.Sh.stSh st) = true then some (tailSh tl') else none
    by_cases hf : frontB (tailSh tl') (linkSh L) (Ground.Sh.stSh st) = true
    · rw [if_pos hf, (front_sh tl' L st).2 hf]
      rfl
    · rw [if_neg hf]
      cases hx : Order.front tl' L st with
      | error e => rfl
      | ok u => exact absurd ((front_sh tl' L st).1 hx) hf

/-- **THE STEP ON THE CHAIN's SHAPE, at a layers' link.** t: the shape of the plan's record of the
smallness test at this link. -/
def layersG (t : TailSh) (a : ChainSh) : Option ChainSh :=
  if a.here != 1 then none else
  match a.tables, a.link with
  | some funs, some L => (closedSh t funs L a.core.st).map a.setTl
  | _, _ => none

/-- **The block's decision at a layers' link is the step on the shape**: it says yes just where the
step returns, and then the state's shape behind is what the step returns. -/
theorem layers_sh (P : PG) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((layers P).decide s rs gs).toOption.map chainSh) = layersG (tailSh P.tl) (chainSh s) := by
  unfold layersG
  cases hh : s.here with
  | lay a =>
    have h1 : (chainSh s).here = 1 := by
      show hereNo s.here = 1
      rw [hh]
      rfl
    have h2 : (chainSh s).tables = a.own.map fun o => o.funs.toList.map funSh := by
      show (s.funs?.map fun x => x.toList.map funSh) = _
      unfold S.funs?
      rw [hh]
      show ((a.own.map (·.funs)).map fun x => x.toList.map funSh) = _
      rw [Option.map_map]
      rfl
    have h3 : (chainSh s).link = some (linkSh a.L) := by
      show s.link?.map linkSh = _
      unfold S.link?
      rw [hh]
      rfl
    have h4 : (chainSh s).core.st = Ground.Sh.stSh s.st := rfl
    obtain ⟨f, hf⟩ : ∃ f : HTailF2 → S, f = fun tl => { s with here := .lay { a with tl := tl } } :=
      ⟨_, rfl⟩
    have key : ∀ tl, chainSh (f tl) = (chainSh s).setTl (tailSh tl) := fun tl => by
      rw [hf, ← chainSh_putTl]
      unfold S.putTl
      rw [hh]
    have hd : (layers P).decide s rs gs = (do
        let own ←
          (a.own.elim (.error "reads: the own rounds' record is not laid") .ok : Except String _)
        let tl ← closed P.tl own.funs a.L s.st
        pure (f tl)) := by
      rw [hf]
      unfold layers
      dsimp only
      rw [hh]
    rw [h1, h2, h3, h4, hd, if_neg (by decide)]
    cases a.own with
    | none => rfl
    | some o =>
      have hc := closed_sh P.tl o.funs a.L s.st
      show ((do
        let tl ← closed P.tl o.funs a.L s.st
        pure (f tl) : Except String S).toOption.map chainSh) =
        (closedSh (tailSh P.tl) (o.funs.toList.map funSh) (linkSh a.L)
          (Ground.Sh.stSh s.st)).map (chainSh s).setTl
      rw [← hc]
      cases closed P.tl o.funs a.L s.st with
      | error e => rfl
      | ok tl => exact congrArg some (key tl)
  | _ =>
    have h1 : ((chainSh s).here != 1) = true := by
      show (hereNo s.here != 1) = true
      rw [hh]
      simp only [hereNo]
      first | rfl | (split <;> rfl)
    rw [if_pos h1]
    unfold layers
    dsimp only
    rw [hh]
    rfl

end VerifiableInference.Desc.K8.ReadsQuiet

#print axioms VerifiableInference.Desc.K8.ReadsQuiet.close_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.closed_sh
#print axioms VerifiableInference.Desc.K8.ReadsQuiet.layers_sh
