-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Later.lean: THE PARTS OF A COMMITMENT (a segment's later moment, the kind
K1) ON SHAPES: the later moment around its sending, and the marks of the arrays that are committed
to. Each part and its step on the shape commute. General laws; nothing is evaluated.

  1 `LinkSh.blank`, `linkSh_blank`: the way back for a link's context. `laidHere_blank`,
    `momentsDue_blank`, `atMoment_blank`: three of the library's readers see the shape alone: by
    rfl.
  2 `laterG`, **`laterOwn_sh`**: K1.laterOwn (Johnson/Desc/K1/Own.lean) behind its sending's
    return: the walk's and the frame's tests, the joinings on the core, the new state of the calls.
  3 `hereB`, `commitOneG`, **`commitOne_sh`**, `commitAllG`,
    **`commitAll_sh`**: L3.commitOne (Johnson/Top/H0/L3/Frame.lean), one array and all, ON THE
    LEDGER's SHAPE: equations: the array has no root yet and is laid here; its mark is set (LedSh
    sees each array's mark: Parts.lean's rooted, setRootedAt, ledSh_taken).

Limits. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Joining
import Johnson.Desc.K1.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState GPar groundG)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)

/-! ## 1 The way back for a link's context -/

def LinkSh.blank (L : LinkSh) : LinkCtx :=
  { check := L.check.blank, link := L.link, arrayOf := L.arrayOf, list := L.list
    moments := L.moments, handed := L.handed, done := L.done }

theorem linkSh_blank (L : LinkSh) : linkSh L.blank = L := by
  cases L
  simp [linkSh, LinkSh.blank, checkSh_blank]

theorem laidHere_blank (L : LinkCtx) : L3.laidHere (linkSh L).blank = L3.laidHere L := rfl
theorem momentsDue_blank (c : ChainCheck) : (checkSh c).blank.momentsDue = c.momentsDue := rfl
theorem atMoment_blank (f : ReqFrame) (m : Nat) : (frameSh f).blank.atMoment m = f.atMoment m := rfl

/-! ## 2 A segment's later moment around the sending -/

/-- K1.laterOwn behind its sending, on shapes. c: the calls' state in front; h: the core BEHIND the
sending. -/
def laterG (P : K1.Par) (n0 : Nat) (c : CheckSh) (h : CoreSh) : Option (CheckSh × CoreSh) :=
  if !(c.inLink && decide (c.moments < c.blank.momentsDue)) then none else
  match c.frame.shape.link[c.frame.link]? with
  | none => none
  | some Lk =>
    if !(c.frame.next == .laterOrClose && decide (c.frame.moment < reqMoments Lk)) then none else
    if (c.frame.blank.atMoment c.frame.moment).length == (idsAt P n0).size then
      (joinAllS c.frame.group (zipT (c.frame.blank.atMoment c.frame.moment) (idsAt P n0).toList)
        h).map fun h' =>
        ({ c with
            frame := { c.frame with moment := c.frame.moment + 1, own := c.frame.own ++ idsAt P n0 }
            sent := idsAt P n0, moments := c.moments + 1 }, h')
    else none

theorem laterOwn_sh (P : K1.Par) (owed : Option Nat) (c : ChainCheck) (w d₁ : DState Unit)
    (rs : List Fmt.RoundView) (n0 : Nat) (hs : K1.decideSend P owed w rs = .ok (idsAt P n0, d₁)) :
    (K1.laterOwn P owed c w rs).toOption.map (fun y => (checkSh y.1, coreSh (coreOf y.2))) =
      laterG P n0 (checkSh c) (coreSh (coreOf d₁)) := by
  unfold K1.laterOwn laterG
  show _ = (if !(c.inLink && decide (c.moments < c.momentsDue)) then none else
    match c.frame.shape.link[c.frame.link]? with
    | none => none
    | some Lk =>
      if !(c.frame.next == .laterOrClose && decide (c.frame.moment < reqMoments Lk)) then none else
      if (c.frame.atMoment c.frame.moment).length == (idsAt P n0).size then
        (joinAllS c.frame.group (zipT (c.frame.atMoment c.frame.moment) (idsAt P n0).toList)
          (coreSh (coreOf d₁))).map fun h' =>
          (checkSh { c with
            frame := { c.frame with moment := c.frame.moment + 1, own := c.frame.own ++ idsAt P n0 }
            sent := idsAt P n0, moments := c.moments + 1 }, h')
      else none)
  by_cases g1 : (!(c.inLink && decide (c.moments < c.momentsDue))) = true
  · simp only [g1, if_true]
    rfl
  · simp only [g1, Bool.false_eq_true, if_false]
    cases hL : c.frame.shape.link[c.frame.link]? with
    | none => rfl
    | some Lk =>
      simp only []
      by_cases g2 : (!(c.frame.next == .laterOrClose &&
          decide (c.frame.moment < reqMoments Lk))) = true
      · simp only [g2, if_true]
        rfl
      · simp only [g2, Bool.false_eq_true, if_false, hs]
        unfold Send.joinOwnP
        by_cases g3 : ((c.frame.atMoment c.frame.moment).length == (idsAt P n0).size) = true
        · simp only [g3, if_true]
          rw [← joinAll_core P.gp]
          cases Send.joinAll groundG P.gp c.frame.group
            (zipT (c.frame.atMoment c.frame.moment) (idsAt P n0).toList) d₁ <;> rfl
        · simp only [g3, Bool.false_eq_true, if_false]
          rfl

/-! ## 3 The arrays of a commitment -/

/-- Array t was born at this link, and the layout lays it at the link's present moment. -/
def hereB (arrayOf : Array (Nat × String)) (link : Nat) (laid : List (String × Nat)) (t : Nat) :
    Bool :=
  match arrayOf[t]? with
  | some (born, name) => born == link && laid.any fun a => a.1 == name
  | none => false

/-- L3.commitOne on the ledger's shape: the array has no root yet and is laid here: its mark is
set. -/
def commitOneG (L : LinkSh) (Ld : LedSh) (t : Nat) : Option LedSh :=
  if !((Ld.rooted[t]?).getD true) && hereB L.arrayOf L.link (L3.laidHere L.blank) t then
    some (Ld.setRootedAt t)
  else none

theorem commitOne_sh (L : LinkCtx) (F : Fork) (t : Nat) :
    (L3.commitOne L F t).toOption.map ledSh = commitOneG (linkSh L) (ledSh F) t := by
  have hc : ((F.trees[t]?).map (·.root.isSome)).getD true = (((ledSh F).rooted)[t]?).getD true := by
    rw [rooted_ledSh]
    simp
  have hl : L3.commitOne L F t =
      if !(((F.trees[t]?).map (·.root.isSome)).getD true) &&
          hereB L.arrayOf L.link (L3.laidHere L) t then .ok (F.rootTaken t 0)
      else .error s!"plan-link: array {t}" := rfl
  have hg : commitOneG (linkSh L) (ledSh F) t =
      if !((((ledSh F).rooted)[t]?).getD true) && hereB L.arrayOf L.link (L3.laidHere L) t then
        some ((ledSh F).setRootedAt t)
      else none := rfl
  rw [hl, hg, hc]
  split
  · show some (ledSh (F.rootTaken t 0)) = _
    rw [ledSh_taken]
  · rfl

/-- The arrays of one commitment, one after the other. -/
def commitAllG (L : LinkSh) : List Nat → LedSh → Option LedSh
  | [], Ld => some Ld
  | t :: l, Ld => (commitOneG L Ld t).bind (commitAllG L l)

theorem commitAll_sh (L : LinkCtx) : ∀ (l : List Nat) (F : Fork),
    (l.foldlM (L3.commitOne L) F).toOption.map ledSh = commitAllG (linkSh L) l (ledSh F)
  | [], _ => rfl
  | t :: l, F => by
    rw [List.foldlM_cons]
    have h1 := commitOne_sh L F t
    show _ = (commitOneG (linkSh L) (ledSh F) t).bind _
    rw [← h1]
    cases hF : L3.commitOne L F t with
    | error e => rfl
    | ok G => exact commitAll_sh L l G

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.commitOne_sh
#print axioms VerifiableInference.Desc.First.Shape.commitAll_sh
#print axioms VerifiableInference.Desc.First.Shape.linkSh_blank
#print axioms VerifiableInference.Desc.First.Shape.laterOwn_sh
#print axioms VerifiableInference.Desc.First.Shape.laidHere_blank
#print axioms VerifiableInference.Desc.First.Shape.momentsDue_blank
#print axioms VerifiableInference.Desc.First.Shape.atMoment_blank
