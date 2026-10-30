-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Made/LinksReturn.lean: **THE 25 SUB-PROOFS' PLANS RETURN**: of the planner's
second half: the four premises a₁ to a₄ of shapesOf_of_parts (Johnson/AtFull/Made/Ledger.lean):
linksOf · headLast · linksCount · declareLinks return, AND AT WHICH VALUES, FROM WHAT THE FOUR
ROUTINES READ OF X. Definitions, and statements with their proofs.

  viewsFull           the 25 links' views (Johnson/AtFull/Made/DeclView.lean: LV) at the full size,
                      as the evaluator printed them off the verifier's own publicOf at the stored
                      files.
  small               the 25 small links with these views.
  small_views · small_head · small_count · small_decl · small_rest
                      [Lean's kernel] at the small links the three routines return; declareLinks at
                      the two values that are written already (Johnson/AtFull/Made/LinksFull.lean:
                      viewFull's fourth parts · declaredFull).
  head_bend · gid_bend · name_bend · owner_bend · width_bend · value_bend
                      [Lean's kernel] the tests can fail: two heads · one identifier twice · an
                      array without a name · an owner out of range · a foreign array of another
                      width · one column more (it returns, at another declaration).
  links_return        **the join.**

How. a₁: the three «…PlanOf» copy fields and lay the check as a closure; listLinksH has one need, on
two sizes: the library's listLinksH_returns (OnBytes/Flat/CoveredJoin.lean). What it returns is
listedOf X (OnBytes/TieK/LinksAll.lean: linksOf_listed). a₂ a₃ a₄: equal views, equal returns
(DeclView.lean), then the kernel's facts. fv · gid · ns stay over declareLinks (the library's
declareLinks_keeps, OnBytes/TieK/LinksEnd.lean).
Premises, all on X's own fields: hN : X.NGr = 12 · h4 : X.p4 = true · hG : X.G.size = 12 ·
hA : X.A.size = 12 · hV : (listedOf X default).map viewL = viewsFull. NONE IS PAID HERE: that X's
view is the written one is owed by whoever shows that publicOf returns.
Limits. Of X nothing is shown. The check of no sub-proof is applied. No soundness is claimed. No
example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth.
-/
import Johnson.AtFull.Made.DeclView
import Johnson.AtFull.Made.LinksFull
import OnBytes.Flat.CoveredJoin
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made.Decl
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ## The 25 written views, and the kernel at the small links -/

/-- **The 25 links' views at the full size**, as the evaluator printed them off the verifier's own
publicOf at the stored files. -/
def viewsFull : List LV := [
  ⟨"G0", 0, 1, true, 4059, 33, #[0, 1, 2, 3, 4, 5, 8], #[6, 7], #[], #[1, 2, 3, 4, 5, 6, 7], #[8,
    9], #[], [none, none, some 0, none], 10, 11, #[1, 2, 3, 4, 5, 6, 8, 9, 7], #[3, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1], #[(1, 407626), (21846, 5990), (21846, 5990), (21846, 5990), (10923, 3200),
    (2731, 324), (21846, 256), (21846, 400), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048)]⟩,
  ⟨"A0", 1, 14, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 0, some 7)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G1", 0, 2, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 0, some 8)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A1", 1, 15, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 1, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G2", 0, 3, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 1, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A2", 1, 16, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 2, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G3", 0, 4, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 2, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A3", 1, 17, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 3, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G4", 0, 5, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 3, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A4", 1, 18, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 4, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G5", 0, 6, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 4, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A5", 1, 19, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 5, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G6", 0, 7, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 5, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A6", 1, 20, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 6, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G7", 0, 8, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 6, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A7", 1, 21, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 7, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G8", 0, 9, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 7, some 7)], #[1, 2, 3, 4, 5,
    6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A8", 1, 22, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 8, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G9", 0, 10, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 8, some 7)], #[1, 2, 3, 4,
    5, 6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A9", 1, 23, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 9, some 6)], #[1, 2, 3, 4], #[], #[7],
    [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1, 60640),
    (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048), (21846,
    1536)]⟩,
  ⟨"G10", 0, 11, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 9, some 7)], #[1, 2, 3, 4,
    5, 6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A10", 1, 24, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 10, some 6)], #[1, 2, 3, 4], #[],
    #[7], [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1,
    60640), (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048),
    (21846, 1536)]⟩,
  ⟨"G11", 0, 12, true, 4058, 32, #[0, 1, 2, 3, 4, 5], #[6, 7], #[(some 10, some 7)], #[1, 2, 3, 4,
    5, 6], #[7, 8], #[11], [none, none, some 0, none], 9, 10, #[1, 2, 3, 4, 5, 6, 7, 8, 11], #[3,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], #[(1, 407226), (21846, 5990), (21846, 5990), (21846, 5990),
    (10923, 3200), (2731, 324), (21846, 256), (21846, 1536), (21846, 400), (128, 999424), (32,
    2048), (21846, 400)]⟩,
  ⟨"A11", 1, 25, false, 4190, 0, #[0, 1, 2, 3], #[], #[(some 11, some 6)], #[1, 2, 3, 4], #[],
    #[7], [none, none, some 0, none], 5, 6, #[1, 2, 3, 4, 7], #[3, 1, 1, 1, 1, 1, 1, 1], #[(1,
    60640), (21846, 7200), (2731, 360), (21846, 640), (5462, 512), (128, 442368), (32, 2048),
    (21846, 1536)]⟩,
  ⟨"H", 2, 13, true, 3570, 1, #[0, 1, 2, 3, 4, 5, 6], #[], #[(some 11, some 7)], #[1, 2, 3, 4, 5,
    6, 7], #[], #[10], [none, none, some 0, none], 8, 9, #[1, 2, 3, 4, 5, 6, 7, 10], #[3, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1], #[(1, 61680), (21846, 4816), (21846, 4816), (21846, 4816), (21846,
    4816), (5462, 640), (2731, 15), (10923, 384), (128, 770048), (32, 2048), (21846, 400)]⟩]

/-- The 25 small links. -/
def small : Array LinkH := (viewsFull.map ofView).toArray

def okU : Except String Unit → Bool
  | .ok _ => true
  | .error _ => false

theorem ok_of_okU {r : Except String Unit} (h : okU r = true) : r = .ok () := by
  cases r with
  | ok u => rfl
  | error e => cases h

/-- What is kept of declareLinks' return: the arrays' names link by link, and the declarations. -/
def projD (r : Except String (Array LinkH × Array FrameLink)) :
    Option (Array (Array (Nat × String)) × Array FrameLink) :=
  match r with
  | .ok x => some (x.1.map (·.arrayOf), x.2)
  | .error _ => none

theorem small_views : small.map viewL = viewsFull.toArray := by decide +kernel

theorem small_head : okU (headLast small) = true := by decide +kernel

theorem small_count : okU (linksCount small) = true := by decide +kernel

/-- **By the kernel: declareLinks returns at the small links, at the two written values.** -/
theorem small_decl : projD (declareLinks small 12 true) =
    some ((Johnson.AtFull.Made.viewFull.map (·.2.2.2)).toArray,
      Johnson.AtFull.Made.declaredFull) := by
  decide +kernel

theorem small_rest : viewsFull.map (fun v => (v.fv, v.gid, v.ns)) =
    Johnson.AtFull.Made.viewFull.map fun w => (w.1, w.2.1, w.2.2.1) := by decide +kernel

/-! ### The tests can fail -/

/-- The views with number i turned by f. -/
def bent (i : Nat) (f : LV → LV) : Array LinkH :=
  ((viewsFull.zipIdx.map fun x => if x.2 = i then f x.1 else x.1).map ofView).toArray

/-- Two heads. -/
theorem head_bend : okU (headLast (bent 3 fun v => { v with kind := 2 })) = false := by
  decide +kernel

/-- One identifier twice. -/
theorem gid_bend : okU (headLast (bent 3 fun v => { v with gid := 1 })) = false := by decide +kernel

/-- An array more in a link's list: it gets no name. -/
theorem name_bend :
    (projD (declareLinks (bent 0 fun v => { v with nt := v.nt.push 1 }) 12 true)).isSome =
      false := by
  decide +kernel

/-- A foreign matrix's owner out of range. -/
theorem owner_bend :
    (projD (declareLinks (bent 1 fun v => { v with plFor := #[(some 12, some 7)] }) 12
      true)).isSome = false := by
  decide +kernel

/-- A foreign array of another width than its owner's. -/
theorem width_bend : (projD (declareLinks (bent 1 fun v =>
    { v with trees := v.trees.set! 7 (21846, 1537) }) 12 true)).isSome = false := by decide +kernel

/-- One column more in an own array: it returns, at another declaration. -/
theorem value_bend : (projD (declareLinks (bent 0 fun v =>
    { v with trees := v.trees.set! 0 (1, 407627) }) 12 true)).map (·.2) ≠
    some Johnson.AtFull.Made.declaredFull := by decide +kernel

/-! ## The join -/

theorem views_zip : ∀ (l : List LinkH) (w : List Johnson.AtFull.Made.LinkView),
    l.map (fun X => (X.fv, X.gid, X.ns)) = w.map (fun w => (w.1, w.2.1, w.2.2.1)) →
    l.map (·.arrayOf) = w.map (·.2.2.2) → l.map Johnson.AtFull.Made.viewOf = w
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | X :: l, (a, b, c, d) :: w, h, k => by
    have h1 : (X.fv, X.gid, X.ns) = (a, b, c) := (List.cons.inj h).1
    have k1 : X.arrayOf = d := (List.cons.inj k).1
    have e : Johnson.AtFull.Made.viewOf X = (a, b, c, d) := by
      show (X.fv, X.gid, X.ns, X.arrayOf) = (a, b, c, d)
      have f1 : X.fv = a := congrArg Prod.fst h1
      have f2 : X.gid = b := congrArg (fun z => z.2.1) h1
      have f3 : X.ns = c := congrArg (fun z => z.2.2) h1
      rw [f1, f2, f3, k1]
    show Johnson.AtFull.Made.viewOf X :: l.map Johnson.AtFull.Made.viewOf = (a, b, c, d) :: w
    rw [e, views_zip l w (List.cons.inj h).2 (List.cons.inj k).2]

/-- **THE 25 SUB-PROOFS' PLANS RETURN**: the four premises a₁ to a₄ of shapesOf_of_parts
(Johnson/AtFull/Made/Ledger.lean), with what the steps behind read of their values, from what the
four routines read of X. -/
theorem links_return {X : Verify.Public} (hN : X.NGr = 12) (h4 : X.p4 = true) (hG : X.G.size = 12)
    (hA : X.A.size = 12) (hV : (OnBytes.TieK.listedOf X default).map viewL = viewsFull) :
    ∃ links₀ links, Verify.linksOf X default = .ok links₀ ∧ headLast links₀ = .ok () ∧
      linksCount links₀ = .ok () ∧
      declareLinks links₀ X.NGr X.p4 = .ok (links, Johnson.AtFull.Made.declaredFull) ∧
      links.toList.map Johnson.AtFull.Made.viewOf = Johnson.AtFull.Made.viewFull ∧
      links.toList.map (·.gid) = Johnson.AtFull.Made.idsFull := by
  obtain ⟨links₀, a₁⟩ : ∃ ls, Verify.linksOf X default = .ok ls := by
    unfold Verify.linksOf
    exact OnBytes.Flat.listLinksH_returns _ (by rw [Array.size_mapIdx, hG, hN])
      (fun _ => by rw [Array.size_map, hA, hN])
  have hl := OnBytes.TieK.linksOf_listed a₁
  have hvl : links₀.toList.map viewL = viewsFull := by rw [hl]; exact hV
  have hv : links₀.map viewL = small.map viewL := by
    rw [small_views]
    apply Array.toList_inj.1
    rw [Array.toList_map]
    exact hvl
  have a₂ : headLast links₀ = .ok () := (headLast_view hv).trans (ok_of_okU small_head)
  have a₃ : linksCount links₀ = .ok () := (linksCount_view hv).trans (ok_of_okU small_count)
  have hd := declareLinks_view hv 12 true
  have hs := small_decl
  cases e : declareLinks small 12 true with
  | error x =>
    rw [e] at hs
    cases hs
  | ok r =>
    rw [e] at hs hd
    have hs' : (r.1.map (·.arrayOf), r.2) =
        ((Johnson.AtFull.Made.viewFull.map (·.2.2.2)).toArray, Johnson.AtFull.Made.declaredFull) :=
      Option.some.inj hs
    cases e0 : declareLinks links₀ 12 true with
    | error x =>
      rw [e0] at hd
      cases hd
    | ok r0 =>
      rw [e0] at hd
      have hd' : (r0.1.map (·.arrayOf), r0.2) = (r.1.map (·.arrayOf), r.2) := Except.ok.inj hd
      have t := hd'.trans hs'
      have t1 : r0.1.map (·.arrayOf) = (Johnson.AtFull.Made.viewFull.map (·.2.2.2)).toArray :=
        congrArg Prod.fst t
      have t2 : r0.2 = Johnson.AtFull.Made.declaredFull := congrArg Prod.snd t
      have keep := OnBytes.TieK.declareLinks_keeps (fun X : LinkH => (X.fv, X.gid, X.ns))
        (fun _ _ => rfl) e0
      have g3 : r0.1.toList.map (fun X : LinkH => (X.fv, X.gid, X.ns)) =
          Johnson.AtFull.Made.viewFull.map fun w => (w.1, w.2.1, w.2.2.1) := by
        rw [keep, ← small_rest, ← hvl, List.map_map]
        rfl
      have g4 : r0.1.toList.map (·.arrayOf) = Johnson.AtFull.Made.viewFull.map (·.2.2.2) := by
        have z := congrArg Array.toList t1
        rw [Array.toList_map] at z
        exact z
      have hview := views_zip _ _ g3 g4
      refine ⟨links₀, r0.1, a₁, a₂, a₃, ?_, hview, ?_⟩
      · rw [hN, h4, e0, ← t2]
      · show r0.1.toList.map (·.gid) = Johnson.AtFull.Made.viewFull.map (·.2.1)
        rw [← hview, List.map_map]
        rfl

end Johnson.AtFull.Made.Decl

#print axioms Johnson.AtFull.Made.Decl.ok_of_okU
#print axioms Johnson.AtFull.Made.Decl.small_views
#print axioms Johnson.AtFull.Made.Decl.small_head
#print axioms Johnson.AtFull.Made.Decl.small_count
#print axioms Johnson.AtFull.Made.Decl.small_decl
#print axioms Johnson.AtFull.Made.Decl.small_rest
#print axioms Johnson.AtFull.Made.Decl.head_bend
#print axioms Johnson.AtFull.Made.Decl.gid_bend
#print axioms Johnson.AtFull.Made.Decl.name_bend
#print axioms Johnson.AtFull.Made.Decl.owner_bend
#print axioms Johnson.AtFull.Made.Decl.width_bend
#print axioms Johnson.AtFull.Made.Decl.value_bend
#print axioms Johnson.AtFull.Made.Decl.views_zip
#print axioms Johnson.AtFull.Made.Decl.links_return
