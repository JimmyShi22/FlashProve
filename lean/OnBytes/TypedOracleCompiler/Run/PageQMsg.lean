-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageQMsg.lean: A PROVER's MESSAGE OF A ROUND AS A PARTIAL CODE OF (THE LIST OF ITS
ROOTS, TYPED PLAIN PART). After the library's Run/PageQMsg.lean, declaration for declaration.
THE LIBRARY's FILE STANDS ON NO DECLARATION OF THE ROAD: IT TURNS BY MATTER.
Its RootOf l (one digest for each item "root"), msgBits, eqR, eqP, pMsg, pMsg_len, word0 ARE GENERAL
IN THE NUMBER OF ROOTS ALREADY and are taken from it as they stand. What refused two roots was the
passage from the typed query's "root or none" to RootOf l: toRoots, ofRoots. Said anew here, on
lists: toRoots, ofRoots, their two laws, rtTo, rtOf, their two laws, pMsgO, pMsgO_len, pRound,
pRound_len: twelve declarations.

Terms: lean/GLOSSARY.md.

-/
import Run.PageQMsg

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Iop _root_.Run _root_.Run.PQ
open _root_.Fmt (Item)

/-- the list of a query's roots as RootOf l: as many as l has items "root", in order; else none -/
def toRoots : (l : List Item) → List (Dig 256) → Option (RootOf l)
  | [], [] => some ()
  | [], _ :: _ => none
  | .root :: l, r :: rt => (toRoots l rt).map fun y => ((r, y) : Dig 256 × RootOf l)
  | .root :: _, [] => none
  | .f :: l, rt => toRoots l rt
  | .word :: l, rt => toRoots l rt
  | .e :: l, rt => toRoots l rt
  | .answer :: l, rt => toRoots l rt

def ofRoots : (l : List Item) → RootOf l → Option (List (Dig 256))
  | [], _ => some []
  | .root :: l, (y : Dig 256 × RootOf l) => (ofRoots l y.2).map fun rt => y.1 :: rt
  | .f :: l, y => ofRoots l y
  | .word :: l, y => ofRoots l y
  | .e :: l, y => ofRoots l y
  | .answer :: l, y => ofRoots l y

theorem ofRoots_toRoots :
    ∀ (l : List Item) (rt : List (Dig 256)) (y : RootOf l),
      toRoots l rt = some y → ofRoots l y = some rt
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | .root :: l, r :: rt, y, h => by
      have h0 : (toRoots l rt).map (fun y => ((r, y) : Dig 256 × RootOf l)) = some y := h
      cases hy : toRoots l rt with
      | none => rw [hy] at h0; cases h0
      | some y' =>
          rw [hy] at h0
          rw [← Option.some.inj h0]
          show (ofRoots l y').map (fun rt => r :: rt) = some (r :: rt)
          rw [ofRoots_toRoots l rt y' hy]
          rfl
  | .root :: _, [], _, h => by cases h
  | .f :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .word :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .e :: l, rt, y, h => ofRoots_toRoots l rt y h
  | .answer :: l, rt, y, h => ofRoots_toRoots l rt y h

theorem toRoots_ofRoots :
    ∀ (l : List Item) (y : RootOf l) (rt : List (Dig 256)),
      ofRoots l y = some rt → toRoots l rt = some y
  | [], _, rt, h => by
      rw [← Option.some.inj h]
      rfl
  | .root :: l, (y : Dig 256 × RootOf l), rt, h => by
      have h0 : (ofRoots l y.2).map (fun rt => y.1 :: rt) = some rt := h
      cases hy : ofRoots l y.2 with
      | none => rw [hy] at h0; cases h0
      | some o =>
          rw [hy] at h0
          rw [← Option.some.inj h0]
          show (toRoots l o).map (fun z => ((y.1, z) : Dig 256 × RootOf l)) = some y
          rw [toRoots_ofRoots l y.2 o hy]
          rfl
  | .f :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .word :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .e :: l, y, rt, h => toRoots_ofRoots l y rt h
  | .answer :: l, y, rt, h => toRoots_ofRoots l y rt h

def rtTo (l : List Item) (x : List (Dig 256) × PlainOf l) : Option (RootOf l × PlainOf l) :=
  (toRoots l x.1).map fun y => (y, x.2)

def rtOf (l : List Item) (y : RootOf l × PlainOf l) : Option (List (Dig 256) × PlainOf l) :=
  (ofRoots l y.1).map fun rt => (rt, y.2)

theorem rtOf_rtTo (l : List Item) (x : List (Dig 256) × PlainOf l)
    (y : RootOf l × PlainOf l) (h : rtTo l x = some y) : rtOf l y = some x := by
  unfold rtTo at h
  unfold rtOf
  cases hr : toRoots l x.1 with
  | none => rw [hr] at h; cases h
  | some r =>
      rw [hr] at h
      rw [← Option.some.inj h]
      show (ofRoots l r).map (fun rt => (rt, x.2)) = some x
      rw [ofRoots_toRoots l x.1 r hr]
      rfl

theorem rtTo_rtOf (l : List Item) (y : RootOf l × PlainOf l)
    (x : List (Dig 256) × PlainOf l) (h : rtOf l y = some x) : rtTo l x = some y := by
  unfold rtOf at h
  unfold rtTo
  cases hr : ofRoots l y.1 with
  | none => rw [hr] at h; cases h
  | some rt =>
      rw [hr] at h
      rw [← Option.some.inj h]
      show (toRoots l rt).map (fun z => (z, y.2)) = some y
      rw [toRoots_ofRoots l y.1 rt hr]
      rfl

/-- the message, on the list of its roots -/
def pMsgO (l : List Item) : PCode (List (Dig 256) × PlainOf l) :=
  (pMsg l).1.pull (rtTo l) (rtOf l) (rtOf_rtTo l) (rtTo_rtOf l)

theorem pMsgO_len (l : List Item) : (pMsgO l).Len (msgBits l) :=
  PCode.pull_len _ _ _ _ _ _ (pMsg_len l)

/-- The message and then the nonce's word. -/
def pRound : (w : ℕ) → (l : List Item) → PCode (List (Dig 256) × GPlain ℕ w (PlainOf l))
  | 0, l =>
    ((pMsgO l).cons (msgBits l) (pMsgO_len l) fun _ => pUnit word0).congr
      ⟨fun x => x.1, fun y => (y, ()), fun _ => rfl, fun _ => rfl⟩
  | _ + 1, l =>
    ((pMsgO l).cons (msgBits l) (pMsgO_len l) fun _ => pWord).congr ⟨fun x =>
        (x.1.1, ((x.1.2, x.2) : PlainOf l × ℕ)),
      fun y => ((y.1, (show PlainOf l × ℕ from y.2).1), (show PlainOf l × ℕ from y.2).2),
      fun _ => rfl, fun _ => rfl⟩

theorem pRound_len : ∀ (w : ℕ) (l : List Item), (pRound w l).Len (msgBits l + 64)
  | 0, _ => PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pUnit_len word0)
  | _ + 1, _ => PCode.congr_len _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pWord_len)

/-- TWO: a message with two items "root" is written: both roots at their places. -/
example (r1 r2 : Dig 256) :
    toRoots [.root, .word, .root] [r1, r2] = some ((r1, (r2, ())) : Dig 256 × (Dig 256 × Unit)) :=
        rfl

end TypedOracleCompiler.Run.PQ
