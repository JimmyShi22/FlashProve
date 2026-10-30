-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Decl/RequestItemLaw.lean: the port's function for the value of the item "request" in the
statement of a proof file's first chain is the one under Fmt/ at the port's second hash function.

Fmt/RequestItem.lean holds the port's text with the second hash function as an argument. This file
imports both and proves, helper by helper, that each function of the port is the one under Fmt/ at
k := OnBytes.secondHashFunction. Theorems, and one definition (`toReq`).
Main names:
  `requestItem_eq`: for all three files p, s, r:
    OnBytes.Proof.requestItem p s r = Fmt.requestItem OnBytes.secondHashFunction p s r.
  `allOf_map`: the port's allOf on a mapped list is List.mapM in Option.
  `toReq`: the port's lines as the lines under Fmt/. The other theorems are named after the port's
    function of which they speak.
Limits: no theorem here has a hypothesis: each is for all arguments. Nothing about OnBytes.secondHashFunction
itself, or about the C++ programs. The functions under Fmt/ of which these theorems speak are the
ones without a W, that is, at the monad Id.
-/
import OnBytes.Proof.RequestItem
import Fmt.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Decl.RequestItemLaw

open OnBytes OnBytes.Proof

/-! ## All or nothing: the port's walk on a mapped list is List.mapM in Option -/

theorem allOfFrom_map {α β : Type} (f : α → Option β) : ∀ (l : List α) (seen : List β),
    Params.allOfFrom seen (l.map f) = (l.mapM f).map (seen.reverse ++ ·)
  | [], seen => by simp [Params.allOfFrom]
  | a :: l, seen => by
    cases h : f a with
    | none => simp [Params.allOfFrom, List.mapM_cons, h]
    | some b =>
      simp only [List.map_cons, h, Params.allOfFrom, allOfFrom_map f l (b :: seen), List.mapM_cons]
      cases l.mapM f <;> simp

theorem allOf_map {α β : Type} (f : α → Option β) (l : List α) :
    Params.allOf (l.map f) = l.mapM f := by
  simp only [Params.allOf, allOfFrom_map]
  cases l.mapM f <;> simp

/-! ## What stands around the hash -/

theorem word32_eq (x : Nat) : word32 x = Fmt.lowBytes 4 x := rfl

theorem textWords_eq (t : ByteArray) : textWords t = Fmt.textWords t := rfl

theorem olderLevel_eq (num : Nat) (w : ByteArray) :
    secondHashFunctionTreeLevel num w = Id.run (Fmt.olderLevelW (m := Id) secondHashFunction num w) := rfl

theorem olderLevels_eq : ∀ (j num : Nat) (w : ByteArray),
    secondHashFunctionTreeLevels j num w = Id.run (Fmt.olderLevelsW (m := Id) secondHashFunction j num w)
  | 0, _, _ => rfl
  | j + 1, num, w => by
    show (if (secondHashFunctionTreeLevel num w).size == 32 then some (secondHashFunctionTreeLevel num w)
      else secondHashFunctionTreeLevels j 11 (secondHashFunctionTreeLevel num w)) = _
    rw [olderLevels_eq j 11]
    rfl

theorem olderTK_eq (w : ByteArray) : secondHashFunctionTree w = Fmt.olderTK secondHashFunction w := by
  show (if w.size % 4 != 0 || w.size < 32 then none else secondHashFunctionTreeLevels 16 10 w) = _
  rw [olderLevels_eq]
  rfl

/-! ## The lines -/

/-- The port's lines as the type under Fmt/. -/
def toReq (L : ParamLines) : Fmt.ReqLines := ⟨L.lines⟩

theorem splitAt_eq (c : UInt8) (l : List UInt8) : splitAt c l = Fmt.splitAt c l := rfl

theorem read_eq (file : ByteArray) : toReq (ParamLines.read file) = Fmt.ReqLines.read file := rfl

theorem named_eq (L : ParamLines) (name : String) : L.named name = (toReq L).named name := rfl

theorem values_eq (L : ParamLines) (name : String) : L.values name = (toReq L).values name := rfl

theorem number_eq (w : List UInt8) : Params.number w = Fmt.lineNumber w := rfl

theorem number32_eq (w : List UInt8) : number32 w = Fmt.number32 w := rfl

theorem value_eq (L : ParamLines) (name : String) : L.value name = (toReq L).value name := rfl

theorem words_eq (L : ParamLines) (names : String) : L.words names = (toReq L).words names := by
  show (Params.allOf ((names.splitOn " ").map L.value)).map _ = _
  rw [allOf_map]
  rfl

theorem eight_eq (L : ParamLines) (name : String) : L.eight name = (toReq L).eight name := by
  show (Params.allOf ((List.range 8).map fun i => L.value (name ++ toString i))).map _ = _
  rw [allOf_map]
  rfl

theorem text_eq (L : ParamLines) (name : String) : L.text name = (toReq L).text name := rfl

theorem calls_eq (L : ParamLines) (name : String) (ifNone : Option String) :
    L.calls name ifNone = (toReq L).calls secondHashFunction name ifNone := by
  cases ifNone <;> rfl

theorem lastWords_eq (L : ParamLines) : L.lastWords = (toReq L).lastWords := by
  unfold ParamLines.lastWords Fmt.ReqLines.lastWords
  simp only [allOf_map]
  rfl

theorem names_eq : names2 = Fmt.names2 ∧ names37 = Fmt.names37 ∧ names103 = Fmt.names103 ∧
    names130 = Fmt.names130 ∧ callHIfNone = Fmt.callHIfNone := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The item -/

/-- The port's function is the one under Fmt/ at the port's second hash function, on all files. -/
theorem requestItem_eq (parameterFile scaleFile requestFile : ByteArray) :
    requestItem parameterFile scaleFile requestFile =
      Fmt.requestItem secondHashFunction parameterFile scaleFile requestFile := by
  unfold requestItem
  simp only [words_eq, eight_eq, lastWords_eq, calls_eq, olderTK_eq]
  rfl

end OnBytes.Tie.Decl.RequestItemLaw

#print axioms OnBytes.Tie.Decl.RequestItemLaw.allOfFrom_map
#print axioms OnBytes.Tie.Decl.RequestItemLaw.allOf_map
#print axioms OnBytes.Tie.Decl.RequestItemLaw.word32_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.textWords_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.olderLevel_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.olderLevels_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.olderTK_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.splitAt_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.read_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.named_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.values_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.number_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.number32_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.value_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.words_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.eight_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.text_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.calls_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.lastWords_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.names_eq
#print axioms OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq
