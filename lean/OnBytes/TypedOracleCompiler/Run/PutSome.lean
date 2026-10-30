-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PutSome.lean: what the library's ways of joining partial codes write, as equations:
where the parts write, the joined code writes this string.

The library's laws on `PCode.cons`, `PCode.pre`, `PCode.ins` and `PCode.pull` (library,
Run/CodingSeq.lean, Run/CodingPut.lean) go from a written string to its parts. To say that a code
WRITES at a given point, and what, one needs the other direction.

Main theorems: `cons_some`, `pre_some`, `ins_some`, `pull_some`.

Not claimed. Nothing but these four unfoldings. General in the types; no file of OnBytes is
imported.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPut

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PutSome
open _root_.Run

variable {A B : Type}

/-- What a code of pairs writes, if both parts are written: the first part's string, then the
second's. -/
theorem cons_some (a : PCode A) (n : ℕ) (ha : a.Len n) (p : A → PCode B) (x : A) (y : B)
    (u v : List Bool) (hu : a.put x = some u) (hv : (p x).put y = some v) :
    (a.cons n ha p).put (x, y) = some (u ++ v) := by
  show (a.put x).bind (fun u => ((p x).put y).map (u ++ ·)) = _
  rw [hu, hv]
  rfl

/-- What a code behind a fixed string writes, where the code writes. -/
theorem pre_some (c : List Bool) (p : PCode A) (x : A) (v : List Bool) (hv : p.put x = some v) :
    (PCode.pre c p).put x = some (c ++ v) := by
  show (p.put x).map (c ++ ·) = _
  rw [hv]
  rfl

/-- What a code writes that lays a second string in before the last k bits of a first, if both are
written. -/
theorem ins_some (p : PCode B) (a : PCode A) (k n : ℕ) (ha : a.Len n)
    (hp : ∀ y s, p.put y = some s → k ≤ s.length) (y : B) (x : A) (s w : List Bool)
    (hs : p.put y = some s) (hw : a.put x = some w) :
    (p.ins a k n ha hp).put (y, x) =
      some (s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) := by
  show (p.put y).bind (fun s =>
    (a.put x).map fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) = _
  rw [hs, hw]
  rfl

/-- What a code pulled along two partial maps writes, where the first map gives a value at which the
code writes. -/
theorem pull_some (p : PCode A) (f : B → Option A) (g : A → Option B)
    (h1 : ∀ b a, f b = some a → g a = some b) (h2 : ∀ a b, g a = some b → f b = some a) (b : B)
    (a : A) (s : List Bool) (hf : f b = some a) (hs : p.put a = some s) :
    (p.pull f g h1 h2).put b = some s := by
  show (f b).bind p.put = _
  rw [hf]
  exact hs

end TypedOracleCompiler.Run.PutSome
