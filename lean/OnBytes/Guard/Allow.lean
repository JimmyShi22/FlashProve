-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Lean
/-!
# The guard on compiled code: the rules of Mathlib that are let through unproved

Mathlib's command compile_inductive% writes a function in place of a recursor (the induction
principle that Lean generates for a type, for which Lean's compiler makes no code) and marks the
equation between the two as a rule for the compiler without proving it. The declaration that stands
where the proof should be is not a theorem. Its name is generated (it carries a macro scope), so the
list below names the recursor and the module that declares the rule. The check lets one such rule
through for each pair, and only if the function on the right side is declared in the same module.

How to remake the list. Run the check of Csimp.lean with an empty list on the nine files of Mathlib
(at the commit that this library pins, 5e932f97) whose text holds "compile_inductive%":
Mathlib/Util/CompileInductive.lean, Algebra/Free.lean, Combinatorics/Quiver/Path.lean,
SetTheory/Lists.lean, SetTheory/Ordinal/Notation.lean, Computability/TuringMachine/ToPartrec.lean,
Computability/PartrecCode.lean, Data/Ordmap/Ordnode.lean, Data/Tree/Basic.lean.
It rejects 36 rules, those listed below. They are trusted, not checked. Lean's core and the other
packages have none.

The Lean text verify-on-bytes (this repository builds no stand-alone program from it) imports no
package, and its guard file (Program.lean) does not pass this list to any command. The list is here
for test (b) of #guard_pinned (Cmd.lean), and for a program that imports Mathlib.
-/
set_option autoImplicit false

namespace OnBytes.Guard

/-- The 36 recursors for which Mathlib adds a rule for the compiler without a proof, each with the
module that adds it. -/
def mathlibRecursors : List (Lean.Name × Lean.Name) :=
  ([`And.rec, `Array.rec, `BitVec.rec, `Bool.rec, `ByteArray.rec, `Fin.rec, `Float.rec,
    `Lean.Name.rec, `List.rec, `Option.rec, `PEmpty.rec, `PSum.rec, `PUnit.rec, `Prod.rec,
    `Sigma.rec, `String.rec, `Sum.rec, `UInt16.rec, `UInt32.rec, `UInt64.rec, `UInt8.rec,
    `USize.rec].map fun r => (r, `Mathlib.Util.CompileInductive)) ++
  [(`FreeAddMagma.rec, `Mathlib.Algebra.Free), (`FreeAddSemigroup.rec, `Mathlib.Algebra.Free),
   (`FreeMagma.rec, `Mathlib.Algebra.Free), (`FreeSemigroup.rec, `Mathlib.Algebra.Free),
   (`Lists'.rec, `Mathlib.SetTheory.Lists),
   (`Nat.Partrec.Code.rec, `Mathlib.Computability.PartrecCode),
   (`ONote.rec, `Mathlib.SetTheory.Ordinal.Notation), (`Ordnode.rec, `Mathlib.Data.Ordmap.Ordnode),
   (`Quiver.Path.rec, `Mathlib.Combinatorics.Quiver.Path), (`Tree.rec, `Mathlib.Data.Tree.Basic),
   (`Turing.PartrecToTM2.Cont'.rec, `Mathlib.Computability.TuringMachine.ToPartrec),
   (`Turing.PartrecToTM2.K'.rec, `Mathlib.Computability.TuringMachine.ToPartrec),
   (`Turing.PartrecToTM2.Λ'.rec, `Mathlib.Computability.TuringMachine.ToPartrec),
   (`Turing.ToPartrec.Code.rec, `Mathlib.Computability.TuringMachine.ToPartrec)]

end OnBytes.Guard
