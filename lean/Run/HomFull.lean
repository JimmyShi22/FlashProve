-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HomFull.lean: a morphism of monads passes through the reader that hashes the opened leaves and
walks, and through the parser that fills whole paths.

The reader and the parser of Run/ParseFull.lean are written over any monad, with the hash as their
first argument. A morphism of monads φ (Run/Hom.lean) carries the definition at h to the same
definition at φ ∘ h (`φ.on h`). So the parser as a tree of oracle queries and the parser as a
function are one definition, read in two monads. The file is a companion of Run/HomLax.lean (the
lenient reader), which it uses.

1. What the file contains. The lemmas `Hom.fullOpens`, `Hom.fullWhole`, `Hom.parseFullW`, one for
the definition of each name.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `hom_full` (statement `Run.Spec.hom_full`): for every morphism φ and every hash h:
      φ.app (fullWhole h S b) = fullWhole (φ.on h) S b, and
      φ.app (parseFullW h S T b) = parseFullW (φ.on h) S T b.

4. What is not claimed. Nothing on what the parser's output is; see Run/ParseFull.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.HomLax
import Run.ParseFull

set_option autoImplicit false

namespace Run

open Iop Compile.Batch in
def Spec.hom_full : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
      (S : _root_.Fmt.Spec) (b : ByteArray),
    φ.app (fullWhole h S b) = fullWhole (φ.on h) S b ∧
    ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (T : Typing Q),
      φ.app (parseFullW h S T b) = parseFullW (φ.on h) S T b

namespace Hom
variable {m n : Type → Type}
  [Monad m] [Monad n] (φ : Hom m n) (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
open _root_.Fmt (Plan Spec Shape Src)

theorem fullOpens (cfg : ByteArray) (P : Plan) (b : ByteArray) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) :
    ∀ (os : List (Shape × Src)) (i : Nat), φ.app (Run.fullOpens h cfg P b run roots poss os i) =
      Run.fullOpens (φ.on h) cfg P b run roots poss os i
  | [], _ => φ.app_pure _
  | (sh, src) :: os, i => by
    unfold Run.fullOpens
    simp only []
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, readOpeningW]
      refine congrArg _ (funext fun q => ?_)
      cases q with
      | none => exact φ.app_pure _
      | some o =>
        simp only [φ.app_bind, fullOpens cfg P b run roots poss os]
        refine congrArg _ (funext fun q => ?_)
        cases q <;> exact φ.app_pure _

theorem fullWhole (S : Spec) (b : ByteArray) :
    φ.app (Run.fullWhole h S b) = Run.fullWhole (φ.on h) S b := by
  unfold Run.fullWhole
  rw [cutWhole]
  refine congrArg (fun ops => Run.cutWhole (φ.on h) ops S b)
    (funext fun b' =>
      funext fun run => funext fun roots => funext fun poss => funext fun os => funext fun i => ?_)
  exact fullOpens φ h S.cfg S.plan b' run roots poss os i

open Iop Compile.Batch in
theorem parseFullW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) :
    φ.app (Run.parseFullW h S T b) = Run.parseFullW (φ.on h) S T b := by
  simp only [Run.parseFullW, φ.app_bind, φ.app_pure, fullWhole]

end Hom

theorem hom_full : Spec.hom_full := fun _ _ _ _ φ h S b =>
  ⟨φ.fullWhole h S b, fun _ _ _ T => φ.parseFullW h S T b⟩

end Run
