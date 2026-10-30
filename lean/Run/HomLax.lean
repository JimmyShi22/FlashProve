-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HomLax.lean: a morphism of monads passes through the lenient reader of a chain's file and
through the lenient parser.

A statement (`Run.Spec.hom_lax`) and proofs.

Why: Run/HomFmt.lean states the same, and Run/HomFmtProofs.lean proves it, for the functions of the
format's own files (those that are one call of the hash need no statement), up to the strict
reader. Run/ParseLax.lean has a second reader, which cuts the file and leaves the work tests, the
leaves and the walks to the typed verifier (proof of work is tested where the protocol's `accept`
tests it: `Q.loc.accept`); the second reader stands in front of that verifier in a run (what the
lenient reader still asks the hash, what it refuses and what it does not test: part 1 of the head
of Run/ParseLax.lean). The second reader's functions are written over a variable monad too, and
loop by structural recursion alone.

Main names:
  Each function F: φ.app (F h ..) = F (φ.on h) ..; where F takes a reader of openings: .. = F (φ.on
    h) (that reader read through φ) ..
  `laxWhole`, `parseLaxW`: the reader of openings is a value ("parsed only"): nothing is left of φ
    on the right but φ.on h. These two equations are `Spec.hom_lax`.

Limits: this file says nothing on what the functions compute. This file does not say the counts:
Run/CostLax.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.HomFmtProofs
import Run.ParseLax

set_option autoImplicit false

namespace Run

/-- A reader of openings, read through the morphism. -/
abbrev Hom.onOps {m n : Type → Type} [Monad m] [Monad n] (φ : Hom m n) (ops : OpsW m) : OpsW n :=
  fun run roots poss os i => φ.app (ops run roots poss os i)

open Iop Compile.Batch in
/-- States: every morphism of monads passes through the lenient reader and the lenient parser. -/
def Spec.hom_lax : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
      (S : _root_.Fmt.Spec) (b : ByteArray),
    φ.app (laxWhole h S b) = laxWhole (φ.on h) S b ∧
    ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (T : Typing Q),
      φ.app (parseLaxW h S T b) = parseLaxW (φ.on h) S T b

namespace Hom
variable {m n : Type → Type}
  [Monad m] [Monad n] (φ : Hom m n) (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
open _root_.Fmt (Plan Spec St Chain Kind Round)

theorem laxQueryW (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    φ.app (Run.laxQueryW h c msg kind work nonce K) =
      Run.laxQueryW (φ.on h) c msg kind work nonce K := by
  unfold Run.laxQueryW
  split
  · simp only [φ.app_bind, φ.app_pure, fetchW]
  · exact φ.app_pure _

theorem cutStep (ops : OpsW m) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) :
    φ.app (Run.cutStep h ops P run b s r) = Run.cutStep (φ.on h) (φ.onOps ops) P run b s r := by
  unfold Run.cutStep
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, laxQueryW]
        refine congrArg _ (funext fun q => ?_)
        cases q with
        | none => exact φ.app_pure _
        | some cv =>
          simp only []
          split
          · exact φ.app_pure _
          · simp only [φ.app_bind]
            refine congrArg _ (funext fun q => ?_)
            cases q <;> exact φ.app_pure _

theorem cutFold (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      φ.app (Run.cutFold h ops P run b rs s) = Run.cutFold (φ.on h) (φ.onOps ops) P run b rs s
  | [], _ => φ.app_pure _
  | r :: rs, s => by
    simp only [Run.cutFold, φ.app_bind, cutStep]
    refine congrArg _ (funext fun q => ?_)
    cases q with
    | none => exact φ.app_pure _
    | some s' => exact cutFold ops P run b rs s'

theorem cutChain (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) (i : Nat) :
    φ.app (Run.cutChain h ops S b i) = Run.cutChain (φ.on h) (fun b => φ.onOps (ops b)) S b i := by
  unfold Run.cutChain
  split
  · exact φ.app_pure _
  · simp only []
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, startChainW]
      refine congrArg _ (funext fun pd => ?_)
      refine congrArg _ (funext fun q => ?_)
      cases q with
      | none => exact φ.app_pure _
      | some hd =>
        simp only [φ.app_bind, cutFold]
        refine congrArg _ (funext fun q => ?_)
        cases q <;> exact φ.app_pure _

theorem cutWhole (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) :
    φ.app (Run.cutWhole h ops S b) = Run.cutWhole (φ.on h) (fun b => φ.onOps (ops b)) S b := by
  simp only [Run.cutWhole, φ.app_bind, cutChain]
  refine congrArg _ (funext fun q => ?_)
  cases q <;> exact φ.app_pure _

theorem laxWhole (S : Spec) (b : ByteArray) :
    φ.app (Run.laxWhole h S b) = Run.laxWhole (φ.on h) S b := by
  unfold Run.laxWhole
  rw [cutWhole]
  refine congrArg (fun ops => Run.cutWhole (φ.on h) ops S b)
    (funext fun b' =>
      funext fun _ => funext fun roots => funext fun poss => funext fun os => funext fun i => ?_)
  exact φ.app_pure _

open Iop Compile.Batch in
theorem parseLaxW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) :
    φ.app (Run.parseLaxW h S T b) = Run.parseLaxW (φ.on h) S T b := by
  simp only [Run.parseLaxW, φ.app_bind, φ.app_pure, laxWhole]

end Hom

theorem hom_lax : Spec.hom_lax := fun _ _ _ _ φ h S b =>
  ⟨φ.laxWhole h S b, fun _ _ _ T => φ.parseLaxW h S T b⟩

end Run
