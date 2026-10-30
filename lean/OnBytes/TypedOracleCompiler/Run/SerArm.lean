-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SerArm.lean: serialisers of a plain part of some round, by recursion over a shape
and over the rounds' data of a file with three joined chains; and of a function on the corners of a
cube.

Why. The total code behind the escape (`backP`, OnBytes/TypedOracleCompiler/Run/SerThin.lean) takes, for each of an
interface's three protocols, a serialiser of `PlainPart s A`: the plain part of one of the two components
of the prover message of some round of the shape s under the annotation A
(OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean). A key file's and a proof file's protocol have as many
rounds as their three chains. Their shape is made from lists of rounds' data
(OnBytes/Maker/Whole.lean), so the serialiser is made from the same lists.

 - `serPB s A`: a serialiser of `PlainPart s A`, from `SerA s A` (Iop/SerB.lean): for each round of s a
   serialiser of each of the two components' plain parts;
 - `SerPl s`: for each round of s a serialiser of the round's plain part; `SerPl.lo`, `SerPl.sh`:
   from these, `SerA` under the annotation "all local" and under "only the shared part is sent";
 - `serChains G`: `SerA G.sh G.ann` for the rounds G of a file with three joined chains
   (Compile/Joined/Types.lean);
 - `serPlT C ds`: `SerPl` of the shape of a list of rounds' data with trees
   (OnBytes/Maker/Trees.lean): a round's items, and its nonce where the round has work;
 - `serWhole`: a serialiser of a plain part of some round of `reductionOfWholeFile`'s shape under `annOf`;
 - `cubeEquiv`, `serCube A v`: functions on `Fin v → Bool`, corner by corner; `serOnCube`: functions
   on `(Fin v → Bool) × Fin n`.

Main definitions: `serPB`, `SerPl`, `serChains`, `serPlT`, `serWhole`, `serCube`, `serOnCube`.

Not claimed. What the strings are: any total one-to-one code serves behind the escape. Nothing was
evaluated. Nothing on soundness. No theorem is stated: the laws of a serialiser are fields of `Ser`.


-/
import OnBytes.TypedOracleCompiler.Run.PageESer
import OnBytes.Maker.Whole
import Iop.SerB

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SerArm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open OnBytes.Maker _root_.Compile.Joined

/-! ## Over a shape -/

/-- **A serialiser of a plain part of some round**, from serialisers of the two components' plain
parts round by round. The text of the library's `serPB` (Compile/Batch/Ser.lean), at this folder's
`PlainPart`. -/
def serPB : (s : Shape) → (A : RoundSplits s) → SerA s A → Ser (PlainPart s A)
  | [], _, _ => Ser.empty
  | _ :: s, (_, A), ((a, b), e) => Ser.sum (Ser.sum a b) (serPB s A e)

/-- For each round a serialiser of the round's plain part. -/
def SerPl : Shape → Type
  | [] => Unit
  | r :: s => Ser r.Plain × SerPl s

/-- Local rounds only: the shared component's plain part is the one element of Unit. -/
def SerPl.lo : (s : Shape) → SerPl s → SerA s (RoundSplits.allLocal s)
  | [], _ => ()
  | _ :: s, (d, D) => ((Ser.unit, d), SerPl.lo s D)

/-- Only the shared part is sent: a slot's plain part is the one element of Unit. -/
def SerPl.sh : (s : Shape) → SerPl s → SerA s (RoundSplits.const (RAnn.ofShared .sh) s)
  | [], _ => ()
  | _ :: s, (d, D) => ((d, Ser.unit), SerPl.sh s D)

/-! ## Over a file with three joined chains -/

/-- The rounds of a file: the front and chain 1 local, the joining round by its own annotation,
chain 2 shared, the seam and chain 3 local. -/
def serChains (G : Chains) (sF : Ser G.rF.Plain) (S₁ : SerPl G.s₁)
    (sJ : Ser G.aJ.P0 × Ser G.aJ.Pj) (S₂ : SerPl G.s₂) (s3 : Ser G.r3.Plain) (S₃ : SerPl G.s₃) :
    SerA G.sh G.ann :=
  ((Ser.unit, sF), SerA.app (SerPl.lo G.s₁ S₁)
    (B := G.annJ) (sJ, SerA.app (SerPl.sh G.s₂ S₂) (SerPl.lo G.sh₃ (s3, S₃))))

/-- The rounds of a chain, from their data: a round's items, and its nonce where it has work. -/
def serPlT (C : CK) : (ds : List RDT) → SerPl (uLT C ds)
  | [] => ()
  | d :: ds => (serG (serPl d.items) d.entry.work, serPlT C ds)

/-- **A serialiser of a plain part of some round of a whole file's protocol.** sF, sJ, s3: of what
the front round, the joining round and the seam send. -/
def serWhole (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) (sF : Ser TF)
    (sJ : Ser TJ) (s3 : Ser T3) :
    Ser (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :=
  serPB _ _ (serChains (chainsOf C D tF tJ t3) sF (serPlT C D.ds₁) (sJ, Ser.unit)
    (serPlT C D.ds₂) s3 (serPlT C D.ds₃))

/-! ## Functions on the corners of a cube -/

/-- A function on the one corner of the cube of dimension 0 as its value. -/
def cubeZero (α : Type) : ((Fin 0 → Bool) → α) ≃ α where
  toFun := fun f => f Fin.elim0
  invFun := fun a _ => a
  left_inv := fun f => funext fun _ => congrArg f (funext fun i => i.elim0)
  right_inv := fun _ => rfl

/-- A function on the corners of a cube as its two halves: first coordinate false, then true. -/
def cubeEquiv (α : Type) (v : ℕ) :
    ((Fin (v + 1) → Bool) → α) ≃ ((Fin v → Bool) → α) × ((Fin v → Bool) → α) where
  toFun := fun f => (fun g => f (Fin.cons false g), fun g => f (Fin.cons true g))
  invFun := fun p h => if h 0 then p.2 (Fin.tail h) else p.1 (Fin.tail h)
  left_inv := fun f => funext fun h => by
    cases e : h 0
    · simp only [e, Bool.false_eq_true, if_false]
      rw [← e, Fin.cons_self_tail]
    · simp only [e, if_true]
      rw [← e, Fin.cons_self_tail]
  right_inv := fun p => by
    refine Prod.ext (funext fun g => ?_) (funext fun g => ?_)
    · simp only [Fin.cons_zero, Bool.false_eq_true, if_false, Fin.tail_cons]
    · simp only [Fin.cons_zero, if_true, Fin.tail_cons]

/-- Functions on `Fin v → Bool`, corner by corner. -/
def serCube {α : Type} (A : Ser α) : (v : ℕ) → Ser ((Fin v → Bool) → α)
  | 0 => Ser.ofEquiv (cubeZero α) A
  | v + 1 => Ser.ofEquiv (cubeEquiv α v) (Ser.prod (serCube A v) (serCube A v))

/-- Functions on `(Fin v → Bool) × Fin n`. -/
def serOnCube {α : Type} (A : Ser α) (v n : ℕ) : Ser ((Fin v → Bool) × Fin n → α) :=
  Ser.ofEquiv (Equiv.curry (Fin v → Bool) (Fin n) α) (serCube (PageESer.serVec A n) v)

end TypedOracleCompiler.Run.SerArm
