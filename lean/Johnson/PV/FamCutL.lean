-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FamCutL.lean: THE FAST FAMILY IN A FORM FOR A LONG EVALUATION, AFTER famL
  (Johnson/RunOne/FamL.lean, not in this library; its Cells | cellsOf | Cells.at are said again
  here, so that this file stands on imports in the library's build and this folder's alone).
WHY. A chain keeps every answer to its end. famCut (Johnson/PV/FamCut.lean) lays K + 1 delayed
  values at every chain query, read or not, and the function behind them holds the query (through
  bk's argument), whose plain part is as large as the round's number.
HERE: a chain answer under the key file's or the proof file's tag keeps a delayed hash for as many
  blocks as a hint says, and the last block's; the others stay a function; AND THE ESCAPE's STRING
  IS ONE CONSTANT e (): so under the proof file's tag what is kept
does not hold the query. (Under the key file's tag it does: the seeds' spelling reads it.)
  famCutL P ΦK ΦP R e O mK mP          mK, mP: the hints, by the typed round (Lite.needAt DK | DP)
  **famCutL_eq : famCutL P ΦK ΦP R e O mK mP = famCut P ΦK ΦP R (fun _ => e ()) O**: AT EVERY HINT;
    no premise.
THE PRICE: bk IS A CONSTANT FUNCTION HERE: that is the shouting stub of the rehearsals (it returns
  no bit), NOT a total code: a family of this make at a real bk would have to hold the query.
LIMITS (famL's file's, word for word in sense): a hint is for speed and memory alone; a block at
  or beyond it that is read is hashed anew for every bit that is read. What an evaluator keeps and
  computes how often are facts about the compiler and the run.
No soundness.


-/
import Johnson.PV.FamCut

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bitsOfByte bytesToBits bitsToBytes toBytes strOf digS)

/-- The blocks of a chain answer: the first n and the last delayed; all of them as a function. -/
structure Cells (K : ℕ) where
  n : ℕ
  /-- n delayed values, then the last block's -/
  th : Array (Thunk ByteArray)
  f : Fin (K + 1) → ByteArray

/-- From the blocks as a function: the first min m K and the last are kept. -/
def cellsOf (K m : ℕ) (f : Fin (K + 1) → ByteArray) : Cells K where
  n := min m K
  th := (Array.ofFn (n := min m K) fun j : Fin (min m K) =>
    Thunk.mk fun _ => f ⟨j.val, by have := j.isLt; omega⟩).push (Thunk.mk fun _ => f (Fin.last K))
  f := f

/-- Block j. -/
def Cells.at {K : ℕ} (a : Cells K) (j : Fin (K + 1)) : ByteArray :=
  if j.val = K then getT a.th a.n
  else if j.val < a.n then getT a.th j.val
  else a.f j

theorem cellsOf_at {K : ℕ} (m : ℕ) (f : Fin (K + 1) → ByteArray) (j : Fin (K + 1)) :
    (cellsOf K m f).at j = f j := by
  unfold Cells.at cellsOf getT
  dsimp only
  by_cases hK : j.val = K
  · rw [if_pos hK, Array.getElem?_push, Array.size_ofFn, if_pos rfl]
    show f (Fin.last K) = f j
    rw [show j = Fin.last K from Fin.ext hK]
  · rw [if_neg hK]
    by_cases hm : j.val < min m K
    · rw [if_pos hm, Array.getElem?_push, Array.size_ofFn, if_neg (Nat.ne_of_lt hm),
        Array.getElem?_ofFn, dif_pos hm]
      rfl
    · rw [if_neg hm]

/-- An answer as data. -/
inductive AnsC (K : ℕ)
  | cells (a : Cells K)
  | arr (a : Array (Thunk ByteArray))

/-- The data as a typed answer. -/
def decC (K : ℕ) : (o : TypedOracleCompiler.Compile.Batch.OracleName) → AnsC K → rngOf 256 K o
  | .fb _, .cells a => (fun k => digS (a.at k.castSucc), digS (a.at (Fin.last K)))
  | o, .arr a => decRun K o a
  | o, .cells _ => decRun K o #[]

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}
  (P : PageJ L K) (ΦK : FitJ L .test) (ΦP : FitJ L .onl) (R : RunJ P)
  (e : Unit → List Bool) (O : ByteArray → ByteArray) (mK mP : ℕ → ℕ)

/-- A block of the proof file's row, from data that do not hold the query. -/
def blockP (O : ByteArray → ByteArray) (e : Unit → List Bool) (K : ℕ) (fit : Bool) (c : OnceJ) (j :
    Fin (K + 1)) :
    ByteArray := O (rowBytes fit (c.call K j) e)

/-- **The answer to a typed query as data.** -/
def famCutLB : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → AnsC K
  | .fb .test, q =>
    let fit := fitPart ΦK q.round q.rt q.plain q.head
    let c := R.key q
    .cells (cellsOf K (mK q.round) fun j =>
      match P.seeds (q, j) with
      | some s => O (toBytes s)
      | none => blockP O e K fit c j)
  | .fb .onl, q =>
    .cells (cellsOf K (mP q.round) (blockP O e K (fitPart ΦP q.round q.rt q.plain q.head) (R.proof
        q)))
  | o, q => .arr (famRunB (fun _ => L) (cutAll (bothOf P ΦK ΦP)) (fun _ => e ()) O o q)

/-- **The typed oracle functions, for a long evaluation.** -/
def famCutL : Fam (typedOracleFamily 256 K L) := fun o q => decC K o (famCutLB P ΦK ΦP R e O mK mP o q)

/-- A chain answer decoded from all K + 1 delayed values is the pair of the blocks' digests. -/
theorem decRun_fb (t : Tag) (f : Fin (K + 1) → ByteArray) :
    decRun K (.fb t) (PageRun.thunksOf (K + 1) f) =
      ((fun k : Fin K => digS (f k.castSucc)), digS (f (Fin.last K))) := by
  refine Prod.ext ?_ ?_
  · funext k
    show digS (getT (PageRun.thunksOf (K + 1) f) k.val) = _
    exact congrArg digS (getT_thunksOf (K + 1) f k.castSucc)
  · show digS (getT (PageRun.thunksOf (K + 1) f) K) = _
    exact congrArg digS (getT_thunksOf (K + 1) f (Fin.last K))

/-- And so from the cells, at every hint. -/
theorem decC_fb (t : Tag) (m : ℕ) (f : Fin (K + 1) → ByteArray) :
    decC K (.fb t) (.cells (cellsOf K m f)) =
      ((fun k : Fin K => digS (f k.castSucc)), digS (f (Fin.last K))) := by
  refine Prod.ext ?_ ?_
  · funext k
    show digS ((cellsOf K m f).at k.castSucc) = _
    rw [cellsOf_at]
  · show digS ((cellsOf K m f).at (Fin.last K)) = _
    rw [cellsOf_at]

/-- **THE EQUATION: AT EVERY HINT IT IS famCut AT THE CONSTANT bk.** No premise. -/
theorem famCutL_eq :
    famCutL P ΦK ΦP R e O mK mP = famCut P ΦK ΦP R (fun _ => e ()) O := by
  funext o q
  cases o with
  | fb t =>
    cases t with
    | test =>
      show decC K (.fb .test) (.cells (cellsOf K (mK q.round) _)) =
        decRun K (.fb .test) (PageRun.thunksOf (K + 1) _)
      rw [decC_fb, decRun_fb]
      rfl
    | onl =>
      show decC K (.fb .onl) (.cells (cellsOf K (mP q.round) _)) =
        decRun K (.fb .onl) (PageRun.thunksOf (K + 1) _)
      rw [decC_fb, decRun_fb]
      rfl
    | link => rfl
  | _ => rfl

end W4M

#print axioms W4M.cellsOf_at
#print axioms W4M.famCutL_eq
