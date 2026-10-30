-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FamCut.lean: THE ONE CODING's WRITING SIDE AS CODE, AND A FAMILY FOR A RUN, GENERAL IN
  THE INTERFACE L AND THE NUMBER OF BLOCKS K.
ONE TEXT FOR THE CODING: put := cutAll C (Johnson/PV/CutAll.lean), bk := the total code's put behind
  the escape. THREE WAYS TO RUN IT:
  codeRun (fun _ => L) (cutAll C) bk        the string of a block
    (OnBytes/TypedOracleCompiler/Run/PageRun.lean:82): the field «code» of the writing side
  famRunFast (fun _ => L) (cutAll C) bk O   the family for a run (PageRunFast.lean:87;
    famRunFast_eq): it calls put anew at every block that is read
  **famCut P ΦK ΦP R bk O**                 HERE: at a chain query of the key file's or the proof
    file's: the test on what the query holds ONCE, what its calls share ONCE (a record R : RunJ P),
    and a
                                            row's string as BYTES, never as bits; at every other
                                              oracle: famRunFast's own text
  **famCut_eq : famCut … = famRunFast (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk O**: at every oracle
    and query; no premise.
bothOf P ΦK ΦP: the cut of both files at the page P and the tests ΦK, ΦP: keyCutOf | proofCutOf's
  four tests (what MemberOne's bothOne is).
No soundness.


-/
import Johnson.PV.CutAll
import OnBytes.K.Arm.KeyGlue
import OnBytes.K.Arm.ProofGlue
import OnBytes.K.Arm.GuardCut
import OnBytes.TypedOracleCompiler.Run.PageRunFastLaws
import Johnson.RunOne.FamT
import Run.ParserHashProofs

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.Maker.Page Johnson.RunOne
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bitsOfByte bytesToBits bitsToBytes toBytes strOf digS)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- The cut of both files at a page and two tests of fitness. -/
def bothOf (P : PageJ L K) (ΦK : FitJ L .test) (ΦP : FitJ L .onl) : BothCut L K :=
  ⟨P, fun x => fitFb ΦK P.key K x.1 x.2, fitG ΦK P.key, fun x => fitFb ΦP P.proof K x.1 x.2,
    fitG ΦP P.proof⟩

/-- The bytes that are hashed at a block of a row: the call's own string where the query fits and
  the call lies in the domain; else the escape's. -/
def rowBytes (fit : Bool) (oc : Option Fmt.OQ) (esc : Unit → List Bool) : ByteArray :=
  match oc with
  | some c => if fit && callIn c && inDom c then strOf c else toBytes (bitsOfByte 2 ++ esc ())
  | none => toBytes (bitsOfByte 2 ++ esc ())

/-- In the domain a call's string, as bits and back, is itself. -/
theorem toBytes_str (c : Fmt.OQ) (h : inDom c = true) : toBytes (bytesToBits (strOf c)) = strOf c :=
    by
  have hh : c.half = 0 ∨ c.half = 1 := by
    unfold inDom at h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h
    exact h.1.imp (fun e => eq_of_beq e) fun e => eq_of_beq e
  have hp : _root_.Run.plainB (bytesToBits (strOf c)) = true :=
    _root_.Run.plain_oStr c.half c.number c.tree c.index c.start c.bytes hh
  rw [_root_.Run.toBytes_plain _ hp]
  exact _root_.Run.bitsToBytes_bytesToBits _

/-- **The step**: the bytes of a row's block are the bytes of the string that the cut's text gives.
  -/
theorem rowBytes_eq (fit : Bool) (oc : Option Fmt.OQ) (esc : Unit → List Bool) :
    rowBytes fit oc esc =
      toBytes (match (if (fit && oc.any callIn) = true then oc else none).bind bitsOf with
        | some s => s
        | none => bitsOfByte 2 ++ esc ()) := by
  cases oc with
  | none => cases fit <;> rfl
  | some c =>
    cases fit with
    | false => rfl
    | true =>
      cases hc : callIn c with
      | false => simp [rowBytes, hc]
      | true =>
        cases hd : inDom c with
        | false => simp [rowBytes, hc, hd, bitsOf]
        | true => simp [rowBytes, hc, hd, bitsOf, toBytes_str c hd]

variable (P : PageJ L K) (ΦK : FitJ L .test) (ΦP : FitJ L .onl) (R : RunJ P)
  (bk : AllPts 256 K L → List Bool) (O : ByteArray → ByteArray)

/-- **The answer to a typed query as data.** -/
def famCutB : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → Array (Thunk ByteArray)
  | .fb .test, q =>
    let fit := fitPart ΦK q.round q.rt q.plain q.head
    let c := R.key q
    PageRun.thunksOf (K + 1) fun j =>
      match P.seeds (q, j) with
      | some s => O (toBytes s)
      | none => O (rowBytes fit (c.call K j) fun _ => bk (.inl (fbPt .test q j)))
  | .fb .onl, q =>
    let fit := fitPart ΦP q.round q.rt q.plain q.head
    let c := R.proof q
    PageRun.thunksOf (K + 1) fun j => O (rowBytes fit (c.call K j) fun _ => bk (.inl (fbPt .onl q
        j)))
  | o, q => famRunB (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk O o q

/-- **The typed oracle functions, for a run.** -/
def famCut : Fam (typedOracleFamily 256 K L) := fun o q => decRun K o (famCutB P ΦK ΦP R bk O o q)

/-- The data are famRunB's (OnBytes/TypedOracleCompiler/Run/PageRunFast.lean). -/
theorem famCutB_eq (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 L o) :
    famCutB P ΦK ΦP R bk O o q = famRunB (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk O o q := by
  cases o with
  | fb t =>
    cases t with
    | test =>
      show PageRun.thunksOf (K + 1) _ = PageRun.thunksOf (K + 1) _
      congr 1
      funext j
      show (match P.seeds (q, j) with
        | some s => O (toBytes s)
        | none => O (rowBytes (fitPart ΦK q.round q.rt q.plain q.head) ((R.key q).call K j)
            fun _ => bk (.inl (fbPt .test q j)))) =
        O (toBytes (match (match P.seeds (q, j) with
            | some s => some s
            | none => (if (fitPart ΦK q.round q.rt q.plain q.head &&
                (fbCallJ P.key K q j).any callIn) = true then fbCallJ P.key K q j else none).bind
                  bitsOf) with
          | some s => s
          | none => bitsOfByte 2 ++ bk (.inl (fbPt .test q j))))
      rw [R.hk, onceJ_call]
      cases P.seeds (q, j) with
      | some s => rfl
      | none => exact congrArg O (rowBytes_eq _ _ _)
    | onl =>
      show PageRun.thunksOf (K + 1) _ = PageRun.thunksOf (K + 1) _
      congr 1
      funext j
      show O (rowBytes (fitPart ΦP q.round q.rt q.plain q.head) ((R.proof q).call K j)
            fun _ => bk (.inl (fbPt .onl q j))) =
        O (toBytes (match (if (fitPart ΦP q.round q.rt q.plain q.head &&
                (fbCallJ P.proof K q j).any callIn) = true then fbCallJ P.proof K q j else
                    none).bind
                  bitsOf with
          | some s => s
          | none => bitsOfByte 2 ++ bk (.inl (fbPt .onl q j))))
      rw [R.hp, onceJ_call]
      exact congrArg O (rowBytes_eq _ _ _)
    | link => rfl
  | _ => rfl

/-- **THE EQUATION: famCut IS THE FAMILY FOR A RUN famRunFast AT put := cutAll.** No premise. -/
theorem famCut_eq :
    famCut P ΦK ΦP R bk O = famRunFast (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk O := by
  funext o q
  show decRun K o _ = decRun K o _
  rw [famCutB_eq]

/-- **AND SO THE FAMILY THAT THE WRITING SIDE READS OUT OF THE HASH FUNCTION gOf O.** -/
theorem famCut_famRun :
    famCut P ΦK ΦP R bk O = famRun (fun _ => L) (cutAll (bothOf P ΦK ΦP)) bk (gOf O) :=
  (famCut_eq P ΦK ΦP R bk O).trans (famRunFast_eq _ _ _ _)

end W4M

#print axioms W4M.rowBytes_eq
#print axioms W4M.famCut_eq
#print axioms W4M.famCut_famRun
