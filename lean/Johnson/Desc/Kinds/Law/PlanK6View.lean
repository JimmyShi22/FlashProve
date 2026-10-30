-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6View.lean: the cheap test planK6C (Law/PlanK6ByBlocks.lean) reads
little of its large arguments: it equals the light test planK6Door
(Johnson/Desc/Kinds/PlanK6Door.lean, no Mathlib) at plain arguments read off the large ones. So
acceptance by the light test implies PlanK6's four clauses. Two definitions and theorems.

Why. planK6C takes the verifier's public part (Verify.Public), the table of numbers, the list of
typed oracle messages, the codes and the request's layout, and its file imports Mathlib. An entry of
the verifier's list of public tests must have light imports. Also, at fixed public files the large
arguments are large terms: Lean's kernel cannot compute them from the files (tried: it runs out of
memory).

What is proved.
  plainOf msR     of each typed oracle message: its shape and its (tree, tenant).
viewOf cs arr msR N Wp lay6 num   the View (Johnson/Desc/Kinds/PlanK6Test.lean) of these arguments:
viewPlain at what is read off them.
  planK6C_eq      planK6C cs arr msR N Wp lay6 num n rb = planK6V (viewOf cs arr msR N Wp lay6 num)
          n rb, for all arguments.
  planK6C_door    the same with planK6Door written out.
  planK6_of_door  under Meaning.laidThere Wp (sizesOf Wp) lay6 = true: acceptance by planK6Door at
          the plain arguments implies the four clauses named, seats, maskNamed, maskIn of PlanK6
          (Law/K6Cut.lean).

No existential quantifier in these statements.
Not proved here. The View of any particular public files. Meaning.laidThere. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6ByBlocks
import Johnson.Desc.Kinds.PlanK6Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqArray ReqLayout)
open OnBytes.Model.Verify (borderOf)
open Johnson.Pack (pMain pMask)
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem seatOf numOf namedOnce)

/-- Of each typed oracle message: its shape and its (tree, tenant). -/
def plainOf (msR : List Mem) : List (OnBytes.OracleShape × (ℕ × ℕ)) :=
  msR.map fun y => ((y.1.l.get y.2).1, seatOf y)

variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- What the test reads of its arguments. -/
def viewOf : View :=
  viewPlain cs lay6 (Meaning.sizesOf Wp 24).NM Wp.hS.NHf Wp.H.ns (Meaning.labAt Wp 24) num arr
    (N.group 24) (N.sent 24 0) (plainOf msR)

/-- What it reads of a typed oracle message. -/
abbrev memV (y : Mem) : MemV :=
  memP cs arr (N.group 24) (N.sent 24 0) ((y.1.l.get y.2).1, seatOf y)

theorem owner_eq (lab : ℕ) :
    ownerP lab = (Meaning.ownerK lab, Meaning.nameOf (Meaning.ownerA lab)) := rfl

theorem once_eq (k : ℕ) :
    namedOnce arr N 24 k = onceV (viewOf cs arr msR N Wp lay6 num) k := by
  unfold namedOnce onceV viewOf viewPlain
  dsimp only
  rw [List.filter_map, List.length_map]
  rfl

theorem copy_eq (k : ℕ) (ok : OnBytes.OracleShape → Bool) (okV : MemV → Bool)
    (h : ∀ y : Mem, ok (y.1.l.get y.2).1 = okV (memV cs arr N y)) :
    copyIn arr msR N k ok = copyV (viewOf cs arr msR N Wp lay6 num) k okV := by
  unfold copyIn copyV viewOf viewPlain plainOf
  dsimp only
  rw [List.map_map, List.any_map, List.all_map]
  have e1 : ∀ y : Mem, Decidable.decide (seatOf y ∈ N.group 24) = (memV cs arr N y).inGroup :=
    fun y => (List.contains_eq_mem _ _).symm
  have e2 : ∀ y : Mem, Decidable.decide (seatOf y ∈ N.sent 24 0) = (memV cs arr N y).atZero :=
    fun y => (List.contains_eq_mem _ _).symm
  congr 1
  · refine congrArg (fun f => msR.any f) (funext fun y => ?_)
    rw [e1 y]
    rfl
  · refine congrArg (fun f => msR.all f) (funext fun y => ?_)
    rw [e1 y, e2 y, h y]
    rfl

theorem inside_eq (k : ℕ) (A : ReqArray) (y : Mem) :
    insideB cs (y.1.l.get y.2).1 A = insideV (arrV num k A) (memV cs arr N y) := by
  unfold insideB insideV arrV
  dsimp only
  rw [List.all_map]
  rfl

theorem mat_eq (a : ℕ) :
    matC cs arr msR N Wp lay6 num a =
      matV (viewOf cs arr msR N Wp lay6 num)
        ((arrayOfD lay6 (ownerP (Meaning.labAt Wp 24 a)).1 (ownerP (Meaning.labAt Wp 24 a)).2).map
          (arrV num (ownerP (Meaning.labAt Wp 24 a)).1)) := by
  unfold matC
  rw [owner_eq]
  dsimp only
  cases arrayOfD lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => rfl
  | some A =>
    show (namedOnce arr N 24 _ && copyIn arr msR N _ _) = (onceV _ _ && copyV _ _ _)
    rw [once_eq cs arr msR N Wp lay6 num,
      copy_eq cs arr msR N Wp lay6 num _ _ _ fun y => inside_eq cs arr N num _ A y]
    rfl

/-- **The test is a function of the View.** -/
theorem planK6C_eq (n rb : ℕ) :
    planK6C cs arr msR N Wp lay6 num n rb = planK6V (viewOf cs arr msR N Wp lay6 num) n rb := by
  unfold planK6C planK6V
  rw [once_eq cs arr msR N Wp lay6 num n,
    copy_eq cs arr msR N Wp lay6 num n (maskOk cs Wp.H.ns rb)
      (maskV (viewOf cs arr msR N Wp lay6 num).ns rb) fun _ => rfl]
  congr 2
  show _ = ((List.range (Meaning.sizesOf Wp 24).NM).map _).all _
  rw [List.all_map]
  refine congrArg (fun f => (List.range (Meaning.sizesOf Wp 24).NM).all f) (funext fun a => ?_)
  rw [mat_eq cs arr msR N Wp lay6 num a]
  rfl

/-- The same with the light test written out. -/
theorem planK6C_door (n rb : ℕ) :
    planK6C cs arr msR N Wp lay6 num n rb =
      planK6Door cs lay6 (Meaning.sizesOf Wp 24).NM Wp.hS.NHf Wp.H.ns (Meaning.labAt Wp 24) num arr
        (N.group 24) (N.sent 24 0) (plainOf msR) n rb :=
  planK6C_eq cs arr msR N Wp lay6 num n rb

/-- **Acceptance by the light test implies PlanK6's four clauses.** -/
theorem planK6_of_door (n rb : ℕ) (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (h : planK6Door cs lay6 (Meaning.sizesOf Wp 24).NM Wp.hS.NHf Wp.H.ns (Meaning.labAt Wp 24) num
      arr (N.group 24) (N.sent 24 0) (plainOf msR) n rb = true) :
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      InCopy cs arr (ms0 msR N) msR N 24 (seatLay Wp lay6 num 24 μ r c).1 false
        (seatLay Wp lay6 num 24 μ r c).2.1 (seatLay Wp lay6 num 24 μ r c).2.2) ∧
    (∀ j, j < Wp.H.ns → namedOnce arr N 24 (plAt n rb j).1 = true) ∧
    (∀ j, j < Wp.H.ns → InCopy cs arr (ms0 msR N) msR N 24 (plAt n rb j).1
      (plAt n rb j).2.1 (plAt n rb j).2.2.1 (plAt n rb j).2.2.2) :=
  planK6_of_C cs arr msR N Wp lay6 num n rb T
    ((planK6C_door cs arr msR N Wp lay6 num n rb).trans h)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6C_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_of_door
