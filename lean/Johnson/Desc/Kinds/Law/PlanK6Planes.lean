-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6Planes.lean: the clause "named" of the cheap public test planK6C
(Law/PlanK6ByBlocks.lean) AT ONE MATRIX MORE: the matrix of planes, number NHf + 2 of the output
head's list, which planK6C passes over. A test with code, its theorem, its form on the View, and
Lean's kernel's evaluation at the written View of the full size.

What is proved.
  namedAtC a        the test at matrix number a: the request's layout holds its array, and exactly
          one sampled oracle message of the head's segment has the number of the message that holds
          it.
  **named_of_namedAtC**   under Meaning.laidThere Wp (sizesOf Wp) lay6 = true: where the test
          accepts at a, namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true at every row of
          symbols r and column c of the matrix μ with μ.val = a.
  namedAtV v a      the same test as a function of the View (Johnson/Desc/Kinds/PlanK6Test.lean).
  namedAtC_eq       for a below the list's length: namedAtC a = namedAtV (viewOf ...) a, for all
          arguments.
  viewFull_planes   namedAtV viewFull 6 = true: at the full size NHf + 2 = 6. Lean's kernel
          evaluates it.
  viewFull_planes_no   a negative test: with one more oracle message of the segment numbered 145 it
          rejects.

No existential quantifier in these statements.
Not proved here. Meaning.laidThere. That viewFull is the View of any arguments. Nothing on whether
the matrix's elements lie inside the oracle message (planK6C's clause "seats" is not walked here).
Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6ViewFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqArray ReqLayout)
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem namedOnce)

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- The test at matrix number a of the head's list. -/
def namedAtC (a : ℕ) : Bool :=
  match arrayOfD lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => false
  | some A => namedOnce arr N 24 (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message)

/-- **Where the test accepts, every element of that matrix lies in a message whose number exactly
one oracle message of the head's segment has.** -/
theorem named_of_namedAtC (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true) {a : ℕ}
    (h : namedAtC arr N Wp lay6 num a = true) (μ : Fin (Meaning.sizesOf Wp 24).NM)
    (hμ : μ.val = a) (r c : ℕ) (hr : r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ))
    (hc : c < (Meaning.sizesOf Wp 24).k μ) :
    namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true := by
  subst hμ
  obtain ⟨A, x, hA, -, -, -, hs⟩ :=
    Meaning.seat_of_laidThere T num (by norm_num : 24 < 25) μ hr hc
  unfold namedAtC at h
  rw [hA] at h
  have hs' : seatLay Wp lay6 num 24 μ r c =
      (num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message, x.1, x.2) := hs
  rw [hs']
  exact h

end

/-- The same test as a function of the View. -/
def namedAtV (v : View) (a : Nat) : Bool :=
  match v.arrs.lookup a with
  | some (some A) => onceV v A.num
  | _ => false

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- A list of pairs (a, f a) over a range, looked up below its length. -/
theorem lookup_range {β : Type} (f : ℕ → β) : ∀ (n a : ℕ), a < n →
    ((List.range n).map fun a => (a, f a)).lookup a = some (f a) := by
  intro n a ha
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.lookup_append]
    by_cases h : a < n
    · rw [ih h]
      rfl
    · obtain rfl : a = n := by omega
      have : ((List.range a).map fun a => (a, f a)).lookup a = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
        have hb' := List.mem_range.1 hb
        have hne : a ≠ b := by omega
        simpa using hne
      rw [this]
      simp

theorem namedAtC_eq {a : ℕ} (ha : a < (Meaning.sizesOf Wp 24).NM) :
    namedAtC arr N Wp lay6 num a = namedAtV (viewOf cs arr msR N Wp lay6 num) a := by
  unfold namedAtC namedAtV
  have e : (viewOf cs arr msR N Wp lay6 num).arrs.lookup a =
      some ((arrayOfD lay6 (ownerP (Meaning.labAt Wp 24 a)).1
        (ownerP (Meaning.labAt Wp 24 a)).2).map (arrV num (ownerP (Meaning.labAt Wp 24 a)).1)) :=
    lookup_range _ _ a ha
  rw [e, owner_eq]
  dsimp only
  cases arrayOfD lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => rfl
  | some A => exact once_eq cs arr msR N Wp lay6 num _

end

/-- At the written View of the full size. Lean's kernel evaluates it. -/
theorem viewFull_planes : namedAtV viewFull 6 = true := by
  decide +kernel

/-- A negative test. -/
theorem viewFull_planes_no :
    namedAtV { viewFull with groupNums := 145 :: viewFull.groupNums } 6 = false := by
  decide +kernel

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.named_of_namedAtC
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.namedAtC_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewFull_planes
