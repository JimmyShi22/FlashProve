-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Means.lean: the sample row, written out, and its coefficients as a sum over the
pads' places.

Main names: Msg.ten, padStep, row₀, sampleRow_eq; padW, coefAt_fold, fold_kind, coefAt_sampleRow.
Lemmas on pure functions of the verifier program's page of rows are spent: coefAt_add,
coefAt_addUnit, coefAt_sampleStart (OnBytes/Slice/BlkRow.lean, BlkSend.lean).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-! ## The row, written out -/

/-- The equality vector on one of a message's two tables. -/
def Msg.ten (m : Msg) (z : List E) : Part → Tensor
  | .main => Tensor.eq (z.take m.mainBits) (m.front z m.mainBits false)
  | .mask => Tensor.eq (z.take m.maskBits) (m.front z m.maskBits true)

/-- One step of the loop over the pads' places. -/
def Msg.padStep (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (r : OnBytes.Row)
    (x : Nat × Nat × Nat) : OnBytes.Row :=
  r.addUnit o m.padPart x.2.1
    (subE (if x.1 == i then mulE β (thetaE x.2.2) else zeroE) ((m.ten z m.padPart).entry x.2.1))

/-- The row behind the loop. -/
def Msg.row₀ (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) : OnBytes.Row :=
  m.pads.foldl (m.padStep o z β i) { kind := .sample }

theorem sampleRow_eq (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) :
    sampleRow m o z β i y =
      { (if m.Kzk != 0 then
          (if m.K != 0 then (m.row₀ o z β i).add o .main (m.ten z .main)
            else m.row₀ o z β i).add o .mask (m.ten z .mask)
          else (if m.K != 0 then (m.row₀ o z β i).add o .main (m.ten z .main)
            else m.row₀ o z β i)) with target := y } := by
  unfold sampleRow Msg.row₀ Msg.pads Msg.padStep Msg.padPart
  cases h : (m.Kzk != 0) <;> rfl

/-! ## Its coefficients -/

/-- What a pad's place has in the row of answer i. -/
def padW (β : E) (i : Nat) (x : Nat × Nat × Nat) : GE :=
  if x.1 == i then readE β * readE (thetaE x.2.2) else 0

theorem coefAt_fold (m : Msg) (o : Nat) (z : List E) (β : E) (i o' : Nat) (part : Part) (j : Nat) :
    ∀ (l : List (Nat × Nat × Nat)) (r : OnBytes.Row),
      coefAt (l.foldl (m.padStep o z β i) r) o' part j = coefAt r o' part j +
        (l.map fun x => if o == o' && m.padPart == part && x.2.1 == j then
          padW β i x - readE ((m.ten z m.padPart).entry x.2.1) else 0).sum
  | [], r => by simp
  | x :: l, r => by
    rw [List.foldl_cons, coefAt_fold m o z β i o' part j l, List.map_cons, List.sum_cons]
    unfold Msg.padStep
    rw [coefAt_addUnit, readE_sub, add_assoc]
    congr 2
    unfold padW
    by_cases h : (x.1 == i) = true
    · simp only [h, if_true, readE_mul]
    · simp only [h, if_false, readE_zero, Bool.false_eq_true]

theorem fold_kind (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) :
    ∀ (l : List (Nat × Nat × Nat)) (r : OnBytes.Row),
      (l.foldl (m.padStep o z β i) r).kind = r.kind
  | [], _ => rfl
  | _ :: l, _ => fold_kind m o z β i l _

theorem coefAt_sampleRow (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) (o' : Nat)
    (part : Part) (j : Nat) :
    coefAt (sampleRow m o z β i y) o' part j =
      (if o == o' && m.has part then readE ((m.ten z part).entry j) else 0) +
        (m.pads.map fun x => if o == o' && m.padPart == part && x.2.1 == j then
          padW β i x - readE ((m.ten z m.padPart).entry x.2.1) else 0).sum := by
  have h0 := coefAt_fold m o z β i o' part j m.pads { kind := .sample }
  rw [coefAt_sampleStart, zero_add] at h0
  rw [sampleRow_eq]
  show coefAt (if m.Kzk != 0 then
          (if m.K != 0 then (m.row₀ o z β i).add o .main (m.ten z .main)
            else m.row₀ o z β i).add o .mask (m.ten z .mask)
          else (if m.K != 0 then (m.row₀ o z β i).add o .main (m.ten z .main)
            else m.row₀ o z β i)) o' part j = _
  unfold Msg.row₀
  cases hK : (m.K != 0) <;> cases hZ : (m.Kzk != 0) <;> cases part <;>
    simp [coefAt_add, h0, Msg.has, hK, hZ, add_comm]

end VerifiableInference.Desc.K1
