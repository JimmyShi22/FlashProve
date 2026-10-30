-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMidAtWritten.lean: the relation after a lookup's first challenge (E2E/KeyPadding.lean) at the
library's written sizes of the key (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean): no
premise on the item "ranges" or on the codes is left. Statements and proofs.

What is shown.
  `item_written`: at `keyFull`: the item's lookups are the two written ones; the oracle message of
    the multiplicities has two main rows and the number 1; its code has messages of 2^18 entries;
    the matrix has 2^18 columns and 3,076,096 rows: by an evaluation in Lean's kernel. (The first
    clause is also the library's `looks_full`, Johnson/Top/Fire/Code/KeyHeldAtName.lean.)
  `faces_written`: the verifier program's own list of lookups at these sizes (`Wf.lookupsOf`) is
    `Wf.lookupOf` at the two lookups.
  **`mid_written0`**, **`mid_written1`**: for every matrix M in range and machine words that spell
    its cells, at every alpha and theta: the product of the twelve parts' roots over `keyVec` is the
    face's public factor times the product over the 40 (39) real planes j of (the product over the
    table's rows t of 1 + bit · (alpha - 1 - t))^(2^j), the bits read by `bitVec`, at the written
    item and codes, off the honest array.

Limits. All limits of E2E/KeyPadding.lean stand but the one on the three premises. That the written
sizes are those of the IOP as written in Lean at public files in scope is the library's, under its
own premises; it is not joined here. Nothing on hiding follows from this file.


-/
import E2E.KeyPadding
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open Johnson.Pack (lk0Full lk1Full)
open VerifiableInference.Desc.Key (keyVec bitVec)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- The item, the code and the matrix's size at the written sizes of the key. -/
theorem item_written : keyFull.ranges.x.lookups = [lk0Full, lk1Full] ∧
    keyFull.ranges.x.message.shape.mainRows = 2 ∧
    (keyFull.codes.base.getD keyFull.ranges.x.message.shape.code default).ell = 2 ^ 18 ∧
    keyFull.ranges.x.messageId = 1 ∧
    OnBytes.Wf.matrixOf keyFull.once.shape = ⟨kRef, 3076096⟩ := by decide +kernel

/-- The verifier program's own list of lookups at these sizes. -/
theorem faces_written :
    OnBytes.Wf.lookupsOf keyFull.ranges.x (OnBytes.Wf.matrixOf keyFull.once.shape) =
      [OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk0Full,
        OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk1Full] := by
  unfold OnBytes.Wf.lookupsOf
  rw [item_written.1, item_written.2.2.2.1, item_written.2.2.2.2]
  rfl

section
variable (M : Fin Inst.Model.Layout.hRef → Fin (2 ^ kRef) → GE)
  (hM : VerifiableInference.OnPublicFiles.Flat.InRange M) (mat : ℕ → ℕ → OnBytes.F)
  (hmat : ∀ (y c : ℕ) (hy : y < Inst.Model.Layout.hRef) (hc : c < 2 ^ kRef),
    toF (mat y c) = (M ⟨y, hy⟩ ⟨c, hc⟩).c0)
include hM hmat

/-- **The first lookup at the written sizes of the key.** -/
theorem mid_written0 (theta alpha : OnBytes.E) :
    ∏ f : Fin lk0Full.parts.length,
        ∏ i ∈ range (2 ^ (lk0Full.parts.get f).logPlaces * 2 ^ kRef),
          (readE alpha - readE (keyVec ⟨kRef, 3076096⟩ lk0Full mat f.val i)) =
      readE ((VerifiableInference.Desc.K3.faceOfLkp
          (OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk0Full)).factor theta alpha) *
        ∏ j ∈ range 40, (∏ t : Fin (2 ^ lk0Full.d),
          (1 + readE (bitVec keyFull.ranges.x keyFull.codes 0
              (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)
              (j + 2 ^ lk0Full.mu * t.val)) *
            (readE alpha - 1 - ((t.val : ℕ) : GE)))) ^ 2 ^ j :=
  mid_full0 M hM mat hmat 3076096 1 keyFull.ranges.x keyFull.codes item_written.1
    item_written.2.1 item_written.2.2.1 theta alpha

/-- **The second lookup.** -/
theorem mid_written1 (theta alpha : OnBytes.E) :
    ∏ f : Fin lk1Full.parts.length,
        ∏ i ∈ range (2 ^ (lk1Full.parts.get f).logPlaces * 2 ^ kRef),
          (readE alpha - readE (keyVec ⟨kRef, 3076096⟩ lk1Full mat f.val i)) =
      readE ((VerifiableInference.Desc.K3.faceOfLkp
          (OnBytes.Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk1Full)).factor theta alpha) *
        ∏ j ∈ range 39, (∏ t : Fin (2 ^ lk1Full.d),
          (1 + readE (bitVec keyFull.ranges.x keyFull.codes 1
              (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)
              (j + 2 ^ lk1Full.mu * t.val)) *
            (readE alpha - 1 - ((t.val : ℕ) : GE)))) ^ 2 ^ j :=
  mid_full1 M hM mat hmat 3076096 1 keyFull.ranges.x keyFull.codes item_written.1
    item_written.2.1 item_written.2.2.1 theta alpha

end

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.item_written
#print axioms AtPublicFiles.Key.faces_written
#print axioms AtPublicFiles.Key.mid_written0
#print axioms AtPublicFiles.Key.mid_written1
