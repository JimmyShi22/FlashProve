-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/KeyFace.lean: the honest side of the kind "lookup" (K3): AT A
KEY FILE'S LOOKUP: the public numbers of the specification, made of the lookup's own
public structure, and the three public ties between the verifier's face there and these numbers.
Definitions with code, theorems with proofs. No course is read: the facts are on a face, a shift,
alpha and a point.

The face is `K3.faceOfLkp (Wf.lookupOf id m l)` (Johnson/Desc/First/Look/K3Key.lean;
OnBytes/Iop/Wf.lean): no shift; a range table (row u is the number u); padding by runs, each a
number of places and a row.

  `faceK`, `rowK`, `padsK`, `numsK`   the face; the table's row; the padding as (row, how many); the
     specification's public numbers, by `numsOf` (Honest/K3/JobsSpec.lean)
  `tab_key`       CONDITIONAL ON d ≤ 64: row u below 2 ^ d, read, is the number u
  `padding_key`   as many keys are padding
  `factor_key`    CONDITIONAL ON d ≤ 64 and on padding rows below 2 ^ d: the face's public factor,
                  read, is the specification's
  `leaf_key`      CONDITIONAL ON d ≤ 64, at a point of mu + d coordinates: the face's `leaf`, read,
                  is the extension of alpha - 1 - the table at the rows' coordinates of
                  the translated point

These are the clauses `padding`, `factor` and `leaf` of `SpecAtP` (Honest/K3/Parts/Lawful.lean), at
every shift, alpha and point.

It leans on `KeyLaw.factor_faceOfLkp` (Johnson/Desc/First/Look/KeyLaw/FaceAt.lean),
`Lk6.Mid.read_rowAt` (KeyLaw/TableFacts.lean), `Planes.read_tableAt`
(OnBytes/Slice/BlkTableRead.lean), `Planes.sum_bits` (OnBytes/Slice/KeyPlanesVals.lean),
`Fo.eqN_total`.

Limits. No structure l is shown here that meets the two conditions: NO MEMBER.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecPoints
import Johnson.Desc.First.Look.KeyLaw.FaceAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts.Key
open OnBytes
open OnBytes.Slice (readE readE_sub readE_mul readE_one readE_pow)
open VerifiableInference.Desc.K3 (faceOfLkp)

variable (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup)

/-- The face of a key file's lookup. -/
def faceK : LFace := faceOfLkp (Wf.lookupOf id m l)

/-- The table's row u, of the shift. -/
def rowK (theta : E) (u : Nat) : E := Lkp.rowAt (Wf.lookupOf id m l) theta u

/-- The padding as the specification has it: (row, how many). -/
def padsK : List (Nat × Nat) := (Lkp.paddingList (Wf.lookupOf id m l)).map fun p => (p.2, p.1)

/-- **The specification's public numbers at a key file's lookup.** -/
def numsK : KE → TwV.Nums Unit KE := numsOf (faceK id m l) (rowK id m l) (padsK id m l)

/-- CONDITIONAL ON d ≤ 64: a row of the range table, read, is its number. No member here. -/
theorem tab_key (theta : KE) (u : Nat) (hu : u < 2 ^ l.d) (hd : l.d ≤ 64) :
    (numsK id m l theta).tab u = (u : KE) :=
  Lk6.Mid.read_rowAt id m l (down theta) u hu hd

/-- As many keys are padding. -/
theorem padding_key (theta : KE) :
    ((numsK id m l theta).pads.map (·.2)).sum = ((faceK id m l).padding.map (·.1)).sum := by
  show ((padsK id m l).map (·.2)).sum =
    (((Lkp.paddingList (Wf.lookupOf id m l)).map fun p =>
      (p.1, fun theta => Lkp.rowAt (Wf.lookupOf id m l) theta p.2)).map (·.1)).sum
  unfold padsK
  rw [List.map_map, List.map_map]
  rfl

/-- A product that is folded, read. -/
theorem fold_prod_read {α : Type} (g : α → E) : ∀ (L : List α) (a : E),
    up (L.foldl (fun a p => mulE a (g p)) a) = up a * (L.map fun p => up (g p)).prod
  | [], a => by simp
  | p :: L, a => by
    rw [List.foldl_cons, fold_prod_read g L, List.map_cons, List.prod_cons,
      show up (mulE a (g p)) = up a * up (g p) from readE_mul _ _, mul_assoc]

/-- **CONDITIONAL ON d ≤ 64 and on padding rows below 2 ^ d: the face's public factor is the
specification's.** No member here. -/
theorem factor_key (theta alpha : E) (hd : l.d ≤ 64)
    (hp : ∀ p ∈ Lkp.paddingList (Wf.lookupOf id m l), p.2 < 2 ^ l.d) :
    up ((faceK id m l).factor theta alpha) =
      Cb.Lkp.padFac (numsK id m l (up theta)).tab (numsK id m l (up theta)).pads (up alpha) := by
  unfold faceK
  rw [VerifiableInference.Desc.K3.KeyLaw.factor_faceOfLkp]
  unfold Lkp.factorOf
  rw [fold_prod_read, show up oneE = 1 from readE_one, one_mul]
  show _ = ((padsK id m l).map fun e =>
    (up alpha - (numsK id m l (up theta)).tab e.1) ^ e.2).prod
  unfold padsK
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun p hpm => ?_
  show readE (powE (subE alpha (Lkp.rowAt (Wf.lookupOf id m l) theta p.2)) p.1) =
    (up alpha - (numsK id m l (up theta)).tab p.2) ^ p.1
  rw [readE_pow, readE_sub, Lk6.Mid.read_rowAt id m l theta p.2 (hp p hpm) hd,
    tab_key id m l _ p.2 (hp p hpm) hd]

/-- The two texts of the equality weight are one. -/
theorem eqW_eq : ∀ (z : List KE) (j : Nat), OnBytes.Slice.Leaves.eqW z j = TwV.eqN z j
  | [], _ => rfl
  | x :: xs, j => by
    show (if j % 2 = 1 then x else 1 - x) * OnBytes.Slice.Leaves.eqW xs (j / 2) =
      (if j % 2 = 1 then x else 1 - x) * TwV.eqN xs (j / 2)
    rw [eqW_eq xs (j / 2)]

/-- **CONDITIONAL ON d ≤ 64: the face's table at a point of mu + d coordinates is the
specification's.** No member here. -/
theorem leaf_key (theta alpha : E) (z : Array E) (hz : z.size = l.mu + l.d) (hd : l.d ≤ 64) :
    up ((faceK id m l).leaf theta alpha z) =
      ((List.range (2 ^ l.d)).map fun r => TwV.eqN ((byBit z).drop l.mu) r *
        (up alpha - 1 - (numsK id m l (up theta)).tab r)).sum := by
  have hlen : ((byBit z).drop l.mu).length = l.d := by
    rw [List.length_drop, byBit_length, hz]
    omega
  have e1 : up ((faceK id m l).leaf theta alpha z) =
      up alpha - 1 - OnBytes.Slice.Planes.bitsVal ((byBit z).drop l.mu) := by
    show readE (subE (subE alpha oneE)
      (Lkp.tableAt (Wf.lookupOf id m l) theta (z.toList.reverse.drop l.mu))) = _
    rw [readE_sub, readE_sub, readE_one, OnBytes.Slice.Planes.read_tableAt id m l theta _ hd,
      List.map_drop]
    show _ - OnBytes.Slice.Planes.bitsVal (((byBit z).drop l.mu).take l.d) = _
    rw [List.take_of_length_le (by rw [hlen])]
  have t1 := _root_.Fo.eqN_total ((byBit z).drop l.mu)
  have t2 := OnBytes.Slice.Planes.sum_bits ((byBit z).drop l.mu)
  rw [hlen] at t1 t2
  rw [e1, _root_.Fo.lsum, ← t2,
    Finset.sum_congr rfl fun r hr => show TwV.eqN ((byBit z).drop l.mu) r *
        (up alpha - 1 - (numsK id m l (up theta)).tab r) =
      TwV.eqN ((byBit z).drop l.mu) r * (up alpha - 1) -
        OnBytes.Slice.Leaves.eqW ((byBit z).drop l.mu) r * (r : KE) by
      rw [tab_key id m l _ r (Finset.mem_range.1 hr) hd, eqW_eq]
      ring,
    Finset.sum_sub_distrib, ← Finset.sum_mul, t1, one_mul]

#print axioms ProofFile.Honest.K3.Parts.Key.tab_key
#print axioms ProofFile.Honest.K3.Parts.Key.padding_key
#print axioms ProofFile.Honest.K3.Parts.Key.fold_prod_read
#print axioms ProofFile.Honest.K3.Parts.Key.factor_key
#print axioms ProofFile.Honest.K3.Parts.Key.eqW_eq
#print axioms ProofFile.Honest.K3.Parts.Key.leaf_key

end ProofFile.Honest.K3.Parts.Key
