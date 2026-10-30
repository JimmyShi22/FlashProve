-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/FaceAt.lean: the condition FaceIs (Statement.lean) AT THE FACE OF A
KEY FILE'S LOOKUP: faceOfLkp (Johnson/Desc/First/Look/K3Key.lean) at what the caller of a key file's
lookups makes of the plan's item "ranges" (Wf.lookupOf, OnBytes/Iop/Wf.lean).

The face's three public functions are computed by code: the factor and the count from the padding,
the leaf's factor from the table. Here each, read in the field, is shown to be the typed lookup's:
  factor: (alpha - the padding's row) ^ (the places of padding);
  count: all keys less the places of padding;
  leaf: alpha - 1 - the multilinear extension of the table at the row's coordinates.

Main names: factor_faceOfLkp, count_faceOfLkp, faceIs_lookupOf.

Conditions of faceIs_lookupOf, all on public data: the typed lookup's public record is the record
made of the plan's lookup (pubOf); that record is admissible; the typed lookup's table is the range
table (row u is the number u); d is at most 64.

-/
import Johnson.Desc.First.Look.KeyLaw.Statement
import Johnson.Desc.First.Look.KeyLaw.TableFacts
import OnBytes.Tie.Pv.KeyLookup.PartsPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open Lk6 (Dat Pub pubOf)
open Lk6.Mid (ordFirst ordDown)

/-- The face's factor, computed from its padding, is the program's public factor. -/
theorem factor_faceOfLkp (S : Lkp.Public) (theta alpha : E) :
    (faceOfLkp S).factor theta alpha = Lkp.factorOf S theta alpha := by
  unfold Face.factor faceOfLkp Lkp.factorOf
  rw [List.foldl_map]

/-- The face's count, computed from its padding. -/
theorem count_faceOfLkp (S : Lkp.Public) :
    (faceOfLkp S).count = S.allKeys - Lkp.paddingCount S := by
  unfold Face.count Face.allKeys faceOfLkp Lkp.paddingCount Lkp.Public.allKeys
  rw [List.map_map]
  rfl

/-- **The face of a key file's lookup is the typed lookup's.** -/
theorem faceIs_lookupOf {p : ℕ} (id : ℕ) (m : Wf.Matrix) (l : Params.WfLookup) (A : Dat GE)
    (st : A.St) (hA : A.toPub = pubOf (Wf.lookupOf id m l)) (hadm : A.toPub.Adm p)
    (htab : ∀ u < 2 ^ A.d, A.tab st u = (u : GE)) (hd : l.d ≤ 64) :
    FaceIs A st (faceOfLkp (Wf.lookupOf id m l)) where
  noShift := rfl
  mu := (congrArg Pub.mu hA).symm
  planes := (congrArg Pub.pl hA).symm
  parts := (congrArg Pub.parts hA).symm
  d := (congrArg Pub.d hA).symm
  orders := fun i n => by
    have e1 : A.v i = (Wf.lookupOf id m l).parts.getD i 0 := congrArg (fun S : Pub => S.v i) hA
    have e2 : A.order = (Wf.lookupOf id m l).lastKeyLevelOrder := congrArg Pub.order hA
    show (if n + 1 == (Wf.lookupOf id m l).parts.getD i 0 then
      Lkp.orderBeginning (Wf.lookupOf id m l).lastKeyLevelOrder n else Lkp.defaultOrder n) = _
    rw [e1, e2]
    by_cases h : n + 1 = (Wf.lookupOf id m l).parts.getD i 0
    · rw [if_pos h, if_pos (by simpa using h)]
      rfl
    · rw [if_neg h, if_neg (by simpa using h)]
      rfl
  factor := fun al => by
    have e1 : A.padRow = (pubOf (Wf.lookupOf id m l)).padRow := congrArg Pub.padRow hA
    have e2 : A.padCount = (pubOf (Wf.lookupOf id m l)).padCount := congrArg Pub.padCount hA
    have ed : A.d = l.d := congrArg Pub.d hA
    have hr : (pubOf (Wf.lookupOf id m l)).padRow < 2 ^ l.d := by
      rw [← e1, ← ed]
      exact hadm.row
    rw [factor_faceOfLkp, Lk6.read_factor_one (Lk6.oneRow_lookupOf id m l) zeroE al,
      Lk6.Mid.read_rowAt id m l zeroE _ hr hd]
    show _ = (readE al - A.tab st A.padRow) ^ A.padCount
    rw [htab _ hadm.row, e1, e2]
  count := by
    have e1 : A.allKeys = (pubOf (Wf.lookupOf id m l)).allKeys := congrArg Pub.allKeys hA
    have e2 : A.padCount = (pubOf (Wf.lookupOf id m l)).padCount := congrArg Pub.padCount hA
    rw [count_faceOfLkp, Lk6.paddingCount_eq (Lk6.oneRow_lookupOf id m l), e1, e2]
    rfl
  leaf := fun al z => by
    have ed : l.d = A.d := (congrArg Pub.d hA).symm
    have em : (Wf.lookupOf id m l).mu = A.mu := (congrArg Pub.mu hA).symm
    have e : (fun r : Fin A.d → Bool => A.tab st (Cb.LdLkp.numLE r)) =
        fun r => ((Cb.LdLkp.numLE r : ℕ) : GE) :=
      funext fun r => htab _ (Lk6.Mid.numLE_lt r)
    show readE (subE (subE al oneE)
      (Lkp.tableAt (Wf.lookupOf id m l) zeroE (z.toList.reverse.drop (Wf.lookupOf id m l).mu))) = _
    rw [readE_sub, readE_sub, readE_one, Planes.read_tableAt id m l zeroE _ hd, ed,
      Lk6.Mid.bitsVal_take, e, Lk6.Mid.mle_numLE, em, List.map_drop]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.faceIs_lookupOf
