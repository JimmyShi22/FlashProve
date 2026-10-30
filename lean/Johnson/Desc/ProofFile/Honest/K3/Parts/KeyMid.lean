-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/KeyMid.lean: the honest side of the kind "lookup" (K3): AT A
KEY FILE'S LOOKUP: the relation after the challenge at parts (`DataP.Mid`,
Honest/K3/Parts/Data.lean) FROM THREE SENTENCES ON TWO READERS, one of keys and one of bits. A
definition with code, a structure of propositions, theorems with proofs.

The three sentences are typed in the form in which mathematics on a key file's keys and counts
concludes them: products and sums over `Fin`, part by part, all read in the field, with the face's
own public factor and count; the table's row t written out as the number t.

  `hidK`           the structure of keys and bits, of the two readers: key x of part i; the bit of
                   row u and plane j at place j + 2 ^ mu * u
  `KeyMidHyp`      THE PREMISE, three clauses: `prod`: the product of the parts' roots is the face's
                   public factor times the planes' roots to their powers · `bit`: at a real plane a
                   bit reads 0 or 1 · `count`: the bits, each with its weight, add up to the face's
                   number of keys that are no padding
  `restFrom_prod`, `parts_len`, `part_size`   re-indexing
  `mid_key`        CONDITIONAL ON `KeyMidHyp`, the verifier's tests on the face and `okK`:
                   `DataP.Mid` at the specification's own numbers `numsK` and the structure `hidK`
  `lawful_key_of`  so `lawful_key` (Honest/K3/Parts/KeyAt.lean) with that premise in
                   the relation's stead

The reader of bits is never read at a plane that is not real: there the specification's data hold 0.

Limits. `KeyMidHyp` IS SHOWN OF NO READERS HERE: NO MEMBER. No file on a key file's keys and counts
is imported. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts.Key
open OnBytes
open OnBytes.Slice (GE readE)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (planesOf)

/-- **The structure of keys and bits, of two readers.** -/
def hidK (l : OnBytes.Params.WfLookup) (kvec : Nat → Nat → E) (bvec : Nat → E) : Hidden where
  key := fun _ i x => kvec i x
  bit := fun u j => bvec (j + 2 ^ l.mu * u)

/-- **THE PREMISE: three sentences on the two readers**, at a shift and an alpha. -/
structure KeyMidHyp (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup) (kvec : Nat → Nat → E)
    (bvec : Nat → E) (theta alpha : E) : Prop where
  /-- the product of the parts' roots -/
  prod : ∏ f : Fin l.parts.length,
      ∏ i ∈ Finset.range (2 ^ (l.parts.get f).logPlaces * 2 ^ m.kCol),
        (readE alpha - readE (kvec f.val i)) =
    readE ((faceK id m l).factor theta alpha) *
      ∏ j ∈ Finset.range (faceK id m l).planes, (∏ t : Fin (2 ^ l.d),
        (1 + readE (bvec (j + 2 ^ l.mu * t.val)) * (readE alpha - 1 - ((t.val : Nat) : GE)))) ^ 2 ^
          j
  /-- at a real plane a bit reads 0 or 1 -/
  bit : ∀ u, u < 2 ^ l.d → ∀ j, j < (faceK id m l).planes →
    readE (bvec (j + 2 ^ l.mu * u)) = 0 ∨ readE (bvec (j + 2 ^ l.mu * u)) = 1
  /-- the bits, each with its weight, add up -/
  count : ∑ t : Fin (2 ^ l.d), ∑ j ∈ Finset.range (faceK id m l).planes,
      (2 : GE) ^ j * readE (bvec (j + 2 ^ l.mu * t.val)) = ((faceK id m l).count : GE)

/-- The product of k numbers from number i on, as a product over a range. -/
theorem restFrom_prod (z : Nat → KE) : ∀ (k i : Nat),
    restFrom z k i = ∏ t ∈ Finset.range k, z (i + t)
  | 0, _ => rfl
  | k + 1, i => by
    show z i * restFrom z k (i + 1) = _
    rw [restFrom_prod z k (i + 1), Finset.prod_range_succ', Nat.add_zero, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun t _ => by rw [Nat.add_assoc, Nat.add_comm 1 t]

/-- The face has a part for each part of the structure. -/
theorem parts_len (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup) :
    (faceK id m l).parts.length = l.parts.length := by
  show (l.parts.map fun p => p.logPlaces + m.kCol).length = _
  rw [List.length_map]

/-- A part's number of levels. -/
theorem part_size (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup)
    (f : Fin l.parts.length) :
    (faceK id m l).parts.getD f.val 0 = (l.parts.get f).logPlaces + m.kCol := by
  show (l.parts.map fun p => p.logPlaces + m.kCol).getD f.val 0 = _
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact f.isLt), List.getElem_map]
  rfl

/-- **CONDITIONAL ON `KeyMidHyp`, the verifier's tests on the face and `okK`: the relation after the
challenge at parts**, at the specification's own numbers and the structure of the two readers.
No member here. -/
theorem mid_key (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup) (kvec : Nat → Nat → E)
    (bvec : Nat → E) (p : Pts) (H : KeyMidHyp id m l kvec bvec p.theta p.alpha)
    (hok : (faceK id m l).ok = true) (hk : okK id m l = true) :
    (dataP (numsK id m l) (faceK id m l).parts (faceK id m l).orders (hidK l kvec bvec) p).Mid := by
  obtain ⟨hd, hp⟩ := okK_spec hk
  have h2 := two_le_planes_of_ok _ hok
  have hn : (faceK id m l).planes - 2 + 2 = (faceK id m l).planes := by omega
  have hbits : ∀ u j, j < (faceK id m l).planes →
      (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j = readE (bvec (j + 2 ^ l.mu * u)) :=
    fun u j hj => if_pos (by
      show j < (faceK id m l).planes - 2 + 2
      omega)
  refine ⟨fun u hu j _ => ?_, ?_, ?_⟩
  · show (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j *
      ((dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j - 1) = 0
    by_cases hj : j < (faceK id m l).planes
    · rw [hbits u j hj]
      rcases H.bit u hu j hj with e | e <;> rw [e] <;> ring
    · have e : (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j = 0 := if_neg (by
        show ¬ j < (faceK id m l).planes - 2 + 2
        omega)
      rw [e]
      ring
  · show ∑ u ∈ Finset.range (2 ^ l.d), ∑ j ∈ Finset.range ((faceK id m l).planes - 2 + 2),
        (2 : KE) ^ j * (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j = _
    rw [hn, Finset.sum_range fun u => ∑ j ∈ Finset.range (faceK id m l).planes,
        (2 : KE) ^ j * (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j,
      Finset.sum_congr rfl fun (t : Fin (2 ^ l.d)) _ => Finset.sum_congr rfl fun j hj => by
        rw [hbits t.val j (Finset.mem_range.1 hj)], H.count]
    congr 1
    unfold VerifiableInference.Desc.K3.Face.count VerifiableInference.Desc.K3.Face.allKeys
    rw [← padding_key id m l (up p.theta)]
    rfl
  · have hpos : ∀ f : Fin l.parts.length, 1 ≤ (faceK id m l).parts.getD f.val 0 := fun f =>
      (facts_of_ok hok).1 _ (by
        rw [List.getD_eq_getElem _ _ (by rw [parts_len]; exact f.isLt)]
        exact List.getElem_mem _)
    have e1 : (dataP (numsK id m l) (faceK id m l).parts (faceK id m l).orders (hidK l kvec bvec)
        p).rest 0 = ∏ f : Fin l.parts.length,
          ∏ i ∈ Finset.range (2 ^ (l.parts.get f).logPlaces * 2 ^ m.kCol),
            (readE p.alpha - readE (kvec f.val i)) := by
      unfold DataP.rest
      rw [restFrom_prod]
      show ∏ t ∈ Finset.range ((faceK id m l).parts.length - 0), _ = _
      rw [Nat.sub_zero, parts_len, Finset.prod_range]
      refine Finset.prod_congr rfl fun f _ => ?_
      rw [Nat.zero_add]
      show ∏ b ∈ Finset.range (2 ^ ((faceK id m l).parts.getD f.val 0 - 1 + 1)),
        (readE p.alpha - readE (kvec f.val b)) = _
      rw [show (faceK id m l).parts.getD f.val 0 - 1 + 1 = (l.parts.get f).logPlaces + m.kCol by
        have := hpos f
        rw [← part_size id m l f]
        omega, pow_add]
    rw [e1, H.prod]
    congr 1
    · exact factor_key id m l _ _ hd hp
    · show _ = ∏ j ∈ Finset.range ((faceK id m l).planes - 2 + 2), _
      rw [hn]
      refine Finset.prod_congr rfl fun j hj => ?_
      congr 1
      show _ = ∏ u ∈ Finset.range (2 ^ l.d),
        (1 + (dataAt (numsK id m l) (hidK l kvec bvec) p).bits u j *
          (readE p.alpha - 1 - (numsK id m l (up p.theta)).tab u))
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [hbits t.val j (Finset.mem_range.1 hj), tab_key id m l _ t.val t.isLt hd]

/-- **CONDITIONAL ON `Fit R`, `okK`, an input that is the two readers' structure at every list, AND
`KeyMidHyp` at the run's shift and alpha: at a key file's lookup the specification's summands at
parts are lawful.** No course is shown that meets the premises. -/
theorem lawful_key_of (R : Course Ask) (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup)
    (kvec : Nat → Nat → E) (bvec : Nat → E) (hf : R.f = faceK id m l)
    (hJ : R.J = (specJobsPAt (faceK id m l) (rowK id m l) (padsK id m l)).asked) (hF : Fit R)
    (hk : okK id m l = true) (hone : ∀ s ∈ stages R.f, R.t.input (R.front s).heard =
      hidK l kvec bvec)
    (H : KeyMidHyp id m l kvec bvec R.pts.theta R.pts.alpha) :
    Lawful R (planesOf (dataAt (numsK id m l) (hidK l kvec bvec) R.pts))
      (keysOfP (dataP (numsK id m l) R.f.parts R.f.orders (hidK l kvec bvec) R.pts)) :=
  lawful_key R id m l _ hf hJ hF hk hone (by
    rw [hf]
    exact mid_key id m l kvec bvec _ H (by rw [← hf]; exact hF.ok) hk)

#print axioms ProofFile.Honest.K3.Parts.Key.restFrom_prod
#print axioms ProofFile.Honest.K3.Parts.Key.parts_len
#print axioms ProofFile.Honest.K3.Parts.Key.part_size
#print axioms ProofFile.Honest.K3.Parts.Key.mid_key
#print axioms ProofFile.Honest.K3.Parts.Key.lawful_key_of

end ProofFile.Honest.K3.Parts.Key
