-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/KeyAt.lean: the honest side of the kind "lookup" (K3): the
premises of `lawfulSpecP` (Honest/K3/Parts/Proof.lean) AT A KEY FILE'S LOOKUP: which of `SpecAtP`'s
clauses follow from tests on public numbers, and what is left. A definition with code, theorems with
proofs, `#guard` lines.

  `okK`, `okK_spec`   the two conditions of Honest/K3/Parts/KeyFace.lean, as a test on the lookup's
                    public structure: d ≤ 64; every padding row below 2 ^ d
  `specAtP_key`     CONDITIONAL ON `Fit R`, an acceptance by `okK`, an input that yields
                    one structure at all the stages' fronts, and THE RELATION AFTER THE CHALLENGE AT
                    PARTS: `SpecAtP` at a course whose face is the key file's lookup's and whose
                    summands are the specification's at parts
  `lawful_key`      CONDITIONAL ON the same: `Lawful` there

THE PUBLIC CONDITIONS HAVE MEMBERS: the two lookups of the key file at full size, as the library
writes them out (`lk0Full`, `lk1Full`, Johnson/Top/H/KeyRangesFull.lean), at the matrix ⟨18, 0⟩:
`okK` and the verifier's own tests on the face accept both, by evaluation; the faces' numbers are
held against written ones.

WHAT IS LEFT. The relation after the challenge at parts (`DataP.Mid`) of a key file's honest keys
and counts: whoever states the key file's honest prover concludes it; it is stated nowhere yet. NO
COURSE at these faces is shown: a part has 2 ^ 36 or 2 ^ 35 keys (the written lists of parts below).

Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Corollaries
import Johnson.Desc.ProofFile.Honest.K3.Parts.Member
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyFace
import Johnson.Top.H.KeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts.Key
open OnBytes
open VerifiableInference.Desc.K3 (entriesV)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (planesOf)

/-- The two public conditions, as a test. -/
def okK (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup) : Bool :=
  decide (l.d ≤ 64) && (Lkp.paddingList (Wf.lookupOf id m l)).all fun p => decide (p.2 < 2 ^ l.d)

/-- An acceptance by the test gives the two conditions. -/
theorem okK_spec {id : Nat} {m : Wf.Matrix} {l : OnBytes.Params.WfLookup} (h : okK id m l = true) :
    l.d ≤ 64 ∧ ∀ p ∈ Lkp.paddingList (Wf.lookupOf id m l), p.2 < 2 ^ l.d := by
  simp only [okK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h

/-- **CONDITIONAL ON `Fit R`, an acceptance by `okK`, one structure at all the stages' fronts, AND
THE RELATION AFTER THE CHALLENGE AT PARTS: `SpecAtP` at a key file's lookup.** No course is shown
that meets them. -/
theorem specAtP_key (R : Course Ask) (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup)
    (w : Hidden) (hf : R.f = faceK id m l)
    (hJ : R.J = (specJobsPAt (faceK id m l) (rowK id m l) (padsK id m l)).asked) (hF : Fit R)
    (hk : okK id m l = true) (hone : ∀ s ∈ stages R.f, R.t.input (R.front s).heard = w)
    (hM : (dataP (numsK id m l) R.f.parts R.f.orders w R.pts).Mid) :
    SpecAtP R (numsK id m l) w := by
  obtain ⟨hd, hp⟩ := okK_spec hk
  have hdd : R.f.d = l.d := by rw [hf]; rfl
  have hmu : R.f.mu = l.mu := by rw [hf]; rfl
  have hz : R.zb0.size = l.mu + l.d := by
    rw [← hmu, ← hdd]
    show ((varChals _ _ _ _ (R.f.mu + R.f.d)).toArray).size = _
    simp [varChals]
  refine ⟨?_, hone, ?_, ?_, ?_, ?_, hM⟩
  · rw [hJ, hf]
    rfl
  · rw [hf]
    exact numsShared_of_ok (faceK id m l) _ _ _ (by rw [← hf]; exact hF.ok)
  · show up (R.f.factor R.pts.theta R.pts.alpha) = _
    rw [show R.f.factor = (faceK id m l).factor by rw [hf]]
    exact factor_key id m l _ _ hd hp
  · rw [show R.f.leaf = (faceK id m l).leaf by rw [hf], hdd, hmu]
    exact leaf_key id m l _ _ _ hz hd
  · rw [show R.f.padding = (faceK id m l).padding by rw [hf]]
    exact padding_key id m l _

/-- **CONDITIONAL ON the same: at a key file's lookup the specification's summands at parts are
lawful.** No course is shown that meets the premises. -/
theorem lawful_key (R : Course Ask) (id : Nat) (m : Wf.Matrix) (l : OnBytes.Params.WfLookup)
    (w : Hidden) (hf : R.f = faceK id m l)
    (hJ : R.J = (specJobsPAt (faceK id m l) (rowK id m l) (padsK id m l)).asked) (hF : Fit R)
    (hk : okK id m l = true) (hone : ∀ s ∈ stages R.f, R.t.input (R.front s).heard = w)
    (hM : (dataP (numsK id m l) R.f.parts R.f.orders w R.pts).Mid) :
    Lawful R (planesOf (dataAt (numsK id m l) w R.pts))
      (keysOfP (dataP (numsK id m l) R.f.parts R.f.orders w R.pts)) :=
  lawfulP_of_fit _ w R hF (specAtP_key R id m l w hf hJ hF hk hone hM)

/-! ## The public conditions at the key file's two lookups at full size -/

/-- The matrix. -/
def m18 : Wf.Matrix := ⟨18, 0⟩

def f0 : LFace := faceK 0 m18 Johnson.Pack.lk0Full
def f1 : LFace := faceK 0 m18 Johnson.Pack.lk1Full

-- the test accepts both; so do the verifier's own tests on the face
#guard okK 0 m18 Johnson.Pack.lk0Full && okK 0 m18 Johnson.Pack.lk1Full
#guard f0.ok && f1.ok
-- written: no shift; mu; planes; twelve parts; d
#guard (f0.shifted, f0.mu, f0.planes, f0.parts, f0.d) == (false, 6, 40, List.replicate 12 36, 8)
#guard (f1.shifted, f1.mu, f1.planes, f1.parts, f1.d) == (false, 6, 39, List.replicate 12 35, 13)
-- written: hidden values; rounds; stages (1 + 39 + 11 + 1 + 12 * 72 + 16 + 3; 1 + 38 + 11 + 1 + 12
-- * 70 + 26 + 3)
#guard (f0.slots, (entriesV f0).length, (stages f0).length) == (17817, 9581, 935)
#guard (f1.slots, (entriesV f1).length, (stages f1).length) == (17116, 9220, 920)
-- the test can reject: a table of one row; a table too wide
#guard !okK 0 m18 { Johnson.Pack.lk0Full with d := 65 }
#guard !okK 0 m18 { Johnson.Pack.lk0Full with paddingKey := 256 }

#print axioms ProofFile.Honest.K3.Parts.Key.okK_spec
#print axioms ProofFile.Honest.K3.Parts.Key.specAtP_key
#print axioms ProofFile.Honest.K3.Parts.Key.lawful_key

end ProofFile.Honest.K3.Parts.Key
