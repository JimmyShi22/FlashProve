-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryPlaceRec.lean: the block and the description that `entryPlaceR` returns
(OnBytes/Tie/EntryWithRec.lean), whatever the function sd that gives the
seeds.

It is said first over the hypothesis `Params.LinkDryBySizes`
(OnBytes/Params/EntryRoundsRecord.lean). The law on a block's dry run (`linkVerify_rounds_sizes`,
OnBytes/Iop/DrySizes.lean) meets that hypothesis at every shape (`dryBySizes`).

Not claimed. It speaks of the description alone. The decision (`P.block.decides …`) hangs on the
keys' values: nothing is said of it here.

-/
import OnBytes.Tie.EntryWithRec
import OnBytes.Params.EntryRoundsRecord
import OnBytes.Iop.DrySizes

set_option autoImplicit false

namespace OnBytes.Tie

/-- **UNDER `Params.LinkDryBySizes p.link` (A HYPOTHESIS: the dry run of the link's block hangs on
the keys' sizes and items, not on their values), WHATEVER sd:** what
`entryPlaceR` returns: its block is the link's block at the two keys that `keyWith sd` gave for the
two tables; ITS DESCRIPTION IS MADE OF THE ROUNDS AT KEYS OF ZEROS AND OF THE STATEMENT ON THE TWO
TABLES: so it hangs on sd's values in no way; the further table's root has 32 bytes. -/
theorem entryPlaceR_spec {sd : Seeds} {p : Params.Link} {first : Params.TableName} {file : ByteArray}
    {P : EntryPlace} (H : Params.LinkDryBySizes p.link)
    (h : entryPlaceR sd p first file = some P) :
    (∃ k0 k1, keyWith sd p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      keyWith sd p.given.plan.field p.given.cfg p.link.table P.further 1 = some k1 ∧
      P.block = linkVerify p.link k0 k1) ∧
      (∃ r, Params.entryRoundsAny p = some r ∧
        P.spec = Params.entrySpecOf p r (Params.Link.statement first P.further)) ∧
      P.further.root.size = 32 := by
  unfold entryPlaceR at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i further j ht
        split at h
        · rename_i k0 k1 h0 h1
          have e : (linkVerify p.link k0 k1).rounds (Entry.start p) = Params.entryRoundsAny p :=
            H _ _ _ _ _ (keyWith_fits h0).1 (Params.zeroKey_fits _ _) (keyWith_fits h1).1
              (Params.zeroKey_fits _ _) (keyWith_fits h0).2 (keyWith_fits h1).2
          rw [e] at h
          cases hr : Params.entryRoundsAny p with
          | none =>
            rw [hr] at h
            cases h
          | some r =>
            rw [hr] at h
            simp only [Option.bind_some] at h
            cases hd : p.describe first further r with
            | none =>
              rw [hd] at h
              cases h
            | some S' =>
              rw [hd] at h
              cases h
              exact ⟨⟨k0, k1, h0, h1, rfl⟩, ⟨r, rfl, Params.Given.describe_eq hd⟩,
                readTable_root _ _ _ _ _ _ ht⟩
        · cases h

/-- So, under the same hypothesis: two places that `entryPlaceR` returns, AT TWO FUNCTIONS sd AND
sd', on files that hold the same further table, have ONE description. -/
theorem entryPlaceR_spec_same {sd sd' : Seeds} {p : Params.Link} {first : Params.TableName}
    {file file' : ByteArray} {P P' : EntryPlace} (H : Params.LinkDryBySizes p.link)
    (h : entryPlaceR sd p first file = some P) (h' : entryPlaceR sd' p first file' = some P')
    (hf : P.further = P'.further) : P.spec = P'.spec := by
  obtain ⟨_, ⟨r, hr, e⟩, _⟩ := entryPlaceR_spec H h
  obtain ⟨_, ⟨r', hr', e'⟩, _⟩ := entryPlaceR_spec H h'
  obtain rfl : r = r' := Option.some.inj (hr.symm.trans hr')
  rw [e, e', hf]

/-! ## The hypothesis is met at every shape (by the law of OnBytes/Iop/DrySizes.lean) -/

/-- `Params.LinkDryBySizes` holds at every shape: it is `linkVerify_rounds_sizes`. -/
theorem dryBySizes (S : Params.LinkShape) : Params.LinkDryBySizes S :=
  fun st _ _ _ _ f0 f0' f1 f1' i0 i1 => linkVerify_rounds_sizes st f0 f0' f1 f1' i0 i1

/-- **WITH NO HYPOTHESIS BUT THAT `entryPlaceR` RETURNED P; WHATEVER sd:**
`entryPlaceR_spec`'s three conclusions. -/
theorem entryPlaceR_spec_any {sd : Seeds} {p : Params.Link} {first : Params.TableName}
    {file : ByteArray} {P : EntryPlace} (h : entryPlaceR sd p first file = some P) :
    (∃ k0 k1, keyWith sd p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      keyWith sd p.given.plan.field p.given.cfg p.link.table P.further 1 = some k1 ∧
      P.block = linkVerify p.link k0 k1) ∧
      (∃ r, Params.entryRoundsAny p = some r ∧
        P.spec = Params.entrySpecOf p r (Params.Link.statement first P.further)) ∧
      P.further.root.size = 32 :=
  entryPlaceR_spec (dryBySizes _) h

/-- **WITH NO HYPOTHESIS BUT THE TWO VALUES AND ONE FURTHER TABLE:** two places at two functions sd,
sd' have one description. -/
theorem entryPlaceR_spec_same_any {sd sd' : Seeds} {p : Params.Link} {first : Params.TableName}
    {file file' : ByteArray} {P P' : EntryPlace}
    (h : entryPlaceR sd p first file = some P) (h' : entryPlaceR sd' p first file' = some P')
    (hf : P.further = P'.further) : P.spec = P'.spec :=
  entryPlaceR_spec_same (dryBySizes _) h h' hf

end OnBytes.Tie

#print axioms OnBytes.Tie.dryBySizes
#print axioms OnBytes.Tie.entryPlaceR_spec_any
#print axioms OnBytes.Tie.entryPlaceR_spec_same_any
#print axioms OnBytes.Tie.entryPlaceR_spec
#print axioms OnBytes.Tie.entryPlaceR_spec_same
