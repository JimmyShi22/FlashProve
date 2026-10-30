-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/OkStartAtInstK.lean: THE KEY FILE's
TEST ON THE INSTANCE (`okStart` of `Key.descriptionFromSource X N P`) AT THE INSTANCE OF A TYPED RECORD
(`Key.keyInstanceOfOutOfDomainSample rec`), conjunct by conjunct: which follow from the record's type, and which one does
not.

What is said.
  `item_instK`, `words_instK`, `factors_instK`, `okKey_instK`: at every record: the key names item
    0; every word of it is below the prime; no seed's factor is 0; the shared chain's own test on
    the key says yes where its parameters name item 0.
  `fits_instK_iff`: THE ONE CONJUNCT THAT A TYPED RECORD CAN FAIL: the key's sizes fit an index's
    shape JUST WHERE the shape's three numbers are the type's: as many rows as the full size's
    table, one answer, 29 cube bits.
  `okStart_instK_iff`: so `okStart (keyInstanceOfOutOfDomainSample rec)` says yes just where these three equations hold at
    the source's shape; the record is not read.

Limits. By unfolding and the library's laws on `keyOf`. That a laid piece's source has that shape is
not shown here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Slot
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Sound

open OnBytes OnBytes.Slice OnBytes.Flat VerifiableInference.Desc

/-- The key names the statement's item 0. -/
theorem item_instK (rec : RecFull) : (Key.keyInstanceOfOutOfDomainSample rec).key.item = 0 := rfl

/-- Every entry of a written key's array has words below the prime. -/
theorem record_keyOf {v lg s : ℕ} (rec : RecP NZ v lg s) (x : E)
    (hx : x ∈ (keyOf (fun β : NZ => β.val) rec).record) : okE x = true := by
  unfold keyOf at hx
  obtain ⟨n, rfl⟩ := Array.mem_ofFn.1 hx
  exact okE_writeE _

/-- Every entry of the record's array has words below the prime. -/
theorem record_instK (rec : RecFull) (x : E) (hx : x ∈ (Key.keyInstanceOfOutOfDomainSample rec).key.record) :
    okE x = true := record_keyOf rec x hx

/-- Every seed has 29 coordinates; they and its factor are written elements. -/
theorem seeds_instK (rec : RecFull) (z : SampleSeed) (hz : z ∈ (Key.keyInstanceOfOutOfDomainSample rec).key.seeds) :
    (∀ c ∈ z.z, okE c = true) ∧ z.z.length = 29 ∧ okE z.beta = true := by
  have hz' : z ∈ List.ofFn fun i : Fin 1 =>
      (⟨List.ofFn fun t : Fin 29 => writeE ((rec.1 i).1 t), writeE ((rec.1 i).2).val⟩ :
        SampleSeed) := hz
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz'
  refine ⟨fun c hc => ?_, List.length_ofFn, okE_writeE _⟩
  obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 hc
  exact okE_writeE _

/-- Every word of the key is below the prime. -/
theorem words_instK (rec : RecFull) : Key.keyWordsBelow (Key.keyInstanceOfOutOfDomainSample rec).key = true := by
  unfold Key.keyWordsBelow
  refine Bool.and_eq_true_iff.2 ⟨Array.all_eq_true_iff_forall_mem.2 (record_instK rec),
    List.all_eq_true.2 fun z hz => ?_⟩
  obtain ⟨h1, -, h3⟩ := seeds_instK rec z hz
  exact Bool.and_eq_true_iff.2 ⟨List.all_eq_true.2 h1, h3⟩

/-- No seed's factor is 0. -/
theorem factors_instK (rec : RecFull) :
    ((Key.keyInstanceOfOutOfDomainSample rec).key.seeds.all fun z => !isZeroE z.beta) = true := keyOf_nz rec

/-- The shared chain's own test on the key, where its parameters name item 0. -/
theorem okKey_instK (Q : _root_.Desc.K14.P14) (hQ : Q.item = 0) (rec : RecFull) :
    _root_.Desc.K14.okKey Q (Key.keyInstanceOfOutOfDomainSample rec).key = true := by
  unfold _root_.Desc.K14.okKey
  refine Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine List.all_eq_true.2 fun z hz => ?_
    obtain ⟨h1, -, h3⟩ := seeds_instK rec z hz
    exact Bool.and_eq_true_iff.2 ⟨h3, List.all_eq_true.2 h1⟩
  · exact Array.all_eq_true_iff_forall_mem.2 (record_instK rec)
  · rw [hQ]
    rfl

/-- **The one conjunct that a typed record can fail**: the key's sizes fit a shape just where the
shape's three numbers are the type's. -/
theorem fits_instK_iff (sh : Params.IndexShape) (rec : RecFull) :
    (Key.keyInstanceOfOutOfDomainSample rec).key.fits sh = true ↔
      sh.rows = 2 ^ frS.P.v ∧ sh.answers = 1 ∧ sh.cubeBits = 29 := by
  have hsz : (Key.keyInstanceOfOutOfDomainSample rec).key.record.size = 2 ^ frS.P.v * 1 := keyOf_size _ rec
  have hln : (Key.keyInstanceOfOutOfDomainSample rec).key.seeds.length = 1 := keyOf_seeds_length _ rec
  unfold TableKey.fits
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, hsz, hln]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨z, hz⟩ : ∃ z, z ∈ (Key.keyInstanceOfOutOfDomainSample rec).key.seeds :=
      List.exists_mem_of_length_pos (by rw [hln]; exact Nat.one_pos)
    refine ⟨?_, h2.symm, ((seeds_instK rec z hz).2.1).symm.trans (h3 z hz) |>.symm⟩
    rw [← h2, Nat.mul_one, Nat.mul_one] at h1
    exact h1.symm
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by rw [h1, h2], h2.symm⟩, fun z hz => ?_⟩
    rw [h3]
    exact (seeds_instK rec z hz).2.1

/-- The test on the instance, written out. -/
theorem okStart_eq (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (x : Key.Xi) :
    (Key.descriptionFromSource X N P).okStart x = (Key.instanceOk X.Y.k.shared.lin x &&
                       _root_.Desc.K14.okKey (Key.sharedPar X.chains []) x.key) := rfl

/-- **The test on the instance, at a typed record's instance**: yes just where the source's shape
has the type's three numbers. -/
theorem okStart_instK_iff (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (rec : RecFull) :
    (Key.descriptionFromSource X N P).okStart (Key.keyInstanceOfOutOfDomainSample rec) = true ↔
      X.Y.k.shared.lin.fold.index.rows = 2 ^ frS.P.v ∧ X.Y.k.shared.lin.fold.index.answers = 1 ∧
        X.Y.k.shared.lin.fold.index.cubeBits = 29 := by
  rw [← fits_instK_iff _ rec, okStart_eq, okKey_instK _ rfl rec, Bool.and_true]
  unfold Key.instanceOk
  rw [words_instK rec, factors_instK rec, Bool.and_true, Bool.and_true,
    show ((Key.keyInstanceOfOutOfDomainSample rec).key.item == 0) = true from rfl, Bool.true_and]

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.words_instK
#print axioms Johnson.RunOne.Sound.factors_instK
#print axioms Johnson.RunOne.Sound.okKey_instK
#print axioms Johnson.RunOne.Sound.fits_instK_iff
#print axioms Johnson.RunOne.Sound.okStart_instK_iff
