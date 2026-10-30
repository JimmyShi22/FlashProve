-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/KeyTests.lean: THE DESCRIPTION's OWN TEXT FOR THE THREE YES-OR-NO TESTS THAT READ A
STORED TABLE's KEY (the kinds K15 and K14 ask them; under a common name),
EACH WITH A STATEMENT IN Prop OF WHAT IT CHECKS, PROVED AGAINST THE TEXT.
WHY. The rule here: a piece of the description may call the older hand-written
program's TOOLS but none of its plain yes-or-no TESTS; a copy of such a test under a new name, with
rfl to the older, is NO cure; «own text» is a text whose meaning is stated and proved. The kinds'
checks ON THE PLAN ALONE (Codes.lengthsOk · linkOk and what lies beneath them) read the plan's
numbers only, know nothing of a proof,
and stay as they are, classed as tools by the same ruling.
  p · Below x          the prime 2^64 - 2^32 + 1 · each of an element's three words, as a number, is
  less than p: so the element is spelt by its least residues
  below · elemOk       the tests, with code · below_iff · elemOk_iff: what they check
  seedsOk key          every word of every seed of the key is below p (the factor; the point's
  coordinates) · seedsOk_iff
  recordOk key         every word of the key's record is · recordOk_iff
  keyFits key s        the key's sizes fit the table's shape · keyFits_iff: the record has rows ·
  answers entries; there is a seed for each answer; each seed's point has a coordinate for each bit
  of an entry's number
  …_eq                 THE AGREEMENT: each has the older test's value (okF · okE · Maker.okSeeds ·
  TableKey.fits): BESIDE the statements, not instead of them: so what the library proves of the
  older test's yes is had of ours
SAID PLAINLY: the four texts are short conjunctions of comparisons and were typed after reading the
older definitions (OnBytes/Field/Word.lean:49 · Field/Ext.lean:45 · Maker/OkView.lean:71 ·
Iop/Foldeq.lean:133).

-/
import OnBytes.Iop.Foldeq
import OnBytes.Maker.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

/-- The prime of the programs' field. -/
def p : Nat := 2 ^ 64 - 2 ^ 32 + 1

/-- Each of the element's three words is a least residue. -/
def Below (x : E) : Prop := x.c0.toNat < p ∧ x.c1.toNat < p ∧ x.c2.toNat < p

def below (w : UInt64) : Bool := decide (w < 18446744069414584321)
def elemOk (x : E) : Bool := below x.c0 && below x.c1 && below x.c2
def seedsOk (key : TableKey) : Bool := key.seeds.all fun s => elemOk s.beta && s.z.all elemOk
def recordOk (key : TableKey) : Bool := key.record.all elemOk
def keyFits (key : TableKey) (s : IndexShape) : Bool :=
  key.record.size == s.rows * s.answers && key.seeds.length == s.answers &&
    key.seeds.all fun x => x.z.length == s.cubeBits

/-! ## What each checks -/

theorem below_iff (w : UInt64) : below w = true ↔ w.toNat < p := by
  unfold below
  rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  rfl

theorem elemOk_iff (x : E) : elemOk x = true ↔ Below x := by
  unfold elemOk Below
  simp only [Bool.and_eq_true, below_iff, and_assoc]

theorem seedsOk_iff (key : TableKey) :
    seedsOk key = true ↔ ∀ s ∈ key.seeds, Below s.beta ∧ ∀ z ∈ s.z, Below z := by
  unfold seedsOk
  simp only [List.all_eq_true, Bool.and_eq_true, elemOk_iff]

theorem recordOk_iff (key : TableKey) : recordOk key = true ↔ ∀ x ∈ key.record, Below x := by
  unfold recordOk
  simp only [Array.all_eq_true_iff_forall_mem, elemOk_iff]

theorem keyFits_iff (key : TableKey) (s : IndexShape) :
    keyFits key s = true ↔ key.record.size = s.rows * s.answers ∧ key.seeds.length = s.answers ∧
      ∀ x ∈ key.seeds, x.z.length = s.cubeBits := by
  unfold keyFits
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc]

/-! ## The agreement with the older tests -/

theorem below_eq (w : UInt64) : below w = okF w := rfl
theorem elemOk_eq (x : E) : elemOk x = okE x := rfl
theorem seedsOk_eq (key : TableKey) : seedsOk key = Maker.okSeeds key := rfl
theorem recordOk_eq (key : TableKey) : recordOk key = key.record.all okE := rfl
theorem keyFits_eq (key : TableKey) (s : IndexShape) : keyFits key s = key.fits s := rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.below_iff
#print axioms VerifiableInference.Desc.Own.elemOk_iff
#print axioms VerifiableInference.Desc.Own.seedsOk_iff
#print axioms VerifiableInference.Desc.Own.recordOk_iff
#print axioms VerifiableInference.Desc.Own.keyFits_iff
