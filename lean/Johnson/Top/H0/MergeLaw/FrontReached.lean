-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FrontReached.lean: `MergeFront` (EntryFront.lean), WHOLE, at the states in
front of the merge of the claims on the committed table: a joining of the test on the segment's mask
row with the three facts on the index masks' message; in general letters, and at the composed
meaning, the full size's written lists and border 346. Theorems with their proofs.

Why. The theorem that ties the merge's sub-protocol at its place (`merge_tiedAtR`, TiesReached.lean)
takes one premise on a state in front, hFr: the table's condition at border k, a condition Rch k
that every accepting step hands on, and "no mark" give `MergeFront own xM R ni`. The field mask
follows from an accept of `maskAtB` (`maskAt_of_test`, MaskRow.lean); the fields left, made and size
from `front_facts` (FrontFacts.lean). Here the four are laid together, in that premise's own form.

Main names:
  `mergeFront_reached`: IN GENERAL LETTERS: its conclusion is hFr to the letter, with the fence as
    it stands there: "not: the mark is not none". The premises: closed: the place p behind border k
    is piece 2 or a later one of segment m; an entry is left by the listed numbers; the listed shape
    of the index masks' message; the table's size. with the table's condition in hand (hmask, hix):
    `maskAtB` accepts at the member's place; `indexIsC ix` accepts. hmask has the form of the
    conclusion of `maskAtB_reached` (MaskReached.lean): whatever ends in that form serves. on the
    family alone, at border k (hroom, hpile, hsh, hcs): three listed tests accept and the codes are
    the listed ones: each in the form in which it is listed.
  `front_facts_reached`: left, made and size alone, in the same general letters, with the fence "the
    mark is none".
  `index_at_346`: at the composed meaning (`mgAll D Mg₀`, Mg₀ with no extra public test) and the
    full size's written lists: the table's condition at border 346, without a mark, gives `indexIsC
    D.N.indexNo`: the public test "indexIs" is asked there (`k11_hIn`, K11PubClosed.lean), and at
    the composed meaning it is that test (`pubAll_indexIs`, Johnson/Desc/First/PubAllAt.lean).
  `front_facts_346`: left, made and size there: from four facts on the family, each named, at border
    346 alone (hroom, hpile, hsh, hcs), three closed premises (hpos, hM, hni), and that Mg₀ has no
    extra public test.
  `mergeFront_346`: the structure there, in hFr's form: with hmask beside.
  `mergeFront_of_foldFacts`: the same under the one structure of facts on the reached states
    (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean): it spends the fields room, pileWithin,
    msgShapes and codes, at border 346; ni is written out: 2 to the sum of the bits that number the
    listed shape's mask rows and the bits that number the places of its mask code under the listed
    codes. (This is the text of `FillP1.niOf`, Johnson/Top/H0/Fill/WtAtZ.lean, with `logUp` for
    `ceilLog2`, which have one body; that file is not imported.)

Limits. Every premise on the family is a premise: shown of no family here. Who lays free0 and fvs is
not said: in `mergeFront_of_foldFacts` they are two fields of the structure's data, which no
equation here ties to the public files; the premise hpos is closed only where they are numerals. At
a family that holds nowhere the theorem says nothing. No example at the release's own values.
Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.EntryFront
import Johnson.Top.H0.MergeLaw.FrontFacts
import Johnson.Top.H0.MergeLaw.K11PubClosed
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open Fmt.Places (logUp)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound (Mem seatOf MgData mgAll mgAll_pub CellsQ MsgT linksFull k11_hIn
  k11_place k11PlaceW)
open VerifiableInference.Desc.K13.Law (LedgerAt)
open VerifiableInference.Desc.K13 (pileWithinC indexIsC)
open VerifiableInference.Desc.K12.Door (atFirstShapes)
open Johnson.Desc.First.Walk.Tied (leftIsB roomIsB rowsBefore)

/-- **`MergeFront` AT THE STATES IN FRONT OF THE MERGE**, in the form in which the theorem that ties
the merge's sub-protocol takes it. -/
theorem mergeFront_reached {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (own : List (ℕ × ℕ)) (xM : Mem) (R ni k free0 m ix : ℕ) (fvs : List Bool)
    (M : List OracleShape) (cs : Codes) (sh : OracleShape) (p : Place) (hp : ps[k]? = some p)
    (hl : p.link = some m) (h2 : 2 ≤ p.piece) (hpos : 0 < free0 - rowsBefore fvs m)
    (hM : M[ix]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni)
    (hmask : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → maskAtB own (seatOf xM) R a.1 = true)
    (hix : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → indexIsC ix a.1 = true)
    (hroom : ∀ a p' m', Rch k a → a.1.2.failed = none → ps[k]? = some p' → p'.link = some m' →
      2 ≤ p'.piece → roomIsB free0 fvs m' a.1.2 = true)
    (hpile : ∀ a, Rch k a → a.1.2.failed = none → pileWithinC a.1.2 = true)
    (hsh : ∀ a, Rch k a → a.1.2.failed = none → atFirstShapes M a.1.2 = true)
    (hcs : ∀ a, Rch k a → a.1.2.failed = none → a.1.2.st.codes = cs) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1 := by
  intro z a hon hr hm
  have hf : a.1.failed = none := Decidable.not_not.1 hm
  obtain ⟨f1, f2, f3⟩ := front_facts (hroom _ p m hr hf hp hl h2) hpos (hpile _ hr hf)
    (hix z a hon hr hf) (hsh _ hr hf) (hcs _ hr hf) hM hni
  exact ⟨maskAt_of_test (hmask z a hon hr hf), f1, f2, f3⟩

/-- **left, made and size at the states in front of the merge**, at the same general lists and
numbers. -/
theorem front_facts_reached {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (ni k free0 m ix : ℕ) (fvs : List Bool)
    (M : List OracleShape) (cs : Codes) (sh : OracleShape) (p : Place) (hp : ps[k]? = some p)
    (hl : p.link = some m) (h2 : 2 ≤ p.piece) (hpos : 0 < free0 - rowsBefore fvs m)
    (hM : M[ix]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni)
    (hix : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → indexIsC ix a.1 = true)
    (hroom : ∀ a p' m', Rch k a → a.1.2.failed = none → ps[k]? = some p' → p'.link = some m' →
      2 ≤ p'.piece → roomIsB free0 fvs m' a.1.2 = true)
    (hpile : ∀ a, Rch k a → a.1.2.failed = none → pileWithinC a.1.2 = true)
    (hsh : ∀ a, Rch k a → a.1.2.failed = none → atFirstShapes M a.1.2 = true)
    (hcs : ∀ a, Rch k a → a.1.2.failed = none → a.1.2.st.codes = cs) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none →
      (∃ n : ℕ, 0 < n ∧ leftIsB n a.1 = true) ∧ (∃ j : ℕ, LedgerAt a.1.st a.1.out.indexMasks j) ∧
        tableSize a.1.st a.1.out.indexMasks .mask = ni :=
  fun z a hon hr hf =>
    front_facts (s := a.1) (hroom ((z, a.1), a.2) p m hr hf hp hl h2) hpos
      (hpile ((z, a.1), a.2) hr hf) (hix z a hon hr hf) (hsh ((z, a.1), a.2) hr hf)
      (hcs ((z, a.1), a.2) hr hf) hM hni

/-! ## At the composed meaning, the full size's written lists and border 346 -/

section
variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Sound.Frame}
  (D : MgData Xi Pp Tok rows cols nR X) (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))

/-- **The table's condition in front of the merge says which number the index masks' message
has.** -/
theorem index_at_346 (hM₀ : Mg₀.more = {}) (Nn : Numbers) (z : Pp) (a : S × Fr.E.Str)
    (hon : Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) : indexIsC D.N.indexNo a.1 = true := by
  unfold Sound.onQ onAt at hon
  obtain ⟨_, hmk | ⟨hb, _⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨_, hpub⟩, _⟩ := hb
    unfold pubHeld at hpub
    have h0 : (mgAll D Mg₀).pub .indexIs (z, a.1) = true :=
      List.all_eq_true.1 hpub .indexIs (k11_hIn D Mg₀ hM₀ .indexIs (by simp))
    rw [mgAll_pub, pubAll_indexIs] at h0
    exact h0

/-- **left, made and size at the states in front of the merge**: from four named facts on the
family at border 346 alone, three closed premises, and that Mg₀ has no extra public test. -/
theorem front_facts_346 (hM₀ : Mg₀.more = {}) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (Nn : Numbers) (free0 ni : ℕ) (fvs : List Bool) (M : List OracleShape) (cs : Codes)
    (sh : OracleShape) (hpos : 0 < free0 - rowsBefore fvs 24) (hM : M[D.N.indexNo]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni)
    (hroom : ∀ a p' m', Rch 346 a → a.1.2.failed = none →
      (flatPlacesOf linksFull true)[346]? = some p' → p'.link = some m' → 2 ≤ p'.piece →
      roomIsB free0 fvs m' a.1.2 = true)
    (hpile : ∀ a, Rch 346 a → a.1.2.failed = none → pileWithinC a.1.2 = true)
    (hsh : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstShapes M a.1.2 = true)
    (hcs : ∀ a, Rch 346 a → a.1.2.failed = none → a.1.2.st.codes = cs) :
    ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none →
      (∃ n : ℕ, 0 < n ∧ leftIsB n a.1 = true) ∧ (∃ k : ℕ, LedgerAt a.1.st a.1.out.indexMasks k) ∧
        tableSize a.1.st a.1.out.indexMasks .mask = ni :=
  front_facts_reached Rch Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) ni 346 free0 24
    D.N.indexNo fvs M cs sh k11PlaceW k11_place rfl (by decide) hpos hM hni
    (fun z a hon _ hf => index_at_346 D Mg₀ hM₀ Nn z a hon hf) hroom hpile hsh hcs

/-- **`MergeFront` there**, in the form in which the theorem that ties the merge's sub-protocol
takes it. -/
theorem mergeFront_346 (hM₀ : Mg₀.more = {}) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers)
    (own : List (ℕ × ℕ)) (xM : Mem) (R ni free0 : ℕ) (fvs : List Bool) (M : List OracleShape)
    (cs : Codes) (sh : OracleShape) (hpos : 0 < free0 - rowsBefore fvs 24)
    (hM : M[D.N.indexNo]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni)
    (hmask : ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none → maskAtB own (seatOf xM) R a.1 = true)
    (hroom : ∀ a p' m', Rch 346 a → a.1.2.failed = none →
      (flatPlacesOf linksFull true)[346]? = some p' → p'.link = some m' → 2 ≤ p'.piece →
      roomIsB free0 fvs m' a.1.2 = true)
    (hpile : ∀ a, Rch 346 a → a.1.2.failed = none → pileWithinC a.1.2 = true)
    (hsh : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstShapes M a.1.2 = true)
    (hcs : ∀ a, Rch 346 a → a.1.2.failed = none → a.1.2.st.codes = cs) :
    ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1 :=
  mergeFront_reached Rch Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) own xM R ni 346
    free0 24 D.N.indexNo fvs M cs sh k11PlaceW k11_place rfl (by decide) hpos hM hni hmask
    (fun z a hon _ hf => index_at_346 D Mg₀ hM₀ Nn z a hon hf) hroom hpile hsh hcs

/-- **The same under the one structure of facts on the reached states**: it spends the fields room,
pileWithin, msgShapes and codes, at border 346. -/
theorem mergeFront_of_foldFacts (hM₀ : Mg₀.more = {}) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (Nn : Numbers) (d : FoldData) (reqW : Pp → Array UInt32)
    (F : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (own : List (ℕ × ℕ)) (xM : Mem) (R : ℕ) (sh : OracleShape)
    (hpos : 0 < d.free0 - rowsBefore d.fvs 24) (hM : d.M[D.N.indexNo]? = some sh)
    (hmask : ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none → maskAtB own (seatOf xM) R a.1 = true) :
    ∀ (z : Pp) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      MergeFront own xM R
        (2 ^ (logUp sh.maskRows + logUp (d.sent.codes.mask.getD sh.maskCode default).ell)) a.1 :=
  mergeFront_346 D Mg₀ hM₀ Rch Nn own xM R _ d.free0 d.fvs d.M d.sent.codes sh hpos hM rfl hmask
    (fun a p' m' ha hf => F.room 346 a p' m' ha hf) (F.pileWithin 346) (F.msgShapes 346)
    (F.codes 346)

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mergeFront_reached
#print axioms VerifiableInference.Desc.First.MergeLaw.front_facts_reached
#print axioms VerifiableInference.Desc.First.MergeLaw.index_at_346
#print axioms VerifiableInference.Desc.First.MergeLaw.front_facts_346
#print axioms VerifiableInference.Desc.First.MergeLaw.mergeFront_346
#print axioms VerifiableInference.Desc.First.MergeLaw.mergeFront_of_foldFacts
