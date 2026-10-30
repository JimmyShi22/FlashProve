-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Ood.lean: the out-of-domain (OOD) sample of one committed table, for an
honest prover in Lean, which this file does not write: from what such a prover keeps of that table
(index, coins, seeds) to the table's key as the linear claim's shared rounds (the shared chain) read
it (`OnBytes.TableKey`); what its answers are; and that it passes the description's tests on a key.

Main names (namespace `Bind.ForProver`).
  **`oodAt sh entry ρ sd`**   the key at a shape, plain entries, coins in the field and a list of
    seeds: `keyAt` (Johnson/Bind/ForProver/Key.lean) at the table `tableOfRand entry ρ`
    (Johnson/Bind/ForProver/Rows.lean). `oodAt_eq`: written out.
  **`ood Z k`**   the same off the public part Z and k, a part of the index secret key
    (`ProofFile.Honest.Isk`, Johnson/Desc/ProofFile/Honest/Committer.lean): the shape and the matrix's
    numbers as `encW` reads them (Johnson/Bind/ForProver/Enc.lean); the coins of item 0; the seed is
    typed: `Seed (shapeOf Z)`, with a copy's number beside it, which is not read; it is spelled
    here.
  **`oodSh sh Z k`**   the same with the seed typed at a shape sh that is a letter: its type does
    not depend on Z. `oodSh_shapeOf`: at Z's own shape it is `ood Z k`. `okSeeds_oodSh`,
    `okKey_oodSh`, `keyFits_oodSh`: the laws at every sh; `answers_oodSh`: where 3 s ≤ l;
    `keyFits_oodSh_of`: at Z's shape, where sh is that shape. That no factor is 0:
    `factorsOwn_oodSh` (Johnson/Bind/ForProver/RecRows.lean), in the description's own spelling.
  `answersOf Z k`   the answers alone, as a list: those of `ood Z k`, by definition.
  `msgsAt`, `msgsOf Z k`   the rows' messages over the extension field: entry by entry `rowMsgF`
    (Johnson/Bind/ForProver/Rows.lean), the function through which `encAt_values`
    (Johnson/Bind/ForProver/Laws.lean) tells the encoded index's columns.
  **`answers_ood`**, `answers_oodAt`   what the answers are, of k: the library's sample map
    (`OnBytes.Slice.recZ`) at k's typed seed, on the messages of the rows that are laid of k's index
    and k's coins of item 0, spelled. Asked: a message has room for its pads (3 s ≤ l).
  `ofWords`, `wordsOf_ofWords`, `ofWords_wordsOf`   seeds in triples of words, as a run of the
    stand-in committer returns them, written as a list of `SampleSeed`; the two ways undo each
    other.
  `answers_randOf`, `oodAt_randOf`   at the committer's coins, read in the field, the answers are
    those at the committer's own table: every shape, all seeds, no premise.
  **`okSeeds_ood`**, **`okKey_ood`**, **`keyFits_ood`**, `fits_ood`   an explicit input whose key is
    `ood Z k` passes the description's tests on the key: no premise, since a spelled seed meets
    `SeedsFit` (`fits_spell`, Johnson/Bind/ForProver/Seeds.lean). `factors_ood`: no factor is the
    triple of zeros (in the older test's spelling).
  `indexOf_shapeOf`   the shape that these tests take is the public part's own.
  `answers_spell`, `record_spell`   at a spelled seed and any table the key's answers are that
    sample map at the typed seed, spelled: `Bind.Twin.answers_spelled`
    (Johnson/Bind/TwinAnswers.lean) at sh.cube coordinates; the first reads both sides as triples of
    words.
In this file `randOf` is this folder's own (`Bind.ForProver.randOf`,
Johnson/Bind/ForProver/Laws.lean): the stand-in committer's coins, read in the field.

Limits. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. READ, NOT PROVED: in the library's typed schemes that are cited here a session's OOD sample is
a copy's, at that copy's own pads and encoding randomness and at the seed asked at the copy's root
(`allY`, Johnson/Prover/All/Defs.lean; `proveAt`, Johnson/WholeKey/Defs.lean). The item 0 is a
session's
numbering, not the link's (Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). The coins are
total functions here. Where they are made of coins on finite ranges (`AtPublicFiles.Key.padReader`, the
library's E2E/KeyReaders.lean, which gives 0 outside its range), the pads 3 i + t that the answers
read lie inside the range under `Bind.Column.Agree sh S cut` (Johnson/Bind/ColumnDefs.lean), and
without it nothing here says so (paid at the full size's shape: `paid_full`,
Johnson/Bind/ForProver/LawsSizes.lean). The seed is a letter beside index and coins. In the format's
Lean rendering a table's seeds are a function of its name and of public data alone (the field, the
bits, the count) (R4.8: `OnBytes.recordSeeds`, OnBytes/Entry/Table.lean): at these, one list of
seeds to a name; no statement here is over two seeds at one index and coins. Whoever states a
distribution over the coins binds index and coins first and writes the seed as the term made of
them, at the run's own name, with no letter for the seed beside the coins. Why: of two
OOD samples on one table's pads the library's theorem on a table's OOD answers says nothing
(E2E/TableHides.lean, Limits). The type of `ood Z`'s seed depends on Z: it can be laid only where Z
is bound; `oodSh` is the form without that. At another sh than Z's shape `oodSh` lays entries that
are packed for Z's shape into a table of the shape sh: nothing is said of that. `encW` has no column
where the test `rowsFit` fails; `ood` gives a key there all the same (at no public part that the
maker returns in scope: `rowsFit_inScope`, ShapeInScope.lean), and that key passes every test
below: nothing here ties key and columns but `rowMsgF`, of which both are told (`columnsAndAnswersFromIndexAndCoins`,
Johnson/Bind/ForProver/CommitterAt.lean, sets the two side by side). Where 3 s > l there is no plain
entry, the answers read pads that are in no message, and `answers_ood` is silent; wherever the maker
of the public part returns of files in scope the premise is paid (`rowsFit_inScope` with
`rowsFit_spec`, Johnson/Bind/ForProver/K14Rows.lean); at other files it is not shown here. No
root, no hash function and no salt enter: the seeds come in as a part of k, and nothing here says
that they are those of the table's name. At a run the
name and the seeds are the stand-in committer's own text (Johnson/Bind/Twin.lean). They are held
against the library's `OnBytes.Key.nameOf` and `seedsOf` (OnBytes/Key/Table.lean) by #guard rows at
small shapes (Johnson/Bind/TwinPort.lean); no theorem of this folder ties them to these, or to the
library's maker of a key (`OnBytes.tableKey`, OnBytes/Entry/Table.lean). Z is any value of
`ProofFile.Pub`: nothing here says that it was made of three public files. The tests are on sizes, on
words and on the item's number: that a key passes them says nothing on whether the Lean verifier
accepts a proof under it. Lean has code for `oodAt`, `ood` and `oodSh`, and none for `msgsAt` and
`msgsOf`, which stand in statements alone. No theorem of this file ties these answers to a program.
This file writes no honest prover. A like law to `map_ofTriple_triple` stands at
OnBytes/G4/FlatLaws.lean; it and its mirror `map_triple_ofTriple` stand here so that the file does
not import that file's cone. No correctness of extraction, no binding of the commitment (the opening
form, `BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index
privacy. Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Laws
import Johnson.Bind.ForProver.Key
import Johnson.Bind.TwinAnswers
import Johnson.Desc.ProofFile.Honest.Committer
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey isZeroE)
open ProofFile.Honest (TableRand Weights Isk)
open VerifiableInference.Desc.Own (keyFits)

/-- **The key at a shape, plain entries, coins in the field and a list of seeds.** Total at every
list: at a list longer than sh.s the answers read pads beyond 3 s, and at a factor 0 the pads do not
enter an answer. Neither happens at a spelled seed (`spell sh σ`: sh.s members and no factor 0, both
by type), at which `ood` and `oodSh` call it, or under `SeedsFit`. -/
def oodAt (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (sd : List SampleSeed) : TableKey :=
  keyAt sh (tableOfRand entry ρ) sd

/-- Written out. -/
theorem oodAt_eq (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (sd : List SampleSeed) :
    oodAt sh entry ρ sd =
      ⟨0, ((Bind.Twin.answers sh (tableOfRand entry ρ)
        (sd.map fun y => (y.z.map E.triple, y.beta.triple))).map E.ofTriple).toArray, sd⟩ := rfl

/-- **The key off the public part and what the prover keeps.** -/
def ood (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) : TableKey :=
  oodAt (shapeOf Z) (entryOfPub Z k.index) (k.coins 0) (spell (shapeOf Z) k.seed.1)

/-- The answers alone. -/
def answersOf (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) : List E :=
  (ood Z k).record.toList

/-! ### Seeds in triples of words -/

/-- Seeds in triples of words, written as a key holds them. -/
def ofWords (l : List (List Fmt.Ext × Fmt.Ext)) : List SampleSeed :=
  l.map fun y => ⟨y.1.map E.ofTriple, E.ofTriple y.2⟩

/-- Triples of words, written as elements and read again, come back. -/
theorem map_triple_ofTriple : ∀ l : List Fmt.Ext, (l.map E.ofTriple).map E.triple = l
  | [] => rfl
  | a :: l => by
    show (E.ofTriple a).triple :: (l.map E.ofTriple).map E.triple = a :: l
    rw [map_triple_ofTriple l, E.triple_ofTriple]

/-- Read again, they come back. -/
theorem wordsOf_ofWords : ∀ l : List (List Fmt.Ext × Fmt.Ext), wordsOf (ofWords l) = l
  | [] => rfl
  | y :: l => by
    show ((y.1.map E.ofTriple).map E.triple, (E.ofTriple y.2).triple) :: wordsOf (ofWords l) =
      y :: l
    rw [wordsOf_ofWords l, map_triple_ofTriple, E.triple_ofTriple]

/-- Elements, read as triples of words and written again, come back. -/
theorem map_ofTriple_triple : ∀ l : List E, (l.map E.triple).map E.ofTriple = l
  | [] => rfl
  | a :: l => by
    show E.ofTriple a.triple :: (l.map E.triple).map E.ofTriple = a :: l
    rw [map_ofTriple_triple l, E.ofTriple_triple]

/-- And the other way round: seeds as a key holds them, read and written again, come back. -/
theorem ofWords_wordsOf : ∀ sd : List SampleSeed, ofWords (wordsOf sd) = sd
  | [] => rfl
  | y :: sd => by
    show (⟨(y.z.map E.triple).map E.ofTriple, E.ofTriple y.beta.triple⟩ : SampleSeed) ::
      ofWords (wordsOf sd) = y :: sd
    rw [ofWords_wordsOf sd, map_ofTriple_triple, E.ofTriple_triple]

/-! ### The committer's own table -/

/-- **At the committer's coins, read in the field, the answers are the committer's own.** -/
theorem answers_randOf (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (c : Bind.Twin.Coins) :
    Bind.Twin.answers sh (tableOfRand entry (randOf c)) =
      Bind.Twin.answers sh (Bind.Twin.Table.of entry c) := by
  funext seeds
  unfold Bind.Twin.answers Bind.Twin.answerAt
  simp only [tableOfRand, randOf, Bind.Twin.Table.of, Bind.Column.ofF_toF,
    Bind.Twin.mulE_residue_right]

/-- So the key is that of the committer's own table. -/
theorem oodAt_randOf (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (c : Bind.Twin.Coins)
    (sd : List SampleSeed) :
    oodAt sh entry (randOf c) sd = keyAt sh (Bind.Twin.Table.of entry c) sd := by
  unfold oodAt keyAt
  rw [answers_randOf]

/-! ### The description's tests on an explicit input's key -/

/-- The two ways between the shapes undo each other. -/
theorem indexOf_shapeOfIndex (s : OnBytes.Params.IndexShape) : indexOf (shapeOfIndex s) = s := rfl

/-- The other way round. -/
theorem shapeOfIndex_indexOf (sh : Bind.Twin.Shape) : shapeOfIndex (indexOf sh) = sh := rfl

/-- The shape that the tests take is the public part's own. -/
theorem indexOf_shapeOf (Z : ProofFile.Pub) : indexOf (shapeOf Z) = (linOf Z).fold.index := rfl

section
variable (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ))

/-- **The test on the seeds' words passes.** -/
theorem okSeeds_ood : OnBytes.Maker.okSeeds (ood Z k) = true :=
  okSeeds_keyAt _ _ _ (fits_spell _ _)

/-- **The shared rounds' test on the explicit input passes**, at the parameters that are read off
any planner's chains: the test reads their item alone. -/
theorem okKey_ood (c : OnBytes.Model.Verify.Chains) (before : List (Nat × Nat)) :
    Desc.K14.okKey (Desc.K14.p14Of c before) (ood Z k) = true :=
  okKey_p14Of c before _ _ _ (fits_spell _ _)

/-- **The key's sizes fit the public part's shape.** -/
theorem keyFits_ood : keyFits (ood Z k) (linOf Z).fold.index = true :=
  keyFits_keyAt (shapeOf Z) _ _ (fits_spell _ _)

/-- The same of the older test. -/
theorem fits_ood : (ood Z k).fits (linOf Z).fold.index = true :=
  fits_keyAt (shapeOf Z) _ _ (fits_spell _ _)

/-- No factor is the triple of zeros. -/
theorem factors_ood : ((ood Z k).seeds.all fun x => !isZeroE x.beta) = true :=
  factors_keyAt _ _ _ (fits_spell _ _)

end

/-! ### The answers at a spelled seed -/

/-- **At a spelled seed the key's answers are the library's sample map at the typed seed, spelled**:
both read as triples of words; `record_spell` has the bare form. u: any table of messages over the
extension field that the table's plain entries and pads spell, row by row. -/
theorem answers_spell (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (h : 3 * sh.s ≤ sh.l)
    (ρ : Seed sh) (u : (Fin sh.v → Bool) × Fin sh.l → Cb.Gl.E)
    (hu1 : ∀ (b : ℕ) (j : Fin (sh.l - 3 * sh.s)), b < 2 ^ sh.v →
      u (OnBytes.Slice.vtx sh.v b, (OnBytes.Slice.entryEquiv sh.l sh.s h).symm (.inl j)) =
        algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (T.entry b j.val)))
    (hu2 : ∀ (b : ℕ) (a : Fin sh.s) (t : Fin 3), b < 2 ^ sh.v →
      u (OnBytes.Slice.vtx sh.v b, (OnBytes.Slice.entryEquiv sh.l sh.s h).symm (.inr (a, t))) =
        algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (T.pad b (3 * a.val + t.val)))) :
    (keyAt sh T (spell sh ρ)).record.toList.map E.triple =
      (OnBytes.K.IdTable.spellAns sh.v sh.s
        (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val ρ u)).map
          E.triple := by
  show (((Bind.Twin.answers sh T (wordsOf (spell sh ρ))).map E.ofTriple).toArray.toList).map
    E.triple = _
  rw [List.toList_toArray, map_triple_ofTriple, wordsOf_spell]
  exact (Bind.Twin.answers_spelled sh T sh.cube h ρ u hu1 hu2).symm

/-- The same without the reading as triples. -/
theorem record_spell (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (h : 3 * sh.s ≤ sh.l)
    (ρ : Seed sh) (u : (Fin sh.v → Bool) × Fin sh.l → Cb.Gl.E)
    (hu1 : ∀ (b : ℕ) (j : Fin (sh.l - 3 * sh.s)), b < 2 ^ sh.v →
      u (OnBytes.Slice.vtx sh.v b, (OnBytes.Slice.entryEquiv sh.l sh.s h).symm (.inl j)) =
        algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (T.entry b j.val)))
    (hu2 : ∀ (b : ℕ) (a : Fin sh.s) (t : Fin 3), b < 2 ^ sh.v →
      u (OnBytes.Slice.vtx sh.v b, (OnBytes.Slice.entryEquiv sh.l sh.s h).symm (.inr (a, t))) =
        algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (T.pad b (3 * a.val + t.val)))) :
    (keyAt sh T (spell sh ρ)).record.toList =
      OnBytes.K.IdTable.spellAns sh.v sh.s
        (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val ρ u) := by
  have k := congrArg (List.map E.ofTriple) (answers_spell sh T h ρ u hu1 hu2)
  rw [map_ofTriple_triple, map_ofTriple_triple] at k
  exact k

/-! ### What the answers are, of index, coins and seed -/

/-- **The rows' messages, over the extension field**: at a row's vertex and an entry's number, the
entry `rowMsgF` (Johnson/Bind/ForProver/Rows.lean) of the row with the vertex's number. -/
noncomputable def msgsAt (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) :
    (Fin sh.v → Bool) × Fin sh.l → Cb.Gl.E :=
  fun x => algebraMap Cb.Gl.F Cb.Gl.E
    (rowMsgF sh entry ρ (OnBytes.Slice.Sz.rowNo x.1) x.2.val)

/-- **At a spelled seed the answers of `oodAt` are the library's sample map, at the typed seed, on
the rows' messages.** -/
theorem answers_oodAt (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (h : 3 * sh.s ≤ sh.l) (σ : Seed sh) :
    (oodAt sh entry ρ (spell sh σ)).record.toList =
      OnBytes.K.IdTable.spellAns sh.v sh.s
        (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val σ
          (msgsAt sh entry ρ)) := by
  refine record_spell sh (tableOfRand entry ρ) h σ (msgsAt sh entry ρ) ?_ ?_
  · intro b j hb
    show algebraMap Cb.Gl.F Cb.Gl.E
      (rowMsgF sh entry ρ (OnBytes.Slice.Sz.rowNo (OnBytes.Slice.vtx sh.v b)) j.val) = _
    rw [OnBytes.Slice.ProxRun.rowNo_vtx sh.v b hb]
    unfold rowMsgF
    rw [if_pos (show j.val < sh.plain from j.isLt)]
    rfl
  · intro b a t hb
    have ha := a.isLt
    have ht := t.isLt
    show algebraMap Cb.Gl.F Cb.Gl.E
      (rowMsgF sh entry ρ (OnBytes.Slice.Sz.rowNo (OnBytes.Slice.vtx sh.v b))
        (sh.l - 3 * sh.s + 3 * a.val + t.val)) = _
    rw [OnBytes.Slice.ProxRun.rowNo_vtx sh.v b hb]
    unfold rowMsgF Bind.Twin.Shape.plain
    rw [if_neg (by omega), if_pos (by omega)]
    have e : sh.l - 3 * sh.s + 3 * a.val + t.val - (sh.l - 3 * sh.s) = 3 * a.val + t.val := by
      omega
    rw [e]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
      (OnBytes.Slice.toF (OnBytes.Slice.ofF (ρ.pad b (3 * a.val + t.val))))
    rw [OnBytes.Slice.toF_ofF]

/-- The rows' messages off the public part and what the prover keeps. -/
noncomputable def msgsOf (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) :
    (Fin (shapeOf Z).v → Bool) × Fin (shapeOf Z).l → Cb.Gl.E :=
  msgsAt (shapeOf Z) (entryOfPub Z k.index) (k.coins 0)

/-- **What the answers of `ood Z k` are, of k**: the library's sample map at k's typed seed, on the
messages of the rows that are laid of k's index and k's coins of item 0, spelled. -/
theorem answers_ood (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ))
    (h : 3 * (shapeOf Z).s ≤ (shapeOf Z).l) :
    answersOf Z k =
      OnBytes.K.IdTable.spellAns (shapeOf Z).v (shapeOf Z).s
        (((OnBytes.Slice.recZ (shapeOf Z).l (shapeOf Z).cube (shapeOf Z).s).rows
          (Fin (shapeOf Z).v → Bool)).val k.seed.1 (msgsOf Z k)) :=
  answers_oodAt (shapeOf Z) _ (k.coins 0) h k.seed.1

/-! ### The seed typed at a shape that is a letter -/

/-- **The key where the seed's type does not depend on the public part**: sh is a letter; the plain
entries are read off Z. Nothing ties sh to Z: the number of seeds and the pads that the answers read
(3 i + t, i below sh.s) are sh's, the packing's numbers Z's; the laws that join key and columns ask
sh = `shapeOf Z`. -/
def oodSh (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) :
    TableKey :=
  oodAt sh (entryOfPub Z k.index) (k.coins 0) (spell sh k.seed.1)

/-- At the public part's own shape it is `ood`. -/
theorem oodSh_shapeOf (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) :
    oodSh (shapeOf Z) Z k = ood Z k := rfl

section
variable (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ))

/-- The test on the seeds' words passes. -/
theorem okSeeds_oodSh : OnBytes.Maker.okSeeds (oodSh sh Z k) = true :=
  okSeeds_keyAt _ _ _ (fits_spell _ _)

/-- The shared rounds' test on the explicit input passes. -/
theorem okKey_oodSh (c : OnBytes.Model.Verify.Chains) (before : List (Nat × Nat)) :
    Desc.K14.okKey (Desc.K14.p14Of c before) (oodSh sh Z k) = true :=
  okKey_p14Of c before _ _ _ (fits_spell _ _)

/-- The key's sizes fit the shape sh. -/
theorem keyFits_oodSh : keyFits (oodSh sh Z k) (indexOf sh) = true :=
  keyFits_keyAt sh _ _ (fits_spell _ _)

/-- **They fit the public part's shape where sh is that shape.** -/
theorem keyFits_oodSh_of (h : sh = shapeOf Z) :
    keyFits (oodSh sh Z k) (linOf Z).fold.index = true := by
  rw [← indexOf_shapeOf Z, ← h]
  exact keyFits_oodSh sh Z k

/-- **What its answers are.** -/
theorem answers_oodSh (h : 3 * sh.s ≤ sh.l) :
    (oodSh sh Z k).record.toList =
      OnBytes.K.IdTable.spellAns sh.v sh.s
        (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val k.seed.1
          (msgsAt sh (entryOfPub Z k.index) (k.coins 0))) :=
  answers_oodAt sh _ (k.coins 0) h k.seed.1

end

end Bind.ForProver

#print axioms Bind.ForProver.oodAt_eq
#print axioms Bind.ForProver.map_triple_ofTriple
#print axioms Bind.ForProver.wordsOf_ofWords
#print axioms Bind.ForProver.answers_randOf
#print axioms Bind.ForProver.oodAt_randOf
#print axioms Bind.ForProver.indexOf_shapeOfIndex
#print axioms Bind.ForProver.shapeOfIndex_indexOf
#print axioms Bind.ForProver.indexOf_shapeOf
#print axioms Bind.ForProver.okSeeds_ood
#print axioms Bind.ForProver.okKey_ood
#print axioms Bind.ForProver.keyFits_ood
#print axioms Bind.ForProver.fits_ood
#print axioms Bind.ForProver.factors_ood
#print axioms Bind.ForProver.answers_spell
#print axioms Bind.ForProver.map_ofTriple_triple
#print axioms Bind.ForProver.ofWords_wordsOf
#print axioms Bind.ForProver.record_spell
#print axioms Bind.ForProver.answers_oodAt
#print axioms Bind.ForProver.answers_ood
#print axioms Bind.ForProver.oodSh_shapeOf
#print axioms Bind.ForProver.okSeeds_oodSh
#print axioms Bind.ForProver.okKey_oodSh
#print axioms Bind.ForProver.keyFits_oodSh
#print axioms Bind.ForProver.keyFits_oodSh_of
#print axioms Bind.ForProver.answers_oodSh
#print axioms Bind.ForProver.oodAt
#print axioms Bind.ForProver.ood
#print axioms Bind.ForProver.answersOf
#print axioms Bind.ForProver.ofWords
#print axioms Bind.ForProver.msgsAt
#print axioms Bind.ForProver.msgsOf
#print axioms Bind.ForProver.oodSh
