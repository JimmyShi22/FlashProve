-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Defs.lean: A DESCRIPTION WITH A COMMITTER LAID INTO ITS COMMIT FIELD, AT A LETTER
AND AT THE COMMITTER THAT RUNS, AND THE STATEMENTS ON IT, WHICH THIS FILE DOES NOT PROVE.
Definitions, with three small theorems.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

Why. The honest committer is not written in Lean for the description of the theorem on soundness:
its own is hollow. So correctness of extraction (the extractor gives the honest committer's weights)
and the goals on binding (G9, G9bits: Ladder.lean, Ladder/Bits.lean), which speak of a description's
own committer, cannot hold at it (argued: a commitment of zeros opens to any two weights). A
committer is written as mathematics over the description's told structure (LayoutsByPublicReading.commitAtCoins,
Johnson/Top/ToldCommitPlain.lean), and its binding is a theorem (bindsWith_plain_law,
Johnson/Goal/Conditions/BindsTold.lean); it cannot be run and is tied to no program of the release
by a theorem. A committer that runs is written in Johnson/Bind/Twin.lean, as a model of one part of
the release's committing program. No theorem ties it to the program. Evaluations have compared it
with runs of the program at the small stored example's public files, on synthetic weights, and
nowhere else; what was compared, and what was not, stands in Johnson/Bind/README.md ("What is run,
not proved"). Here the two are set face to face.

Words. The told structure: the structure over which the library's theorem on binding is stated
(LayoutsByPublicReading). The written committer: LayoutsByPublicReading.commitAtCoins. The running committer: Bind.Twin.twinID.
The frame: what the description lays at given public files (plan, data, the salts' length). A
filling: the body of a leaf beyond the table's positions; none is read here. Owed: stated as a
proposition and not proved in this file; paid: proved.

Main names.
  General in the description (namespace VerifierAndGoals.Fit): HonestSide, Description.withHonest: another
    honest side; all that the verifier reads, the parser and the extractor are kept.
  Namespace Bind.Cpp:
  Coins: the committer's coins, each value by its address: encoding randomness (tail), pads, a
    leaf's salt bytes. Seed, Rand := Seed ⊕ Coins: what an opener names. Free of the public files.
  Letters (id, gen): a committer and a generator from a seed to coins, as letters. theTwin g: id :=
    Bind.Twin.twinID; THE GENERATOR STAYS A LETTER IN EVERY STATEMENT.
  Letters.commitAt: the committer, general in the shape, the files and the table.
  shapeFull, idxOf, entryOf, cppCommit: what stands in the commit field at the full size. They stand
    outside every noncomputable section. None of entryOf, idxOf, cppCommit has been run.
  riOf, saltLen, saltOf, fence, typed: the coins in the written committer's typed form.
    numerals_are: the shape's numerals.
  theCpp T prove: descriptionOfDataOnBytes flashProveData with that honest side; the prover is a letter.
THE STATEMENTS, each a definition of a proposition (where each is proved: at its name below):
  SaltAt Z: A FACT ON THE DESCRIPTION's FRAME, NOT ON THE COMMITTER: the plan that the library's
    planner makes of the public files has salts of 40 bytes. SaltInScope: at all files in scope that
    are read. IT IS NOT PROVED: where the planner rejects them, the description lays a fixed plan
    whose salts have no bytes; no theorem says that it rejects no files in scope.
  **TieAt T Z**, Tie T: THE TIE: at every hash function the written committer's value IS T.id's
    value. TieCellsAt, EntryIs: its core at any matrix of cells, and the digits' text. Proved at T
    := theTwin g: tieAt, tie (Johnson/Bind/Cpp/TheTie.lean); entryIs
    (Johnson/Bind/Cpp/ColumnAt.lean).
  **TieKeyAt Z**: the tie at the key: the written committer's typed key, spelled as the commitment
    ID's string spells it, is the running committer's root, out-of-domain (OOD) seeds and OOD
    answers. Proved under SaltAt Z: tieKeyAt (TheTie.lean).
  CountAt T Z, Count T: T.id's own number of queries. Proved at theTwin g: count_theTwin
    (Johnson/Bind/Cpp/AtTwin.lean).

Choices, and why.
- THE START OF A LEAF's HASH IS THE PUBLIC FILES' DIGEST c: A PUBLIC LABEL, NO COIN. By a reading,
  no theorem: the written committer's coding of queries spells a committed table's leaf as the
  format's string only where the typed salt's first 256 bits are c (leafOK2,
  OnBytes/TypedOracleCompiler/StringsStoredAt.lean); elsewhere it writes an escape and a total code: strings of no
  format. So a tie at other first bits would be false.
- A word from the prime on counts as its residue; a salt is cut, or filled with zero bytes, to the
  frame's length (Fmt.fit, the running committer's own rule). So no value of the randomness is
  malformed, and two values may name one setting of coins.
- The weights enter through the library's own matrix of digits (backThe). That this is the programs'
  placement or quantization is compared nowhere.
- The tie asks SaltAt Z alone: not "in scope", not "read", not that the description's test on the
  files (protocolDataWellFormed) passes: the leaf, the vertex, the OOD seed and the ID read c, the salt's length
  and constants of the full size alone. Under that premise alone it is proved (tie, TheTie.lean).

Limits.
- WITH T A LETTER the theorems under the tie say no more than the written committer's own law: that
  committer, read off the table, is itself a T that meets the tie (tie_has_member,
  Johnson/Bind/Cpp/Vapid.lean). What says more begins at T := theTwin g, where the tie is an
  equation between two closed texts.
- WHAT THE TIE CANNOT SEE: the encoder's symbol function, the frame of the strings and the weights'
  digits are ONE Lean text on both sides of the tie's equation, so an error in them shows on neither
  side. Of these only the first two are reached from outside, by the evaluations against the program
  at a small shape; the weights' digits are compared with the programs' nowhere. (Their names:
  Fmt.M1.symF; Fmt.oStr, Fmt.colBytes, Fmt.leafPlace; indexOfWeights.) What the tie compares is how
  the two committers put them together: the order and places of entries, pads and tails, the tree,
  the start and the salt of a leaf, the seeds' chain, the OOD answers, the name and the ID's string.
- withHonest turns four fields: Rand, sample, commit, prove. The field P (the honest provers of the
  three protocols, round by round: silent ones at descriptionOfDataOnBytes flashProveData), on which the types of keys and
  proofs hang, stays D's, and so do Shown, shown, Form and parse. So a prover from weights to a
  proof's bytes can be laid in; a description with other provers in P, another form or another
  parser is not reached.
- AT THE FULL-SIZE SHAPE: the commit field stands at the constant shapeFull, whatever the public
  files' own line on the table says; in scope that line is fixed. The shape's six numbers are public
  numbers of the full-size parameter file as Ladder/Stored.lean spells it (its lines
  "table 11 32 402653184 44040191 0 18", "answers 1", "record 1" and "salt 40"); 402653181 is
  402653184 less a row's three pads; 3076096 and 7 are the library's numbers of the matrix of digits
  (numsRef, Johnson/Flat/ThreeFull.lean); all are typed here as numerals, and numerals_are holds
  them against other Lean terms, not against that file.
- "Runs": Lean has code for it. Letters.commitAt has been run at one toy shape
  (Johnson/Bind/Cpp/Known.lean), the running committer's text at a few more
  (Johnson/Bind/TwinKnown.lean). AT THE FULL SIZE's SHAPE IT CAN NEVER BE RUN: 2^32 positions, 2^11
  rows and about 2^28.7 multiplications a symbol: about 2^72.
- The committer returns the commitment ID alone: no key file and nothing that a prover could read.
- One shape has three names: Bind.Cpp.shapeFull, Bind.Twin.fullShape (numerals_are ties these two),
  Bind.Column.shFull. One structure stands as two types: Bind.Cpp.Coins, Bind.Twin.Coins (the maps:
  Johnson/Bind/Cpp/WithSampler.lean).
- The tie's left side and SaltAt reach the second hash function by name (thePlan; T₀ over
  flashProveData).
- Nothing on soundness, completeness or index privacy (hiding); nothing on any program. theCpp is
  one more description with the verifier of the theorem on soundness; no goal is stated here.
The four fields of HonestSide are those of VerifierAndGoals.Description (Rand, sample, commit, prove:
Ladder.lean), with their types: withHonest fills that structure with them.







Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" above.

-/
import Johnson.Goal.Conditions.BindsTold
import Johnson.Goal.Conditions.MoreAtDigits
import Johnson.Top.CoinsAnchor
import Johnson.Bind.TwinAlgorithm
import Johnson.Bind.TwinBudget
import OnBytes.Maker.TablesBack
import OnBytes.Tie.DigestPoint
import OnBytes.K.IdSeedSpell
import Run.CodingPage160

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

/-! ## 0. General in the description: another honest side -/

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

/-- An honest side: the committer's randomness, its sampler, the committer, the prover. -/
structure HonestSide (Form : Type) where
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

/-- The description with another honest side. All that the verifier reads, the parser and the
extractor are D's own fields. -/
def _root_.VerifierAndGoals.Description.withHonest (D : Description) (H : HonestSide D.Form) : Description :=
  { D with
    Rand := H.Rand
    sample := H.sample
    commit := H.commit
    prove := H.prove }

end VerifierAndGoals.Fit

/-! ## 1. What runs -/

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open Bind.Twin (Shape Table)

/-- The committer's coins, each value by its address: the encoding randomness (row, place), the pads
(row, number), a leaf's salt bytes. No value has a length that could be wrong but a salt. -/
structure Coins where
  tail : ℕ → ℕ → UInt64
  pad : ℕ → ℕ → UInt64
  salt : ℕ → ByteArray

/-- The table of given plain entries and coins. -/
def Coins.table (x : Coins) (entry : ℕ → ℕ → UInt64) : Table := ⟨entry, x.tail, x.pad, x.salt⟩

/-- The committer's secret seed: 32 bytes, as a number. -/
abbrev Seed : Type := Fin (2 ^ 256 - 1 + 1)

/-- The randomness that an opener names: a seed, or the coins themselves. Free of the files. -/
abbrev Rand : Type := Seed ⊕ Coins

/-- **THE LETTERS.** id: the running committer: from a shape, the three public files and a table to
the commitment ID; it asks the files' digest c itself and lays c as every leaf's and vertex's start.
gen: a generator from the shape, a seed and two answers of the hash function (c and the coin key's
digest) to coins: A LETTER IN EVERY STATEMENT: no theorem reads what it is. -/
structure Letters where
  id : Shape → ByteArray → ByteArray → ByteArray → Table → DeterministicAlgorithm Commitment
  gen : Shape → Seed → Digest → Digest → Coins

/-- The letters at the running committer of Johnson/Bind/Twin.lean (Bind.Twin.twinID); the generator
stays a letter. -/
def theTwin (g : Shape → Seed → Digest → Digest → Coins) : Letters := ⟨Bind.Twin.twinID, g⟩

/-- The shape's six words, as a table's name has them. -/
def words (sh : Shape) : ByteArray :=
  TypedOracleCompiler.Run.SeedVals.shapeBytes sh.a sh.l sh.r sh.v sh.s sh.sigma

/-- **The committer, general in the shape, the files and the table.** It stands in the commit field
at the full size's shape. At a seed it asks c and the coin key's digest, makes the coins and runs
id; at coins it runs id. Johnson/Bind/Cpp/Known.lean runs this term at one toy shape; the wider
tests (Johnson/Bind/TwinKnown.lean) run Bind.Twin.commit, the same text (commitW) at the identity
monad and the format's own hash; Bind.Twin.evaluate_twinID ties twinID's value to commitO at every
hash function. -/
def Letters.commitAt (T : Letters) (sh : Shape) (Z : PublicFiles) (entry : ℕ → ℕ → UInt64) :
    Rand → DeterministicAlgorithm Commitment
  | .inl seed => .query (configString Z) fun c => .query (anchorString c (words sh)) fun I =>
      T.id sh Z.pol Z.lay Z.KL ((T.gen sh seed c I).table entry)
  | .inr x => T.id sh Z.pol Z.lay Z.KL (x.table entry)

/-- The full size's shape. -/
def shapeFull : Shape := ⟨32, 402653184, 44040191, 11, 1, 40⟩

/-- The matrix of digits of given weights: the index that backThe lays. -/
def idxOf (s : IntegerTransformer.Settings) (w : ModelWeights s) : Cm.Idx :=
  if hv : settingsAreValid s = true then indexOfWeights hv w
  else Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero

/-- The word of an integer: its least residue modulo the prime. -/
def wordOfInt (d : ℤ) : UInt64 := UInt64.ofNat (d % (Code.pGold : ℤ)).toNat

/-- **The table's plain entries at given weights**: entry e of row b is the digit at
(e / 2^kLo, b 2^kLo + e % 2^kLo), or 0 where the matrix has no such cell. -/
def entryOf (s : IntegerTransformer.Settings) (w : ModelWeights s) (b e : ℕ) : UInt64 :=
  if e / 2 ^ numsRef.kLo < numsRef.rows ∧
      b * 2 ^ numsRef.kLo + e % 2 ^ numsRef.kLo < 2 ^ (numsRef.kLo + 11) then
    wordOfInt ((idxOf s w).mat (e / 2 ^ numsRef.kLo) (b * 2 ^ numsRef.kLo + e % 2 ^ numsRef.kLo))
  else 0

/-- What stands in the commit field. -/
def cppCommit (T : Letters) (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (ρ : Rand) : DeterministicAlgorithm Commitment :=
  T.commitAt shapeFull Z (entryOf s w) ρ

/-- The bytes of a leaf's salt in the frame that the description lays at Z: off the plan that the
library's planner makes of the public files; 0 where it rejects them. -/
def saltLen (Z : PublicFiles) : ℕ := LPFD.Full.saltG (thePlan (asDescriptionFiles Z))

noncomputable section

/-! ## 2. The typed side of the coins -/

/-- The pads and the encoding randomness, read in the field: a word counts modulo the prime. -/
def riOf (Z : PublicFiles) (x : Coins) : (R₀ Z).protocol.EncodingRandomness :=
  (fun b j => toF (x.pad b.val j.val), fun b q => toF (x.tail b.val q.val))

/-- **The typed salts**: the files' digest c, then the leaf's salt bytes, cut or filled with zero
bytes to the frame's length: what the verifier's parser lays at a committed table. -/
def saltOf (Z : PublicFiles) (c : Digest) (x : Coins) : ℕ → Rom.Bits :=
  fun j => _root_.Run.leafSalt (_root_.Run.digToBytes c) (Fmt.fit (saltLen Z) (x.salt j))

/-- Whether the description's test on the files passes or fails, the frame's salt is the plan's. -/
theorem saltG_built (Z : PublicFiles) : LPFD.Full.saltG (dataAtFiles flashProveData Z).G = saltLen Z := by
  show LPFD.Full.saltG (flashProveData.filesParametersOrDefault (asDescriptionFiles Z)) = _
  unfold DescriptionData.filesParametersOrDefault
  split <;> rfl

/-- Every typed salt has the length that the written committer's coins ask, at every Z. -/
theorem fence (Z : PublicFiles) (c : Digest) (x : Coins) (j : ℕ) :
    (saltOf Z c x j).length = (R₀ Z).compilerParameters.sMT := by
  have h := OnBytes.Maker.length_leafSalt (_root_.Run.digToBytes c)
    (Fmt.fit (saltLen Z) (x.salt j))
  rw [_root_.Run.size_digToBytes, OnBytes.Tie.size_fit] at h
  rw [sMT_R₀, saltG_built]
  exact h

/-- The coins as a member of the written committer's coins at Z. -/
def typed (Z : PublicFiles) (c : Digest) (x : Coins) : Coins₀ Z :=
  ⟨(riOf Z x, saltOf Z c x), fun j _ => fence Z c x j⟩

/-- **The shape's numerals**: shapeFull bears the description's four numbers; its plain entries end
where the library's pads begin; it is the running committer's own fullShape
(Johnson/Bind/TwinBudget.lean, which holds its six words against the library's table of the full
size by a test); the matrix's two numbers. -/
theorem numerals_are :
    (shapeFull.a, shapeFull.l, shapeFull.r, shapeFull.v) =
        (frS.P.T.a, frS.P.T.l, frS.P.T.r, frS.P.v) ∧
      shapeFull.plain = 402653181 ∧ shapeFull = Bind.Twin.fullShape ∧
      ((3076096, 7) : ℕ × ℕ) = (numsRef.rows, numsRef.kLo) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3. What is owed -/

/-- **A FACT ON THE DESCRIPTION's FRAME AT Z, NOT ON THE COMMITTER**: the frame's salts have 40
bytes, the number that the table's name bears as a constant. Where the planner rejects the public
files this is false. -/
def SaltAt (Z : PublicFiles) : Prop := saltLen Z = 40

/-- The same at all public files in scope that are read. IT IS NOT PROVED: it says that the planner
returns at all of them, and no theorem says so. -/
def SaltInScope : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp → SaltAt Z

/-- **THE TIE AT Z.** At all settings and weights, all coins, every filling and EVERY hash function:
the written committer's value, at the matrix that backThe lays, at the coins read in the field and
at the typed salts "c, then the salt bytes", c the hash function's answer at the string of the three
public files, IS the running committer's ID at the full size's shape, at the table that the weights'
digits spell, and the same coins. -/
def TieAt (T : Letters) (Z : PublicFiles) : Prop :=
  ∀ (s : IntegerTransformer.Settings) (w : ModelWeights s) (x : Coins) (b : (R₀ Z).LeafBody)
    (hash : Hash),
    ((T₀ Z).commitAtCoins b (backThe Z s w) (riOf Z x)
        (saltOf Z (hash (configString Z)) x)).evaluate hash =
      (T.id shapeFull Z.pol Z.lay Z.KL (x.table (entryOf s w))).evaluate hash

/-- **THE TIE, whole**: at every Z at which the frame's salts have 40 bytes. It says nothing unless
some Z has them. -/
def Tie (T : Letters) : Prop := ∀ Z : PublicFiles, SaltAt Z → TieAt T Z

/-- The table's plain entries that a matrix of cells spells: the library's own words, pads of 0. -/
def entryOfCells (M : Cells (frS.toDecR frZ 402653181) numsRef) (b e : ℕ) : UInt64 :=
  cellEntry frS frZ 402653181 numsRef M (fun _ _ => 0) b e

/-- The tie's core: at every matrix of cells, weights or not. -/
def TieCellsAt (T : Letters) (Z : PublicFiles) : Prop :=
  ∀ (M : (R₀ Z).Index) (x : Coins) (b : (R₀ Z).LeafBody) (hash : Hash),
    ((T₀ Z).commitAtCoins b M (riOf Z x) (saltOf Z (hash (configString Z)) x)).evaluate hash =
      (T.id shapeFull Z.pol Z.lay Z.KL (x.table (entryOfCells M))).evaluate hash

/-- The running text of the table's entries is what backThe's matrix spells. -/
def EntryIs : Prop :=
  ∀ (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s),
    entryOf s w = entryOfCells (backThe Z s w)

/-- A typed key's root and OOD sample as the commitment ID's string spells them
(Fmt.publishedBytes):
the root's 32 bytes; the seeds as one flat list (seed by seed the coordinates, then the factor); the
answers. Of these the key file holds the root and the answers; the seeds and c are in no file: a
verifier computes them. -/
def keySpelled (cm : _root_.Iop.Dig 256) (rcd : RecFull) :
    ByteArray × List Fmt.Ext × List Fmt.Ext :=
  (_root_.Run.digToBytes cm, (OnBytes.K.IdTable.spellSeed 29 1 rcd.1).map OnBytes.E.triple,
    (OnBytes.K.IdTable.spellAns 11 1 rcd.2).map OnBytes.E.triple)

/-- The written committer's typed key at a hash function: the told part, the root, the OOD sample.
-/
def keyAt (Z : PublicFiles) (M : (R₀ Z).Index) (b : (R₀ Z).LeafBody) (x : Coins) (hash : Hash) :
    _root_.Iop.Dig 256 × TypedOracleCompiler.Compile.Batch.Cms.KeyRoot 256 (R₀ Z).protocol :=
  ((T₀ Z).keyAtCoins b M (riOf Z x) (saltOf Z (hash (configString Z)) x)).det
    (_root_.Run.famOne hash)

/-- **THE TIE AT THE KEY**, at every matrix of cells: the told part is the files' digest; the root,
the OOD seeds and the OOD answers, spelled, are those that the running committer, as a function over
the hash function read on byte strings, computes. With the ID's equation (SpellsId,
Johnson/Bind/Cpp/Spells.lean) it gives the tie's core. -/
def TieKeyAt (Z : PublicFiles) : Prop :=
  ∀ (M : (R₀ Z).Index) (x : Coins) (b : (R₀ Z).LeafBody) (hash : Hash),
    (keyAt Z M b x hash).1 = hash (configString Z) ∧
      keySpelled (keyAt Z M b x hash).2.cm (keyAt Z M b x hash).2.rcd =
        (fun o : Bind.Twin.Out => (o.root, Fmt.flatSeeds o.seeds, o.answers))
          (Bind.Twin.commitO (_root_.Run.oB hash) shapeFull [Z.pol, Z.lay, Z.KL]
            (x.table (entryOfCells M)))

/-- A bound on the running committer's own queries at the full size. Its calls of the format's hash:
c; 2^32 leaves; 2^32 - 1 vertices; the OOD seed's; the ID: about 2^33. A call costs at most two
queries. -/
def twinBudget : ℕ := 2 ^ 35

/-- **THE COUNT**, owed of the running committer as an algorithm: the tie speaks of values alone. -/
def CountAt (T : Letters) (Z : PublicFiles) : Prop :=
  ∀ t : Table, (T.id shapeFull Z.pol Z.lay Z.KL t).toRandomized.QueryBound twinBudget

/-- The count at all public files. -/
def Count (T : Letters) : Prop := ∀ Z : PublicFiles, CountAt T Z

/-! ## 4. The description -/

/-- The honest side: the opener names a seed or coins; the sampler samples a seed uniformly and asks
the hash function nothing; the committer is cppCommit; the prover is a letter. -/
def cppSide (T : Letters)
    (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
      List Token → RandomizedAlgorithm flashProveDescription.Form) : HonestSide flashProveDescription.Form where
  Rand := Rand
  sample := .sample (2 ^ 256 - 1) fun t => .done (.inl t)
  commit := cppCommit T
  prove := prove

/-- **THE DESCRIPTION**: descriptionOfDataOnBytes flashProveData with that honest side. -/
def theCpp (T : Letters)
    (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
      List Token → RandomizedAlgorithm flashProveDescription.Form) : SecondHashFunctionType → Description :=
  fun _ => flashProveDescription.withHonest (cppSide T prove)

/-- The algorithm that makes the written committer's coins of the randomness: it asks c, and at a
seed the coin key's digest. -/
def coinsAlg (T : Letters) (Z : PublicFiles) : Rand → DeterministicAlgorithm (Coins₀ Z)
  | .inl seed => .query (configString Z) fun c =>
      .query (anchorString c (words shapeFull)) fun I =>
        .done (typed Z c (T.gen shapeFull seed c I))
  | .inr x => .query (configString Z) fun c => .done (typed Z c x)

end

end Bind.Cpp

#print axioms Bind.Cpp.saltG_built
#print axioms Bind.Cpp.fence
#print axioms Bind.Cpp.numerals_are
