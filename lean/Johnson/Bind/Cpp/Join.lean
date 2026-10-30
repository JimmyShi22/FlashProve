-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Join.lean: THE JOIN AT THE FULL SIZE's TOLD STRUCTURE: where the frame's salts have
40 bytes (SaltAt Z), the seven equations of the interface (Johnson/Bind/Cpp/Spells.lean) give the
tie at the key; and the tie at the key with the ID's equation gives the tie's core
(Johnson/Bind/Cpp/Defs.lean). Two theorems, each to the letter of
a proposition that is defined there: `join_at : JoinAt Z` and `idJoin_at : IdJoinAt Z`. Beside them
`tieCells_of_seven`: the tie's core from the same premises, by the theorem at letters that goes up
to the commitment ID (`tie_of_spells`, Johnson/Bind/CoreTie.lean): its one call. Nobody calls
`idJoin_at`: it stands as the proof of IdJoinAt.

Why. The joint itself is proved at letters (Johnson/Bind/CoreValue.lean, the written committer's key
as a pure function of the typed oracles; Johnson/Bind/CoreJoin.lean, that key spelled against the
running committer). Here the letters are filled: the wire, the seed's wire and the typed oracles of
the told structure at Z and a hash function; the format's hash over that hash function; the full
size's shape; a digest spelled as its 32 bytes, a seed and the answers as a file spells them.

What is added to the letters, all bookkeeping:
  `size_hAt`, `turn`   under a number other than 162 the format's hash over a hash function gives 32
     bytes, so "the digest is the reading of these bytes" turns into "the digest's bytes are these".
  `cfg_at`   the running committer's first call gives the bytes of the files' digest.
  `cube_full`, `seedsW_full`   at the full size's shape a seed's point has 29 coordinates, and one
     seed is sampled.
  `flat_map`   the seeds as one flat list, spelled before or after flattening.
  `commitO_at`   the running committer over the hash function is `coreW` behind the files' digest.
  `saltOf_at`   where the frame's salts have 40 bytes, the typed salts are "c, then 40 bytes".
  `leafId_full`, `idId_full`, `id_coreW`, `recOf_snd`   definitions written out.
The premises of the joint at these letters, each from the interface's equations: `leaf_at`,
`treeSpells_at`, `seedSpells_at`, `ansSpells_at`, `idSpells_at`; `tie_at`: `tie_of_spells` taken at
the told structure at Z.
How the proofs are kept light: the told structure, the typed oracles and the hash on bytes are
compared by their names from a marked line on, and in the two joins the typed key and the running
committer's output are replaced by variables before anything is compared.

Limits. THE SEVEN PREMISES ARE NOT PROVED HERE, nor is it shown here that they can hold; AN EIGHTH
STANDS BESIDE THEM: SaltAt Z, which may fail (Defs.lean). Where one fails, these theorems say
nothing. Values alone: nothing on a count of queries; no binding of the commitment (the opening
form, BindsWith), no correctness of extraction, no index privacy (hiding of the weights); nothing on
any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Spells
import Johnson.Bind.CoreTie
import Johnson.Bind.Column
import Run.ParserHashProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.IdTable
open _root_.Iop (Dig)
open Bind.Core

/-! ### Bookkeeping -/

/-- Under a number other than 162 the format's hash over a hash function gives 32 bytes. -/
theorem size_hAt (hash : Hash) (n t i : ℕ) (st bs : ByteArray) (hn : n ≠ 162) :
    (Id.run (hAt hash n t i st bs)).size = 32 := by
  unfold hAt
  rw [Fmt.HM_id]
  unfold Fmt.HO
  rw [if_neg hn]
  exact _root_.Run.size_digToBytes _

/-- A digest that is the reading of 32 bytes has these bytes. -/
theorem turn {d : Dig 256} {v : ByteArray} (hv : v.size = 32) (h : d = _root_.Run.bytesToDig v) :
    _root_.Run.digToBytes d = v := by
  rw [h, _root_.Run.digToBytes_bytesToDig v hv]

/-- The running committer's first call gives the bytes of the files' digest. -/
theorem cfg_at (Z : PublicFiles) (hash : Hash) :
    Id.run (Fmt.configDigestW (m := Id) (hAt hash) [Z.pol, Z.lay, Z.KL]) = cAt Z hash := by
  unfold Fmt.configDigestW hAt
  rw [Fmt.HM_id]
  rfl

/-- At the full size's shape a seed's point has 29 coordinates. -/
theorem cube_full : shapeFull.cube = 29 := by decide +kernel

/-- At the full size's shape the running committer samples one seed with 29 coordinates. -/
theorem seedsW_full (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (name : ByteArray) :
    Id.run (Bind.Twin.seedsW h shapeFull name) =
      (Id.run (Fmt.recordSeedsW h .two name 29 1)).getD [] := by
  unfold Bind.Twin.seedsW
  rw [if_neg (show ¬ shapeFull.s = 0 by decide), cube_full]
  rfl

/-- Flattening a list of seeds commutes with spelling its elements. -/
theorem flat_map {A B : Type} (t : A → B) : ∀ l : List (List A × A),
    ((l.map fun y => (y.1.map t, t y.2)).flatMap fun y => y.1 ++ [y.2]) =
      (l.flatMap fun y => y.1 ++ [y.2]).map t
  | [] => rfl
  | y :: l => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_nil, flat_map t l]

/-- The running committer's leaf at the full size's shape, written out. -/
theorem leafId_full (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (cfg : ByteArray)
    (col : ℕ → List UInt64) (salt : ℕ → ByteArray) (j : ℕ) :
    Bind.Twin.leafId h shapeFull (fun _ => cfg) col salt j =
      Id.run (Fmt.leafW h 174 0 32 j cfg (col j) (Fmt.fit 40 (salt j))) := rfl

/-- A committed table's leaf over a hash function has 32 bytes. -/
theorem size_leafW (hash : Hash) (a x : ℕ) (st : ByteArray) (col : List UInt64)
    (salt : ByteArray) : (Id.run (Fmt.leafW (hAt hash) 174 0 a x st col salt)).size = 32 :=
  size_hAt hash _ _ _ _ _ (by decide)

/-- A vertex over a hash function has 32 bytes. -/
theorem size_vertexW (hash : Hash) (cfg l r : ByteArray) :
    (Id.run (Fmt.vertexW (hAt hash) cfg l r)).size = 32 :=
  size_hAt hash _ _ _ _ _ (by decide)

/-- The running committer's ID is the ID's text at its own root, seeds and answers. -/
theorem id_coreW (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (sh : Bind.Twin.Shape)
    (cfg : ByteArray) (col : ℕ → List UInt64) (T : Bind.Twin.Table) :
    (Id.run (Bind.Twin.coreW h sh cfg col T)).id =
      idId h sh cfg (Id.run (Bind.Twin.coreW h sh cfg col T)).root
        (Id.run (Bind.Twin.coreW h sh cfg col T)).seeds
        (Id.run (Bind.Twin.coreW h sh cfg col T)).answers := rfl

/-- The ID's text at the full size's shape, written out. -/
theorem idId_full (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (cfg root : ByteArray)
    (seeds : List (List Fmt.Ext × Fmt.Ext)) (given : List Fmt.Ext) :
    idId h shapeFull cfg root seeds given =
      Id.run (Fmt.publishedIDW h cfg (Fmt.tableName root cfg 32 402653184 44040191 11 1 40)
        (Fmt.flatSeeds seeds) given []) := rfl

/-- The second part of an honest OOD sample is the honest answer. -/
theorem recOf_snd {I X : Type} (L : _root_.Iop.HolographicProtocol I X) (i : I) (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) :
    (L.recOf i r s).2 = L.honestOutOfDomainAnswer i r s := rfl

/-- The running committer's columns at a table. -/
abbrev colAt (T : Bind.Twin.Table) : ℕ → List UInt64 :=
  Bind.Twin.columnOf shapeFull (Bind.Twin.laid shapeFull T)

/-- A column has 2^11 words. -/
theorem length_colAt (T : Bind.Twin.Table) (j : ℕ) : (colAt T j).length = 2 ^ 11 :=
  Bind.Column.length_columnOf shapeFull T j

/-- The running committer over the hash function, read on byte strings, is `coreW` behind the bytes
of the files' digest, at the plain encoder's columns. -/
theorem commitO_at (Z : PublicFiles) (hash : Hash) (T : Bind.Twin.Table) :
    Bind.Twin.commitO (_root_.Run.oB hash) shapeFull [Z.pol, Z.lay, Z.KL] T =
      Id.run (Bind.Twin.coreW (hAt hash) shapeFull (cAt Z hash) (colAt T) T) := by
  rw [← cfg_at]
  rfl

/-- Where the frame's salts have 40 bytes, the typed salts are "c, then 40 bytes". -/
theorem saltOf_at {Z : PublicFiles} (hs : SaltAt Z) (hash : Hash) (x : Coins) :
    saltOf Z (hash (configString Z)) x =
      fun i => _root_.Run.leafSalt (cAt Z hash) (Fmt.fit 40 (x.salt i)) := by
  unfold saltOf cAt
  rw [show saltLen Z = 40 from hs]

/-- The written committer's typed key at a hash function is the pure key. -/
theorem keyAt_value (Z : PublicFiles) (M : (R₀ Z).Index) (b : (R₀ Z).LeafBody) (x : Coins) (hash : Hash) :
    keyAt Z M b x hash =
      ((T₀ Z).part (dAt Z hash),
        keyF (R₀ Z).queryLayout ((T₀ Z).Sd (dAt Z hash)) (famAt Z hash) b M (riOf Z x)
          (saltOf Z (hash (configString Z)) x)) :=
  keyAtCoins_value (T₀ Z) b (_root_.Run.famOne hash) M (riOf Z x)
    (saltOf Z (hash (configString Z)) x)

/-! ### The letters, filled -/

/-- A typed seed as the running committer's list of seeds. -/
def spS (Z : PublicFiles) (sd : (R₀ Z).protocol.OutOfDomainSeed) : List (List Fmt.Ext × Fmt.Ext) :=
  (spellSeedL 29 1 sd).map fun y => (y.1.map OnBytes.E.triple, y.2.triple)

/-- The typed answers as the running committer's list of answers. -/
def spA (Z : PublicFiles) (a : (R₀ Z).protocol.OutOfDomainAnswer) : List Fmt.Ext := (spellAns 11 1 a).map OnBytes.E.triple

/-- The seeds as one flat list: the two spellings agree. -/
theorem flat_spS (Z : PublicFiles) (sd : (R₀ Z).protocol.OutOfDomainSeed) :
    Fmt.flatSeeds (spS Z sd) = (spellSeed 29 1 sd).map OnBytes.E.triple :=
  flat_map OnBytes.E.triple (spellSeedL 29 1 sd)

/- From here on Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed FlashProve.thePlan FlashProve.theItem

/-- **The tie at letters, taken at the told structure at Z and a hash function**: from the three
premises of the joint and the ID's, each at this file's names. -/
theorem tie_at (Z : PublicFiles) (hash : Hash) {b : (R₀ Z).LeafBody} {M : (R₀ Z).Index} {r : (R₀ Z).protocol.EncodingRandomness}
    {σ : ℕ → Bits} {T : Bind.Twin.Table}
    (Ht : TreeSpells (R₀ Z).queryLayout (famAt Z hash) (hAt hash) shapeFull (cAt Z hash)
      _root_.Run.digToBytes b ((R₀ Z).protocol.encodeIndex M r) σ (colAt T) T.salt)
    (Hs : SeedSpells (R₀ Z).queryLayout ((T₀ Z).Sd (dAt Z hash)) (famAt Z hash) (hAt hash) shapeFull
      (cAt Z hash) _root_.Run.digToBytes (spS Z))
    (Ha : AnsSpells shapeFull (spS Z) (spA Z) M r T)
    (Hi : ∀ k : KeyRoot 256 (R₀ Z).protocol,
      ZKCP.digestUnder hash (T₀ Z).encT ((T₀ Z).part (dAt Z hash), k) =
        _root_.Run.bytesToDig (idId (hAt hash) shapeFull (cAt Z hash) (_root_.Run.digToBytes k.cm)
          (spS Z k.rcd.1) (spA Z k.rcd.2))) :
    ((T₀ Z).commitAtCoins b M r σ).evaluate hash =
      _root_.Run.bytesToDig
        (Bind.Twin.commitO (_root_.Run.oB hash) shapeFull [Z.pol, Z.lay, Z.KL] T).id := by
  rw [← cfg_at] at Ht Hs Hi
  exact tie_of_spells Ht Hs Ha Hi

/- And these. -/
attribute [local irreducible] T₀ dAt famAt hAt cAt

/-! ### The three premises of the joint, from the interface's equations -/

/-- One leaf, at any word whose symbols are (position, column). -/
theorem leaf_at {Z : PublicFiles} {hash : Hash} (hl : SpellsLeaf Z hash)
    (y : Fin (R₀ Z).protocol.wordLength → (R₀ Z).protocol.Symbol) (col : ℕ → List UInt64) (salt : ℕ → ByteArray)
    (hlen : ∀ j, (col j).length = 2 ^ 11) (hy : ∀ j : Fin (R₀ Z).protocol.wordLength, y j = (j.val, col j.val))
    (b : (R₀ Z).LeafBody) (j : ℕ) (hj : j < (R₀ Z).protocol.wordLength) :
    _root_.Run.digToBytes (leafF (R₀ Z).queryLayout (famAt Z hash) (committerLeafInput (R₀ Z).queryLayout b y
                  (fun i => _root_.Run.leafSalt (cAt Z hash) (Fmt.fit 40 (salt i))) j)) =
      Bind.Twin.leafId (hAt hash) shapeFull (fun _ => cAt Z hash) col salt j := by
  have h1 : (y ⟨j, hj⟩).1 = j := congrArg Prod.fst (hy ⟨j, hj⟩)
  have h2 : (y ⟨j, hj⟩).2 = col j := congrArg Prod.snd (hy ⟨j, hj⟩)
  have e := hl y (fun i => Fmt.fit 40 (salt i)) b j hj (OnBytes.Tie.size_fit 40 _) h1
    (by rw [h2]; exact hlen j)
  rw [h2] at e
  rw [leafId_full]
  exact turn (size_leafW hash _ _ _ _ _) e

/-- The tree's single queries. -/
theorem treeSpells_at {Z : PublicFiles} (hs : SaltAt Z) {hash : Hash} (hl : SpellsLeaf Z hash)
    (hn : SpellsNode Z hash) (hc : ColumnIs Z) (M : (R₀ Z).Index) (x : Coins) (b : (R₀ Z).LeafBody) :
    TreeSpells (R₀ Z).queryLayout (famAt Z hash) (hAt hash) shapeFull (cAt Z hash) _root_.Run.digToBytes b
      ((R₀ Z).protocol.encodeIndex M (riOf Z x)) (saltOf Z (hash (configString Z)) x)
      (colAt (x.table (entryOfCells M))) (x.table (entryOfCells M)).salt where
  depth := rfl
  leaf := fun j hj => by
    rw [saltOf_at hs]
    exact leaf_at hl _ _ x.salt (length_colAt _) (hc M x) b j hj
  node := fun a c => turn (size_vertexW hash _ _ _) (hn a c)

/-- The seed's two queries. -/
theorem seedSpells_at {Z : PublicFiles} {hash : Hash} (h : SpellsSeed Z hash) :
    SeedSpells (R₀ Z).queryLayout ((T₀ Z).Sd (dAt Z hash)) (famAt Z hash) (hAt hash) shapeFull (cAt Z hash)
      _root_.Run.digToBytes (spS Z) := fun root => by
  unfold seedsId
  rw [seedsW_full]
  exact h root

/-- The answers. -/
theorem ansSpells_at {Z : PublicFiles} (h : AnswersAre Z) (M : (R₀ Z).Index) (x : Coins) :
    AnsSpells shapeFull (spS Z) (spA Z) M (riOf Z x) (x.table (entryOfCells M)) := fun sd => by
  have e := h M x sd
  rw [recOf_snd] at e
  unfold spA spS
  exact e

/-- The last query: the ID. -/
theorem idSpells_at {Z : PublicFiles} {hash : Hash} (hc : SpellsC Z hash) (hi : SpellsId Z hash)
    (k : KeyRoot 256 (R₀ Z).protocol) :
    ZKCP.digestUnder hash (T₀ Z).encT ((T₀ Z).part (dAt Z hash), k) =
      _root_.Run.bytesToDig (idId (hAt hash) shapeFull (cAt Z hash) (_root_.Run.digToBytes k.cm)
        (spS Z k.rcd.1) (spA Z k.rcd.2)) := by
  rw [show (T₀ Z).part (dAt Z hash) = hash (configString Z) from hc, idId_full, flat_spS]
  exact hi k.cm k.rcd

/-! ### The two joins -/

/-- **Where the frame's salts have 40 bytes (SaltAt Z), the seven give the tie at the key.** None of
the eight is proved in this file. -/
theorem join_at (Z : PublicFiles) : JoinAt Z := by
  intro hs hSp hc ha M x b hash
  have key := key_spelled
    (treeSpells_at hs (hSp hash).leaf (hSp hash).node hc M x b)
    (seedSpells_at (hSp hash).seed) (ansSpells_at ha M x)
  rw [keyAt_value, commitO_at]
  generalize keyF _ _ _ _ _ _ _ = K at key ⊢
  generalize Id.run (Bind.Twin.coreW _ _ _ _ _) = o at key ⊢
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨(hSp hash).c, ?_⟩
  show (_root_.Run.digToBytes K.cm, (spellSeed 29 1 K.rcd.1).map OnBytes.E.triple,
    (spellAns 11 1 K.rcd.2).map OnBytes.E.triple) = (o.root, Fmt.flatSeeds o.seeds, o.answers)
  rw [← h1, ← h2, ← h3, flat_spS]
  rfl

set_option maxRecDepth 100000 in
/-- **THE TIE AT THE KEY, WITH THE ID's EQUATION, GIVES THE TIE's CORE** at the running committer
of Johnson/Bind/Twin.lean (Bind.Twin.twinID). The statement does not read the generator g. -/
theorem idJoin_at (Z : PublicFiles) : IdJoinAt Z := by
  intro hk hid g M x b hash
  have h01 := hk M x b hash
  show ((T₀ Z).commitAtCoins b M (riOf Z x) (saltOf Z (hash (configString Z)) x)).evaluate hash =
    (Bind.Twin.twinID shapeFull Z.pol Z.lay Z.KL (x.table (entryOfCells M))).evaluate hash
  rw [evaluate_commitAtCoins, Bind.Twin.evaluate_twinID, commitO_at, id_coreW]
  rw [commitO_at] at h01
  change ZKCP.digestUnder hash (T₀ Z).encT (keyAt Z M b x hash) = _
  generalize keyAt Z M b x hash = k at h01 ⊢
  generalize Id.run (Bind.Twin.coreW _ _ _ _ _) = o at h01 ⊢
  obtain ⟨k1, cm, rcd⟩ := k
  obtain ⟨h0, h1⟩ := h01
  have h0' : k1 = hash (configString Z) := h0
  subst h0'
  unfold keySpelled at h1
  dsimp only at h1
  obtain ⟨r1, r23⟩ := Prod.mk.inj h1
  obtain ⟨r2, r3⟩ := Prod.mk.inj r23
  rw [hid hash cm rcd, idId_full, ← r1, ← r2, ← r3]
  rfl

/-- **Where the frame's salts have 40 bytes (SaltAt Z), the seven give the tie's core**: at every
matrix of cells, all coins, every filling and every hash function the written committer's value is
the running committer's ID. The statement does not read the generator g. By the theorem at letters
(`tie_of_spells`). -/
theorem tieCells_of_seven (Z : PublicFiles) (hs : SaltAt Z) (hSp : ∀ hash, Spells Z hash)
    (hc : ColumnIs Z) (ha : AnswersAre Z)
    (g : Bind.Twin.Shape → Seed → Digest → Digest → Coins) : TieCellsAt (theTwin g) Z := by
  intro M x b hash
  show ((T₀ Z).commitAtCoins b M (riOf Z x) (saltOf Z (hash (configString Z)) x)).evaluate hash =
    (Bind.Twin.twinID shapeFull Z.pol Z.lay Z.KL (x.table (entryOfCells M))).evaluate hash
  rw [Bind.Twin.evaluate_twinID]
  exact tie_at Z hash (treeSpells_at hs (hSp hash).leaf (hSp hash).node hc M x b)
    (seedSpells_at (hSp hash).seed) (ansSpells_at ha M x)
    (idSpells_at (hSp hash).c (hSp hash).id)

end Bind.Cpp

end

#print axioms Bind.Cpp.size_hAt
#print axioms Bind.Cpp.turn
#print axioms Bind.Cpp.cfg_at
#print axioms Bind.Cpp.cube_full
#print axioms Bind.Cpp.seedsW_full
#print axioms Bind.Cpp.flat_map
#print axioms Bind.Cpp.leafId_full
#print axioms Bind.Cpp.size_leafW
#print axioms Bind.Cpp.size_vertexW
#print axioms Bind.Cpp.id_coreW
#print axioms Bind.Cpp.idId_full
#print axioms Bind.Cpp.recOf_snd
#print axioms Bind.Cpp.length_colAt
#print axioms Bind.Cpp.commitO_at
#print axioms Bind.Cpp.saltOf_at
#print axioms Bind.Cpp.keyAt_value
#print axioms Bind.Cpp.flat_spS
#print axioms Bind.Cpp.tie_at
#print axioms Bind.Cpp.idSpells_at
#print axioms Bind.Cpp.leaf_at
#print axioms Bind.Cpp.treeSpells_at
#print axioms Bind.Cpp.seedSpells_at
#print axioms Bind.Cpp.ansSpells_at
#print axioms Bind.Cpp.join_at
#print axioms Bind.Cpp.idJoin_at
#print axioms Bind.Cpp.tieCells_of_seven
