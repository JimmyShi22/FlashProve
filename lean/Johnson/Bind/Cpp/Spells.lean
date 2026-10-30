-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Spells.lean: THE INTERFACE BETWEEN THE TWO SIDES OF THE TIE's PROOF
(Johnson/Bind/Cpp/Defs.lean: TieKeyAt, TieCellsAt). Definitions of propositions alone: NOTHING IS
PROVED HERE.

Why. The written committer asks typed oracles, which are read out of one hash function through a
coding of typed queries into strings. The running committer asks the format's hash at strings of
bytes. Both come to one function of an oracle on bytes (Bind.Twin.commitO, Johnson/Bind/Twin.lean;
for the running committer that is Bind.Twin.evaluate_twinID, Johnson/Bind/TwinAlgorithm.lean). What
is left falls into two parts that can be proved apart.
  LEFT OF THE INTERFACE (Spells): five equations, each "a typed query's answer IS the format's own
    function at the hash function, read on byte strings". They name no running committer.
      SpellsC: the told part of the public reading is the files' digest c.
      SpellsLeaf: a leaf's answer, at the body of a stored table's symbol and the typed salt "c,
        then the salt bytes", is Fmt.leafW under the number 174 at the start c.
      SpellsNode: a vertex's answer is Fmt.vertexW at the start c.
      SpellsSeed: the out-of-domain (OOD) seed that the two typed queries at a root give, spelled,
        is Fmt.recordSeedsW at the table's name.
      SpellsId: the hash function's answer at the told code of a key is Fmt.publishedIDW.
  RIGHT OF IT (ColumnIs, AnswersAre): the written encoder's symbols and OOD answers, as words, are
    the running committer's lists. They name no hash function, no query and no string.
The frame's salt (SaltAt, Defs.lean) enters at SpellsLeaf alone, as a hypothesis of whoever proves
it.
Limits. That these seven suffice for the tie is not shown here (it is in Johnson/Bind/Cpp/Join.lean;
where each of the seven is proved: the head of Johnson/Bind/Cpp/TheTie.lean). They are stated at the
full size's told structure; the running committer's text is general in the shape.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Defs
import Run.DetOverOne

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

/-- The public reading's value at a hash function. -/
def dAt (Z : PublicFiles) (hash : Hash) : (T₀ Z).D := (T₀ Z).Pub.det (_root_.Run.famOne hash)

/-- The typed oracles that are read out of a hash function through the coding at that value. -/
def famAt (Z : PublicFiles) (hash : Hash) :
    Fam (typedOracleFamily 256 (R₀ Z).queryLayout.K (typedOracleCarrier (R₀ Z).protocol (R₀ Z).LeafBody (R₀ Z).offlineRoundSplits (R₀ Z).linkRoundSplits)) :=
  readBlocks ((T₀ Z).m (dAt Z hash)) (_root_.Run.famOne hash)

/-- The format's hash over the hash function, read on byte strings. -/
def hAt (hash : Hash) : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray :=
  Fmt.HM (m := Id) (_root_.Run.oB hash)

/-- The bytes of the files' digest. -/
def cAt (Z : PublicFiles) (hash : Hash) : ByteArray := _root_.Run.digToBytes (hash (configString Z))

/-- The first table's name at a root. -/
def nameAt (Z : PublicFiles) (hash : Hash) (root : Dig 256) : ByteArray :=
  Fmt.tableName (_root_.Run.digToBytes root) (cAt Z hash) 32 402653184 44040191 11 1 40

/-- The told part is the files' digest. -/
def SpellsC (Z : PublicFiles) (hash : Hash) : Prop := (T₀ Z).part (dAt Z hash) = hash (configString Z)

/-- A leaf's answer is the format's leaf hash under 174, at the start c. -/
def SpellsLeaf (Z : PublicFiles) (hash : Hash) : Prop :=
  ∀ (y : Fin (R₀ Z).protocol.wordLength → (R₀ Z).protocol.Symbol) (u : ℕ → ByteArray) (b : (R₀ Z).LeafBody) (j : ℕ)
    (hj : j < (R₀ Z).protocol.wordLength), (u j).size = 40 → (y ⟨j, hj⟩).1 = j → (y ⟨j, hj⟩).2.length = 2 ^ 11 →
    (famAt Z hash OracleName.leaf
        (committerLeafInput (R₀ Z).queryLayout b y (fun i => _root_.Run.leafSalt (cAt Z hash) (u i)) j) : Dig 256) =
      _root_.Run.bytesToDig
        (Fmt.leafW (m := Id) (hAt hash) 174 0 32 j (cAt Z hash) (y ⟨j, hj⟩).2 (u j))

/-- A vertex's answer is the format's vertex hash, at the start c. -/
def SpellsNode (Z : PublicFiles) (hash : Hash) : Prop :=
  ∀ a b : Dig 256, (committerNodeHash (R₀ Z).queryLayout a b).det (famAt Z hash) =
    _root_.Run.bytesToDig (Fmt.vertexW (m := Id) (hAt hash) (cAt Z hash)
      (_root_.Run.digToBytes a) (_root_.Run.digToBytes b))

/-- The OOD seed that the written committer reads at a root. -/
def seedAtRoot (Z : PublicFiles) (hash : Hash) (root : Dig 256) : (R₀ Z).protocol.OutOfDomainSeed :=
  ((T₀ Z).Sd (dAt Z hash)).seed
    (famAt Z hash (OracleName.fb ((T₀ Z).Sd (dAt Z hash)).t)
      (seedQ1 (R₀ Z).queryLayout ((T₀ Z).Sd (dAt Z hash))
        (link (famAt Z hash (OracleName.fb ((T₀ Z).Sd (dAt Z hash)).t)
          (seedQ0 (R₀ Z).queryLayout ((T₀ Z).Sd (dAt Z hash)) root) : FsAns 256 (R₀ Z).queryLayout.K))) :
      FsAns 256 (R₀ Z).queryLayout.K).1

/-- That seed, spelled, is the format's draw from the table's name. -/
def SpellsSeed (Z : PublicFiles) (hash : Hash) : Prop :=
  ∀ root : Dig 256, (spellSeedL 29 1 (seedAtRoot Z hash root)).map
      (fun y => (y.1.map OnBytes.E.triple, y.2.triple)) =
    (Fmt.recordSeedsW (m := Id) (hAt hash) .two (nameAt Z hash root) 29 1).getD []

/-- The answer at the key's code is the format's commitment ID. -/
def SpellsId (Z : PublicFiles) (hash : Hash) : Prop :=
  ∀ (root : Dig 256) (rcd : (R₀ Z).protocol.Rec),
    ZKCP.digestUnder hash (T₀ Z).encT (hash (configString Z), ⟨root, rcd⟩) =
      _root_.Run.bytesToDig (Fmt.publishedIDW (m := Id) (hAt hash) (cAt Z hash)
        (nameAt Z hash root) ((spellSeed 29 1 rcd.1).map OnBytes.E.triple)
        ((spellAns 11 1 rcd.2).map OnBytes.E.triple) [])

/-- **THE LEFT SIDE's DEBT**, at Z and a hash function. It names no running committer. -/
structure Spells (Z : PublicFiles) (hash : Hash) : Prop where
  c : SpellsC Z hash
  leaf : SpellsLeaf Z hash
  node : SpellsNode Z hash
  seed : SpellsSeed Z hash
  id : SpellsId Z hash

/-- The written encoder's symbol at a position is the running committer's column there. It names no
hash function. -/
def ColumnIs (Z : PublicFiles) : Prop :=
  ∀ (M : (R₀ Z).Index) (x : Coins) (j : Fin (R₀ Z).protocol.wordLength),
    (R₀ Z).protocol.encodeIndex M (riOf Z x) j =
      (j.val, Bind.Twin.columnOf shapeFull
        (Bind.Twin.laid shapeFull (x.table (entryOfCells M))) j.val)

/-- The written committer's OOD answers at a seed, spelled, are the running committer's at the
spelled seed. It names no hash function. -/
def AnswersAre (Z : PublicFiles) : Prop :=
  ∀ (M : (R₀ Z).Index) (x : Coins) (sd : (R₀ Z).protocol.OutOfDomainSeed),
    (spellAns 11 1 ((R₀ Z).protocol.recOf M (riOf Z x) sd).2).map OnBytes.E.triple =
      Bind.Twin.answers shapeFull (x.table (entryOfCells M))
        ((spellSeedL 29 1 sd).map fun y => (y.1.map OnBytes.E.triple, y.2.triple))

/-- **The join**: where the frame's salts have 40 bytes, the seven give the tie at the key. Proved:
join_at (Johnson/Bind/Cpp/Join.lean). -/
def JoinAt (Z : PublicFiles) : Prop :=
  SaltAt Z → (∀ hash, Spells Z hash) → ColumnIs Z → AnswersAre Z → TieKeyAt Z

/-- And the tie at the key, with the ID's equation, gives the tie's core at the running committer of
Johnson/Bind/Twin.lean (Bind.Twin.twinID). Proved: idJoin_at (Johnson/Bind/Cpp/Join.lean). -/
def IdJoinAt (Z : PublicFiles) : Prop :=
  TieKeyAt Z → (∀ hash, SpellsId Z hash) →
    ∀ g : Bind.Twin.Shape → Seed → Digest → Digest → Coins, TieCellsAt (theTwin g) Z

end Bind.Cpp

end
