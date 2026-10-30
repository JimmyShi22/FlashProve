-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/CoreTie.lean: THE WRITTEN COMMITTER's COMMITMENT IS THE RUNNING COMMITTER's ID, UNDER
NAMED EQUATIONS. General in the input, the told structure, the shape of the committed table, the
public files, the oracle on bytes and the three spellings: one theorem for every size.

Why. Johnson/Bind/CoreValue.lean writes the written committer's commitment at given coins
(`LayoutsByPublicReading.commitAtCoins`, Johnson/Top/ToldCommitPlain.lean) as a pure function of a hash function.
Johnson/Bind/CoreJoin.lean compares the typed key with the running committer behind the public
files' digest. Here the two are put together, up to the commitment ID and down to the running
committer's first call (`Bind.Twin.commitO`, Johnson/Bind/Twin.lean).

Main names (namespace `Bind.Core`).
  `IdSpells`   what is owed of the last query: at every typed key, the hash function's answer at the
    told code of (the told part, the key) is the reading of the format's ID at the spelled key.
  **`tie_of_spells`**   from `TreeSpells`, `SeedSpells`, `AnsSpells` (CoreJoin.lean) and `IdSpells`,
    taken at the typed oracles that are read out of the hash function through the told coding, and
    at the digest that the running committer's first call gives.

Limits. The four premises are owed by whoever calls this: NOTHING HERE SAYS THAT THEY HOLD AT ANY
SIZE. At the full size it is called once (tie_at, for tieCells_of_seven:
Johnson/Bind/Cpp/Join.lean), under premises that other files prove, one of them where the frame's
salts have 40 bytes (Johnson/Bind/Cpp/TheTie.lean). No told structure of a small size is written in
this library, so at a small size it has no instance. The oracle on bytes O and the hash function are
tied by the premises alone. Values alone: nothing on a count of queries; no binding of the
commitment (the opening form, BindsWith), no correctness of extraction, no index privacy (hiding of
the weights); nothing on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.CoreJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Bind.Core
open Rom ZKCP VerifiableInference VerifiableInference.OnPublicFiles Bind.Twin
open Fmt (Ext)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop (Dig)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (hash : Hash) (O : ByteArray → ByteArray) (sh : Shape)
  (files : List ByteArray) (sp : Dig 256 → ByteArray) (spS : R.protocol.OutOfDomainSeed → List (List Ext × Ext))
  (spA : R.protocol.OutOfDomainAnswer → List Ext)

/-- The public reading's value at a hash function. -/
abbrev dOf : T.D := T.Pub.det (_root_.Run.famOne hash)

/-- The typed oracle functions that are read out of a hash function through the told coding. -/
abbrev famOf : Fam (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) :=
  readBlocks (T.m (dOf T hash)) (_root_.Run.famOne hash)

/-- The digest of the public files that the running committer's first call gives. -/
abbrev cfgOf : ByteArray := Id.run (Fmt.configDigestW (m := Id) (Fmt.HM (m := Id) O) files)

/-- **What is owed of the last query.** -/
def IdSpells : Prop :=
  ∀ k : KeyRoot 256 R.protocol, ZKCP.digestUnder hash T.encT (T.part (dOf T hash), k) =
    _root_.Run.bytesToDig
      (idId (Fmt.HM (m := Id) O) sh (cfgOf O files) (sp k.cm) (spS k.rcd.1) (spA k.rcd.2))

variable {T hash O sh files sp spS spA}

/-- **The tie, general in the told structure, the shape and the spellings**: under the four premises
the written committer's value at a hash function is the running committer's commitment ID, read as a
digest. -/
theorem tie_of_spells {b₀ : R.LeafBody} {i : R.Index} {r : R.protocol.EncodingRandomness} {σ : ℕ → Bits} {Tb : Table}
    (Ht : TreeSpells R.queryLayout (famOf T hash) (Fmt.HM (m := Id) O) sh (cfgOf O files) sp b₀
      (R.protocol.encodeIndex i r) σ (columnOf sh (laid sh Tb)) Tb.salt)
    (Hs : SeedSpells R.queryLayout (T.Sd (dOf T hash)) (famOf T hash) (Fmt.HM (m := Id) O) sh (cfgOf O files)
      sp spS)
    (Ha : AnsSpells sh spS spA i r Tb) (Hi : IdSpells T hash O sh files sp spS spA) :
    (T.commitAtCoins b₀ i r σ).evaluate hash =
      _root_.Run.bytesToDig (commitO O sh files Tb).id := by
  rw [commitAtCoins_value]
  exact id_spelled Ht Hs Ha (fun k => ZKCP.digestUnder hash T.encT (T.part (dOf T hash), k))
    _root_.Run.bytesToDig Hi

end Bind.Core

end

#print axioms Bind.Core.tie_of_spells
