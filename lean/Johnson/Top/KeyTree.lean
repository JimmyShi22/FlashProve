-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/KeyTree.lean: the reading of a key file as ONE algorithm over the hash function: it asks
the function for the public digests and then reads the file with the reader's hash asked.

`keyAt8` (Johnson/Top/PreThreeKey.lean) is the key file's part at public digests d. Here `pub8`
(Johnson/Top/PreThreePub.lean), which draws d, stands in front. Definitions; one small law with a
proof of its own (`par7_length`); four laws that are compositions of laws of the files beneath.

Main names:
  `keyTree Gd Z ty`: a key file's bytes to an algorithm over the hash function. It asks for the
    digest of Z's three public files and for seven digests of parameter bytes; takes the planner's
    plain steps at the first; parses the file's head; runs the key file's reader with its hash
    asked, its three calls with the number 169 answered out of what was drawn; and types what was
    read, at the digest that stands in the one-time chain's parameters. It sees the key file alone:
    the public files are Z's: fixed before a function is drawn where Z is; here Z is a letter beside
    g.
  `par7_length`, `pub8_queries`: `pub8` asks at most eight strings.
  `keyTree_noCoin`: no coin. No premise.
  `keyTree_asks`: at most 8 + `cKey` p₀ t₀ questions, at every file, under three premises on a
    reference plan at Z's files.
  `keyTree_det`: under every family g its value is that of the reading without a pin at g's own
    digest.
  `keyTreeFull`, `keyTreeSmall`: at the typing of Johnson/Top/KeyTypesRead.lean.
Limits: ty is a letter in the first five. Nothing on what the reading returns. That the digest in
the one-time chain's parameters is the digest that was drawn is a law on the planner's plain steps;
it is not shown here. NO LAW ON THE LOG STANDS HERE: `keyTree_det` is on values. By the text, all
that the reading without a pin asks stands in this tree's log, the three pinned strings in `pub8`'s
part; no theorem says so. The log holds up to four strings that the key file's check never asks: of
the parameter bytes of the entry's chain and of the proof file's three. The planner's plain steps
(`plannedAt`) hash with the second hash function, a fixed function, at places that read the three
public files alone. Gd enters through the first of the seven strings alone: it is idle for the key
file's reading. No tie. No probability. Nothing on soundness.
`set_option maxRecDepth`: at the default Lean stops at `pub8_queries`.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.PreThreeKey
import Johnson.Top.KeyTypesRead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open OnBytes _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm.Pub (D8 pub8 par7 cfg8 key8 pub8_noCoin s0Of ssOf partKU)
open OnBytes.KeyLink (ksPlanned ksPlanned_wipe)
open OnBytes.Tie (preTQ_noCoin preTQ_asks_one plannedAt)
open _root_.Run (digToBytes)

/-- At most seven strings of parameter bytes. -/
theorem par7_length (Gd : OnBytes.Tie.EntryGround) (pol KL lay c : ByteArray) :
    (par7 Gd pol KL lay c).length ≤ 7 := by
  unfold par7
  cases plannedAt pol KL (some lay) c <;> simp

/-- The public algorithm asks at most eight strings. -/
theorem pub8_queries (Gd : OnBytes.Tie.EntryGround) (pol KL lay : ByteArray) :
    (pub8 Gd pol KL lay).QueryBound (7 + 1) :=
  pubN_queries _ _ _ 7 fun c => by
    unfold ssOf
    rw [List.length_map]
    exact par7_length Gd pol KL lay _

section
variable {Out : Type} (Gd : OnBytes.Tie.EntryGround) (Z : K.Pub)
  (ty : ByteArray → Params.TableName → OnBytes.Proof.TailRead → ByteArray → List ByteArray →
    Option Out)

/-- **The reading of a key file as one algorithm over the hash function.** -/
def keyTree (uK : ByteArray) : OComp (rom 256) (Option Out) :=
  (pub8 Gd Z.pol Z.KL Z.lay).bind fun d => keyAt8 Z.pol Z.KL Z.lay ty d uK

/-- It tosses no coin. -/
theorem keyTree_noCoin (uK : ByteArray) : (keyTree Gd Z ty uK).NoCoin :=
  OComp.NoCoin.bind (pub8_noCoin _ _ _ _) fun _ => preTQ_noCoin _ _ _ _ _ _

/-- **One number at every file.** -/
theorem keyTree_asks {c₀ : ByteArray} {p₀ : OnBytes.Model.Verify.Planned} (hc₀ : c₀.size = 32)
    (hp₀ : plannedAt Z.pol Z.KL (some Z.lay) c₀ = .ok p₀)
    (hb₀ : ∀ n : OnBytes.Model.Verify.ChainName, (p₀.chains.bytes n).size < 2 ^ 64)
    (t₀ : Params.TableName) (uK : ByteArray) :
    (keyTree Gd Z ty uK).QueryBound (7 + 1 + cKey p₀ t₀) :=
  OComp.QueryBound.bind (pub8_queries _ _ _ _) fun d =>
    preTQ_asks_one _ _ _ _ p₀.chains.key t₀
      (fun d' _ hk => ksPlanned_wipe hp₀ hc₀ hb₀ (_root_.Run.size_digToBytes (cfg8 d')) hk) d uK

/-- **Under every family its value is that of the reading without a pin, at g's own digest.** -/
theorem keyTree_det (g : Fam (rom 256)) (uK : ByteArray) :
    (keyTree Gd Z ty uK).det g =
      (partKU (ksPlanned Z.pol Z.KL Z.lay) (asmSlotC ty)
        (digToBytes (g () (s0Of Z.pol Z.lay Z.KL))) uK).det g := by
  unfold keyTree
  rw [OComp.det_bind]
  exact keyAt8_unseen Gd Z.pol Z.KL Z.lay g ty uK

end

open OnBytes.Flat OnBytes.Slice OnBytes.RunA VerifiableInference.OnPublicFiles OnBytes.K.Arm in
/-- **At the full size**, at the typing of Johnson/Top/KeyTypesRead.lean; the table rides along. -/
def keyTreeFull {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A)
    (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)
    (Gd : OnBytes.Tie.EntryGround) (Z : K.Pub) (sb : ℕ) : ByteArray →
    OComp (rom 256) (Option (Params.TableName ×
      OneProtocolProof 256 (batTC (LrG (restFullAt A E G P)) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT))) :=
  keyTree Gd Z fun cfg t r s q => (tyReadFull A E G P sb cfg t r s q).map fun π => (t, π)

open OnBytes.Flat OnBytes.Slice OnBytes.RunA VerifiableInference.OnPublicFiles OnBytes.K.Arm in
/-- **At the small size.** -/
def keyTreeSmall {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A)
    (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)
    (Gd : OnBytes.Tie.EntryGround) (Z : K.Pub) (sb : ℕ) : ByteArray →
    OComp (rom 256) (Option (Params.TableName ×
      OneProtocolProof 256 (batTC (LrG (restSmallAt A E G P)) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT))) :=
  keyTree Gd Z fun cfg t r s q => (tyReadSmall A E G P sb cfg t r s q).map fun π => (t, π)

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.pub8_queries
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyTree_noCoin
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyTree_asks
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyTree_det
