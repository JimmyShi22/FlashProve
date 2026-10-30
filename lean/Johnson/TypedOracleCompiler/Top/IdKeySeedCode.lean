-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean: the commitment ID's string with the record's seed in it, as the
code of the verifier's typed key: no bit string is the code of two keys, if the spellings of a
record's answers and seed are one to one and, at the key that also holds c, c is determined by its
digests.

What this file states. The string is that of OnBytes/Tie/IdKeySeed.lean, with the record's seed and
the further public digests in it. `idCodeSeed S cfg told` is the code of a key (root, record), with
the configuration's digest and the further digests as constants (`idCodeSeed_oneToOne`). `encSeed S
cfgOf toldOf` is the code of a key (c, (root, record)): the digests are read off c; it is one
function, which holds nothing of any hash. `encSeed_oneToOne`: if c is determined by its digests.
`commitmentBinds_seed`, `commitmentBinds_encSeed`: `Rec.CommitmentBinds` at these codes, for every
scheme G over such keys and every extractor E: at the library's extractor, which reads the
commitment and the committer's log alone, and at (t + 2)² / 2^256. A string that holds the root and
the answers and leaves the record's seed out (Johnson/Top/IdKeyCode.lean) is, on keys (root, (seed,
answers)), one to one only up to the seed, so the library's theorem on a key behind a digest
(`ZKCP.HasIndexBindingWith.digestKey`; `Rec.commitmentBinds_of_code`, Johnson/Top/FrontCommit.lean),
whose one premise is `ZKCP.CodeIsOneToOne`, cannot be called at it.

Under which hypotheses. Two premises on parameters: the two spellings are one to one; and a third
for `encSeed_oneToOne` and `commitmentBinds_encSeed`: c is determined by its digests. They are shown
of no object here. (`IdSpellS L` holds the tables' shape, and how a record's answers and its seed
are spelled as lists of field elements.)

What it does not show. A key has a code only within `OnBytes.Tie.idOkS`: at a cfg or a further
digest that has not 32 bytes, or at a shape out of range, no key has one, and the theorems here then
hold vacuously: they claim nothing there. That every key has a code is shown at two written sets of
fixed public parameters in Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean. That the programs spell the ID's
string so is not said here (OnBytes/Tie/IdKeySeed.lean, Limits; that the string is
`Fmt.publishedBytes`: OnBytes/Tie/IdKeySeedFmt.lean). `Rec.CommitmentBinds` is an implication: from
index binding of the scheme whose verifier holds the key itself, with an extractor that reads key
and log alone; that antecedent is shown of no scheme here. Nothing says that a key's seed is the
hash function's at its root, or that its c is the digest of any files: that is for the checks to
test. Soundness alone. For proofs only; the program does not import this file.


-/
import OnBytes.Tie.IdKeySeed
import Johnson.Top.IdKeyCode
import Johnson.Top.FrontCommit
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.VerifiableInference.Rec
open Rom ZKCP _root_.VerifiableInference _root_.VerifiableInference.Rec
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type}

/-- The tables' shape, and how a record's answers and its seed are spelled. -/
structure IdSpellS (L : HolographicProtocol I X) where
  /-- the tables' shape: the six words of a table's name -/
  shape   : OnBytes.Params.IndexShape
  /-- the answers of a record, as the list of elements that a key file holds -/
  answers : L.OutOfDomainAnswer → List OnBytes.E
  /-- the seed of a record, as the list of elements that the programs draw -/
  seed    : L.OutOfDomainSeed → List OnBytes.E

variable {L : HolographicProtocol I X}

/-- The key as the byte format has it, at a configuration's digest and told digests. -/
def IdSpellS.keyAt (S : IdSpellS L) (cfg : ByteArray) (told : List ByteArray)
    (k : KeyRoot 256 L) : OnBytes.Tie.IdKeyS :=
  ⟨(S.shape, cfg, ⟨_root_.Run.digToBytes k.cm, S.answers k.rcd.2⟩), S.seed k.rcd.1, told⟩

/-- The code of a key (root, record); the digests are constants. -/
def idCodeSeed (S : IdSpellS L) (cfg : ByteArray) (told : List ByteArray) (k : KeyRoot 256 L) :
    Option ZKCP.Str :=
  OnBytes.Tie.idCodeS (S.keyAt cfg told k)

/-- Two keys that the byte format has as one are one. -/
theorem IdSpellS.keyAt_inj (S : IdSpellS L) (hA : Function.Injective S.answers)
    (hS : Function.Injective S.seed) {cfg cfg' : ByteArray} {told told' : List ByteArray}
    {k k' : KeyRoot 256 L} (q : S.keyAt cfg told k = S.keyAt cfg' told' k') :
    cfg = cfg' ∧ told = told' ∧ k = k' := by
  have q1 : cfg = cfg' := congrArg (fun x => x.base.2.1) q
  have q2 : (⟨_root_.Run.digToBytes k.cm, S.answers k.rcd.2⟩ : OnBytes.Params.TableName) =
      ⟨_root_.Run.digToBytes k'.cm, S.answers k'.rcd.2⟩ := congrArg (fun x => x.base.2.2) q
  have q3 : S.seed k.rcd.1 = S.seed k'.rcd.1 := congrArg (fun x => x.seed) q
  have q4 : told = told' := congrArg (fun x => x.told) q
  obtain ⟨c, s, a⟩ := k
  obtain ⟨c', s', a'⟩ := k'
  have r := OnBytes.Params.TableName.mk.inj q2
  have e1 : c = c' := digToBytes_injective r.1
  have e2 : a = a' := hA r.2
  have e3 : s = s' := hS q3
  subst e1 e2 e3
  exact ⟨q1, q4, rfl⟩

/-- **No bit string is the code of two keys (root, record).** -/
theorem idCodeSeed_oneToOne (S : IdSpellS L) (hA : Function.Injective S.answers)
    (hS : Function.Injective S.seed) (cfg : ByteArray) (told : List ByteArray) :
    ZKCP.CodeIsOneToOne (idCodeSeed S cfg told) := fun _ _ code e e' =>
  (S.keyAt_inj hA hS (OnBytes.Tie.idCodeS_oneToOne _ _ code e e')).2.2

variable {C : Type}

/-- The code of a key (c, (root, record)): the digests are read off c. -/
def encSeed (S : IdSpellS L) (cfgOf : C → Dig 256) (toldOf : C → List (Dig 256))
    (k : C × KeyRoot 256 L) : Option ZKCP.Str :=
  OnBytes.Tie.idCodeS
    (S.keyAt (_root_.Run.digToBytes (cfgOf k.1)) ((toldOf k.1).map _root_.Run.digToBytes) k.2)

/-- **No bit string is the code of two keys (c, (root, record))**, if c is determined by its
digests. -/
theorem encSeed_oneToOne (S : IdSpellS L) (hA : Function.Injective S.answers)
    (hS : Function.Injective S.seed) {cfgOf : C → Dig 256} {toldOf : C → List (Dig 256)}
    (hc : Function.Injective fun c => (cfgOf c, toldOf c)) :
    ZKCP.CodeIsOneToOne (encSeed S cfgOf toldOf) := by
  intro k k' code e e'
  obtain ⟨q1, q4, q⟩ := S.keyAt_inj hA hS (OnBytes.Tie.idCodeS_oneToOne _ _ code e e')
  have d1 : cfgOf k.1 = cfgOf k'.1 := digToBytes_injective q1
  have d2 : toldOf k.1 = toldOf k'.1 :=
    List.map_injective_iff.2 digToBytes_injective q4
  have ec : k.1 = k'.1 := hc (Prod.ext d1 d2)
  exact Prod.ext ec q

variable {ISK Pf : Type}

/-- The hypothesis on the commitment at the key (root, record): proved from the two spellings' being
one to one, with an extractor that reads the commitment and the log alone. -/
theorem commitmentBinds_seed (G : ZKCP.Gen.Arg (rom 256) I X Unit (KeyRoot 256 L) ISK Pf)
    (E : ZKCP.Gen.Extractor (rom 256) I X Unit (KeyRoot 256 L) Pf) (S : IdSpellS L)
    (hA : Function.Injective S.answers) (hS : Function.Injective S.seed) (cfg : ByteArray)
    (told : List ByteArray) (IsTrue : I → X → Prop) (ε : ℕ → ℕ → ℝ≥0∞) :
    CommitmentBinds G E (idCodeSeed S cfg told)
      ((Special.extOf E).digestKey (idCodeSeed S cfg told)) IsTrue ε
      fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  commitmentBinds_of_code G E _ (idCodeSeed_oneToOne S hA hS cfg told) IsTrue ε

/-- The same at the key that holds the public digests. -/
theorem commitmentBinds_encSeed
    (G : ZKCP.Gen.Arg (rom 256) I X Unit (C × KeyRoot 256 L) ISK Pf)
    (E : ZKCP.Gen.Extractor (rom 256) I X Unit (C × KeyRoot 256 L) Pf) (S : IdSpellS L)
    (hA : Function.Injective S.answers) (hS : Function.Injective S.seed) {cfgOf : C → Dig 256}
    {toldOf : C → List (Dig 256)} (hc : Function.Injective fun c => (cfgOf c, toldOf c))
    (IsTrue : I → X → Prop) (ε : ℕ → ℕ → ℝ≥0∞) :
    CommitmentBinds G E (encSeed S cfgOf toldOf)
      ((Special.extOf E).digestKey (encSeed S cfgOf toldOf)) IsTrue ε
      fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  commitmentBinds_of_code G E _ (encSeed_oneToOne S hA hS hc) IsTrue ε

end TypedOracleCompiler.VerifiableInference.Rec

#print axioms TypedOracleCompiler.VerifiableInference.Rec.idCodeSeed_oneToOne
#print axioms TypedOracleCompiler.VerifiableInference.Rec.encSeed_oneToOne
#print axioms TypedOracleCompiler.VerifiableInference.Rec.commitmentBinds_seed
#print axioms TypedOracleCompiler.VerifiableInference.Rec.commitmentBinds_encSeed
