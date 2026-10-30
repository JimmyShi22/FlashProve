-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesArms.lean: the main soundness statement for a verifier that is the conjunction of
three checks, one for each file that a prover sends, from one bound for each check, under named
hypotheses that this file proves at no input.

What this file states. `verify_sound_arms_of_binds`, `verify_sound_arms_for`, `verify_sound_arms`:
the statement `SoundForWith` at the sum of the errors. Johnson/Top/InnerCompiledVerifier.lean runs the whole
compiled verifier over the one hash function through ONE coding of the typed oracles. Here each
check is a computation over the one hash function in its own right: it may come from a typed
verifier through a coding of its own. Nothing here names a coding. In the namespace
`VerifiableInference.OnPublicFiles`: `InputArms`: what the verifier reads: the object with records L, the
three checks over the hash function, the key's code, the builder of instances, and the honest side's
parameters. `BesideArms r`: what only the theorems need: `wordOf` (the word under a root, read off a
log of strings), the relaxed relation, the extractors, the four errors. `KeyHolds`, `EntryHolds`,
`ProofHolds`: what each check promises. y is the word under the key's root, read off THE COMMITTER's
LOG ALONE, as the extractor of the public statement reads it; y' is the word under the proof's
further root, read off the committer's log followed by the prover's. key file's check: y collides at
its record's seed, or y decodes at its record; entry file's check: neither y nor y' collides at its
seed, and y does not decode or y' decodes to what y decodes to; proof file's check: y' collides at
its seed, or y' does not decode, or the instance is true at what y' decodes to.

Under which hypotheses. `HoleArms.*`, `HolesArms b`: the named hypotheses: the three checks' bounds,
the extractor's form, no check draws a coin, the commitment, the meaning.

What it does not show.
- All of `HolesArms b` are hypotheses of the theorem: Lean's list of axioms does not show them,
  and this file proves none at any input.
- Seven named hypotheses are not fewer assumptions than the sixteen of
  Johnson/Top/InnerCompiledVerifier.lean: three of the seven are bounds on a probability, of the conclusion's
  own kind, and a fourth is an arrow between two such: what that file proves from its hypotheses is
  assumed here check by check.
- The three bounds speak of logs of strings without the verifier's own queries: whoever proves one
  from a bound on the trace of a maker and the verifier owes that the word under a root does not
  change when the log grows, outside an event that the bound already covers, and that the word read
  through the check's own coding is `wordOf`.
- The hypothesis on the commitment may lean on more than the key file's check: an extractor that
  reads a seed's queries off the log reads them as some check spells them.
- By an informal argument (no theorem): a check that takes a record and does not test its seed
  cannot meet its hypothesis where the seed is not bound into the check's first query: a committer
  or prover names the seed after it has seen the check's challenges. Of the entry file's check it is
  plain from its promise, which has no exception for a collision.
- What is intended: the seed at the key's root is tested in the key file's check and in the entry
  file's check, the seed at the further root in the entry file's check and in the proof file's
  check. A seed that two checks test is spelt by two codings. If the two spell the seed's queries by
  different strings, the two checks read two independent seeds under a random function, the
  conjunction accepts almost never, and every bound here can be true and is then vacuous: that the
  two checks read a seed at one string is a condition of not being empty, and no hypothesis here
  asks it.
- This file and the linking statement (Johnson/Top/TieOnFilesArms.lean) say
  something together only of an input r that holds nothing of the fixed hash function: the three
  checks, the key's code and the builder must reach the hash function by their queries alone
  (OnBytes/K/Top.lean's condition (c)). No hypothesis here asks it. A check that compares an answer
  with BLAKE2b's own value accepts under a random function with probability 2^-256 and always at
  BLAKE2b: at such an r all named hypotheses of both files hold and nothing is said (shown by a
  probe in Lean's kernel, outside this tree).
- At the input that is meant today this is not met: the linking statement's step on the commitment
  ID makes the key's code the ID's own string, which holds the public files' digest, an answer of
  the hash function, and the key's type has no place for it: so it is in the code as a constant, and
  a bound for each fixed constant gives none for one that the function chooses. The entry file's
  check at that input holds two such answers as constants too: the public files' digest and the
  digest of the link's parameters.
- The cure that is intended: the digest goes into the typed key, and the checks test it against the
  hash function's own answer (Johnson/Top/OnFilesArmsC.lean); or each check asks the hash function
  for these digests itself. Either way that is another term: a linking statement proved at that
  input does not carry over by itself (for the entry file Johnson/Top/TieOnFilesArmsEntryG.lean
  [not in this library] states the form that a joining to a bound asks, and
  Johnson/Top/Pub/EntryTieG.lean [not in this library; so here read: not proved in this library]
  proves it at the terms of both sizes of
  Johnson/Top/Pub/EntryAtG.lean [not in this library] (`tieGFull`, `tieGSmall`), over parameters
  whose types are not shown to have a member together, where the parameter file says the ground's
  lines and two tests on the numbers of blocks say yes).
- At a code that leaves the record's seed out, this file's hypothesis on the commitment, whose
  extractor reads the committer's log alone, has no proof in this library at the full bound:
  Johnson/Top/OnFilesArmsO.lean and Johnson/Top/OnFilesArmsLess.lean [not in this library] ask
  another form in its place, whose extractor may query the hash function (`HoleArms.commitmentO`);
  that this form is proved at an `InputArms` is not said here. The code that the step on the
  commitment ID forces is the ID's string, which holds the record's seed (`Fmt.publishedBytes`,
  Fmt/Rules4.lean). At that string the like hypothesis at the key that also holds the public digest
  is proved (`commitment_inputIdS`, Johnson/TypedOracleCompiler/Top/IdSeedAt.lean); at this file's type of key the
  like lemma stands
  (`commitmentBinds_seed`, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean, under two premises on the spellings)
  and no file applies it here.
- With every error equal to 1 or more the theorem holds and says nothing.
- All named hypotheses of both files also hold together at inputs that hold no hash and still say
  nothing: checks that always accept or that recompute the model, with `Served` true of true claims
  alone (shown by a second probe in Lean's kernel, outside this tree). So that all of them hold at
  one input is no test of saying something.
- What a concrete instance (defined in this library, not a parameter) must meet beyond them, at
  least, by further probes: (1) every statement that passes the concrete test `servedAt Z`
  (OnBytes/K/Served.lean), and a concrete further test whose verdict does not hang on the values of
  the claimed output tokens, is served ("no model stands in it" would be a property of a term, not
  of a value, and shuts nothing out: a list of true claims passes it): `exit_verifyArms_served`
  (Johnson/Top/TieOnFilesArmsServed.lean [not in this library]) has a premise of that shape, in
  which the further test is an unconstrained parameter; (2) the linking statements hold at every
  hash function, with the rewriting of the Lean port over a monad in which the hash is asked, at
  that function, in the program's place: the premise of Johnson/Top/SoundVia.lean; neither (1) nor
  (2) alone is enough;
  (3) the weights' type, the model and the claim are the description's own; (4) some call is served,
  ends in 0 and is not excepted; (5) `Excepted` is a concrete definition with a bound on its
  probability.
- No input is given. The hash function is one random function.

-/
import Johnson.Top.Arms
import Johnson.Top.InnerCompiledVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What the verifier reads. -/
structure InputArms where
  I : Type
  X : Type
  /-- the object with records: of it the theorems read the encoded index's length and symbols, the
  records, the collision predicate and the decoder -/
  L : HolographicProtocol I X
  aT : RoundSplits L.offline.shape
  aL : RoundSplits L.link.shape
  /-- the key file's check, over the one hash function: at the key's root and record and the test's
  proof string. What is intended: the test of the seed at the key's root, then Test. -/
  armK : Dig 256 → L.Rec → OneProtocolProof 256 (batTC L aT) → Rom.OComp (rom 256) Bool
  /-- the entry file's check: at the key's root, the further root, their records and the link's
  proof string. What is intended: the tests of the two seeds at the two roots, then Link. -/
  armE : Dig 256 → Dig 256 → L.Rec → L.Rec → OneProtocolProof 256 (batLC L aL) → Rom.OComp (rom 256) Bool
  /-- the proof file's check: at the further root, the instance, the further record, the number of
  the stored copy and the session's proof string. What is intended: the test of the seed at the
  further root, then the session. -/
  armP : Dig 256 → X → L.Rec → ℕ → OneProtocolProof 256 L.onlineBatch → Rom.OComp (rom 256) Bool
  enc : KeyRoot 256 L → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : I → List Token → Option Token
  ISK : Type
  commit : I → Rom.OComp (rom 256) (KeyRoot 256 L × ISK)
  prove : ISK → (l : List (X × Unit)) → Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 L aT aL) l)
  bound : ℕ
  π₀ : KeyRoot 256 L × OfflineLinkOnlineProof 256 L aT aL

/-- What only the theorems need. -/
structure BesideArms (r : InputArms) where
  /-- the word under a root, read off a log of strings -/
  wordOf : Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol
  Wn : Type
  Rno : r.I → r.X → Wn → Prop
  /-- the extractor of the scheme whose verifier holds the key itself -/
  E : ZKCP.Gen.Extractor (rom 256) r.I r.X Unit (KeyRoot 256 r.L) (OfflineLinkOnlineProof 256 r.L r.aT r.aL)
  /-- the extractor behind the commitment -/
  ext : ZKCP.Extractor 256 r.I r.X Unit (ZKCP.Digest 256)
    (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)
  εK : ℕ → ℕ → ℝ≥0∞
  εE : ℕ → ℕ → ℝ≥0∞
  εP : ℕ → ℕ → ℝ≥0∞
  εId : ℕ → ℝ≥0∞
  x₀ : r.X

variable (r : InputArms)

/-- The key file's check on a key and a proof: it rejects a proof without the test's string. -/
def liftK (k : KeyRoot 256 r.L) (_ : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.piT with
  | some p => r.armK k.cm k.rcd p
  | none => .pure false

/-- The entry file's check on a key and a proof: it rejects a proof without the link's string. -/
def liftE (k : KeyRoot 256 r.L) (_ : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.link.2.2 with
  | some p => r.armE k.cm π.link.1 k.rcd π.link.2.1 p
  | none => .pure false

/-- The proof file's check on an instance and a proof: it rejects a proof without the session's
string. -/
def liftP (_ : KeyRoot 256 r.L) (x : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.piB with
  | some p => r.armP π.link.1 x π.link.2.1 π.copy p
  | none => .pure false

/-- The scheme: its verifier runs the three checks one after the other and accepts if all three do.
-/
def schemeArms : ZKCP.Gen.Arg (rom 256) r.I r.X Unit (KeyRoot 256 r.L) r.ISK
    (OfflineLinkOnlineProof 256 r.L r.aT r.aL) where
  C := r.commit
  P := r.prove
  V k x π := (liftK r k x π).bind fun a => (liftE r k x π).bind fun b =>
    (liftP r k x π).bind fun c => .pure (a && b && c)

/-- The argument system. -/
def systemArms : ArgumentSystem :=
  Rec.tokenArgumentSystem (schemeArms r) r.enc r.bound r.build r.π₀ r.nextToken

/-- The verifier. -/
def verifyArms := (systemArms r).verify

variable {r} (b : BesideArms r)

/-- The instance is true at the index: the relaxed relation has a witness. -/
def IsTrueArms (i : r.I) (x : r.X) : Prop := ∃ w, b.Rno i x w

/-- What the key file's check promises. -/
def KeyHolds (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (_ : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (_ : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf trC k.cm) k.rcd.1 ∨ r.L.decodeIndex (b.wordOf trC k.cm) k.rcd ≠ none

/-- What the entry file's check promises. -/
def EntryHolds (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  ¬ r.L.hasCollisionAt (b.wordOf trC k.cm) k.rcd.1 ∧
    ¬ r.L.hasCollisionAt (b.wordOf (trC ++ trP) π.link.1) π.link.2.1.1 ∧
    (r.L.decodeIndex (b.wordOf trC k.cm) k.rcd = none ∨
      r.L.decodeIndex (b.wordOf (trC ++ trP) π.link.1) π.link.2.1 = r.L.decodeIndex (b.wordOf trC k.cm) k.rcd)

/-- What the proof file's check promises. -/
def ProofHolds (_ : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf (trC ++ trP) π.link.1) π.link.2.1.1 ∨
    r.L.decodeIndex (b.wordOf (trC ++ trP) π.link.1) π.link.2.1 = none ∨
    ∃ i, r.L.decodeIndex (b.wordOf (trC ++ trP) π.link.1) π.link.2.1 = some i ∧ IsTrueArms b i x

/-- The error of the main statement: the three checks' errors and the commitment's cost, at the
worst split of t queries between committer and prover. -/
def soundnessErrorArms (t : ℕ) : ℝ≥0∞ :=
  ⨆ (tC : ℕ) (tP : ℕ) (_ : tC + tP = t), b.εK tC tP + (b.εE tC tP + b.εP tC tP) + b.εId t

namespace HoleArms

/-- The key file's check: for every committer and every prover, it accepts while its promise fails
with probability at most εK tC tP. -/
def keyArm : Prop := ZKCP.Gen.ArmBound (liftK r) (KeyHolds b) b.εK

/-- The entry file's check. -/
def entryArm : Prop := ZKCP.Gen.ArmBound (liftE r) (EntryHolds b) b.εE

/-- The proof file's check. -/
def proofArm : Prop := ZKCP.Gen.ArmBound (liftP r) (ProofHolds b) b.εP

/-- The extractor decodes, at the key's record, the word under the key's root, read off the
committer's log. -/
def extractor : Prop :=
  ∀ (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)),
    b.E.Ei k trC = r.L.decodeIndex (b.wordOf trC k.cm) k.rcd

/-- No check draws a coin. -/
def noCoin : Prop :=
  (∀ cm c p, (r.armK cm c p).NoCoin) ∧ (∀ cm cm' c c' p, (r.armE cm cm' c c' p).NoCoin) ∧
    ∀ cm x c n p, (r.armP cm x c n p).NoCoin

/-- The commitment: index binding of the scheme whose verifier holds the key itself gives index
binding of the scheme behind the hash function's answer at the key's code, with the extractor
`b.ext`, at the cost `b.εId (tC + tP)`. -/
def commitment : Prop :=
  Rec.CommitmentBinds (schemeArms r) b.E r.enc b.ext (IsTrueArms b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) b.εId

/-- The meaning, for a claim: where the builder makes an instance of a prompt and output tokens and
the instance is true at an index, the claim holds at that index. -/
def soundFor (claim : r.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, r.build x' a = some x → IsTrueArms b i x →
    claim i x'.1 x'.2

/-- The meaning: the claim is "the output tokens are the model's". -/
def sound : Prop := soundFor b (systemArms r).IsModelOutput

end HoleArms

/-- The named hypotheses but for the meaning. -/
structure CoreArms : Prop where
  keyArm     : HoleArms.keyArm b
  entryArm   : HoleArms.entryArm b
  proofArm   : HoleArms.proofArm b
  extractor  : HoleArms.extractor b
  noCoin     : HoleArms.noCoin (r := r)
  commitment : HoleArms.commitment b

/-- All named hypotheses. -/
structure HolesArms : Prop extends CoreArms b where
  sound : HoleArms.sound b

/-- The extractor of the main statement. -/
def extractorArms : Commitment → QueryLog → Option r.I :=
  (b.ext.buildInstance : ZKCP.Extractor 256 r.I (List Token × List Token) Unit (ZKCP.Digest 256)
    (List Token × (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL))).Ei

variable {b}

/-- Where all three promises hold, the instance is true at the extracted index. -/
theorem chain_arms (hE : HoleArms.extractor b) (k : KeyRoot 256 r.L) (trC : Rom.Trace (rom 256))
    (x : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256))
    (hK : KeyHolds b k trC x π trP) (hL : EntryHolds b k trC x π trP)
    (hP : ProofHolds b k trC x π trP) :
    ∃ i, b.E.Ei k trC = some i ∧ IsTrueArms b i x := by
  obtain ⟨n0, n1, hl⟩ := hL
  have d0 : r.L.decodeIndex (b.wordOf trC k.cm) k.rcd ≠ none := hK.resolve_left n0
  have e := hl.resolve_left d0
  obtain ⟨i, hi, ht⟩ := (hP.resolve_left n1).resolve_left fun hn => d0 (e.symm.trans hn)
  exact ⟨i, by rw [hE, ← e, hi], ht⟩

/-- Index binding of the scheme whose verifier holds the key itself, over the one hash function, at
the sum of the three checks' errors. -/
theorem CoreArms.binds (h : CoreArms b) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArms b)))
      (schemeArms r) b.E fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP) := by
  refine ZKCP.Gen.binds_of_arms (vK := liftK r) (vE := liftE r) (vP := liftP r) rfl
    h.keyArm h.entryArm h.proofArm fun k trC x π trP hK hL hP => ?_
  obtain ⟨i, hi, ht⟩ := chain_arms h.extractor k trC x π trP hK hL hP
  rw [hi]
  exact ⟨⟨(), ht⟩, ht⟩

/-- Where no check draws a coin, the scheme's verifier draws none. -/
theorem noCoin_schemeArms (hn : HoleArms.noCoin (r := r)) (k : KeyRoot 256 r.L) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) : ((schemeArms r).V k x π).NoCoin := by
  obtain ⟨a1, a2, a3⟩ := hn
  have c1 : (liftK r k x π).NoCoin := by
    unfold liftK
    split
    · exact a1 _ _ _
    · trivial
  have c2 : (liftE r k x π).NoCoin := by
    unfold liftE
    split
    · exact a2 _ _ _ _ _
    · trivial
  have c3 : (liftP r k x π).NoCoin := by
    unfold liftP
    split
    · exact a3 _ _ _ _ _
    · trivial
  exact c1.bind fun _ => c2.bind fun _ => c3.bind fun _ => trivial

/-- The statement of `verify_sound_arms` for any claim, from index binding of the scheme whose
verifier holds the key itself, brought whole, in the place of the three checks' bounds and the
extractor's form. The other three hypotheses stay. -/
theorem verify_sound_arms_of_binds (claim : r.I → List Token → List Token → Prop)
    (hb : ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArms b)))
      (schemeArms r) b.E fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP))
    (hn : HoleArms.noCoin (r := r)) (hc : HoleArms.commitment b)
    (hs : HoleArms.soundFor b claim) :
    SoundForWith (systemArms r) (extractorArms b) claim (soundnessErrorArms b) :=
  Rec.soundForWith_systemE_ext (schemeArms r) b.E r.enc b.ext r.bound r.π₀ r.nextToken hb
    (noCoin_schemeArms hn) hc claim b.x₀ hs fun tC tP =>
      le_iSup_of_le tC (le_iSup_of_le tP (le_iSup_of_le rfl le_rfl))

/-- Under the 6 named hypotheses `CoreArms b` and `HoleArms.soundFor b claim` (hypotheses of the
theorem: Lean's list of axioms does not show them): the statement of `verify_sound_arms` for any
claim. -/
theorem verify_sound_arms_for (claim : r.I → List Token → List Token → Prop) (h : CoreArms b)
    (hs : HoleArms.soundFor b claim) :
    SoundForWith (systemArms r) (extractorArms b) claim (soundnessErrorArms b) :=
  verify_sound_arms_of_binds claim h.binds h.noCoin h.commitment hs

/-- Under the 7 named hypotheses `HolesArms b` (hypotheses of the theorem: Lean's list of axioms
does not show them): for every committer and every prover whose bounds on queries to the hash
function add up to t, the probability that `verifyArms r` accepts while the extractor gives no
index, or an index at which the output tokens are not those of `r.nextToken`, a field of the
parameter r (no model is fixed here), is at most `soundnessErrorArms b t`. -/
theorem verify_sound_arms (h : HolesArms b) :
    SoundForWith (systemArms r) (extractorArms b) (systemArms r).IsModelOutput
      (soundnessErrorArms b) :=
  verify_sound_arms_for _ h.toCoreArms h.sound

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.chain_arms
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_of_binds
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_for
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms
