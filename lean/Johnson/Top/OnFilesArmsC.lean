-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesArmsC.lean: the main soundness statement check by check
(Johnson/Top/OnFilesArms.lean) with the public data in the typed key: `SoundForWithO` of
`systemArmsC r`, a game whose extractor may query the hash function, under named hypotheses.

What this file states. The commitment ID's own string holds the public files' digest, an answer of
the hash function. In Johnson/Top/OnFilesArms.lean the key is a root and a record: it has no place
for that digest, so a key's code that is the ID's own string holds it as a constant, and a bound for
each fixed constant gives none for one that the hash function chooses. Here a key is a pair (c, k):
c is what of the public data is in the key (what is intended: the digest), k the root and the
record. The key's code is one fixed function of (c, k). The checks, the word under a root, the
promises and the extractor read c off the key. What is intended of the checks: each asks the hash
function at the public strings and says no unless the answer is c. So a key with a false c is
refused, the bounds speak of all keys, and the input holds nothing of any hash function. In the
namespace `VerifiableInference.OnPublicFiles`, the names of Johnson/Top/OnFilesArms.lean,
OnFilesArmsO.lean, OnFilesArmsLess.lean [not in this library] and OnFilesPort.lean
[not in this library] with a C behind: `InputArmsC`,
`BesideArmsC r`, `liftKC`, `liftEC`, `liftPC`, `schemeArmsC`, `systemArmsC`; `KeyHoldsC`,
`EntryHoldsC`, `ProofHoldsC`: the three promises, with the word read at the key's c; `CoreArmsC b`:
five named hypotheses: the three checks' bounds (`ZKCP.Gen.ArmBound`, Johnson/Top/Arms.lean, at the
wider key), the extractor's form, no check draws a coin; `CoreArmsC.binds`: index binding of the
scheme whose verifier holds the key itself, in `bindingExp`'s own game: the extractor reads the
key and the committer's log alone; `HoleArmsC.commitmentO`, `verify_sound_arms_C`: `SoundForWithO`
of `systemArmsC r`; `accepts_of_armsC`: a built instance, a key's code that the hash function sends
to the commitment, and three checks' yes are a yes of `systemArmsC r`: for the premise of
Johnson/Top/SoundVia.lean. `InputArms.toC`: an input of Johnson/Top/OnFilesArms.lean is one of these
with nothing in c.

Under which hypotheses. `verify_sound_arms_C` takes `CoreArmsC b`, `HoleArmsC.commitmentO b extO q
εO`, `HoleArmsC.soundFor b claim`, and εO tC tP ≤ ε (tC + tP).

What it does not show.
- The limits of the files named. All premises are hypotheses of the theorems: Lean's list of axioms
  does not show them.
- `InputArms.toC` is a definition alone: no theorem carries a bound, a yes or soundness across, and
  with nothing in c the constant is back in the code.
- That the checks test c is required by no hypothesis: a check that does not can meet its bound only
  if its promise holds at every c that a committer names.
- The error of the conclusion is the parameter εO of the hypothesis on the commitment.
- A committer names c after its queries: so a bound at each fixed c gives none of the three bounds
  at the wider key (the check "ask the public string; yes exactly if the answer is c" has 2^-256 at
  each fixed c and 1 at a committer that names the answer).
- What is intended to give them is a bound in which the public reading (a computation that queries
  the hash function) is drawn in the experiment (`ZKCP.Gen.ArmBoundD`, Johnson/Top/ArmsD.lean), by
  "where the check accepts, c is the reading's value": Johnson/Top/ArmsTold.lean.
- No input is given.

-/
import Johnson.Top.OnFilesArmsO
import Johnson.Top.TieFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What the verifier reads. -/
structure InputArmsC where
  I : Type
  X : Type
  L : HolographicProtocol I X
  aT : RoundSplits L.offline.shape
  aL : RoundSplits L.link.shape
  /-- what of the public data stands in a key -/
  C : Type
  /-- the key file's check. Intended, not required here: the test of c against the hash function's
  answer at the public strings, the test of the seed at the key's root, then Test. -/
  armK : C → Dig 256 → L.Rec → OneProtocolProof 256 (batTC L aT) → Rom.OComp (rom 256) Bool
  /-- the entry file's check. Intended, not required here: the test of c, the tests of the two
  seeds, then Link. -/
  armE : C → Dig 256 → Dig 256 → L.Rec → L.Rec → OneProtocolProof 256 (batLC L aL) → Rom.OComp (rom 256) Bool
  /-- the proof file's check. Intended, not required here: the test of c, the test of the seed at
  the further root, then the session. -/
  armP : C → Dig 256 → X → L.Rec → ℕ → OneProtocolProof 256 L.onlineBatch → Rom.OComp (rom 256) Bool
  enc : C × KeyRoot 256 L → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : I → List Token → Option Token
  ISK : Type
  commit : I → Rom.OComp (rom 256) ((C × KeyRoot 256 L) × ISK)
  prove : ISK → (l : List (X × Unit)) → Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 L aT aL) l)
  bound : ℕ
  π₀ : (C × KeyRoot 256 L) × OfflineLinkOnlineProof 256 L aT aL

/-- What only the theorems need. -/
structure BesideArmsC (r : InputArmsC) where
  /-- the word under a root, read at c off a log of strings -/
  wordOf : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol
  Wn : Type
  Rno : r.I → r.X → Wn → Prop
  /-- the extractor of the scheme whose verifier holds the key itself -/
  E : ZKCP.Gen.Extractor (rom 256) r.I r.X Unit (r.C × KeyRoot 256 r.L)
    (OfflineLinkOnlineProof 256 r.L r.aT r.aL)
  εK : ℕ → ℕ → ℝ≥0∞
  εE : ℕ → ℕ → ℝ≥0∞
  εP : ℕ → ℕ → ℝ≥0∞
  x₀ : r.X

variable (r : InputArmsC)

/-- The key file's check on a key and a proof: it rejects a proof without the test's string. -/
def liftKC (k : r.C × KeyRoot 256 r.L) (_ : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.piT with
  | some p => r.armK k.1 k.2.cm k.2.rcd p
  | none => .pure false

/-- The entry file's check on a key and a proof: it rejects a proof without the link's string. -/
def liftEC (k : r.C × KeyRoot 256 r.L) (_ : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.link.2.2 with
  | some p => r.armE k.1 k.2.cm π.link.1 k.2.rcd π.link.2.1 p
  | none => .pure false

/-- The proof file's check on a key, an instance and a proof: it rejects a proof without the
session's string. -/
def liftPC (k : r.C × KeyRoot 256 r.L) (x : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    Rom.OComp (rom 256) Bool :=
  match π.piB with
  | some p => r.armP k.1 π.link.1 x π.link.2.1 π.copy p
  | none => .pure false

/-- The scheme: its verifier runs the three checks one after the other and accepts if all three
do. -/
def schemeArmsC : ZKCP.Gen.Arg (rom 256) r.I r.X Unit (r.C × KeyRoot 256 r.L) r.ISK
    (OfflineLinkOnlineProof 256 r.L r.aT r.aL) where
  C := r.commit
  P := r.prove
  V k x π := (liftKC r k x π).bind fun a => (liftEC r k x π).bind fun b =>
    (liftPC r k x π).bind fun c => .pure (a && b && c)

/-- The argument system. -/
def systemArmsC : ArgumentSystem :=
  Rec.tokenArgumentSystem (schemeArmsC r) r.enc r.bound r.build r.π₀ r.nextToken

variable {r} (b : BesideArmsC r)

/-- The instance is true at the index: the relaxed relation has a witness. -/
def IsTrueArmsC (i : r.I) (x : r.X) : Prop := ∃ w, b.Rno i x w

/-- What the key file's check promises. -/
def KeyHoldsC (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (_ : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (_ : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf k.1 trC k.2.cm) k.2.rcd.1 ∨ r.L.decodeIndex (b.wordOf k.1 trC k.2.cm) k.2.rcd ≠ none

/-- What the entry file's check promises. -/
def EntryHoldsC (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (_ : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  ¬ r.L.hasCollisionAt (b.wordOf k.1 trC k.2.cm) k.2.rcd.1 ∧
    ¬ r.L.hasCollisionAt (b.wordOf k.1 (trC ++ trP) π.link.1) π.link.2.1.1 ∧
    (r.L.decodeIndex (b.wordOf k.1 trC k.2.cm) k.2.rcd = none ∨
      r.L.decodeIndex (b.wordOf k.1 (trC ++ trP) π.link.1) π.link.2.1 =
        r.L.decodeIndex (b.wordOf k.1 trC k.2.cm) k.2.rcd)

/-- What the proof file's check promises. -/
def ProofHoldsC (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (trP : Rom.Trace (rom 256)) : Prop :=
  r.L.hasCollisionAt (b.wordOf k.1 (trC ++ trP) π.link.1) π.link.2.1.1 ∨
    r.L.decodeIndex (b.wordOf k.1 (trC ++ trP) π.link.1) π.link.2.1 = none ∨
    ∃ i, r.L.decodeIndex (b.wordOf k.1 (trC ++ trP) π.link.1) π.link.2.1 = some i ∧ IsTrueArmsC b i x

/-- The named hypotheses but for the commitment and the meaning. -/
structure CoreArmsC : Prop where
  keyArm    : ZKCP.Gen.ArmBound (liftKC r) (KeyHoldsC b) b.εK
  entryArm  : ZKCP.Gen.ArmBound (liftEC r) (EntryHoldsC b) b.εE
  proofArm  : ZKCP.Gen.ArmBound (liftPC r) (ProofHoldsC b) b.εP
  /-- the extractor decodes, at the key's record, the word under the key's root, read at the key's c
  off the committer's log -/
  extractor : ∀ (k : r.C × KeyRoot 256 r.L) (trC : Rom.Trace (rom 256)),
    b.E.Ei k trC = r.L.decodeIndex (b.wordOf k.1 trC k.2.cm) k.2.rcd
  noCoin    : (∀ c cm rc p, (r.armK c cm rc p).NoCoin) ∧
    (∀ c cm cm' rc rc' p, (r.armE c cm cm' rc rc' p).NoCoin) ∧
    ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin

/-- The commitment, in the game where the extractor may query the hash function. -/
def HoleArmsC.commitmentO
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞) : Prop :=
  Rec.CommitmentBindsO (schemeArmsC r) b.E r.enc extO q (IsTrueArmsC b)
    (fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP)) εO

/-- The meaning, for a claim. -/
def HoleArmsC.soundFor (claim : r.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, r.build x' a = some x → IsTrueArmsC b i x →
    claim i x'.1 x'.2

variable {b}

/-- Index binding of the scheme whose verifier holds the key itself, at the sum of the three checks'
errors. -/
theorem CoreArmsC.binds (h : CoreArmsC b) :
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueArmsC b)))
      (schemeArmsC r) b.E fun tC tP => b.εK tC tP + (b.εE tC tP + b.εP tC tP) := by
  refine ZKCP.Gen.binds_of_arms (vK := liftKC r) (vE := liftEC r) (vP := liftPC r) rfl
    h.keyArm h.entryArm h.proofArm fun k trC x π trP hK hL hP => ?_
  obtain ⟨n0, n1, hl⟩ := hL
  have d0 : r.L.decodeIndex (b.wordOf k.1 trC k.2.cm) k.2.rcd ≠ none := hK.resolve_left n0
  have e := hl.resolve_left d0
  obtain ⟨i, hi, ht⟩ := (hP.resolve_left n1).resolve_left fun hn => d0 (e.symm.trans hn)
  rw [h.extractor k trC, e.symm.trans hi]
  exact ⟨⟨(), ht⟩, ht⟩

/-- Where no check draws a coin, the scheme's verifier draws none. -/
theorem CoreArmsC.noCoin_scheme (h : CoreArmsC b) (k : r.C × KeyRoot 256 r.L) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) : ((schemeArmsC r).V k x π).NoCoin := by
  obtain ⟨a1, a2, a3⟩ := h.noCoin
  have c1 : (liftKC r k x π).NoCoin := by
    unfold liftKC
    split
    · exact a1 _ _ _ _
    · trivial
  have c2 : (liftEC r k x π).NoCoin := by
    unfold liftEC
    split
    · exact a2 _ _ _ _ _ _
    · trivial
  have c3 : (liftPC r k x π).NoCoin := by
    unfold liftPC
    split
    · exact a3 _ _ _ _ _ _
    · trivial
  exact c1.bind fun _ => c2.bind fun _ => c3.bind fun _ => trivial

/-- Under the 5 named hypotheses `CoreArmsC b`, `HoleArmsC.commitmentO b extO q εO`,
`HoleArmsC.soundFor b claim` and εO tC tP ≤ ε (tC + tP) (hypotheses of the theorem: Lean's list of
axioms does not show them): for every committer and every prover whose bounds on queries to the hash
function add up to t, the probability that the verifier of `systemArmsC r` accepts while the
extractor, which reads the commitment and the committer's log and asks the hash function at most q
times, gives no index, or an index at which the claim fails, is at most ε t. -/
theorem verify_sound_arms_C (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) (h : CoreArmsC b) (hc : HoleArmsC.commitmentO b extO q εO)
    (hs : HoleArmsC.soundFor b claim) (hε : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemArmsC r) (fun c l => deterministicOf (extO.Ei c l)) q claim ε :=
  Rec.soundForWithO_systemE (schemeArmsC r) b.E r.enc extO q r.bound r.π₀ r.nextToken h.binds
    h.noCoin_scheme hc claim b.x₀ hs hε

/-- A built instance, a key's code that the hash function sends to the commitment, and three checks'
yes are a yes of `systemArmsC r`. -/
theorem accepts_of_armsC (g : Hash) (c : Commitment) (prompt output aux : List Token)
    (k : r.C × KeyRoot 256 r.L) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) (x : r.X) (code : ZKCP.Str)
    (hb : r.build (prompt, output) aux = some x) (hc : r.enc k = some code) (hd : g code = c)
    (vK : (liftKC r k x π).det (fun _ => g) = true)
    (vE : (liftEC r k x π).det (fun _ => g) = true)
    (vP : (liftPC r k x π).det (fun _ => g) = true) :
    (systemArmsC r).accepts g c prompt output (aux, (k, π)) = true := by
  have hv : ((schemeArmsC r).V k x π).det (fun _ => g) = true := by
    show ((liftKC r k x π).bind fun a => (liftEC r k x π).bind fun b =>
      (liftPC r k x π).bind fun d => OComp.pure (a && b && d)).det (fun _ => g) = true
    simp only [OComp.det_bind]
    rw [vK, vE, vP]
    rfl
  exact OnBytes.K.front_yes (schemeArmsC r) r.enc r.bound r.build r.π₀ g c prompt output aux k π x
    code hb hc hd hv

/-- An input of Johnson/Top/OnFilesArms.lean is one of these with nothing in c. -/
def InputArms.toC (r : InputArms) : InputArmsC where
  I := r.I
  X := r.X
  L := r.L
  aT := r.aT
  aL := r.aL
  C := Unit
  armK := fun _ => r.armK
  armE := fun _ => r.armE
  armP := fun _ => r.armP
  enc := fun k => r.enc k.2
  build := r.build
  nextToken := r.nextToken
  ISK := r.ISK
  commit := fun i => (r.commit i).bind fun o => .pure (((), o.1), o.2)
  prove := r.prove
  bound := r.bound
  π₀ := (((), r.π₀.1), r.π₀.2)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CoreArmsC.binds
#print axioms VerifiableInference.OnPublicFiles.verify_sound_arms_C
#print axioms VerifiableInference.OnPublicFiles.accepts_of_armsC
