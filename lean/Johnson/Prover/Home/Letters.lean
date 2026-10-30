-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Home/Letters.lean: THE LETTERS AND THE NAMED HYPOTHESES OF "THE HONEST SIDE IS
ACCEPTED" FOR AN ARGUMENT SYSTEM WHOSE VERIFIER READS ITS INPUT OFF THE HASH FUNCTION. AT LETTERS:
general in the argument system and in the told record (LayoutsByPublicReading, Johnson/Top/InnerCompiledVerifierByPublicReading.lean).
DEFINITIONS, and one lemma by unfolding.

Main names.
  HomeLetters   all data of the honest side beside the system and the told record.
  HomeLetters.isk, .pd, .Y   the committer's coins at a reading; the prover behind its coins, as an
    algorithm without coins; the typed runs' value at a hash function.
  HomeYes    the pointwise join, as one statement: at every hash function, outside the event of
    allY_law (Johnson/Prover/All/Law.lean), the system's verifier says yes to the printed proof at
    the system's own commitment.
  HomeFits   what the measure asks, and HomeYes.
  JoinRest   what pays HomeYes, but for the committer's two clauses: the typed premises, and the
    interface from the good case to the system's verifier's yes at the printed proof.
  JoinFits, JoinRest.join   JoinRest with the lengths of the committer's salts and the commitment's
    value at a hash function.

Limits. Definitions, and one lemma by unfolding. The one member of HomeFits that is shown in this
library is idle, without teeth: completeOn_home_join's proof
(Johnson/Goal/Conditions/HomeComplete.lean) makes it of premises that idle letters meet
(Johnson/Goal/Conditions/HomeIdle.lean); no theorem states it by that name. (A toy's, in a file that
is not in this repository: Johnson/Goal/Conditions/HomeToy.lean.) None at an
honest strategy, at any intended file. They name no goal's form.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Home.Defs
import Johnson.Prover.All.Good
import Johnson.Prover.All.NoOther
import VerifiableInference.Deterministic

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- ALL LETTERS OF THE HOME, beside the argument system and the told record. -/
structure HomeLetters (system : ArgumentSystem) {R : InnerCompilerInput} (T : LayoutsByPublicReading R) where
  Kap : Type
  b₀ : R.LeafBody
  st : Strats R.protocol Kap
  capT : ℕ → ℕ
  capL : ℕ → ℕ
  capB : ℕ → ℕ
  /-- the numbers of the sampler's and of the prover's draws -/
  B : ℕ
  N : ℕ
  ρOf : Fin (B + 1) → system.CommitmentRandomness
  /-- weights as an index -/
  back : system.Weights → R.Index
  /-- the committer's coins, off ρ and the public reading -/
  r₁ : system.CommitmentRandomness → R.protocol.EncodingRandomness
  s₁ : T.D → system.CommitmentRandomness → ℕ → Bits
  /-- the prover's draw, off ρ, its own number and the public reading -/
  drawOf : T.D → system.CommitmentRandomness → Fin (N + 1) → Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap
  /-- the instance of a request -/
  xOf : List Token → List Token → R.Instance
  /-- how a typed program is carried over the hash function -/
  carry : (d : T.D) → OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) (Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) →
    OComp (rom 256) (Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)
  /-- the printer; it sees the prover's number, and so the draw -/
  print : system.Weights → system.CommitmentRandomness → List Token → List Token → Fin (N + 1) →
    T.D → Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → system.Proof
  /-- the sets outside which the accept laws hold -/
  Bs : system.Weights → List Token → List Token → Fin (B + 1) → Fin (N + 1) → T.D → Bads R.protocol
  ζ₁ : ℝ≥0∞
  ζ₂ : ℝ≥0∞
  δT : ℝ≥0∞
  δL : ℝ≥0∞
  δB : ℝ≥0∞

variable {system : ArgumentSystem} {R : InnerCompilerInput} {T : LayoutsByPublicReading R} (H : HomeLetters system T)

/-- the committer's (index, randomness, salts) at d -/
def HomeLetters.isk (w : system.Weights) (ρ : system.CommitmentRandomness) (d : T.D) :
    R.Index × R.protocol.EncodingRandomness × (ℕ → Bits) := (H.back w, H.r₁ ρ, H.s₁ d ρ)

/-- the prover behind its coins, as the goals' type of an algorithm without coins -/
def HomeLetters.pd (w : system.Weights) (ρ : system.CommitmentRandomness) (p o : List Token)
    (a : Fin (H.N + 1)) : DeterministicAlgorithm system.Proof :=
  deterministicOf (ofRom (proveForm T H.b₀ H.st H.capT H.capL H.capB H.carry (H.isk w ρ) (H.xOf p o)
    (fun d => H.drawOf d ρ a) (H.print w ρ p o a)))

/-- the typed runs' value at a hash function -/
def HomeLetters.Y (w : system.Weights) (ρ : system.CommitmentRandomness) (p o : List Token)
    (a : Fin (H.N + 1)) (hash : Hash) : Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits :=
  (runsAt T H.b₀ H.st H.capT H.capL H.capB (T.Pub.det (Run.famOne hash))
    (H.isk w ρ (T.Pub.det (Run.famOne hash))) (H.xOf p o)
    (H.drawOf (T.Pub.det (Run.famOne hash)) ρ a)).det
      (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))

/-- **home_yes**: THE POINTWISE JOIN, as one named statement: at every hash function: outside the
event the goals' verifier says yes to the printed proof at the home's own commitment. -/
def HomeYes (domain : system.Weights → List Token → List Token → Prop) : Prop :=
  ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a hash,
    H.Y w (H.ρOf t) p o a hash ∉ EvY (H.Bs w p o t a (T.Pub.det (Run.famOne hash))) →
    (system.verify ((system.commit w (H.ρOf t)).evaluate hash) p o
      ((H.pd w (H.ρOf t) p o a).evaluate hash)).evaluate hash = true

/-- **HomeFits AT LETTERS**: what the measure asks and the join as one field. -/
structure HomeFits (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞) :
    Prop where
  /-- the sampler samples one number up to B and returns ρOf of it (B is a letter; 0 is allowed) -/
  sample : system.sampleCommitmentRandomness = .sample H.B fun t => .done (H.ρOf t)
  /-- the prover samples one number up to N and then runs pd at it (N is a letter; 0 is allowed) -/
  prove : ∀ w ρ p o, system.prove w ρ p o = .sample H.N fun a => (H.pd w ρ p o a).toRandomized
  /-- LawFit at every reading d -/
  law : ∀ d, LawFit R.queryLayout (T.Sd d) H.capT H.capL H.capB
  /-- three clauses on the public reading T.Pub and the strings T.Pt -/
  pubNoCoin : T.Pub.NoCoin
  pubAsks : T.Pub.AsksIn fun _ s => T.Pt s
  spare : ∀ d s, T.Pt s → IsOther (T.m d) s
  /-- SetsSmall of the sets Bs, on the domain, at the model's own output -/
  small : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a d,
    SetsSmall R.queryLayout (T.Sd d) (H.Bs w p o t a d) H.ζ₁ H.ζ₂ H.δT H.δL H.δB
  /-- the sum alphaAll is at most α -/
  number : alphaAll R.queryLayout H.capT H.capL H.capB H.ζ₁ H.ζ₂ H.δT H.δL H.δB ≤ α
  /-- the pointwise join, whole -/
  yes : HomeYes H domain

/-- **What pays home_yes, but for the committer's two clauses**, at letters: the typed
premises, and the interface "from the good case to the system's verifier's yes at the printed
proof". -/
structure JoinRest (domain : system.Weights → List Token → List Token → Prop) : Prop where
  /-- the carried runs have the typed runs' value, at the typed functions read out -/
  carry_det : ∀ w ρ p o a d g,
    (H.carry d (runsAt T H.b₀ H.st H.capT H.capL H.capB d (H.isk w ρ d) (H.xOf p o)
      (H.drawOf d ρ a))).det g =
    (runsAt T H.b₀ H.st H.capT H.capL H.capB d (H.isk w ρ d) (H.xOf p o)
      (H.drawOf d ρ a)).det (readBlocks (T.m d) g)
  /-- WiresFit at every reading d -/
  wires : ∀ d, WiresFit R.queryLayout (T.cA d)
  /-- DrawFit at every draw: the lengths of what is drawn -/
  draw : ∀ d ρ a, DrawFit R.queryLayout R.compilerParameters (H.drawOf d ρ a)
  /-- AccAt at the sets Bs, on the domain, at the model's own output -/
  acc : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a d,
    AccAt R.queryLayout (T.Sd d) H.st (H.back w) (H.r₁ (H.ρOf t)) (H.xOf p o) (H.drawOf d (H.ρOf t) a)
      (H.Bs w p o t a d)
  /-- from pack's proof, Ends, the three accepts, the test num and verifyAtKeyRoot's yes to the yes of the
  system's verifier at the printed form. ASKED WHOLE: what ties the printed form to the typed
  proof is all behind this field; nothing of it is split out here. -/
  printed : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a hash π e₁ e₂ τT τL τB,
    pack (H.back w) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a)
      (H.Y w (H.ρOf t) p o a hash) = .ok (π, e₁, e₂, τT, τL, τB) →
    Ends R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) (T.cA (T.Pub.det (Run.famOne hash))) R.fixedSample H.b₀
        H.st
      H.capT H.capL H.capB (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))
      (H.back w) (H.r₁ (H.ρOf t)) (H.s₁ (T.Pub.det (Run.famOne hash)) (H.ρOf t)) (H.xOf p o)
      (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a) π e₁ e₂ τT τL τB →
    R.protocol.offline.accept (R.protocol.recOf (H.back w) (H.r₁ (H.ρOf t)) e₁)
      (R.protocol.encodeIndex (H.back w) (H.r₁ (H.ρOf t))) τT = true →
    R.protocol.link.accept (R.protocol.recOf (H.back w) (H.r₁ (H.ρOf t)) e₁,
               R.protocol.recOf (H.back w) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a).r e₂)
      (R.protocol.encodeIndex (H.back w) (H.r₁ (H.ρOf t)),
        R.protocol.encodeIndex (H.back w) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a).r) τL = true →
    R.protocol.onlineBatch.loc.accept (H.xOf p o,
                       R.protocol.recOf (H.back w) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a).r e₂)
      (R.protocol.encodeIndex (H.back w) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a).r) τB = true →
    (T.Sd (T.Pub.det (Run.famOne hash))).num
      (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a).n τB.plains = true →
    (verifyAtKeyRoot R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) (T.cA (T.Pub.det (Run.famOne hash))) R.fixedSample R.compilerParameters
      ((committerAtFixedCoins R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) H.b₀ (H.back w) (H.r₁ (H.ρOf t))
        (H.s₁ (T.Pub.det (Run.famOne hash)) (H.ρOf t))).det
          (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))).1 (H.xOf p o) π).det
        (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash)) = true →
    (system.verify (ZKCP.digestUnder hash T.encT (T.part (T.Pub.det (Run.famOne hash)),
        ((committerAtFixedCoins R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) H.b₀ (H.back w) (H.r₁ (H.ρOf t))
          (H.s₁ (T.Pub.det (Run.famOne hash)) (H.ρOf t))).det
            (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))).1)) p o
      (H.print w (H.ρOf t) p o a (T.Pub.det (Run.famOne hash))
        (H.Y w (H.ρOf t) p o a hash))).evaluate hash = true

/-- **What pays home_yes**: JoinRest, the lengths of the committer's salts, and the commitment's
value at a hash function. -/
structure JoinFits (domain : system.Weights → List Token → List Token → Prop) : Prop
    extends JoinRest H domain where
  /-- the lengths of the committer's salts -/
  salts : ∀ d ρ j, j < R.protocol.wordLength → (H.s₁ d ρ j).length = R.compilerParameters.sMT
  /-- the commitment's value at a hash function -/
  commit : ∀ w ρ hash, (system.commit w ρ).evaluate hash =
    ZKCP.digestUnder hash T.encT (T.part (T.Pub.det (Run.famOne hash)),
      ((committerAtFixedCoins R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) H.b₀ (H.back w) (H.r₁ ρ)
        (H.s₁ (T.Pub.det (Run.famOne hash)) ρ)).det
          (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))).1)

/-- JoinFits from its three parts. -/
theorem JoinRest.join {H : HomeLetters system T}
    {domain : system.Weights → List Token → List Token → Prop} (J : JoinRest H domain)
    (salts : ∀ d ρ j, j < R.protocol.wordLength → (H.s₁ d ρ j).length = R.compilerParameters.sMT)
    (commit : ∀ w ρ hash, (system.commit w ρ).evaluate hash =
      ZKCP.digestUnder hash T.encT (T.part (T.Pub.det (Run.famOne hash)),
        ((committerAtFixedCoins R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) H.b₀ (H.back w) (H.r₁ ρ)
          (H.s₁ (T.Pub.det (Run.famOne hash)) ρ)).det
            (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne hash))).1)) :
    JoinFits H domain := ⟨J, salts, commit⟩

end OnBytes.Prover
