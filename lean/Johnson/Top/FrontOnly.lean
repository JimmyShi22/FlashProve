-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontOnly.lean: the front verifier with nothing written by hand outside the parser and
the arms, in the frame of Johnson/Top/FrontParts.lean.

At letters: it cannot be run: it says something only at a written r and a written parser, and none
is given here.

`PortArmsC.withCheck` (Johnson/Top/FrontParts.lean) adds an arm beside the front verifier that is
there: a verifier written by hand still runs. Here the front verifier is: parse, once; make the
instance of prompt, output and the further tokens that were parsed; ask the hash function at the
code of the key that was parsed, and say no unless the answer is the commitment; then the three
arms, one after the other, on what was parsed. No other test.
  `afterParse r c prompt output a`: what is done behind the parser, on what it returned.
  `afterParse_yes_iff`: its yes at g: the builder makes an instance, the key has a code, g at that
    code is c, and each of the three arms says yes at g.
  `PortArmsC.only p`: the letters of p with that front verifier: "the parser, then `afterParse`".
    Files, honest prover, parser, budget, way out and price stay.
  `PortArmsC.only_yes_iff`: its yes at g.
  `frontParts_only`: `FrontParts p.only` from the parser's budget and the way out's price alone:
    `request`, `idPart`, `keyPart`, `entryPart`, `proofPart` hold by definition, and none of them
    uses the way out.
  `only_sound`: the top at it: from budget, price, the three arms' bounds, the commitment, the
    meaning and the error's name.

What it is. The verifier of `systemArmsC r` in other words, behind a parser: the same steps as
`accepts_of_armsC` (Johnson/Top/OnFilesArmsC.lean) lists. That at every hash function it decides as
that system's own verifier does: `PortArmsC.only_is`, Johnson/Top/FrontOnlyLaws.lean.

Who brings what, by the types. The commitment, the prompt and the output tokens are the front
verifier's own arguments. The public files are no argument of it: they reach it through r and the
parser alone: "the public files come from the user's side" is true only of a function Z ↦ the front
verifier at an r and a parser made of Z, which is written nowhere here. All else, the key with its
public part (`r.C`) among it, is what the parser makes of the prover's files; that an arm tests the
key's public part lies in that arm's bound. The commitment reaches no arm: the test of the hash
function's answer at the key's code alone ties it to the key that was parsed.

What is not claimed. All that the head of Johnson/Top/FrontParts.lean does not claim. Nothing is won
for soundness by a definition: the whole debt sits in the three arms' bounds (`CoreArmsCD`), the
commitment, the meaning, and the parser's budget; they are hypotheses here. `p.reader`, `r.build`,
`r.enc` and the three arms are letters inside the verifier: at an arm that always says no, or a
parser that returns what the arms refuse, all fields are free. That the key file's and the proof
file's arms begin with the test of the record's seed against the hash function is asked by nothing
here: it lies in the arms' bounds: an arm without it lets a prover name the seed. What kind of terms
the arms are is not said: where an arm is the compiler's verifier at a flat description whose
decision is the verifier program's own blocks, the arithmetic in it is written by hand after the C++
checks, and the soundness of that description's protocol is a hypothesis inside the arm's bound. The
way out and its price are still letters of p though nothing uses them: a way out that never says yes
has the price 0: `exceptionBound_never`, Johnson/Top/FrontOnlyLaws.lean. `FrontParts p.only` holds
under two premises, also where `p.only` never says yes. The game of `only_sound` is `SoundForWithO`
(an extractor that may query the hash function), not the library's `Sound`. With no hand-written
call beside the arms, "it accepts the files that the C++ prover makes" and "the arm's bound is below
1" both hang on what the arm's coding spells: at a format in which the request reaches the proof's
queries through the second hash's digest alone, a fixed public function, the two cannot hold
together (an argument, not a theorem). That this front verifier accepts any file is not shown:
that it accepts what the C++ prover makes is to be shown by running it, or by a tie to a verifier
that does. Whether it can be run at written terms, and in what time, is not said. It is not the
program that ships: what exit code 0 of a program says of it is another statement. For proofs only;
the program does not import this file.


-/
import Johnson.Top.FrontParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (r : InputArmsC) in
/-- Behind the parser: make the instance; ask the hash function at the key's code and hold the
answer to the commitment; then the three arms. -/
def afterParse (c : Commitment) (prompt output : List Token)
    (a : List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :
    DeterministicAlgorithm Bool :=
  match r.build (prompt, output) a.1 with
  | none => .done false
  | some x =>
    match r.enc a.2.1 with
    | none => .done false
    | some code => .query code fun d =>
        if d = c then deterministicOf (Rom.ofRom ((schemeArmsC r).V a.2.1 x a.2.2))
        else .done false

variable {r : InputArmsC}

/-- The scheme's verifier says yes at g exactly if the three arms do. -/
theorem schemeArmsC_yes_iff (g : Fam (rom 256)) (k : r.C × KeyRoot 256 r.L) (x : r.X)
    (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) :
    ((schemeArmsC r).V k x π).det g = true ↔
      (liftKC r k x π).det g = true ∧ (liftEC r k x π).det g = true ∧
        (liftPC r k x π).det g = true := by
  have e : ((schemeArmsC r).V k x π).det g =
      ((liftKC r k x π).det g && (liftEC r k x π).det g && (liftPC r k x π).det g) := by
    show ((liftKC r k x π).bind fun u => (liftEC r k x π).bind fun v =>
      (liftPC r k x π).bind fun w => Rom.OComp.pure (u && v && w)).det g = _
    simp only [Rom.OComp.det_bind]
    all_goals rfl
  rw [e]
  constructor
  · intro h
    have h1 := Bool.and_eq_true_iff.1 h
    have h2 := Bool.and_eq_true_iff.1 h1.1
    exact ⟨h2.1, h2.2, h1.2⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    all_goals rfl

/-- Its yes at g. -/
theorem afterParse_yes_iff (g : Hash) (c : Commitment) (prompt output : List Token)
    (a : List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :
    (afterParse r c prompt output a).evaluate g = true ↔
      ∃ x code, r.build (prompt, output) a.1 = some x ∧ r.enc a.2.1 = some code ∧ g code = c ∧
        (liftKC r a.2.1 x a.2.2).det (fun _ => g) = true ∧
        (liftEC r a.2.1 x a.2.2).det (fun _ => g) = true ∧
        (liftPC r a.2.1 x a.2.2).det (fun _ => g) = true := by
  constructor
  · intro h
    unfold afterParse at h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i x hb
      split at h
      · exact absurd h Bool.false_ne_true
      · rename_i code he
        have h' : (if g code = c then
            deterministicOf (Rom.ofRom ((schemeArmsC r).V a.2.1 x a.2.2))
            else DeterministicAlgorithm.done false).evaluate g = true := h
        by_cases hc : g code = c
        · rw [if_pos hc, OnBytes.K.evaluate_ofRom] at h'
          exact ⟨x, code, hb, he, hc, (schemeArmsC_yes_iff _ _ _ _).1 h'⟩
        · rw [if_neg hc] at h'
          exact absurd h' Bool.false_ne_true
  · rintro ⟨x, code, hb, he, hc, hv⟩
    unfold afterParse
    rw [hb, he]
    show (if g code = c then deterministicOf (Rom.ofRom ((schemeArmsC r).V a.2.1 x a.2.2))
      else DeterministicAlgorithm.done false).evaluate g = true
    rw [if_pos hc, OnBytes.K.evaluate_ofRom]
    exact (schemeArmsC_yes_iff _ _ _ _).2 hv

variable (p : PortArmsC r)

/-- The front verifier with nothing by hand outside the parser and the arms: the parser, then
`afterParse`. -/
def PortArmsC.only : PortArmsC r :=
  { p with
    port := fun c prompt output F =>
      (p.reader prompt output F).andThen (afterParse r c prompt output) }

/-- Its yes at g. -/
theorem PortArmsC.only_yes_iff (g : Hash) (c : Commitment) (prompt output : List Token)
    (F : p.Files) :
    p.only.Yes g c prompt output F ↔
      ∃ x code, r.build (prompt, output) (p.parsed g prompt output F).1 = some x ∧
        r.enc (p.parsed g prompt output F).2.1 = some code ∧ g code = c ∧
        (liftKC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
          (fun _ => g) = true ∧
        (liftEC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
          (fun _ => g) = true ∧
        (liftPC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
          (fun _ => g) = true := by
  have e : p.only.Yes g c prompt output F ↔
      (afterParse r c prompt output (p.parsed g prompt output F)).evaluate g = true := by
    show ((p.reader prompt output F).andThen (afterParse r c prompt output)).evaluate g = true ↔ _
    rw [DeterministicAlgorithm.evaluate_andThen]
    exact Iff.rfl
  rw [e]
  exact afterParse_yes_iff g c prompt output _

/-- **All five fields on the front verifier hold by definition**; the parser's budget and the way
out's price carry over. No field uses the way out. -/
theorem frontParts_only
    (budget : ∀ prompt output F, (p.reader prompt output F).toRandomized.QueryBound p.n)
    (price : ExceptionBound p.exc p.δ) : FrontParts p.only where
  request := fun g c prompt output F h => by
    obtain ⟨x, _, hx, _⟩ := (p.only_yes_iff g c prompt output F).1 h
    exact Or.inl ⟨x, hx⟩
  idPart := fun g c prompt output F h => by
    obtain ⟨_, code, _, he, hc, _⟩ := (p.only_yes_iff g c prompt output F).1 h
    exact Or.inl ⟨code, he, hc⟩
  keyPart := fun g c prompt output F x h hx => by
    obtain ⟨x', _, hx', _, _, v, _, _⟩ := (p.only_yes_iff g c prompt output F).1 h
    have e : x' = x := Option.some.inj (hx'.symm.trans hx)
    subst e
    exact Or.inl v
  entryPart := fun g c prompt output F x h hx => by
    obtain ⟨x', _, hx', _, _, _, v, _⟩ := (p.only_yes_iff g c prompt output F).1 h
    have e : x' = x := Option.some.inj (hx'.symm.trans hx)
    subst e
    exact Or.inl v
  proofPart := fun g c prompt output F x h hx => by
    obtain ⟨x', _, hx', _, _, _, _, v⟩ := (p.only_yes_iff g c prompt output F).1 h
    have e : x' = x := Option.some.inj (hx'.symm.trans hx)
    subst e
    exact Or.inl v
  budget := budget
  price := price

variable {p} {b : BesideArmsCD r}

/-- The top at it. -/
theorem only_sound {claim : r.I → List Token → List Token → Prop}
    {extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)} {q : ℕ} {εO : ℕ → ℕ → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞}
    (budget : ∀ prompt output F, (p.reader prompt output F).toRandomized.QueryBound p.n)
    (price : ExceptionBound p.exc p.δ) (arms : CoreArmsCD b)
    (commitment : HoleArmsCD.commitmentOO b extO q εO) (meaning : HoleArmsCD.soundFor b claim)
    (error : ∀ tC tP, εO tC tP ≤ ε (tC + tP)) :
    SoundForWithO (systemPortC p.only) (fun c l => deterministicOf (extO.Ei c l)) q claim
      fun t => ε (t + p.n) + p.δ t :=
  front_sound ⟨frontParts_only p budget price, arms, commitment, meaning, error⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.schemeArmsC_yes_iff
#print axioms VerifiableInference.OnPublicFiles.afterParse_yes_iff
#print axioms VerifiableInference.OnPublicFiles.PortArmsC.only_yes_iff
#print axioms VerifiableInference.OnPublicFiles.frontParts_only
#print axioms VerifiableInference.OnPublicFiles.only_sound
