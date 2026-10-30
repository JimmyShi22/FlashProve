-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ThreeAtFiles.lean: the theorem on innerCompiledVerifier at the full size with "sound"
proved (Johnson/Flat/ThreeFull.lean), under three named hypotheses and the theorem on codes, where
the table of scales AND the data of the key file's and the proof file's protocols are values made of
the same three public files.

In Johnson/Flat/ThreeFull.lean the table of scales s and the record G (FilesParameters,
OnBytes/Flat/FilesAt.lean) are letters, tied to nothing and not to each other. Here Z are three
public files (K.Pub, OnBytes/K/Served.lean: in the order parameter file, layout file, scale file;
the planner takes them in another order, and planOf turns it).
  s is what scalesOfFiles (Johnson/Flat/ScalesOf.lean) reads off Z's parameter file and scale file.
  G := bigReq p, at the answer p of the program's planner at Z (planOf, OnBytes/Flat/BigAt.lean).

Main definitions and theorems.
  recZeroFull: the record of zeros with the factor 1.
  bigReq p: the key file's chains, the proof file's chains and the depth of a batch's tree are p's
    (bigAt); the first chain's block at a request is the program's own Proof.firstBlock at the links
    and the reply of that request (pubReq p, Johnson/Flat/PubReq.lean); the dry runs are made at
    recZeroFull and at the request firstReq; what of a request is fixed first is the request with
    the reply 0.
  bigReq_eq_bigOf: it is bigOf (pubReq p) recZeroFull (OnBytes/Flat/BigOf.lean).
  atPlan_bigReq: it is at the plan of Z.
  soundThreeFull_atFiles: planOf Z = .ok p and scalesOfFiles Z.pol Z.KL = .ok s give: bigReq p is at
    the plan of Z, and the statement of soundThreeFull_ref holds at that s and G := bigReq p, under
    the three named hypotheses, the theorem on codes, T's builder buildReq and T's model nextTok s.
  guardsAtB Z, guards_of_test, guards_at: "the makers' tests on the dry runs pass" (GuardsPassFull,
    Johnson/Flat/WireAt.lean) at bigReq of the planner's answer at Z, as one test with its theorem.
  soundThreeFull_guarded: conditional, on the three named hypotheses, and no theorem on `verify`
    (that is `sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean):
    the same with guardsAtB Z = true among the premises and
    "the guards pass" in the conclusion: so a telling carries the test in the statement's type. The
    first two clauses of its conclusion follow from the premises by unfolding; the third is the
    theorem.

WHAT IS LEFT A LETTER: the coding E, the provers P and the rest of T. No value of E or T is written
in this library (of P there is one, Files.fixedMessageProvers, OnBytes/Flat/Silent.lean: provers that send fixed
messages, not the prover program): that T's type has a member with the two equations on its builder
and its model is not shown. The three named hypotheses are as unproved as in ThreeFull.lean; here
they speak of one protocol, made of Z.

Limits: those of Johnson/Flat/ThreeFull.lean, but for s and G. No file is evaluated here: that the
planner and scalesOfFiles return at the shipped files, and that guardsAtB says true there, are
evaluations that are owed. WHERE A GUARD FAILS that file's decision says no at every instance and
all views (runKFull_false, runPFull_false, Johnson/Flat/WireAt.lean); by reading (no
theorem) "keySound" and "proofSound" are then true and say nothing: hence soundThreeFull_guarded.
The three premises on Z (the planner returns, the table of scales is read, the guards pass) are met
by evaluations, not by theorems: a telling names Z's three files by their digests, and who has
evaluated what. The reference sizes are typed, not read off Z. That the dry runs do not hang on
which record is taken, and that the dry runs at firstReq give the rounds of every request, is not
shown here.
THE HASH. In the statement the game's hash function is drawn; planOf Z and bigReq p are made with
FIXED functions. p.cfg, which the planner hands to chainsOf and so puts into the chains that bigReq
takes over, is the digest of Z's three files under the format's hash as a fixed function
(configuration, OnBytes/Model/VerifyChains.lean: Params.configurationDigest at formatHashFastForm). Whether the
planner returns hangs on digests under the second hash function, where the parameter file has the
tables' lines: publicOf compares them by tableHeld (OnBytes/Model/Config.lean: secondHashFunction). Its hPar
(secondHashFunctionTree) forms a digest that is dropped, and refuses by the files' lengths alone. p.X.digests holds
the digests of the lists of calls under secondHashFunction (OnBytes/Model/VerifyPublic.lean); bigReq does not
read them. No premise here ties any of these to the drawn function.

-/
import Johnson.Flat.TwoAtPlan
import Johnson.Flat.PubReq
import Johnson.Flat.ThreeFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model

/-- The record of zeros with the factor 1. -/
def recZeroFull : RecFull := (fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩), fun _ => 0)

/-- **The data of the two big files' protocols, made of a planner's answer.** -/
def bigReq (p : Model.Verify.Planned) : FilesParameters Flat.Req RecFull :=
  bigAt p (pubReq p).block recZeroFull (firstReq, recZeroFull) reqWithoutReply

/-- It is bigOf at pubReq. -/
theorem bigReq_eq_bigOf (p : Model.Verify.Planned) :
    bigReq p = bigOf (pubReq p) recZeroFull := by
  have e : Nat.log2 (pubReq p).N = p.chains.proof.first.binding.logLeaves := Nat.log2_two_pow
  unfold bigReq bigAt bigOf
  rw [e]
  rfl

/-- It is at the plan of the three public files. -/
theorem atPlan_bigReq {Z : K.Pub} {p : Model.Verify.Planned} (h : planOf Z = .ok p) :
    AtPlan Z (bigReq p) :=
  atPlan_bigAt h _ _ _ _

section
variable (p : Model.Verify.Planned) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E)
    (bigReq p)).Provers)

/-- **Under the three named hypotheses LeftThreeFull T and the theorem on codes** (hypotheses of the
theorem: Lean's list of axioms does not show them), where planOf Z returns p and scalesOfFiles
returns s, at T's builder buildReq and T's model nextTok s: the theorem on innerCompiledVerifier at the full
size, at the table of scales and the protocols' data of three public files. -/
theorem soundThreeFull_atFiles {Z : K.Pub} (hp : planOf Z = .ok p)
    (hs : scalesOfFiles Z.pol Z.KL = .ok s) (hA : BCHKS46At GF GE)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E (bigReq p) P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    AtPlan Z (bigReq p) ∧
      SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
        (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  ⟨atPlan_bigReq hp, soundThreeFull_files s E (bigReq p) P hs hA T hb hn h⟩

end

/-- A run can decide whether the makers' tests pass. -/
instance decGuardsPassFull {X : Type} (G : FilesParameters X RecFull) : Decidable (GuardsPassFull G) := by
  unfold GuardsPassFull
  infer_instance

/-- "The makers' tests on the dry runs pass" at the data made of three public files, as one test. -/
def guardsAtB (Z : K.Pub) : Bool :=
  match planOf Z with
  | .ok p => decide (GuardsPassFull (bigReq p))
  | .error _ => false

/-- **If the test says true, the planner returns at Z and the makers' tests pass at its data.** -/
theorem guards_of_test {Z : K.Pub} (t : guardsAtB Z = true) :
    ∃ p, planOf Z = .ok p ∧ GuardsPassFull (bigReq p) := by
  unfold guardsAtB at t
  cases h : planOf Z with
  | error e =>
    rw [h] at t
    cases t
  | ok p =>
    rw [h] at t
    exact ⟨p, rfl, of_decide_eq_true t⟩

/-- The same at a named answer of the planner. -/
theorem guards_at {Z : K.Pub} {p : Model.Verify.Planned} (hp : planOf Z = .ok p)
    (t : guardsAtB Z = true) : GuardsPassFull (bigReq p) := by
  obtain ⟨p', h', g⟩ := guards_of_test t
  obtain rfl : p' = p := Except.ok.inj (h'.symm.trans hp)
  exact g

section
variable (p : Model.Verify.Planned) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E)
    (bigReq p)).Provers)

/-- **Conditional, and no theorem on `verify`**
(that is `sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean):
soundThreeFull_atFiles, under the same hypotheses (the three named
hypotheses LeftThreeFull T and the theorem on codes among them: Lean's list of axioms does not show
them), with the test on the makers' guards among its premises, and "the guards pass" in its
conclusion. -/
theorem soundThreeFull_guarded {Z : K.Pub} (hp : planOf Z = .ok p) (t : guardsAtB Z = true)
    (hs : scalesOfFiles Z.pol Z.KL = .ok s) (hA : BCHKS46At GF GE)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E (bigReq p) P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l) (h : LeftThreeFull T) :
    AtPlan Z (bigReq p) ∧ GuardsPassFull (bigReq p) ∧
      SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
        (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  ⟨atPlan_bigReq hp, guards_at hp t, soundThreeFull_files s E (bigReq p) P hs hA T hb hn h⟩

end

end VerifiableInference.OnPublicFiles
