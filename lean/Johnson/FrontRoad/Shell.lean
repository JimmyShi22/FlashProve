-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Shell.lean: under two premises (fits, reads), and under every fixed hash function,
VerifierAndGoals.verify accepts if and only if four conditions hold; the last is that the compiled verifier at
the public reading's value d accepts.
Terms and the limits that go with any quote: Spec.lean.

What this file proves, for every description D, public files Z, family T and parser.
  verify_iff   Under every hash function, verify D Z parse accepts a commitment, a prompt, an output
      and a form if and only if: (1) the public files are in scope (InScope Z); (2) an instance is
      built from the prompt, the output and the typed proof's further tokens; (3) the key in the
      typed proof, with the told part of d in front, has a code, and the hash function's answer at
      that code is the commitment; (4) the compiled verifier at d (verifyAtKeyRoot), over the one hash function
      through the coding at d, accepts the key, the instance and the proof. Here the typed proof is
      the parser's value, and d the public reading's value, under that hash function.
  verify_whole   The same where the parser's value is computed (lowKey, lowPrf) from a whole key and
      a proof of the scheme with the whole key published. Condition (4) is then that the verifier of
      wholeAt T h d (Johnson/PublicAt/Whole.lean) accepts them.
The two premises. They are among those of the library's step for soundness, under its names
(VerifierAndGoals.Fit.soundForWith_system_of_toldO, Johnson/PV/FitO.lean).
  fits   for all c and m, innerCompiledVerifier at D's input at (c, m) is innerCompiledVerifier at T's input at pair c m.
  reads   under every hash function, pair of the two readings' values is the value of T's public
      reading.

Limits. An equivalence of two decisions under each fixed hash function: nothing on whether either
accepts, and nothing on soundness, completeness or hiding. fits and reads are premises. The parser
is a variable: nothing is said about a form's bytes.

How it fits. VerifierAndGoals.verify is a definition of its own: a test on the public files, a parser, two
public readings, then innerCompiledVerifier at the input made from them. The theorems of Johnson/PublicAt/ and
Johnson/WholeKey/ are about a scheme whose verifier is the compiled verifier at d, over one hash
function, after the public reading. That a shell has the definition of VerifierAndGoals.verify as its verifier
is more than a label only if the two decide alike; Complete.lean uses verify_whole to compare them.
The proofs rest on OnBytes.K.front_yes and front_yes_only (Johnson/Top/FrontGeneral.lean).
-/
import Johnson.PV.FitO
import Johnson.Top.InnerCompiledVerifierParts
import Johnson.PublicAt.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom VerifierAndGoals VerifierAndGoals.Fit
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))

/-- Under fits and reads, for every hash function: verify D Z parse accepts if and only if the
public files are in scope, an instance x is built, the key with the told part of d has a code at
which the hash function's answer is the commitment, and the compiled verifier at d accepts. The
typed proof is the parser's value and d the public reading's value under that hash function. -/
theorem verify_iff (pair : Digest → D.More → T.D)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash, (readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    {Form : Type} (parse : Parser D Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (verify D Z parse commitment prompt output form).evaluate hash = true ↔
      InScope Z = true ∧
        ∃ x code,
          (D.input Z c₀ m₀).buildInstance (prompt, output)
              ((parse prompt output form).evaluate hash).1 = some x ∧
            T.encT (T.part (T.Pub.det fun _ => hash),
              ((parse prompt output form).evaluate hash).2.1) = some code ∧
            hash code = commitment ∧
            ((verifyAtKeyRoot (D.input Z c₀ m₀).queryLayout (T.Sd (T.Pub.det fun _ => hash))
                (T.cA (T.Pub.det fun _ => hash)) (D.input Z c₀ m₀).fixedSample (D.input Z c₀ m₀).compilerParameters
                ((parse prompt output form).evaluate hash).2.1 x
                ((parse prompt output form).evaluate hash).2.2).overOne
              (T.m (T.Pub.det fun _ => hash))).det (fun _ => hash) = true := by
  have e : pair ((readConfig Z).evaluate hash)
      ((D.readMore Z ((readConfig Z).evaluate hash)).evaluate hash) = T.Pub.det fun _ => hash := by
    rw [← reads hash]
    unfold readBoth
    rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
    rfl
  unfold verify verifyAt
  by_cases hs : InScope Z = true
  · rw [if_pos hs]
    simp only [andThen_eq, DeterministicAlgorithm.evaluate_andThen]
    rw [fits, e]
    obtain ⟨aux, key, π⟩ := (parse prompt output form).evaluate hash
    constructor
    · intro h
      exact ⟨hs, OnBytes.K.front_yes_only _ _ _ _ _ hash commitment prompt output aux key π h⟩
    · rintro ⟨-, x, code, hb, hc, hd, hv⟩
      exact OnBytes.K.front_yes _ _ _ _ _ hash commitment prompt output aux key π x code hb hc hd hv
  · rw [if_neg hs]
    constructor
    · intro h
      exact absurd h (by simp [DeterministicAlgorithm.evaluate])
    · rintro ⟨h, -⟩
      exact absurd h hs

/-- The same, under fits and reads, if the parser's value is (aux, (lowKey k, lowPrf k π)) for a
whole key k and a proof π of the scheme with the whole key published (hp): the last condition is
that the verifier of wholeAt T h d accepts k, x and π over the one hash function. -/
theorem verify_whole (pair : Digest → D.More → T.D)
    (fits : ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash, (readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (h : T.D → OnBytes.WholeKey.HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody
      (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)
    {Form : Type} (parse : Parser D Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) (aux : List Token)
    (k : FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)
    (π : RequestProof 256 (D.input Z c₀ m₀).protocol)
    (hp : (parse prompt output form).evaluate hash =
      (aux, (OnBytes.WholeKey.lowKey k, OnBytes.WholeKey.lowPrf k π))) :
    (verify D Z parse commitment prompt output form).evaluate hash = true ↔
      InScope Z = true ∧
        ∃ x code,
          (D.input Z c₀ m₀).buildInstance (prompt, output) aux = some x ∧
            T.encT (T.part (T.Pub.det fun _ => hash), OnBytes.WholeKey.lowKey k) = some code ∧
            hash code = commitment ∧
            ((OnBytes.PublicAt.wholeAt T h (T.Pub.det fun _ => hash)).V k x π).det
              (fun _ => hash) = true := by
  rw [verify_iff D Z c₀ m₀ T pair fits reads parse hash commitment prompt output form, hp]
  rfl

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.verify_whole
#print axioms OnBytes.FrontRoad.verify_iff
