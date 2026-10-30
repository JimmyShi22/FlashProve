-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/ReBound.lean: THE NUMBER OF THE HONEST COMMITTER'S COINS AS A LETTER:
general in the description. Definitions, statements and proofs. Conditionals: no description is
built.

Why. The told committer is run at a number n in Fin (coinBound + 1), from which it reads its coins:
entry n % (ri.n + 1) of the enumeration of pads and tails, entry n / (ri.n + 1) % (sl.n + 1) of that
of salts. `bound` is a field of the compiler's letters (`InnerCompilerInputFieldsOverThreeProtocols`, Johnson/Flat/InnerInputOfThreeProtocols.lean), so of
`D.T`, which `D.withTerms Q` (Johnson/Goal/Conditions/DescribeTerms.lean) leaves as it is. At a
description that lays bound := 0 the number is always 0: the committer has ONE setting of coins, and
the goal on opening-form binding, whose opener names weights and randomness, then speaks of that one
setting alone: AN OPENER THAT PICKS ITS OWN COINS IS NOT IN IT. No
verifier and no goal reads `coinBound`. Here it is laid at a letter b, and everything passes over.

Main names.
  `InnerCompilerInput.reBound R b`, `LayoutsByPublicReading.reBound T b` (namespace `VerifiableInference.OnPublicFiles`): the input
    with coinBound := b; the told record with the same twelve fields over it.
  `D.reBound b` (namespace `VerifierAndGoals`): D with `T`'s field bound laid at b Z.
  `input_reBound`, **`verify_reBound`**: its input is D's with that bound; THE GOALS' VERIFIER IS
    D's: by definition.
  `Q.reBound b coins'` (namespace `VerifierAndGoals.Fit`): `HonestTerms` over `D.reBound b`: Q's fields, the
    told record re-bound, and a coins' algorithm into Fin (b Z + 1).
  **`BindLaws.reBound`**: the laws that opening-form binding owes pass over: eleven as they stand
    (none names coinBound); the coins' count and the test on numbers are asked anew.
  `BindLaws.reaches`: at the number a + (ri.n + 1) c the told scheme's committer runs at entry a of
    Q.ri and entry c of Q.sl.
  **`soundUnderPolicyAt_reBound`**: soundness under the files' policy of `D.withTerms Q` is that of
    `(D.reBound b).withTerms (Q.reBound b coins')`: the same error: it reads the verifier, the
    parser and the extractor, which are the same terms.

WHO READS EACH LETTER. b (at every Z a number): the type of the told committer's number, and nothing
else. coins': the honest committer alone. The rest: as in DescribeTerms.lean.
NOTHING THAT THE VERIFIER READS STANDS UNDER "THERE IS".

Limits. Those of DescribeTerms.lean. Besides:
- A THEOREM ON `(D.reBound b).withTerms …` IS A THEOREM ON THAT DESCRIPTION.
- That the enumerations are onto, or that b is as large as their product asks, is no premise and no
  conclusion here: at a small b, or at enumerations with one member, the committer again has few
  settings of coins.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.DescribeTerms
import Johnson.Top.ToldReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles

/-- The input with the number of coins laid at b. -/
def InnerCompilerInput.reBound (R : InnerCompilerInput) (b : ℕ) : InnerCompilerInput := { R with coinBound := b }

/-- The told record over it: the same twelve fields. -/
def LayoutsByPublicReading.reBound {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : ℕ) : LayoutsByPublicReading (R.reBound b) where
  D := T.D
  Pub := T.Pub
  Pt := T.Pt
  part := T.part
  Sd := T.Sd
  cA := T.cA
  m := T.m
  encT := T.encT
  ISK := T.ISK
  commit := T.commit
  prove := T.prove
  π₀ := T.π₀

/-- Its named extractor is T's. -/
theorem LayoutsByPublicReading.extractor_reBound {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : ℕ) :
    (T.reBound b).extractor = T.extractor := rfl

end VerifiableInference.OnPublicFiles

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat

/-- **The description with the number of coins laid at b.** -/
def Description.reBound (D : Description) (b : PublicFiles → ℕ) : Description :=
  { D with T := fun Z c m => { D.T Z c m with bound := b Z } }

variable (D : Description) (b : PublicFiles → ℕ)

/-- Its input is D's with that number. -/
theorem input_reBound (Z : PublicFiles) (c : Digest) (m : D.More) :
    (D.reBound b).input Z c m = (D.input Z c m).reBound (b Z) := rfl

/-- **The goals' verifier is D's.** -/
theorem verify_reBound (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form) :
    verify (D.reBound b) Z parse = verify D Z parse := rfl

end VerifierAndGoals

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open scoped ENNReal

variable {D : Description} (Q : HonestTerms D) (b : PublicFiles → ℕ)
  (coins' : (Z : PublicFiles) → Q.Rand → DeterministicAlgorithm (Fin (b Z + 1)))

/-- **The honest side's terms over the re-bound description.** -/
def HonestTerms.reBound : HonestTerms (D.reBound b) where
  c₀ := Q.c₀
  m₀ := Q.m₀
  T := fun Z => (Q.T Z).reBound (b Z)
  φ := Q.φ
  back := Q.back
  ri := Q.ri
  sl := Q.sl
  b₀ := Q.b₀
  proveT := Q.proveT
  Rand := Q.Rand
  sample := Q.sample
  coins := coins'
  prove := Q.prove

/-- **The laws that opening-form binding owes pass over.** hc: the new coins' algorithm asks at most
q queries; hn: the test on numbers at q. -/
theorem BindLaws.reBound {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q₀ q : ℕ}
    (h : BindLaws Q Z s tP q₀) (hc : ∀ ρ, (coins' Z ρ).toRandomized.QueryBound q)
    (hn : q + (Q.tCommit Z tP + 1) ≤ honestBudget) :
    BindLaws (Q.reBound b coins') Z s tP q where
  noCoin := h.noCoin
  asks := h.asks
  once := h.once
  spare := h.spare
  word := h.word
  code := h.code
  wire := h.wire
  section_ := h.section_
  decodes := h.decodes
  total := h.total
  reading := h.reading
  coinsWithin := hc
  number := hn

/-- **Which coins the told scheme's committer takes at the number of a pair**: the public reading,
then `committerAtFixedCoins` at entry a of Q.ri and entry c of Q.sl over the coding at d, the told part laid
beside (`commitBehind_reach`, Johnson/Top/ToldReach.lean). -/
theorem BindLaws.reaches {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (i : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).Index) (a : Fin ((Q.ri Z).n + 1))
    (c : Fin ((Q.sl Z).n + 1)) :
    ((Q.T Z).commitBehind (Q.ri Z) (Q.sl Z) (Q.b₀ Z) i).withCoins
        (a.val + ((Q.ri Z).n + 1) * c.val) =
      (Q.T Z).Pub.bind fun d =>
        ((TypedOracleCompiler.Compile.Batch.Cms.committerAtFixedCoins (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout ((Q.T Z).Sd d)
          (Q.b₀ Z) i ((Q.ri Z).e a) ((Q.sl Z).e c)).overOne ((Q.T Z).m d)).bind
          fun o => .pure (((Q.T Z).part d, o.1), o.2) :=
  commitBehind_reach (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) h.noCoin i a c

/-- **Soundness under the files' policy passes over**, at the same error. -/
theorem soundUnderPolicyAt_reBound (eps : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt (D.withTerms Q) eps) :
    SoundUnderPolicyAt ((D.reBound b).withTerms (Q.reBound b coins')) eps :=
  fun Z pp h₁ h₂ => ⟨(sound Z pp h₁ h₂).1, fun Form prove parse n hn =>
    (sound Z pp h₁ h₂).2 Form prove parse n hn⟩

end VerifierAndGoals.Fit

#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.extractor_reBound
#print axioms VerifierAndGoals.input_reBound
#print axioms VerifierAndGoals.verify_reBound
#print axioms VerifierAndGoals.Fit.BindLaws.reBound
#print axioms VerifierAndGoals.Fit.BindLaws.reaches
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_reBound
