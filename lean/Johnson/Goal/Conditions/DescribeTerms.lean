-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DescribeTerms.lean: GENERAL IN THE DESCRIPTION: THE HONEST COMMITTER AND THE
EXTRACTOR OF A DESCRIPTION (Ladder.lean) AS TERMS OVER A TOLD RECORD, AND THE GOAL ON BINDING, G9,
AT A DESCRIPTION IN WHICH THEY ARE LAID; with soundness under the files' policy at that one
extractor: `SoundAndBinding` of the goals' own verifier, in its nearest form (Ladder/Package.lean),
AT A NAMED ERROR. Definitions, statements and proofs. Conditionals: no description and no told
record is built.

Why. Ladder/FitBinds.lean brings G9 to a record `BindAt` at every Z in scope. Five of its hypotheses
are laws on `D.commit`, `D.extractor` and the told record's committer: behind, commits, within, the
goal's own first conjunct, and hext. These fields are free: the verifier reads none of them. Here
they are written once, for every description, so that these five hold by definition or by a count.
THE COINS COME BY AN ALGORITHM THAT MAY ASK THE HASH FUNCTION (as `BindAt.coins` has it): so a
committer that makes its pads, tails and salts by a generator from a key which holds an answer of
the hash function is not shut out.

Main names (namespace `VerifierAndGoals.Fit`).
  `HonestTerms D`: the data from which the honest side is made, total in Z and in the settings: a
    told record over `D`'s input at every Z; the index of given weights (back) and the way back (φ);
    the coins' enumerations; the randomness, with the algorithm that makes the told committer's
    number of it; provers.
  `Q.told Z`: the told record with the committer `commitBehind` laid in
    (Johnson/Top/ToldCommit.lean).
  `D.withTerms Q`: `D` with `commit` := Q.coins' algorithm, then the committer of
    `(Q.told Z).systemOn back` at the number that it returns; `extractor` := the told record's named
    extractor, then φ, by bind; Rand, sample and prove are Q's.
  `input_withTerms`, `verify_withTerms`: the compiler's input and THE GOALS' VERIFIER ARE `D`'s OWN,
    by definition.
  `tCommit Q Z tP`: the count tP + 2 · 2^depth + 2 (K + 1).
  `BindLaws Q Z s tP q`: the hypotheses at one Z: the told law's six, the first of the wire's
    laws, section, decodes, total (every pair (told part, key) has a code), the reading's count, the
    coins' count, and one test on numbers.
  `bindAt_withTerms`: `BindAt` from it.
  **`bindsAt_withTerms`**: the stored `BindsAt` at the named error
    fun t => `epsBind honestBudget` (t + q).
  **`G9_withTerms`**: the stored G9.
  **`nearestSoundAndBinding_withTerms`**: with `SoundUnderPolicyAt` at an error epsS:
    `NearestSoundAndBinding` at `joinError epsS fun t => epsBind honestBudget (t + q)`: no "there
    is" on the error.

WHO READS EACH LETTER (V: `verify`; C: the honest committer; X: the extractor; B: a bound).
- D.C, D.F, D.P, D.readMore, D.T, D.parse, D.Form: V. C and X read D.input at (c₀ Z, m₀ Z) for its
  object, wiring and bound. D.extractor, D.Rand, D.sample, D.commit, D.prove: overwritten.
- Q.T Z: its Pub, part, Sd, m, encT: C; its m, part, encT: X. THAT V's OWN READINGS AND CODINGS ARE
  THESE IS NO PREMISE HERE: binding does not read V. It is the fit's `fits` and `reads`
  (Johnson/PV/FitO.lean), which soundness asks AT THE SAME RECORD.
- Q.back: C. Q.φ: X. `section_` ties the two. Q.ri, Q.sl, Q.b₀, Q.coins: C alone.
- Q.proveT, Q.prove, Q.sample: nobody in these statements.
- tP, q: B; tied by `reading` and `coinsWithin` from below alone, and by `number` from above.
NOTHING THAT V READS STANDS UNDER "THERE IS". G9 begins with one, of an error: `bindsAt_withTerms`
names it. `SoundAndBinding` begins with one, of an extractor: it is `(D.withTerms Q).extractor`.

Limits.
- A THEOREM ON `D.withTerms Q` IS A THEOREM ON THAT DESCRIPTION. It speaks of THE description of the
  protocol only if that one IS of this form. What runs is not touched (`verify_withTerms`); what
  completeness and zero knowledge read (Rand, sample, commit, prove) is.
- `BindLaws` is a bundle of premises: that they can be met together at a Z is not shown here.
  `decodes` is shown at the full size's object with the written honest side
  (`obj_decodes_index_full`, Johnson/Flat/CodingCells.lean).
- THE COMMITTER IS TIED TO NO PROGRAM. THE VERIFIER IS IDLE IN G9: a verifier that refuses
  everything meets `nearestSoundAndBinding_withTerms`'s first clause for nothing: the statement
  weighs only beside completeness of the same description (the head of Ladder/Package.lean).
- The public files are fixed before the hash function is drawn. The error is
  3 (t + q + 2 · 2^48 + 2)² / 2^256.
- Q.coins IS A LETTER: no generator and no string is written here. Nothing on hiding: that coins so
  made are as good as drawn ones is not treated.
- All limits of Johnson/Top/OpensTold.lean, Johnson/Top/ToldCommit.lean and Ladder/FitBinds.lean
  stand.
Terms: lean/GLOSSARY.md.

-/
import Ladder.FitBinds
import Johnson.Top.ToldCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open RandomizedAlgorithm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K (Pub)
open scoped ENNReal

/-- The data from which the honest side of a description is made: total in Z and in the settings. -/
structure HonestTerms (D : Description) where
  /-- the pair at which the told record's input is taken -/
  c₀ : PublicFiles → Digest
  m₀ : PublicFiles → D.More
  /-- the told record; its own committer and prover are not read -/
  T : (Z : PublicFiles) → LayoutsByPublicReading (D.input Z (c₀ Z) (m₀ Z))
  /-- from the extractor's index to weights; it may say none -/
  φ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → (D.input Z (c₀ Z) (m₀ Z)).Index →
    Option (ModelWeights s)
  /-- the index of given weights -/
  back : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ModelWeights s →
    (D.input Z (c₀ Z) (m₀ Z)).Index
  /-- the two enumerations of the committer's coins, and the filling beyond the word -/
  ri : (Z : PublicFiles) → Iop.Enum (D.input Z (c₀ Z) (m₀ Z)).protocol.EncodingRandomness
  sl : PublicFiles → Iop.Enum (ℕ → Rom.Bits)
  b₀ : (Z : PublicFiles) → (D.input Z (c₀ Z) (m₀ Z)).LeafBody
  /-- a prover of the told scheme for what the committer keeps -/
  proveT : (Z : PublicFiles) → (D.input Z (c₀ Z) (m₀ Z)).Index × (D.input Z (c₀ Z) (m₀ Z)).protocol.EncodingRandomness × (ℕ → Rom.Bits)
    → (l : List ((D.input Z (c₀ Z) (m₀ Z)).Instance × Unit)) → Rom.OComp (rom 256) (ZKCP.Gen.Slots
             (OfflineLinkOnlineProof 256 (D.input Z (c₀ Z) (m₀ Z)).protocol (D.input Z (c₀ Z) (m₀ Z)).offlineRoundSplits
               (D.input Z (c₀ Z) (m₀ Z)).linkRoundSplits) l)
  /-- the honest committer's randomness, and the algorithm that makes the told committer's number of
  it; it may ask the hash function -/
  Rand : Type
  sample : RandomizedAlgorithm Rand
  coins : (Z : PublicFiles) → Rand → DeterministicAlgorithm (Fin ((D.input Z (c₀ Z) (m₀ Z)).coinBound + 1))
  /-- the honest prover -/
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm D.Form

variable {D : Description} (Q : HonestTerms D)

/-- The told record with the honest committer behind the public reading laid in. -/
def HonestTerms.told (Z : PublicFiles) : LayoutsByPublicReading (D.input Z (Q.c₀ Z) (Q.m₀ Z)) :=
  (Q.T Z).withCommit (Q.ri Z) (Q.sl Z) (Q.b₀ Z) (Q.proveT Z)

/-- **The description with the honest committer and the extractor laid in.** -/
def _root_.VerifierAndGoals.Description.withTerms (D : Description) (Q : HonestTerms D) : Description :=
  { D with
    extractor := fun Z s commitment queryLog =>
      ((Q.T Z).extractor commitment queryLog).bind (Q.φ Z s)
    Rand := Q.Rand
    sample := Q.sample
    commit := fun Z s w ρ => (Q.coins Z ρ).andThen fun n =>
      ((Q.told Z).systemOn (Q.back Z s) (modelNextToken s)).commit w n
    prove := Q.prove }

/-- The compiler's input is `D`'s. -/
theorem input_withTerms (Z : PublicFiles) (c : Digest) (m : D.More) :
    (D.withTerms Q).input Z c m = D.input Z c m := rfl

/-- **The goals' verifier is `D`'s.** -/
theorem verify_withTerms (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form) :
    verify (D.withTerms Q) Z parse = verify D Z parse := rfl

/-- The told committer's count, where the public reading asks at most tP queries. -/
def HonestTerms.tCommit (Z : PublicFiles) (tP : ℕ) : ℕ :=
  tP + (2 * 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth + 2 * ((D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.K + 1))

/-- **What opening-form binding (`BindsWith`) takes as hypotheses at one Z.** -/
structure BindLaws (Z : PublicFiles) (s : IntegerTransformer.Settings) (tP q : ℕ) : Prop where
  noCoin : (Q.T Z).Pub.NoCoin
  asks : (Q.T Z).Pub.AsksIn fun _ x => (Q.T Z).Pt x
  once : NoRepeat (Q.T Z).Pub
  spare : ∀ d x, (Q.T Z).Pt x → IsOther ((Q.T Z).m d) x
  word : ∀ d d', (Q.T Z).part d = (Q.T Z).part d' →
    (extractorOverOneHashFunction ((Q.T Z).m d) (indexExtractorAtRootAndOutOfDomainSample (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout)).Ei =
      (extractorOverOneHashFunction ((Q.T Z).m d') (indexExtractorAtRootAndOutOfDomainSample (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout)).Ei
  code : ZKCP.CodeIsOneToOne (Q.T Z).encT
  wire : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.OKG
  /-- φ gives back the weights from their index -/
  section_ : ∀ w, Q.φ Z s (Q.back Z s w) = some w
  /-- the decoder gives back the index of every set of weights -/
  decodes : ∀ w r sd, (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.decodeIndex
    ((D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.encodeIndex (Q.back Z s w) r)
    ((D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.recOf (Q.back Z s w) r sd) = some (Q.back Z s w)
  /-- every pair (told part, key) has a code -/
  total : ∀ key, (Q.T Z).encT key ≠ none
  /-- the public reading asks at most tP queries -/
  reading : (Q.T Z).Pub.QueryBound tP
  /-- the coins' algorithm asks at most q queries -/
  coinsWithin : ∀ ρ, (Q.coins Z ρ).toRandomized.QueryBound q
  /-- the one test on numbers: the coins' algorithm and the committer, with the query for the key's
  code, are within the honest side's budget -/
  number : q + (Q.tCommit Z tP + 1) ≤ honestBudget

variable {Q}

/-- **`BindAt` at the description with the terms laid in**: behind, commits and within hold by
definition or by the count. -/
def bindAt_withTerms {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) : BindAt (D.withTerms Q) Z s where
  c₀ := Q.c₀ Z
  m₀ := Q.m₀ Z
  T := Q.told Z
  φ := Q.φ Z s
  back := Q.back Z s
  coins := Q.coins Z
  qCoins := q
  ri := Q.ri Z
  sl := Q.sl Z
  b₀ := Q.b₀ Z
  isk := fun _ k => k
  tS := Q.tCommit Z tP
  noCoin := h.noCoin
  asks := h.asks
  once := h.once
  spare := h.spare
  word := h.word
  code := h.code
  wire := h.wire
  section_ := h.section_
  behind := commitsBehind_withCommit (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) (Q.proveT Z)
  coinsWithin := h.coinsWithin
  commits := fun _ ρ hash => DeterministicAlgorithm.evaluate_andThen hash (Q.coins Z ρ) _
  decodes := h.decodes
  coded := (ZKCP.SpecialAny.oneOf _).keysHaveCodes_of_total h.total
  within := fun _ => queryBound_commitBehind (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) tP h.reading _

/-- The goal's own first conjunct: the honest committer stays within the honest side's budget. -/
theorem commitWithin_withTerms {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (ρ : Q.Rand) :
    ((D.withTerms Q).commit Z s w ρ).toRandomized.QueryBound honestBudget :=
  queryBound_mono_det _ _ _ h.number
    (queryBound_andThen (Q.coins Z ρ) _ q (Q.tCommit Z tP + 1) (h.coinsWithin ρ) fun n =>
      queryBound_commit_systemOn (Q.T Z) (Q.ri Z) (Q.sl Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s)
        (modelNextToken s) tP h.reading w n)

variable (Q)

/-- **THE STORED `BindsAt`, AT A NAMED ERROR.** -/
theorem bindsAt_withTerms (tP q : ℕ)
    (h : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindLaws Q Z (settingsOfRead pp) tP q) :
    BindsAt (D.withTerms Q) fun t => epsBind honestBudget (t + q) :=
  bindsAt_of_bindAt (D.withTerms Q) honestBudget q
    (fun Z pp h₁ h₂ => bindAt_withTerms (h Z pp h₁ h₂))
    (fun Z pp h₁ h₂ => commitWithin_withTerms (h Z pp h₁ h₂)) (fun _ _ _ _ => rfl)
    fun Z pp h₁ h₂ => ⟨le_trans (Nat.le_succ _) (le_trans (Nat.le_add_left _ q)
      (h Z pp h₁ h₂).number), le_refl q⟩

end VerifierAndGoals.Fit

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open OnBytes.K (Pub)
open scoped ENNReal

/-- **THE STORED G9**, at every family of descriptions with the terms laid in. -/
theorem G9_withTerms (D : SecondHashFunctionType → Description) (Q : ∀ o, HonestTerms (D o)) (tP q : ℕ)
    (hq : q ≤ honestBudget)
    (h : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindLaws (Q OnBytes.secondHashFunction) Z (settingsOfRead pp) tP q) :
    G9 fun o => (D o).withTerms (Q o) :=
  ⟨fun t => epsBind honestBudget (t + q),
    epsBind_le_ceiling honestBudget q (by
      have h1 : honestBudget = 2 ^ 48 := rfl
      have h2 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
      have h3 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
      rw [h1, h2] at hq
      rw [h1, h2, h3]
      omega),
    bindsAt_withTerms (Q OnBytes.secondHashFunction) tP q h⟩

/-- **`SoundAndBinding` OF THE GOALS' OWN VERIFIER, IN ITS NEAREST FORM, AT A NAMED ERROR**: from
soundness under the files' policy at the description's one extractor, and the laws that opening-form
binding takes as hypotheses. -/
theorem nearestSoundAndBinding_withTerms (D : SecondHashFunctionType → Description) (Q : ∀ o, HonestTerms (D o))
    (tP q : ℕ) (epsS : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt ((D OnBytes.secondHashFunction).withTerms (Q OnBytes.secondHashFunction)) epsS)
    (h : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindLaws (Q OnBytes.secondHashFunction) Z (settingsOfRead pp) tP q) :
    NearestSoundAndBinding (fun o => (D o).withTerms (Q o))
      (joinError epsS fun t => epsBind honestBudget (t + q)) :=
  nearestSoundAndBinding_of_at (fun o => (D o).withTerms (Q o)) epsS _ sound
    (bindsAt_withTerms (Q OnBytes.secondHashFunction) tP q h)

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.input_withTerms
#print axioms VerifierAndGoals.Fit.verify_withTerms
#print axioms VerifierAndGoals.Fit.commitWithin_withTerms
#print axioms VerifierAndGoals.Fit.bindsAt_withTerms
#print axioms VerifierAndGoals.Fit.G9_withTerms
#print axioms VerifierAndGoals.Fit.nearestSoundAndBinding_withTerms
