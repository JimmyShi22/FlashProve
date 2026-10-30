-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/FitBinds.lean: the goal on binding, G9 (Ladder.lean), follows from named laws on
the
committer of a told record (Johnson/Top/InnerCompiledVerifierByPublicReading.lean); and with the fit for G8
(Johnson/PV/FitO.lean) so does `SoundAndBinding` of `D`'s own verifier, in its nearest form
(Ladder/Package.lean), AT A WRITTEN ERROR. Conditionals: no `D`, no told record, no encoder and no
committer is built here.

What this file states.
  `BindsWith.ofCommit`: general in the two systems: binding passes to any system whose honest
    committer has, at every hash function, the value of the old one at (back weights, what an
    algorithm `coins` makes of the randomness THERE), along a map φ of weights into Option with
    φ (back weights) = some weights. The extractor is the old one, then φ, by bind. `coins` may ask
    the hash function, at most q times: the bound is the old one at t + q.
  `BindAt D Z s`: ALL THAT BINDING ASKS AT ONE Z. Data: c₀ m₀ T φ back coins qCoins ri sl b₀ isk tS.
    Laws: the told law's six (noCoin asks once spare word code) · wire (the first of the wire's
    laws) · section · behind · coinsWithin · commits · decodes · coded · within. NO HYPOTHESIS ON
    SOUNDNESS IS AMONG THEM.
  `bindsWith_record_of_bindAt`: G9's body at one Z.
  `epsBind tMax t` := 3 (t + 2 tMax + 2)² / 2^256; `epsOpensTold_le`, `epsBind_mono`,
    `epsBind_le_ceiling`.
  **`bindsAt_of_bindAt`**: the term `BindsAt D fun t => epsBind tMax (t + qMax)`: THE ERROR IS KEPT.
  **`G9_of_bindAt`**: the term `G9 D`, where 2 tMax + qMax ≤ 2^65. No error is left as a letter.
  `CommitsAt A`, `CommitsAt.toBindAt`: the same laws over a record `ToldAtO` of the fit for G8,
  from
    which the told law's six and the wire's law are read.
  **`nearestSoundAndBinding_of_toldO`**: from the conditions of `soundUnderPolicyAt_of_toldO` and a
    `CommitsAt` over the same family A, SO AT ONE EXTRACTOR: `NearestSoundAndBinding D (joinError
    epsS
    fun t => epsBind tMax (t + qMax))`: THE ERROR IS KEPT.

The bound, written out. `epsOpensTold tS tC tO` (Johnson/Top/OpensTold.lean) is
2 (tC + tO + 2 tS + 1)² / 2^256 + (tC + tO + tS + 2)² / 2^256: the committer's count stands twice in
the first term (once for the run again, once for the step behind the hash of the key's code).
`epsBind` bounds it.

The conditions of `G9_of_bindAt`, each a named hypothesis: B (a `BindAt` at every Z in scope) ·
commitWithin (the goal's own first conjunct, restated: the fit shows nothing of it) · hext (`D`'s
extractor is B's) · count (tS ≤ tMax, qCoins ≤ qMax) · hMax.

What each law of `BindAt` is worth.
- behind is an equation that fixes the told record's free field `commit`: whoever writes T can meet
  it: a definition in a law's place. It says nothing of a program.
- commits ties `D`'s committer to that one IN VALUE, at every hash function. A committer that
derives
  its pads and salts from a secret seed and answers of the hash function can meet it only with those
  derivations in `coins`. That a generator's values are the numbers that `committerOverTypedOracles` reads is part
  of
  commits.
- decodes is the heart: the decoder gives back the index of every set of weights from its honest
  encoding and record, at every seed. It is asked at the indices back w alone. IT IS FALSE AT EVERY
  ENCODER THAT IGNORES THE INDEX WHERE THE RECORD'S ANSWERS IGNORE IT TOO. This file writes
  no encoder. A written one is `codingHonest` (OnBytes/Flat/CodingHonest.lean): under their
  premises, `obj_decodes_full` and `obj_decodes_small` state the decoder's law at the two sizes.
- within and commitWithin are two counts of one committer, tied by nothing: commits speaks of
values.

What it does not show. That the conditions can be met together at any Z. Binding does not read the
verifier. The public files are fixed before the hash function is drawn.

-/
import Johnson.PV.FitO
import Johnson.Top.OpensTold
import Rom.OneOfCount
import Ladder.PackageTies
import VerifiableInference.OfArgumentBinds

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
open MeasureTheory

/-! ## 1. Binding passes along the committer -/

/-- **Binding passes along the committer.** Let the commitment of `old` bind to the extractor's
weights. Let `new` be any system whose honest committer, at every hash function, has the value of
`old`'s at back weights and at what `coins` makes of the randomness at that hash function; let
`coins`
ask at most q queries, and let φ (back weights) = some weights. Then the commitment of `new` binds
to
what φ makes of the old extractor's weights, with the old bound at q queries more. -/
theorem BindsWith.ofCommit (old new : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option old.Weights) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith old extractor ε)
    (φ : old.Weights → Option new.Weights) (back : new.Weights → old.Weights)
    (coins : new.CommitmentRandomness → DeterministicAlgorithm old.CommitmentRandomness) (q : ℕ)
    (hq : ∀ randomness, (coins randomness).toRandomized.QueryBound q)
    (hBack : ∀ weights, φ (back weights) = some weights)
    (hCommit : ∀ weights randomness hash, (new.commit weights randomness).evaluate hash =
      (old.commit (back weights) ((coins randomness).evaluate hash)).evaluate hash) :
    BindsWith new (fun commitment queryLog => (extractor commitment queryLog).bind φ)
      fun t => ε (t + q) := by
  intro committerQueries proverQueries State committer committerBound opener openerBound
  have key := binds committerQueries (proverQueries + q) State committer committerBound
    (fun state => (opener state).bind fun y =>
      (coins y.2).toRandomized.bind fun r => RandomizedAlgorithm.done (back y.1, r))
    (fun state => queryBound_then _ _ proverQueries q (openerBound state) fun y => by
      have h := queryBound_then (coins y.2).toRandomized
        (fun r => RandomizedAlgorithm.done (back y.1, r)) q 0 (hq y.2) fun _ => trivial
      simpa using h)
  rw [← Nat.add_assoc] at key
  refine le_trans ?_ key
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (opener c.1.2).bind fun y =>
        (new.commit y.1 y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done
            ((extractor c.1.1 c.2).bind φ, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        ((opener c.1.2).bind fun y => (coins y.2).toRandomized.bind fun r =>
          RandomizedAlgorithm.done (back y.1, r)).bind fun z =>
          (old.commit z.1 z.2).toRandomized.bind fun recomputed =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, z.1, recomputed)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, run_bind, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
  rw [ZKCP.prob_pure, ZKCP.prob_pure, hCommit]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  refine ⟨h1, fun he => h2 ?_⟩
  have he' : extractor c.1.1 c.2 = some (back y.1) := he
  show (extractor c.1.1 c.2).bind φ = some y.1
  rw [he']
  exact hBack y.1

/-! ## 2. What binding asks at one Z -/

/-- All that binding asks at one Z: data, the told law's six, the first of the wire's laws, and the
laws on the committer. No hypothesis on soundness is among them. -/
structure BindAt (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings) where
  c₀ : Digest
  m₀ : D.More
  T : LayoutsByPublicReading (D.input Z c₀ m₀)
  /-- from the extractor's index to weights; it may say none -/
  φ : (D.input Z c₀ m₀).Index → Option (ModelWeights s)
  /-- the index of given weights -/
  back : ModelWeights s → (D.input Z c₀ m₀).Index
  /-- the told committer's number, from `D`'s randomness; it may ask the hash function -/
  coins : D.Rand → DeterministicAlgorithm (Fin ((D.input Z c₀ m₀).coinBound + 1))
  /-- a bound on the queries of `coins` -/
  qCoins : ℕ
  ri : Iop.Enum (D.input Z c₀ m₀).protocol.EncodingRandomness
  sl : Iop.Enum (ℕ → Rom.Bits)
  b₀ : (D.input Z c₀ m₀).LeafBody
  isk : T.D → (D.input Z c₀ m₀).Index × (D.input Z c₀ m₀).protocol.EncodingRandomness × (ℕ → Rom.Bits) → T.ISK
  /-- a bound on the whole told committer's queries -/
  tS : ℕ
  noCoin : T.Pub.NoCoin
  asks : T.Pub.AsksIn fun _ s => T.Pt s
  once : NoRepeat T.Pub
  spare : ∀ d s, T.Pt s → IsOther (T.m d) s
  word : ∀ d d', T.part d = T.part d' →
    (extractorOverOneHashFunction (T.m d) (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei =
      (extractorOverOneHashFunction (T.m d') (indexExtractorAtRootAndOutOfDomainSample (D.input Z c₀ m₀).queryLayout)).Ei
  code : ZKCP.CodeIsOneToOne T.encT
  wire : (D.input Z c₀ m₀).queryLayout.OKG
  section_ : ∀ w, φ (back w) = some w
  behind : CommitsBehind T ri sl b₀ isk
  coinsWithin : ∀ ρ, (coins ρ).toRandomized.QueryBound qCoins
  commits : ∀ w ρ hash, (D.commit Z s w ρ).evaluate hash =
    ((T.systemOn back (modelNextToken s)).commit w ((coins ρ).evaluate hash)).evaluate hash
  decodes : ∀ w r sd, (D.input Z c₀ m₀).protocol.decodeIndex ((D.input Z c₀ m₀).protocol.encodeIndex (back w) r)
    ((D.input Z c₀ m₀).protocol.recOf (back w) r sd) = some (back w)
  coded : (ZKCP.SpecialAny.oneOf (T.schemeOn back)).KeysHaveCodes T.encT
  within : ∀ w, (T.commit (back w)).QueryBound tS

/-- The extractor to which the commitment binds. -/
def BindAt.extractor {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    (B : BindAt D Z s) : Commitment → QueryLog → Option (ModelWeights s) :=
  fun commitment queryLog => (B.T.extractor commitment queryLog).bind B.φ

/-- **G9's body at one Z.** -/
theorem bindsWith_record_of_bindAt {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    (B : BindAt D Z s) (eps : ℕ → ℝ≥0∞)
    (bound : ∀ tC tO, epsOpensTold B.tS tC tO ≤ eps (tC + tO)) :
    BindsWith (systemOfRecord D Z s) B.extractor fun t => eps (t + B.qCoins) := by
  have h1 := told_bindsWith_on (T := B.T) B.wire B.back B.φ B.section_
    B.decodes B.behind B.noCoin B.asks B.once B.spare B.word B.code B.coded B.tS B.within
    (fun w => Rom.queryBound_oneOf_C _ w (B.within w)) (modelNextToken s) eps bound
  have h2 := BindsWith.ofCommit (B.T.systemOn B.back (modelNextToken s)) (systemOfRecord D Z s) _
    eps h1 some id B.coins B.qCoins B.coinsWithin (fun _ => rfl) B.commits
  have e : (fun commitment queryLog =>
      ((B.T.extractor commitment queryLog).bind B.φ).bind some) = B.extractor := by
    funext commitment queryLog
    show ((B.T.extractor commitment queryLog).bind B.φ).bind some =
      (B.T.extractor commitment queryLog).bind B.φ
    cases (B.T.extractor commitment queryLog).bind B.φ <;> rfl
  exact e ▸ h2

/-! ## 3. The error written out -/

/-- The error of binding, in t, the sum of the bounds on the committer's and the opener's queries;
tMax bounds the honest committer's own queries. -/
def epsBind (tMax : ℕ) (t : ℕ) : ℝ≥0∞ := ((3 * (t + 2 * tMax + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `epsOpensTold` is at most `epsBind`. -/
theorem epsOpensTold_le (tS tMax : ℕ) (h : tS ≤ tMax) (tC tO : ℕ) :
    epsOpensTold tS tC tO ≤ epsBind tMax (tC + tO) := by
  unfold epsOpensTold epsOpens epsBind
  have e : (2 : ℝ≥0∞) * ((tC + (tO + tS + tS) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
      (((tC + (tO + tS) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      ((2 * (tC + (tO + tS + tS) + 1) ^ 2 + (tC + (tO + tS) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← ENNReal.add_div]
    push_cast
    rfl
  refine le_trans (le_of_eq e) (ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _)
  have h1 : tC + (tO + tS + tS) + 1 ≤ tC + tO + 2 * tMax + 2 := by omega
  have h2 : tC + (tO + tS) + 2 ≤ tC + tO + 2 * tMax + 2 := by omega
  have h3 := Nat.pow_le_pow_left h1 2
  have h4 := Nat.pow_le_pow_left h2 2
  omega

/-- `epsBind` grows with t. -/
theorem epsBind_mono (tMax : ℕ) {t t' : ℕ} (h : t ≤ t') : epsBind tMax t ≤ epsBind tMax t' :=
  ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.mul_le_mul_left 3
    (Nat.pow_le_pow_left (by omega) 2))) _

/-- Where 2 tMax + qMax ≤ 2^65, `epsBind` at t + qMax is under the ceiling up to the budget of
queries. -/
theorem epsBind_le_ceiling (tMax qMax : ℕ) (h : 2 * tMax + qMax ≤ 2 ^ 65) (t : ℕ)
    (ht : t ≤ queryBudget) : epsBind tMax (t + qMax) ≤ ceiling := by
  unfold epsBind ceiling
  have ht' : t ≤ 2 ^ 64 := ht
  have h1 : t + qMax + 2 * tMax + 2 ≤ 2 ^ 66 := by
    have e1 : (2 : ℕ) ^ 66 = 4 * 2 ^ 64 := by norm_num
    have e2 : (2 : ℕ) ^ 65 = 2 * 2 ^ 64 := by norm_num
    have e3 : 2 ≤ (2 : ℕ) ^ 64 := by norm_num
    omega
  have h2 : 3 * (t + qMax + 2 * tMax + 2) ^ 2 ≤ 2 ^ 254 :=
    le_trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h1 2)) (by norm_num)
  calc ((3 * (t + qMax + 2 * tMax + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
      ≤ ((2 ^ 254 : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (Nat.cast_le.2 h2) _
    _ = 4⁻¹ := by
      rw [show (2 : ℝ≥0∞) ^ 256 = ((2 ^ 254 : ℕ) : ℝ≥0∞) * 4 by push_cast; norm_num,
        ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_assoc,
        mul_comm (4 : ℝ≥0∞)⁻¹, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-! ## 4. The stored terms -/

/-- **The stored `BindsAt`, THE ERROR KEPT**: from a `BindAt` at every Z in scope, with one bound
tMax
on the told committers' queries and one bound qMax on those of `coins`. -/
theorem bindsAt_of_bindAt (D : Description) (tMax qMax : ℕ)
    (B : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindAt D Z (settingsOfRead pp))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, (D.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (hext : ∀ Z pp h₁ h₂, D.extractor Z (settingsOfRead pp) = (B Z pp h₁ h₂).extractor)
    (count : ∀ Z pp h₁ h₂, (B Z pp h₁ h₂).tS ≤ tMax ∧ (B Z pp h₁ h₂).qCoins ≤ qMax) :
    BindsAt D fun t => epsBind tMax (t + qMax) :=
  fun Z pp h₁ h₂ => ⟨commitWithin Z pp h₁ h₂, by
    rw [hext Z pp h₁ h₂]
    exact BindsWith.mono (bindsWith_record_of_bindAt (B Z pp h₁ h₂) (epsBind tMax)
      fun tC tO => epsOpensTold_le _ tMax (count Z pp h₁ h₂).1 tC tO)
      fun t => epsBind_mono tMax (Nat.add_le_add_left (count Z pp h₁ h₂).2 t)⟩

/-- **THE STORED G9, NO ERROR LEFT AS A LETTER.** -/
theorem G9_of_bindAt (D : SecondHashFunctionType → Description) (tMax qMax : ℕ) (hMax : 2 * tMax + qMax ≤ 2 ^ 65)
    (B : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindAt (atSecondHashFunction D) Z (settingsOfRead pp))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, ((atSecondHashFunction D).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (hext : ∀ Z pp h₁ h₂, (atSecondHashFunction D).extractor Z (settingsOfRead pp) = (B Z pp h₁ h₂).extractor)
    (count : ∀ Z pp h₁ h₂, (B Z pp h₁ h₂).tS ≤ tMax ∧ (B Z pp h₁ h₂).qCoins ≤ qMax) : G9 D :=
  ⟨fun t => epsBind tMax (t + qMax), epsBind_le_ceiling tMax qMax hMax,
    bindsAt_of_bindAt (atSecondHashFunction D) tMax qMax B commitWithin hext count⟩

/-! ## 5. Beside the fit for G8, at one extractor -/

/-- What binding takes as hypotheses over a record of the fit for G8: data, then laws on the
committer. The told law's six and the wire's law are read off A. -/
structure CommitsAt {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (A : ToldAtO D Z s newClaim) where
  back : ModelWeights s → (D.input Z A.c₀ A.m₀).Index
  coins : D.Rand → DeterministicAlgorithm (Fin ((D.input Z A.c₀ A.m₀).coinBound + 1))
  qCoins : ℕ
  ri : Iop.Enum (D.input Z A.c₀ A.m₀).protocol.EncodingRandomness
  sl : Iop.Enum (ℕ → Rom.Bits)
  b₀ : (D.input Z A.c₀ A.m₀).LeafBody
  isk : A.T.D → (D.input Z A.c₀ A.m₀).Index × (D.input Z A.c₀ A.m₀).protocol.EncodingRandomness × (ℕ → Rom.Bits) → A.T.ISK
  tS : ℕ
  section_ : ∀ w, A.φ (back w) = some w
  behind : CommitsBehind A.T ri sl b₀ isk
  coinsWithin : ∀ ρ, (coins ρ).toRandomized.QueryBound qCoins
  commits : ∀ w ρ hash, (D.commit Z s w ρ).evaluate hash =
    ((A.T.systemOn back (modelNextToken s)).commit w ((coins ρ).evaluate hash)).evaluate hash
  decodes : ∀ w r sd, (D.input Z A.c₀ A.m₀).protocol.decodeIndex ((D.input Z A.c₀ A.m₀).protocol.encodeIndex (back w) r)
    ((D.input Z A.c₀ A.m₀).protocol.recOf (back w) r sd) = some (back w)
  coded : (ZKCP.SpecialAny.oneOf (A.T.schemeOn back)).KeysHaveCodes A.T.encT
  within : ∀ w, (A.T.commit (back w)).QueryBound tS

/-- As a `BindAt`: its extractor is A's. -/
def CommitsAt.toBindAt {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} {A : ToldAtO D Z s newClaim}
    (Q : CommitsAt A) : BindAt D Z s where
  c₀ := A.c₀
  m₀ := A.m₀
  T := A.T
  φ := A.φ
  back := Q.back
  coins := Q.coins
  qCoins := Q.qCoins
  ri := Q.ri
  sl := Q.sl
  b₀ := Q.b₀
  isk := Q.isk
  tS := Q.tS
  noCoin := A.noCoin
  asks := A.asks
  once := A.once
  spare := A.spare
  word := A.word
  code := A.code
  wire := (A.core (A.pair A.c₀ A.m₀)).wires.1
  section_ := Q.section_
  behind := Q.behind
  coinsWithin := Q.coinsWithin
  commits := Q.commits
  decodes := Q.decodes
  coded := Q.coded
  within := Q.within

/-- **`SoundAndBinding` of `D`'s own verifier, in its nearest form, under named conditions, THE
ERROR
KEPT**: the conditions of `soundUnderPolicyAt_of_toldO` (Johnson/PV/FitO.lean) and a `CommitsAt`
over
the same family A: so at one extractor. -/
theorem nearestSoundAndBinding_of_toldO (D : SecondHashFunctionType → Description) (epsS : ℕ → ℕ → ℝ≥0∞)
    (tMax qMax : ℕ)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO (atSecondHashFunction D) Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (Q : ∀ Z pp h₁ h₂, CommitsAt (A Z pp h₁ h₂))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((atSecondHashFunction D).parse Z) honestBudget)
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, ((atSecondHashFunction D).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (hext : ∀ Z pp h₁ h₂, (atSecondHashFunction D).extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (boundS : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ epsS t n)
    (count : ∀ Z pp h₁ h₂, (Q Z pp h₁ h₂).tS ≤ tMax ∧ (Q Z pp h₁ h₂).qCoins ≤ qMax) :
    NearestSoundAndBinding D (joinError epsS fun t => epsBind tMax (t + qMax)) :=
  nearestSoundAndBinding_of_at D epsS _
    (soundUnderPolicyAt_of_toldO (atSecondHashFunction D) epsS A ownParser hext boundS)
    (bindsAt_of_bindAt (atSecondHashFunction D) tMax qMax (fun Z pp h₁ h₂ => (Q Z pp h₁ h₂).toBindAt)
      commitWithin hext count)

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.BindsWith.ofCommit
#print axioms VerifierAndGoals.Fit.bindsWith_record_of_bindAt
#print axioms VerifierAndGoals.Fit.epsOpensTold_le
#print axioms VerifierAndGoals.Fit.epsBind_mono
#print axioms VerifierAndGoals.Fit.epsBind_le_ceiling
#print axioms VerifierAndGoals.Fit.bindsAt_of_bindAt
#print axioms VerifierAndGoals.Fit.G9_of_bindAt
#print axioms VerifierAndGoals.Fit.nearestSoundAndBinding_of_toldO
