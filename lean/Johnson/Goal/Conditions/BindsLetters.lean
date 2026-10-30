-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsLetters.lean: BINDING OVER THE TOLD RECORD OF THE FULL-SIZE FRAME, ALL
ITS PARTS LETTERS: the request's item and the parameter bytes among them: so neither the statement
nor its proof names a hash function. Statements and proofs.

Why. The closed terms of which binding of the commitment in the opening form was stated
(Johnson/Goal/Conditions/BindsPlain.lean: the written committer
(written in Lean beside the IOP: a placeholder that corresponds to no program of the release),
the extractor, `plainSystem`) reach concrete hash functions by name: through the
told record's public reading (`pub8`), its coding (`mD`, which made the request's item inside) and
the lay's plan. A rule laid on this library, no theorem: the verifier and the proofs that go with it
are always to treat the hash function as a random oracle. The law of binding (`told_binds_written`,
Johnson/Goal/Conditions/BindsLaw.lean) names none. Here it is applied at the told record `toldDBy`
(Johnson/Flat/Told/Dec/TAtBy.lean) with `it` and `par` as letters.

Main names (namespace `LPFD.Full`).
  `depthD`, `wireKD`: the tree's depth is `frS.P.T.a`, the wire's K is `KF DK DP + 1`: by
    definition. `wireD`: the wire is in order, from six tests on numbers. `countD`: the told
    committer's count is within the honest side's budget, where KF DK DP + 2 < 2^40.
  **`bindsD`**: for all letters A E G DK DP runK runP dec P h₀ it pol KL lay par sR … N d₀ e: where
    par gives at most seven members (hpar), seven tests on numbers hold (hk hEnt wK dK wP dP hK40),
    and `new` is any argument system whose committer has, at every hash function, the value of
    `(toldDBy … e).commitAtCoins b (back w) (rOf x) (σOf x)` (written), the salts of one length at
    the tree's places (fence), φ gives w back from `back w` (hφ) and the decoder gives back the
    index of every w (hdec): `BindsWith new ((toldDBy … e).extractorOn φ) (epsBind honestBudget)`.

Every "there is": none, in premises or conclusion.
Limits. (1) A LAW FOR ALL LETTERS: A TOOL: no row is paid by it until it is applied at the letters
of the named description. That its twelve premises can be met together is shown where it is applied:
Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean. (2) That neither the statement nor its proof names a hash
function is a walk's word (over the environment, from `bindsD`, through types, values and proofs: a
scratch sheet's print), no theorem's. (3) Those of BindsLaw.lean: the fence; the verifier is idle;
values, not algorithms. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Told.Dec.TAtBy
import Johnson.Flat.Dec.EntrySound
import Johnson.Goal.Conditions.BindsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open OnBytes.K.Arm.Pub
open PV.EntryFive (dsF xsF)
open VerifierAndGoals VerifierAndGoals.Fit

variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull)
  (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (P : (FsAtR A E G DK DP runK runP dec).Provers)
  (h₀ : HId) (it : XF → ByteArray) (pol KL lay : ByteArray)
  (par : ByteArray → List ByteArray) (sR : ℕ) (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true)
  (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
  (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
    (saltG G) P) (d₀ : Dig 256)

/-- The tree's depth at the family's member: by definition. -/
theorem depthD (e : D8) :
    (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).queryLayout.depth =
      frS.P.T.a := rfl

/-- The wire's K there: by definition. -/
theorem wireKD (e : D8) :
    (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).queryLayout.K = KF DK DP +
      1 := rfl

/-- «wire». -/
theorem wireD (e : D8) (hk : kThree .two DK [] DP ≤ KF DK DP) (hEnt : EntryFit (KF DK DP) dsF)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) :
    (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).queryLayout.OKG :=
  (wiresOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP dsF xsF dec _ _ _ _ _ P (KF DK DP)
    (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e).depthReqT hk hEnt.bL hEnt.wLk
      hEnt.own
    hEnt.dL wK dK wP dP).1

/-- The one test on numbers: the written committer's count is within the honest side's budget. -/
theorem countD (e : D8) (hK40 : KF DK DP + 1 + 1 < 2 ^ 40) :
    8 + (2 * 2 ^ (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                   e)).queryLayout.depth +
      2 * ((innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                     e)).queryLayout.K + 1)) + 1 ≤
        honestBudget := by
  have ha : frS.P.T.a = 32 := by decide
  rw [depthD, wireKD, ha]
  show _ ≤ 2 ^ 48
  have h1 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h2 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have h3 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
  rw [h1, h3]
  rw [h2] at hK40
  omega

/-- **BINDING OVER THE TOLD RECORD OF THE FRAME, ALL ITS PARTS LETTERS**: the request's item `it`
  and
the parameter bytes `par` among them: so no hash function is named. -/
theorem bindsD (e : D8) (hpar : ∀ c, (par c).length ≤ 7)
    (hk : kThree .two DK [] DP ≤ KF DK DP) (hEnt : EntryFit (KF DK DP) dsF)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (hK40 : KF DK DP + 1 + 1 < 2 ^ 40) (new : ArgumentSystem)
    (back : new.Weights → (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                   e)).Index)
    (φ : (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).Index → Option
      new.Weights)
    (b : (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).LeafBody)
    (rOf : new.CommitmentRandomness →
      (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).protocol.EncodingRandomness)
    (σOf : new.CommitmentRandomness → ℕ → Bits)
    (written : ∀ w x hash, (new.commit w x).evaluate hash =
      ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀
        e).commitAtCoins b
        (back w) (rOf x) (σOf x)).evaluate hash)
    (len : ℕ)
    (fence : ∀ x k, k < 2 ^ (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                   d₀ e)).queryLayout.depth →
      (σOf x k).length = len)
    (hφ : ∀ w, φ (back w) = some w)
    (hdec : ∀ w r s, (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                   e)).protocol.decodeIndex
      ((innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).protocol.encodeIndex (back w)
        r)
      ((innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).protocol.recOf (back
                            w) r s) =
        some (back w)) :
    BindsWith new
      ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀
        e).extractorOn φ)
      (epsBind honestBudget) :=
  told_binds_written (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    new
    back φ b rOf σOf written len fence
    (wireD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e hk hEnt wK dK wP dP) hφ hdec
    (noCoinDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (asksDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (onceDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (spareDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (wordDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (codeDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e)
    (totalDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e) 8
    (famBy_reading (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) par 7
      hpar)
    honestBudget
    (le_trans (Nat.le_succ _) (countD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e hK40))

end LPFD.Full

#print axioms LPFD.Full.depthD
#print axioms LPFD.Full.wireKD
#print axioms LPFD.Full.wireD
#print axioms LPFD.Full.countD
#print axioms LPFD.Full.bindsD
