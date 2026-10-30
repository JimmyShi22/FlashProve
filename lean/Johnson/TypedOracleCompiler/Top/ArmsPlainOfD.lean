-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/ArmsPlainOfD.lean: from the three arms' bounds with a public reading drawn in the
experiment (`CoreArmsCD`, Johnson/Top/OnFilesArmsCD.lean), whose extractor runs the reading and so
queries the hash function, to the three arms' bounds in the plain shape (`CoreArmsC`,
Johnson/Top/OnFilesArmsC.lean), whose extractor reads the key and the committer's log ALONE. At the
same three errors. Under two named hypotheses.

Why. The arms' codings hang on public digests d, which at a drawn hash function are answers that a
  committer need not have asked for. So the promises and the word under a root are read at d, and an
  extractor that needs d must run the public reading. A statement in the plain notion of soundness
  wants an extractor that asks nothing. The typed key holds a part c of d (the configuration's
  digest). Two facts let c serve for d: (W) the word under a root, read off a log of strings, hangs
  on d through its part c alone; (T) each arm refuses unless the part c of what the reading gives is
  the key's c.
The three promises and the extractor read d through the word ALONE (the texts of `KeyHoldsCD`,
`EntryHoldsCD`, `ProofHoldsCD`, `extArmsCD`). So (W) is one law on one function, for all three arms.

Two definitions, one structure; statements and proofs. The hash function is drawn, or a letter f, in
every statement.


Main names (namespace `ZKCP.Gen`, over any family of oracles S):
  `ArmBoundD.plain`: THE BRIDGE. v: an arm without coins; rd: a reading without coins. If, at every
    f, where the arm says yes, the promise read at the reading's value gives a promise Holds' that
    reads no d (hv), then a bound of v with the first promise is a bound of v with the second: the
    same ε. Pointwise in the oracles.
Main names (namespace `VerifiableInference.OnPublicFiles`); b' : `BesideArmsCD r`; part : what of d stands
in a key; wordC : a word read at c:
  `WordReadsPart b' part wordC`: (W): `b'.wordOf d tr cm = wordC (part d) tr cm`, at every d, log
    and root.
  `ArmsTestC b' part`: (T): three clauses, one an arm: at every f, key, instance and proof: where
    the arm says yes, the part of the reading's value is the key's c.
  `besidePlain b' wordC`: the `BesideArmsC r` with wordC for the word, b' 's relation, errors and
    x₀, and THE EXTRACTOR WRITTEN: decode, at the key's record, the word under the key's root, read
    at the key's c off the committer's log.
  `coreArmsC_of_CD`: `CoreArmsCD b'` → (W) → (T) → `CoreArmsC (besidePlain b' wordC)`.
    `noCoin_lifts`: no arm on a key and a proof draws a coin where no arm does.
  `soundFor_besidePlain`: the meaning carries over word for word.

Limits.
  * (T) IS A HYPOTHESIS, AND WE SEE NO WAY TO SPARE IT: THE ARMS MUST TEST c AGAINST THE HASH
    FUNCTION's OWN DIGEST OF THE PUBLIC FILES, SINCE THE PROVER NAMES c. A bound is said of each arm
    alone: an arm that does not test c can say yes at a key with a false c, where wordC c is another
    word: a false c is refused by (T) and by nothing else here. That is an argument, no theorem. (T)
    is shown of no arm here; it is for each arm's writer to pay.
  * (T) TIES EACH ARM TO `b'.rd`, THE READING OF THE BOUNDS: it is where "the arms draw the same d
    as the reading" is paid. An arm that runs another reading inside meets (T) only if the two give
    one part.
  * THE READING IS HANDED THE KEY. AT A READING THAT RETURNS THE KEY's OWN c (`rd k := pure k.1`,
    part the identity) (T) HOLDS OF EVERY ARM FOR NOTHING: the bounds behind that reading are then
    the plain bounds themselves, and nothing is gained. (T) has content only where `b'.rd` asks the
    hash function at the public strings and does not read c off the key. The bounds that are meant
    stand at fixed public files: the strings at which the reading asks are fixed before the hash
    function is drawn.
  * (W) IS A HYPOTHESIS HERE. Where the word is read through a family of codings, it follows from
    "two members with one part c write every leaf query and every node query alike"
    (`extEnc_codings`, Johnson/TypedOracleCompiler/RecCompile/WordCodings.lean); no family is given here, and (W) is
    laid at no b'.
  * `CoreArmsCD b'` IS A HYPOTHESIS: the three bounds are shown of no arms here. All three are read
    at ONE word b'.wordOf: an arm whose own coding is another must reach that word in its own bound.
  * ONE DIRECTION. Nothing is said of the commitment: the step from the key to the hash function's
    answer at the key's code stands elsewhere (OnFilesArmsCPlain.lean).
  * r, b', part and wordC are letters. All hold for nothing at arms that never say yes, or at errors
    of 1 or more.
  * All limits of the heads of Johnson/Top/OnFilesArmsCD.lean, Johnson/Top/OnFilesArmsC.lean and
    Johnson/Top/ArmsD.lean stand. Soundness alone. For proofs only; no program imports this file.
-/
import Johnson.Top.OnFilesArmsCD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X IVK Pf D : Type}

/-- **The bridge.** An arm without coins, a reading without coins. hv: at every f, where the arm
says yes, the promise read at the reading's value gives the promise that reads no d. Then a bound of
the arm with the first promise is a bound with the second, at the same ε. -/
theorem ArmBoundD.plain {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v : IVK → X → Pf → Rom.OComp S Bool} (hn : ∀ k x π, (v k x π).NoCoin)
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    {Holds' : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (hv : ∀ (f : Fam S) k x π, (v k x π).det f = true → ∀ trC trP,
      Holds ((rd k).det f) k trC x π trP → Holds' k trC x π trP)
    (h : ArmBoundD rd v Holds ε) : ArmBound v Holds' ε := by
  classical
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hp : ∀ (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
  have hr : ∀ k x π, (v k x π).runEager f = PMF.pure ((v k x π).det f) :=
    fun k x π => (hn k x π).runEager f
  simp only [Rom.PrCoins]
  rw [runEager_armExpD hrd]
  unfold armExp
  simp only [runEager_bindO, hp, hr, PMF.pure_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  rw [Prob.pr_pure, Prob.pr_pure]
  by_cases hb : (⟨(v o.1.1 o'.1.1 o'.1.2).det f, o.1.1, o.2, o'.1.1, o'.1.2, o'.2⟩ :
      ArmOut S X IVK Pf) ∈ armBad Holds'
  · rw [if_pos hb, if_pos]
    exact ⟨hb.1, fun hH => hb.2 (hv f _ _ _ hb.1 _ _ hH)⟩
  · rw [if_neg hb]
    exact zero_le _

end ZKCP.Gen

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC} (b' : BesideArmsCD r) (part : b'.D → r.C)
  (wordC : r.C → Rom.Trace (rom 256) → Dig 256 → Fin r.L.wordLength → r.L.Symbol)

/-- (W) The word under a root, read off a log of strings, hangs on what the public reading gives
through its part in the key alone. -/
def WordReadsPart : Prop := ∀ d tr cm, b'.wordOf d tr cm = wordC (part d) tr cm

/-- (T) Each arm tests c: at every f, where the arm says yes at a key, the part of what the public
reading gives there is the key's c. -/
structure ArmsTestC : Prop where
  key : ∀ (f : Fam (rom 256)) k x π, (liftKC r k x π).det f = true →
    part ((b'.rd k).det f) = k.1
  entry : ∀ (f : Fam (rom 256)) k x π, (liftEC r k x π).det f = true →
    part ((b'.rd k).det f) = k.1
  proof : ∀ (f : Fam (rom 256)) k x π, (liftPC r k x π).det f = true →
    part ((b'.rd k).det f) = k.1

/-- What only the theorems need, in the plain shape: the word read at c; the extractor written: it
decodes, at the key's record, the word under the key's root, read at the key's c off the committer's
log, and asks the hash function nothing. -/
def besidePlain : BesideArmsC r where
  wordOf := wordC
  Wn := b'.Wn
  Rno := b'.Rno
  E := ⟨fun k trC => r.L.decodeIndex (wordC k.1 trC k.2.cm) k.2.rcd, fun _ _ _ _ _ => ()⟩
  εK := b'.εK
  εE := b'.εE
  εP := b'.εP
  x₀ := b'.x₀

variable {b' part wordC}

/-- No lifted arm draws a coin where no arm does. -/
theorem noCoin_lifts (hn : HoleArmsC.noCoin r) :
    (∀ k x π, (liftKC r k x π).NoCoin) ∧ (∀ k x π, (liftEC r k x π).NoCoin) ∧
      ∀ k x π, (liftPC r k x π).NoCoin := by
  obtain ⟨a1, a2, a3⟩ := hn
  refine ⟨fun k x π => ?_, fun k x π => ?_, fun k x π => ?_⟩
  · unfold liftKC
    split
    · exact a1 _ _ _ _
    · trivial
  · unfold liftEC
    split
    · exact a2 _ _ _ _ _ _
    · trivial
  · unfold liftPC
    split
    · exact a3 _ _ _ _ _ _
    · trivial

/-- **From the bounds with the public reading drawn in the experiment to the bounds in the plain
shape**, at the same three errors: the extractor reads the key and the committer's log alone. hW:
the word hangs on d through its part in the key alone. hT: each arm tests c. -/
theorem coreArmsC_of_CD (h : CoreArmsCD b') (hW : WordReadsPart b' part wordC)
    (hT : ArmsTestC b' part) : CoreArmsC (besidePlain b' wordC) where
  keyArm := ZKCP.Gen.ArmBoundD.plain (fun k => (h.reading k).1) (noCoin_lifts h.noCoin).1
    (fun f k x π hy trC trP hH => by
      have e := hT.key f k x π hy
      have w : ∀ d tr cm, b'.wordOf d tr cm = wordC (part d) tr cm := hW
      unfold KeyHoldsCD at hH
      simp only [w, e] at hH
      exact hH) h.keyArm
  entryArm := ZKCP.Gen.ArmBoundD.plain (fun k => (h.reading k).1) (noCoin_lifts h.noCoin).2.1
    (fun f k x π hy trC trP hH => by
      have e := hT.entry f k x π hy
      have w : ∀ d tr cm, b'.wordOf d tr cm = wordC (part d) tr cm := hW
      unfold EntryHoldsCD at hH
      simp only [w, e] at hH
      exact hH) h.entryArm
  proofArm := ZKCP.Gen.ArmBoundD.plain (fun k => (h.reading k).1) (noCoin_lifts h.noCoin).2.2
    (fun f k x π hy trC trP hH => by
      have e := hT.proof f k x π hy
      have w : ∀ d tr cm, b'.wordOf d tr cm = wordC (part d) tr cm := hW
      unfold ProofHoldsCD at hH
      simp only [w, e] at hH
      exact hH) h.proofArm
  extractor := fun _ _ => rfl
  noCoin := h.noCoin

/-- The meaning carries over: the relation is the same. -/
theorem soundFor_besidePlain {claim : r.I → List Token → List Token → Prop}
    (hs : HoleArmsCD.soundFor b' claim) : HoleArmsC.soundFor (besidePlain b' wordC) claim :=
  hs

end VerifiableInference.OnPublicFiles

#print axioms ZKCP.Gen.ArmBoundD.plain
#print axioms VerifiableInference.OnPublicFiles.noCoin_lifts
#print axioms VerifiableInference.OnPublicFiles.coreArmsC_of_CD
#print axioms VerifiableInference.OnPublicFiles.soundFor_besidePlain
