-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WiderValue.lean: THE VALUE OF THE HOME's COMMITMENT AT A HASH FUNCTION, DOWN
TO committerAtFixedCoins's OWN KEY: at the member of theWider whose number names the salts that bear c
(Johnson/Goal/Conditions/WiderSalts.lean): the hash function's answer at the told code of the key
(the told part of the public reading d, the root with the honest record that committerAtFixedCoins gives under the
typed oracles that are read out of the hash function through the coding at d).

Why. The law of the compiled provers' outcome speaks of committerAtFixedCoins under typed oracle functions g. The
goals' experiment runs the description's committer under one hash function. This is the tie, at
every hash function and all randomness: no probability.

Main names.
  det_keyAtCoins   the value of LayoutsByPublicReading.keyAtCoins (Johnson/Top/ToldCommitPlain.lean) under a hash
    function: general in the told record.
  fixedCommit_value   the committer with the coins fixed
    (Johnson/Goal/Conditions/CoinsEnumerated.lean): general in the honest side's terms, under the
    laws that binding owes.
  commit_value   THE STATEMENT, at letters (K, ra, sb, idx).

It adds no strength. Calls: commit_systemOn_plain, evaluate_commitAtCoins (ToldCommitPlain.lean);
det_overOne (Run/DetOverOne.lean); commit_named_at (WiderSalts.lean).

Limits. "The answer at the told code" is ZKCP.digestUnder: the digest of zeros where a key has no
code; at this told record every key has one (BindLaws.total), which is not called here. Values, not
algorithms: nothing on a count or a log. No probability, no completeness. WiderSalts.lean's limits
travel whole.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderSalts
import Johnson.Top.ToldCommitPlain
import Run.DetOverOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b₀ : R.LeafBody)

/-- **The key at given coins, under a hash function**: d the public reading's value; the told part
of d; the first part of committerAtFixedCoins's value under the typed oracles read out through the coding at
d. -/
theorem det_keyAtCoins (g : Fam (rom 256)) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    (T.keyAtCoins b₀ i r σ).det g =
      (T.part (T.Pub.det g),
        ((committerAtFixedCoins R.queryLayout (T.Sd (T.Pub.det g)) b₀ i r σ).det
          (readBlocks (T.m (T.Pub.det g)) g)).1) := by
  unfold LayoutsByPublicReading.keyAtCoins
  rw [Rom.OComp.det_bind, Rom.OComp.det_bind, Rom.det_overOne]
  rfl

end VerifiableInference.OnPublicFiles

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat Rom
open TypedOracleCompiler.Compile.Batch.Cms (committerAtFixedCoins)

variable {D : Description} {Q : HonestTerms D}

/-- **The committer with the coins fixed: its value at a hash function.** -/
theorem fixedCommit_value {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) (hash : Hash) :
    (fixedCommit Q Z s w r σ).evaluate hash =
      ZKCP.digestUnder hash (Q.T Z).encT
        ((Q.T Z).part ((Q.T Z).Pub.det (_root_.Run.famOne hash)),
          ((committerAtFixedCoins (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout
            ((Q.T Z).Sd ((Q.T Z).Pub.det (_root_.Run.famOne hash))) (Q.b₀ Z) (Q.back Z s w) r σ).det
            (readBlocks ((Q.T Z).m ((Q.T Z).Pub.det (_root_.Run.famOne hash)))
              (_root_.Run.famOne hash))).1) := by
  unfold fixedCommit
  rw [commit_systemOn_plain (Q.T Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s) (modelNextToken s) h.noCoin w
    r σ, evaluate_commitAtCoins, det_keyAtCoins]

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open TypedOracleCompiler.Compile.Batch.Cms (committerAtFixedCoins)

/- Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

variable (K : TheCoins) (ra : (Z : PublicFiles) → K.Rand → Fin ((K.ri Z).n + 1))
  (sb : K.Rand → ℕ → ByteArray) (idx : (Z : PublicFiles) → (ℕ → Rom.Bits) → Fin ((K.sl Z).n + 1))

/-- The honest side's terms at the member whose number names the salts that bear c. -/
abbrev namedTerms : HonestTerms (flashProveDescription.reBound (WiderCoins.named K ra sb idx).bound) :=
  theWiderTerms K (WiderCoins.named K ra sb idx)

/-- **THE HOME's COMMITMENT AT ρ UNDER A HASH FUNCTION.** -/
theorem commit_value (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) (hash : Hash)
    (hidx : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth →
      (K.sl Z).e (idx Z (saltsAt (hash (configString Z)) (sb ρ))) j =
        saltsAt (hash (configString Z)) (sb ρ) j) :
    ((theWider K (WiderCoins.named K ra sb idx) o).commit Z (settingsOfRead pp) w ρ).evaluate
        hash =
      ZKCP.digestUnder hash ((namedTerms K ra sb idx).T Z).encT
        (((namedTerms K ra sb idx).T Z).part
            (((namedTerms K ra sb idx).T Z).Pub.det (_root_.Run.famOne hash)),
          ((committerAtFixedCoins _ (((namedTerms K ra sb idx).T Z).Sd
                            (((namedTerms K ra sb idx).T Z).Pub.det (_root_.Run.famOne hash)))
            ((namedTerms K ra sb idx).b₀ Z) ((namedTerms K ra sb idx).back Z (settingsOfRead pp) w)
            (((namedTerms K ra sb idx).ri Z).e (ra Z ρ))
            (saltsAt (hash (configString Z)) (sb ρ))).det
            (readBlocks (((namedTerms K ra sb idx).T Z).m
              (((namedTerms K ra sb idx).T Z).Pub.det (_root_.Run.famOne hash)))
              (_root_.Run.famOne hash))).1) :=
  (commit_named_at K ra sb idx o Z pp hr w ρ hash hidx).trans
    (fixedCommit_value (bindLaws_wider K (WiderCoins.named K ra sb idx) Z pp hr) w _ _ hash)

end FlashProve

#print axioms VerifiableInference.OnPublicFiles.det_keyAtCoins
#print axioms VerifierAndGoals.Fit.fixedCommit_value
#print axioms FlashProve.commit_value
