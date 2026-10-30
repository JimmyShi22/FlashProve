-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WiderHome.lean: ONE WRITTEN VALUE OF THE HONEST SIDE's LETTERS, AND THE
MEMBER OF theWider (Johnson/Goal/Conditions/WiderAtThe.lean) AT IT: the sampler draws one number;
the prover draws one number and then runs a program without further draws over the hash function;
the committer's number names the pads that the randomness names and the salts that bear the
configuration's digest (Johnson/Goal/Conditions/WiderSalts.lean).

Why. The frame of completeness (completeOn_of_public, Johnson/Goal/Conditions/CompleteOfPublic.lean)
asks two equations of the honest side's form. Here is a K at which they hold by unfolding.

ARGUMENTS, not chosen here: Rand and ρOf (the type of the randomness; what the drawn number stands
for) · pf (the prover's program at each drawn number: strategies, caps and draws live in it) · ra,
sb (which pads, and which bytes for each leaf, the randomness names).

Main names.
  homeCoins Rand ρOf pf   THE VALUE: placeHolderCoins
    (Johnson/Goal/Conditions/PlaceHolderCoins.lean) with Rand, sample, gen and prove laid anew.
  theHome   the member: theWider at (homeCoins …).digits and named_digits.
  sample_home, prove_home   THE TWO EQUATIONS, at the goals' system: by unfolding.
  coins_field   the coins' algorithm of a member is coinsBoth at K.shape and W.gen.
  commit_value_digits   the value of the commitment at a hash function, down to committerAtFixedCoins's own key
    (commit_value, Johnson/Goal/Conditions/WiderValue.lean), at K.digits: so at theHome.

Limits. WiderAtThe.lean's limits travel whole. "gen := fun _ _ _ => 0" is the place-holder's field:
theTerms K lays it into its coins' algorithm; HonestTerms.reBound lays the coins' algorithm anew
(Johnson/Goal/Conditions/ReBound.lean), and at a member of theWider that one reads W.gen
(coins_field). ri and sl are K.digits'; b₀, proveT and shape are the place-holder's: shape is the
empty string, so the key's digest I is not the programs'. pf is a letter: no prover is written here.
No completeness. WRITTEN, NOT RUN.
This file states no goal. It defines theHome, in which theorems of other files conclude
(honestWithin_home_live, HonestAtLive.lean; honestWithin_theHome, HonestAtWider.lean), and
homeCoins, whose .digits are member's coins (homeK, HomeAtWider.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderValue
import Johnson.Goal.Conditions.PlaceHolderCoins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open TypedOracleCompiler.Compile.Batch.Cms (committerAtFixedCoins)

/-- **The written value of the honest side's letters**: placeHolderCoins
(Johnson/Goal/Conditions/PlaceHolderCoins.lean) with four fields laid anew: Rand, sample, prove, and
gen := fun _ _ _ => 0: a written 0. The five other fields (ri, sl, b₀, proveT, shape) are
placeHolderCoins' own. There ri and sl are lists of one: pads, tails and salts all 0; theHome and
homeK lay both anew by .digits. -/
def homeCoins {B N : ℕ} (Rand : Type) (ρOf : Fin (B + 1) → Rand)
    (pf : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
      List Token → Fin (N + 1) → Rom.OComp (rom 256) FormBytes) : TheCoins :=
  { placeHolderCoins with
    Rand := Rand
    sample := .sample B fun t => .done (ρOf t)
    gen := fun _ _ _ => 0
    prove := fun Z s w ρ p o => .sample N fun a =>
      (deterministicOf (ofRom (pf Z s w ρ p o a))).toRandomized }

/-- The coins' algorithm of a member reads W.gen. -/
theorem coins_field (K : TheCoins) (W : WiderCoins K) :
    (theWiderTerms K W).coins = fun Z => coinsBoth Z (K.shape Z) (W.gen Z) := rfl

section
/- Lean compares these by their names. -/
attribute [local irreducible] descriptionOfDataOnBytes riDigits fieldRows

/-- The honest side's terms at K.digits and the written number of the salts. -/
abbrev digitsTerms (K : TheCoins) (ra : (Z : PublicFiles) → K.digits.Rand → Fin ((K.digits.ri Z).n + 1))
    (sb : K.digits.Rand → ℕ → ByteArray) :=
  namedTerms K.digits ra sb fun Z σ => idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT σ

/-- **commit_value at K.digits**, the salts' number the written one: if ρ holds as many bytes for
each of the tree's leaves as the plan's salt has. -/
theorem commit_value_digits (K : TheCoins)
    (ra : (Z : PublicFiles) → K.digits.Rand → Fin ((K.digits.ri Z).n + 1))
    (sb : K.digits.Rand → ℕ → ByteArray) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : K.digits.Rand)
    (hash : Hash)
    (hs : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G) :
    ((theWider K.digits (named_digits K ra sb) o).commit Z (settingsOfRead pp) w ρ).evaluate
        hash =
      ZKCP.digestUnder hash ((digitsTerms K ra sb).T Z).encT
        (((digitsTerms K ra sb).T Z).part
            (((digitsTerms K ra sb).T Z).Pub.det (_root_.Run.famOne hash)),
          ((committerAtFixedCoins _ (((digitsTerms K ra sb).T Z).Sd
                            (((digitsTerms K ra sb).T Z).Pub.det (_root_.Run.famOne hash)))
            ((digitsTerms K ra sb).b₀ Z) ((digitsTerms K ra sb).back Z (settingsOfRead pp) w)
            (((digitsTerms K ra sb).ri Z).e (ra Z ρ))
            (saltsAt (hash (configString Z)) (sb ρ))).det
            (readBlocks (((digitsTerms K ra sb).T Z).m
              (((digitsTerms K ra sb).T Z).Pub.det (_root_.Run.famOne hash)))
              (_root_.Run.famOne hash))).1) :=
  commit_value K.digits ra sb (fun Z σ => idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT σ) o Z pp hr w ρ hash
    (e_idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt (hash (configString Z)) (sb ρ)) fun j hj =>
      (length_salt _ _ j _ (hs j hj)).trans (sMT_R₀ Z).symm)

end

variable {B N : ℕ} (Rand : Type) (ρOf : Fin (B + 1) → Rand)
  (pf : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → Fin (N + 1) → Rom.OComp (rom 256) FormBytes)
  (ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)) (sb : Rand → ℕ → ByteArray)

/-- **The member.** -/
def theHome : SecondHashFunctionType → Description :=
  theWider (homeCoins Rand ρOf pf).digits (named_digits (homeCoins Rand ρOf pf) ra sb)

/-- **The sampler's form.** -/
theorem sample_home (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (theHome Rand ρOf pf ra sb)) Z s).sampleCommitmentRandomness =
      .sample B fun t => .done (ρOf t) := rfl

/-- **The prover's form.** -/
theorem prove_home (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) :
    (systemOfRecord (atSecondHashFunction (theHome Rand ρOf pf ra sb)) Z s).prove w ρ p o =
      .sample N fun a => (deterministicOf (ofRom (pf Z s w ρ p o a))).toRandomized := rfl

end FlashProve

#print axioms FlashProve.homeCoins
#print axioms FlashProve.coins_field
#print axioms FlashProve.commit_value_digits
#print axioms FlashProve.sample_home
#print axioms FlashProve.prove_home
