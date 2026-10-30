-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescDecides.lean: the file's one verifier WITH A DESCRIPTION'S OWN DECISION
(`FileDescription.run`, Johnson/Desc/Block.lean) in it: what its yes gives. A SHEET OF STATEMENTS: three
propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. `FileDecides` (Johnson/Desc/Sound/FileRule.lean) speaks of the library's reduction
over all the file's rounds (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean) with THE THREE RUNS IN A ROW as
its decision. In the filling that is meant these runs read the instance's public part alone and
hold no last test: SO WHAT IS ASKED OF THE PROOF (the next token) STANDS ON NO TEST OF THAT
VERIFIER, and no premise that ties its yes to a relation on the asked token can be met there. The
verifier that runs has the description's own decision, which asks, beside the three runs, the tests
on the plan, the test on the instance, and THE LAST TEST, which compares what was heard with what is
asked.

What is said. `WholeMono`: the file's verifier is monotone in its decision and in its test on the
silent rounds, also from one instance to another. `DescDecides`: WHERE THE FILE'S VERIFIER WITH THE
DECISION `F.run` SAYS YES AT x, the three reductions in a row of the rule of composition put out AT
EVERY INSTANCE x' WITH THE SAME PUBLIC PART at which the silent rounds' test still says yes: the
premise `decides` of the top theorem for a proof file, with `F.run` in the verifier.
`WholeGivesEnds`: under the same yes there are three ends e₁, e₂, e₃, reached by the three folds ON
THE FILE'S OWN THREE VIEWS (`view₁`, `view₂`, `view₃`, OnBytes/Maker/WholeViews.lean), with all
that `RunEndIs` lists: the tests on the plan, THE TEST ON THE INSTANCE x ITSELF, and
`F.fin x e₁ e₂ e₃`: so a premise that ties the yes to a relation on the asked token has the last
test to read it through.

Limits. (1) General in the description; nothing on soundness: these are facts on what a yes holds.
(2) `OfDesc`, `RowFit` and the three laws on the silent rounds' tests are premises, as in
`FileDecides`. (3) That x without what is asked has the same public part as x, and that the silent
rounds' test does not feel the change, are premises: they are owed where the interface's `early` is
fixed. (4) THE EXTRACTED WITNESS IS NOT TIED TO THE ENDS HERE: that the relation at the first
boundary, at the public part, together with `fin` at the ends, gives the interface's relation at x
is `tieR`'s content and is not touched. (5) A description that says yes to all meets the three
statements, and so does one that says no to all: they say what a yes holds, not when it is given.
(6) NO STEP ASKS ANYTHING OF A VIEW: `RunEndIs`, `RunGivesRow` and `WholeMono` hold at all views, so
also at one whose drawn position lies outside its tree's range; `viewWordsBelowPrime` is carried as it is and
asks nothing of positions. What the fold makes of such a view: Block.step's own test on the rounds
refuses a drawn position at or above 2 ^ logN of its round's entry; a position below that and beyond
a shorter tree's length is the blocks' matter.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescThree
import OnBytes.Maker.WholeViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- **The file's verifier is monotone in its decision and in its test on the silent rounds.** -/
def WholeMono : Prop :=
  ∀ (C : CK) (D : WholeD) (Y TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (silent silent' : Y → TF → TJ → T3 → Bool)
    (run run' : Y → Fmt.View → Fmt.View → Fmt.View → Bool) (x x' : Y),
    (∀ a b c, silent x a b c = true → silent' x' a b c = true) →
    (∀ v₁ v₂ v₃, run x v₁ v₂ v₃ = true → run' x' v₁ v₂ v₃ = true) →
    ∀ (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh),
      (reductionOfWholeFile C D tF tJ t3 silent run).out x y τ = some () →
      (reductionOfWholeFile C D tF tJ t3 silent' run').out x' y τ = some ()

/-- **Where the file's verifier with the description's own decision says yes, the three reductions
in a row put out**, at every instance with the same public part. -/
def DescDecides : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) (okF : Xi → TF → Bool)
    (okJ : F.XiPub × F.S₁ → TJ → Bool) (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (silent : Xi → TF → TJ → T3 → Bool) (P : ((atDesc F T).row tF tJ t3 okF okJ ok3).Snd),
    OfDesc F T → RowFit D all all →
    (∀ x a b c, silent x a b c = true → okF x a = true) →
    (∀ x a b c v x₁, silent x a b c = true → (atDesc F T).run₁ x v = some x₁ → okJ x₁ b = true) →
    (∀ x a b c v v' x₁ x₂, silent x a b c = true → (atDesc F T).run₁ x v = some x₁ →
      (atDesc F T).run₂ x₁ v' = some x₂ → ok3 x₂ c = true) →
    ∀ (x x' : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh),
      F.pub x' = F.pub x → (∀ a b c, silent x a b c = true → silent x' a b c = true) →
      (reductionOfWholeFile C D tF tJ t3 silent F.run).out x y τ = some () →
      ((((atDesc F T).row tF tJ t3 okF okJ ok3).links P).all.out (x', y) τ).isSome = true

/-- **Under the same yes: the three ends, on the file's own three views, with the last test at the
instance itself.** -/
def WholeGivesEnds : Prop :=
  ∀ (C : CK) (D : WholeD) (Xi TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Iop.Tr (chainsOf C D tF tJ t3).sh),
    (reductionOfWholeFile C D tF tJ t3 silent F.run).out x y τ = some () →
    ∃ (e₁ : F.S₁) (e₂ : F.S₂) (e₃ : F.S₃),
      F.planOk = true ∧ F.okStart x = true ∧
        descRun₁ F x (view₁ C D tF tJ t3 y τ) = some (F.pub x, e₁) ∧
        descRun₂ F (F.pub x, e₁) (view₂ C D tF tJ t3 y τ) = some (F.pub x, e₁, e₂) ∧
        viewWordsBelowPrime (view₃ C D tF tJ t3 y τ) = true ∧
        (∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
          chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ (view₃ C D tF tJ t3 y τ) =
            .ok e₃) ∧
        F.fin x e₁ e₂ e₃ = true


end VerifiableInference.Desc.Sound
