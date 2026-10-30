-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WiderSalts.lean: A MEMBER OF theWider
(Johnson/Goal/Conditions/WiderAtThe.lean)
WHOSE COMMITTER LAYS THE CONFIGURATION's DIGEST IN FRONT OF EVERY LEAF's SALT: at every hash
function its commitment at ρ is that of the committer with the coins fixed at (r, σ), r the pads
that ρ names and σ j = Run.leafSalt (the bytes of c) (the bytes that ρ holds for leaf j), c the hash
at configString Z: IF idx names the salts that it is handed (hidx); at K.digits: if ρ holds as many
bytes for each of the tree's leaves as the plan's salt has (hs).

Why. verify()'s parser lays c in front of every stored leaf's salt (Run.leafSalt, Run/ParseBS.lean).
So an honest committer's leaves must have salts of that form. At theWide the number of the coins
cannot hang on c.

Main names.
  commit_wider_reach   commit_withTerms_reach (Johnson/Goal/Conditions/CoinsEnumerated.lean) at
    theWiderTerms: the committer at a ρ whose number, at this hash, is that of a pair.
  WiderCoins.named K ra sb idx   THE GENERATOR: the number of the pair (ra Z ρ, idx Z σ), σ as
    above. ra: which pads; sb: the bytes for each leaf; idx: the number at which given salts stand
    in K.sl.
  commit_named, commit_named_at   THE STATEMENT, at letters: if idx names the salts that it is
    handed; the second with the depth and the list read at R₀ Z and K.
  length_salt   such a salt has 256 + 8 n bits, if ρ holds n bytes for the leaf.
  named_digits, commit_digits   AT K.digits (Johnson/Goal/Conditions/WideDigits.lean), idx := idxOf
    (Johnson/Top/EnumIndex.lean): in idx's place the premise that ρ holds as many bytes for each
    leaf as the plan's salt has.

Limits. Nothing on hiding. This W lays DERIVED salts: right for completeness at a stored set, which
is what the programs do; for hiding, fresh masks and masks derived from a seed are two cases, and
this file treats neither: so no statement on hiding at that W.
ra and sb are letters: nothing is said on how ρ is drawn. WRITTEN, NOT RUN: the numbers have more
digits than a machine holds. The pads and the salts are read at the description's own input (the
warning on Lean's kernel in the head of WideDigits.lean). No completeness. WiderAtThe.lean's limits
travel whole.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderAtThe
import Johnson.Goal.Conditions.WideDigits
import Johnson.Top.EnumIndex
import Run.CodingPage160

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

variable (K : TheCoins)

/-- **The committer of a member at a randomness whose number, at this hash function, is that of a
pair.** -/
theorem commit_wider_reach (W : WiderCoins K) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) (hash : Hash)
    (a : Fin (((theWiderTerms K W).ri Z).n + 1)) (c' : Fin (((theWiderTerms K W).sl Z).n + 1))
    (hv : (W.gen Z ρ (hash (configString Z))
        (hash (anchorString (hash (configString Z)) (K.shape Z)))).val =
      a.val + (((theWiderTerms K W).ri Z).n + 1) * c'.val) :
    ((theWider K W o).commit Z (settingsOfRead pp) w ρ).evaluate hash =
      (fixedCommit (theWiderTerms K W) Z (settingsOfRead pp) w (((theWiderTerms K W).ri Z).e a)
        (((theWiderTerms K W).sl Z).e c')).evaluate hash :=
  commit_withTerms_reach (bindLaws_wider K W Z pp hr) w ρ hash a c' hv

/-- The salts that bear c: the bytes of c, then the bytes that are held for the leaf. -/
def saltsAt (c : Digest) (s : ℕ → ByteArray) : ℕ → Rom.Bits :=
  fun j => _root_.Run.leafSalt (_root_.Run.digToBytes c) (s j)

/-- Such a salt has 256 + 8 n bits, if n bytes are held for the leaf. -/
theorem length_salt (c : Digest) (s : ℕ → ByteArray) (j n : ℕ) (h : (s j).size = n) :
    (saltsAt c s j).length = 256 + 8 * n := by
  unfold saltsAt _root_.Run.leafSalt
  rw [List.length_append, _root_.Run.length_bytesToBits, _root_.Run.length_bytesToBits,
    _root_.Run.size_digToBytes, h]

/-- **The generator**: the number of the pair (the pads that ρ names, the salts that bear c). -/
def WiderCoins.named (ra : (Z : PublicFiles) → K.Rand → Fin ((K.ri Z).n + 1)) (sb : K.Rand → ℕ → ByteArray)
    (idx : (Z : PublicFiles) → (ℕ → Rom.Bits) → Fin ((K.sl Z).n + 1)) : WiderCoins K where
  bound := fun Z => ((K.ri Z).n + 1) * ((K.sl Z).n + 1) - 1
  gen := fun Z ρ c _ =>
    ⟨(ra Z ρ).val + ((K.ri Z).n + 1) * (idx Z (saltsAt c (sb ρ))).val, by
      have h := (reach_pair (K.ri Z).n (K.sl Z).n (ra Z ρ).val (idx Z (saltsAt c (sb ρ))).val
        (ra Z ρ).isLt (idx Z (saltsAt c (sb ρ))).isLt).2.2
      omega⟩

variable (ra : (Z : PublicFiles) → K.Rand → Fin ((K.ri Z).n + 1)) (sb : K.Rand → ℕ → ByteArray)
  (idx : (Z : PublicFiles) → (ℕ → Rom.Bits) → Fin ((K.sl Z).n + 1))

/-- **AT EVERY HASH FUNCTION THE COMMITMENT AT ρ IS THAT OF THE COMMITTER WITH THE COINS FIXED AT
THE PADS THAT ρ NAMES AND THE SALTS THAT BEAR c.** hidx: at the tree's places idx names the salts
that it is handed here. -/
theorem commit_named (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) (hash : Hash)
    (hidx : ∀ j, j < 2 ^ ((flashProveDescription.reBound (WiderCoins.named K ra sb idx).bound).input Z
        ((theWiderTerms K (WiderCoins.named K ra sb idx)).c₀ Z)
        ((theWiderTerms K (WiderCoins.named K ra sb idx)).m₀ Z)).queryLayout.depth →
      ((theWiderTerms K (WiderCoins.named K ra sb idx)).sl Z).e
        (idx Z (saltsAt (hash (configString Z)) (sb ρ))) j =
          saltsAt (hash (configString Z)) (sb ρ) j) :
    ((theWider K (WiderCoins.named K ra sb idx) o).commit Z (settingsOfRead pp) w ρ).evaluate
        hash =
      (fixedCommit (theWiderTerms K (WiderCoins.named K ra sb idx)) Z (settingsOfRead pp) w
        (((theWiderTerms K (WiderCoins.named K ra sb idx)).ri Z).e (ra Z ρ))
        (saltsAt (hash (configString Z)) (sb ρ))).evaluate hash := by
  rw [← fixedCommit_salts (bindLaws_wider K (WiderCoins.named K ra sb idx) Z pp hr) w _ _ _ hidx]
  exact commit_wider_reach K (WiderCoins.named K ra sb idx) o Z pp hr w ρ hash (ra Z ρ)
    (idx Z (saltsAt (hash (configString Z)) (sb ρ))) rfl

/-- The same, with the tree's depth and the list of salts read at K and at `R₀ Z`: the passage is
made here, at letters (the warning on Lean's kernel in the head of WideDigits.lean). -/
theorem commit_named_at (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (ρ : K.Rand) (hash : Hash)
    (hidx : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth →
      (K.sl Z).e (idx Z (saltsAt (hash (configString Z)) (sb ρ))) j =
        saltsAt (hash (configString Z)) (sb ρ) j) :
    ((theWider K (WiderCoins.named K ra sb idx) o).commit Z (settingsOfRead pp) w ρ).evaluate
        hash =
      (fixedCommit (theWiderTerms K (WiderCoins.named K ra sb idx)) Z (settingsOfRead pp) w
        (((theWiderTerms K (WiderCoins.named K ra sb idx)).ri Z).e (ra Z ρ))
        (saltsAt (hash (configString Z)) (sb ρ))).evaluate hash :=
  commit_named K ra sb idx o Z pp hr w ρ hash hidx

/-! ## At K.digits -/

/- From here on Lean compares these by their names. -/
attribute [local irreducible] riDigits fieldRows

/-- The generator at K.digits: the salts' number is the written one. -/
def named_digits (ra : (Z : PublicFiles) → K.digits.Rand → Fin ((K.digits.ri Z).n + 1))
    (sb : K.digits.Rand → ℕ → ByteArray) : WiderCoins K.digits :=
  WiderCoins.named K.digits ra sb fun Z σ => idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT σ

/-- **At K.digits**: if ρ holds as many bytes for each of the tree's leaves as the plan's salt
has. -/
theorem commit_digits (ra : (Z : PublicFiles) → K.digits.Rand → Fin ((K.digits.ri Z).n + 1))
    (sb : K.digits.Rand → ℕ → ByteArray) (o : SecondHashFunctionType) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (ρ : K.digits.Rand)
    (hash : Hash)
    (hs : ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (sb ρ j).size = LPFD.Full.saltG (dataAtFiles flashProveData Z).G) :
    ((theWider K.digits (named_digits K ra sb) o).commit Z (settingsOfRead pp) w ρ).evaluate
        hash =
      (fixedCommit (theWiderTerms K.digits (named_digits K ra sb)) Z (settingsOfRead pp) w
        (((theWiderTerms K.digits (named_digits K ra sb)).ri Z).e (ra Z ρ))
        (saltsAt (hash (configString Z)) (sb ρ))).evaluate hash :=
  commit_named_at K.digits ra sb (fun Z σ => idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT σ) o Z pp hr w ρ hash
    (e_idxOf (R₀ Z).queryLayout.depth (R₀ Z).compilerParameters.sMT (saltsAt (hash (configString Z)) (sb ρ)) fun j hj =>
      (length_salt _ _ j _ (hs j hj)).trans (sMT_R₀ Z).symm)

end FlashProve

#print axioms FlashProve.commit_digits
#print axioms FlashProve.commit_wider_reach
#print axioms FlashProve.length_salt
#print axioms FlashProve.commit_named
#print axioms FlashProve.commit_named_at
