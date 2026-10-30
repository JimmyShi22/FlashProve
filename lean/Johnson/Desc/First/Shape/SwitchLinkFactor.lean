-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchLinkFactor.lean: THE CODE SWITCH AT A SEGMENT's FIRST PLACE (kind
K2): "NO SEED's FACTOR IS 0" (factorV, SwitchLinkFits.lean) FALLS TO THE ROUNDS' OWN TEST ON FORM
TOO, UNDER THE TWO TESTS ON THE PLAN AND THE SHAPE. So rounds and columns that fit meet the whole
test on rounds and columns (linkR, SwitchLinkB.lean). General laws; nothing is evaluated.

Why it can be had. The clause asks of a seed's factor that isZeroE says no, and isZeroE
(OnBytes/Field/Ext.lean) says yes just where all three WORDS are 0. The rounds' test on form
(roundsFit, Johnson/Desc/Block.lean) asks of each drawn element that the format marks as never 0
that its three words are not all 0. The law at the code switch's declared rounds is
rounds_give_shown (Johnson/Desc/K2/Honest/Returns/DrawFits.lean), under two ties of the plan's
numbers to the sending's: the first is a clause of linkP; the second follows from linkB's clause on
the first round's entry (nonZero_of_entry, DrawTies.lean beside it). Both laws are called: nothing
on a round of seeds is proved here.

  `sendingS_sent`, `linkB_entry`: what the sending announces; linkB's clause on the first round's
    entry.
  **`factorV_of_fits`**: roundsFit (K2.rounds p) [R₁, R₂], linkB p x and linkP p x: then factorV p
    x (noDigest R₁) accepts. `factorV_of_Fits`: the same at a block with the kind's declared rounds.
  **`linkR_of_Fits_whole`**: at such a block: Block.Fits, linkB and linkP: then the rounds are two
    and linkR accepts at them, shown without the sealed digest, and at the groups that the step
    shows.

Limits. "Not 0" is said of words, as the kind's text says it; that such an element is not 0 in the
field wants each word below the prime beside it, which is not treated. No plan and shape are shown
at which linkB or linkP accepts. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SwitchLinkFits
import Johnson.Desc.K2.Honest.Returns.DrawTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (switchNotices)

/-- What the sending announces. -/
theorem sendingS_sent (p : P2) (codes : Codes) (T : SwitchTarget) (others : Array OracleNotice) :
    (sendingS p codes T others).sent = switchNotices T others := by
  simp [sendingS, K1.Par.sent]

/-- linkB's clause on the first round's entry. -/
theorem linkB_entry {p : P2} {x : ChainF} {Q : ReqGroup}
    (e : x.1.check.frame.groups[x.1.check.frame.link]? = some Q) (h : linkB p x = true) :
    planOk1 none (switchNotices Q.target (linkOthers x.1.check.frame)) (par9 p).eSeed = true := by
  unfold linkB at h
  split at h
  · rename_i L Q' c₀ z₀ c e1 e2 e3 e4 e5
    obtain rfl : Q = Q' := Option.some.inj (e.symm.trans e2)
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.2
  · cases h

/-- **On rounds that fit no seed's factor is spelt by three words 0.** -/
theorem factorV_of_fits {p : P2} {x : ChainF} {R₁ R₂ : Fmt.RoundView}
    (hf : roundsFit (First.K2.rounds p) [R₁, R₂] = true) (hB : linkB p x = true)
    (hP : linkP p x = true) : factorV p x (noDigest R₁) = true := by
  unfold linkP at hP
  unfold factorV
  split at hP
  · rename_i Q c e2 e5
    rw [e2]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    rw [List.all_eq_true]
    intro z hz
    rw [Bool.not_eq_true']
    exact (K2.Honest.Returns.rounds_give_shown p _ R₁ R₂ hP.1.1.1.1.1
      (K2.Honest.Returns.nonZero_of_entry p _ _ (sendingS_sent p _ _ _) (linkB_entry e2 hB))
      hf).2.2.2.2 z hz
  · cases hP

/-- The same at a block with the kind's declared rounds. -/
theorem factorV_of_Fits {Cl : Type} {blk : Block S Cl} {p : P2} {x : ChainF} {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hP : (linkB p x && linkP p x) = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧ factorV p x (noDigest R₁) = true := by
  rw [Bool.and_eq_true] at hP
  have h1 := hF.1
  rw [hb] at h1
  obtain ⟨R₁, R₂, rfl, -⟩ := k2_fit h1
  exact ⟨R₁, R₂, rfl, factorV_of_fits h1 hP.1 hP.2⟩

/-- **Rounds and columns that fit meet the whole test on rounds and columns.** -/
theorem linkR_of_Fits_whole {Cl : Type} {blk : Block S Cl} {p : P2} {x : ChainF} {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List Col} (hb : blk.rounds = First.K2.rounds p)
    (hF : blk.Fits ft rs cols) (hB : linkB p x = true) (hP : linkP p x = true) :
    ∃ R₁ R₂, rs = [R₁, R₂] ∧
      linkR p x (noDigest R₁) (noDigest R₂) (blk.shown ft rs cols) = true := by
  obtain ⟨R₁, R₂, rfl, h⟩ := linkR_of_Fits hb hF hP
  have h1 := hF.1
  rw [hb] at h1
  exact ⟨R₁, R₂, rfl, h (factorV_of_fits h1 hB hP)⟩

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sendingS_sent
#print axioms VerifiableInference.Desc.First.Shape.linkB_entry
#print axioms VerifiableInference.Desc.First.Shape.factorV_of_fits
#print axioms VerifiableInference.Desc.First.Shape.factorV_of_Fits
#print axioms VerifiableInference.Desc.First.Shape.linkR_of_Fits_whole
