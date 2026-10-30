-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgWide.lean: THE WIDER MEANING, ONCE, FOR ALL AUTHORS: the composed meaning of
the open claims (`mgAll`, Johnson/Desc/Sound/MgAll.lean) with the public tests that have left the
table asked again. Definitions and theorems.
Why. `mgAll` does not ask thirteen names, and its test "in order" lacks four
conjuncts: these say facts on every state that the verifier reaches, and are proved along the run.
Ties that are typed at the wider meaning speak of a meaning at which these are asked. The bridge
`tiedAtR_of_classA` (Johnson/Desc/Sound/PlusDoorA.lean) carries a tie at `widen Mg M pub' io'` to
a tie at Mg under the reached states. If each kind's authors wrote their own M, pub', io', each
would write other authors' rows and tests. Here they stand once.
  `WideData`: the data of the parts that were struck: the proximity test's (d12), the pending
    claim's and the approximate range proof's (dP), the request's words (reqW).
  `moreExtra`: the rows of the names that left, each its own authors' term, merged. `moreW 𝔇 Mg`:
    the term's own rows BEFORE the strike, with these.
  `ioWide 𝔇 E Mg`: "in order" at the wider meaning, without a conjunct on the groups' first senders:
    Mg's own, the start's three equations, the request's words, the last sub-protocols' test, the
    request's bytes.
  `mgWide 𝔇 E Mg := widen (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E
    Mg)`.
  `mgWide_hand`, `mgWide_io`: the bridge's first two premises, at every 𝔇, E, Mg.
  `mgWide_pub`, `mgWide_inOrder_at`, `mgWide_more`; `mgWide_same`: every other field is `mgAll`'s
    own (stated for the fields that a tie reads: pubP, decodes, pin, worth, forms, formsT, tie,
    wo, pile, row).
  `moreWideAll`: the wider list over the closed base, WITH CODE; `moreW_base`: it is `moreW 𝔇
    mgBase`.
Limits: definitions and unfoldings. The bridge's third premise (`doorsFitB`, a test with code on
the two closed lists) is for an evaluation, not shown here. Its fourth (the facts at reached
states) is owed by the names' own authors. The
conjunct on the groups' first senders is not in `ioWide`: no typed lemma called it. No soundness
is claimed.

-/
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.PlusDoorA
import Johnson.Desc.First.PubWide
import Johnson.Desc.First.FillStart
import Johnson.Desc.First.FillReqIs
import Johnson.Desc.First.Look.K3LiveIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Meaning More Pub classA pubWide weightsMore)
open VerifiableInference.Desc.K12.Door (K12Data k12More shapesMore)
open VerifiableInference.Desc.K13.Law (k13Asks pileMasksMore pileWithinMore oneRowMore)
open VerifiableInference.Desc.First.Look (liveMore)

/-- The data of the parts that were struck. -/
structure WideData (P : Type) where
  d12 : K12Data
  dP : First.FillP1.PlusData
  reqW : P → Array UInt32

/-- The rows of the names that left, each its own authors' term. -/
def moreExtra : More :=
((((First.FillP1.moreP1.merge (k12More.merge shapesMore)).merge weightsMore).merge liveMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore))))

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The term's own rows before the strike, with the rows of the names that left. -/
noncomputable def moreW : More := (mgBelow 𝔇 Mg).more.merge moreExtra

/-- "In order", wide. -/
def ioWide (a : P × First.S) : Bool :=
  ((((Mg.inOrder a && First.eqsB 𝔇.cs 𝔇.shape 𝔇.layout a.2) && First.reqIsB (E.reqW a.1) a.2) &&
    K13.Law.inOrderK13 𝔇.cs 𝔇.shape 𝔇.layout a.2) && (_root_.Meaning.backReq (𝔇.reqB a.1)).isSome)

/-- **THE WIDER MEANING.** -/
noncomputable def mgWide : Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  widen (mgAll 𝔇 Mg) (moreW 𝔇 Mg) (pubWide E.d12 E.dP 𝔇.pubD Mg.pub) (ioWide 𝔇 E Mg)

theorem mgWide_pub : (mgWide 𝔇 E Mg).pub = pubWide E.d12 E.dP 𝔇.pubD Mg.pub := rfl

theorem mgWide_inOrder_at (a : P × First.S) : (mgWide 𝔇 E Mg).inOrder a = ioWide 𝔇 E Mg a := rfl

theorem mgWide_more : (mgWide 𝔇 E Mg).more = (mgBelow 𝔇 Mg).more.merge moreExtra := rfl

/-- The bridge's first premise. -/
theorem mgWide_hand (i : Pub) (h : classA i = false) (x : P × First.S) :
    pubWide E.d12 E.dP 𝔇.pubD Mg.pub i x = (mgAll 𝔇 Mg).pub i x := by
  rw [mgAll_pub]
  exact First.pubWide_hand E.d12 E.dP 𝔇.pubD Mg.pub i h x

/-- The bridge's second premise. -/
theorem mgWide_io (x : P × First.S) (h : ioWide 𝔇 E Mg x = true) :
    (mgAll 𝔇 Mg).inOrder x = true := by
  rw [mgAll_inOrder_at]
  unfold ioWide at h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1.1.1, h.2⟩

/-- Every other field is the narrower meaning's own. -/
theorem mgWide_same :
    (mgWide 𝔇 E Mg).pubP = (mgAll 𝔇 Mg).pubP ∧ (mgWide 𝔇 E Mg).decodes = (mgAll 𝔇 Mg).decodes ∧
      (mgWide 𝔇 E Mg).pin = (mgAll 𝔇 Mg).pin ∧ (mgWide 𝔇 E Mg).worth = (mgAll 𝔇 Mg).worth ∧
      (mgWide 𝔇 E Mg).forms = (mgAll 𝔇 Mg).forms ∧ (mgWide 𝔇 E Mg).formsT = (mgAll 𝔇 Mg).formsT ∧
      (mgWide 𝔇 E Mg).tie = (mgAll 𝔇 Mg).tie ∧ (mgWide 𝔇 E Mg).wo = (mgAll 𝔇 Mg).wo ∧
      (mgWide 𝔇 E Mg).pile = (mgAll 𝔇 Mg).pile ∧ (mgWide 𝔇 E Mg).row = (mgAll 𝔇 Mg).row :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

/-- **The wider list over the closed base, with code.** -/
def moreWideAll : More := moreUnstruck.merge moreExtra

theorem moreW_base {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) : moreW 𝔇 mgBase = moreWideAll := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgWide_pub
#print axioms VerifiableInference.Desc.Sound.mgWide_inOrder_at
#print axioms VerifiableInference.Desc.Sound.mgWide_more
#print axioms VerifiableInference.Desc.Sound.mgWide_hand
#print axioms VerifiableInference.Desc.Sound.mgWide_io
#print axioms VerifiableInference.Desc.Sound.mgWide_same
#print axioms VerifiableInference.Desc.Sound.moreW_base
