-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3At.lean: the kind "lookup" (K3): WHAT THE LOOKUPS' THEOREMS ASK OF A
MEANING, AT THE COMPOSED MEANING mgAll Dm Mg (Johnson/Desc/Sound/MgAll.lean:
at the small list of extra public tests): the structure K3At
(Johnson/Desc/First/Look/K3At.lean) and the light sentences of digMeanR_of (K3MeansDigR.lean) on the
fields that read the oracle messages. Each a call of MgAll.lean's own lemma on that field. NO
SOUNDNESS IS CLAIMED.

Main names.
  k3At_mgAll: K3At X Dm.sent Dm.l3 (mgAll Dm Mg): ALL EIGHT FIELDS, at every Dm and every Mg.
  heldReads_mgAll: HeldReads (mgAll Dm Mg).
  inOrderReads_mgAll: InOrderReads (mgAll Dm Mg) FROM InOrderReads Mg (the term's "in order" is Mg's
    own and a test on the public part).
  digPart_mgAll: where Dm.digitsPart is digitsPartK3 X Dm.sent Dm.l3, constr l lookDigits at the
    term is that sentence (hdigF).
  The three equations hshownF, hnoCollF, hdecF are MgAll.lean's mgAll_shown, mgAll_noColl,
    mgAll_decodes as they lie: not said again.
OBJECT. No sub-protocol's text: one term of the type Meaning.
Used by K3Calls.lean, K3CallsAsks.lean, K3CallsBareAt.lean (Johnson/Desc/Sound/MgAt/) and 17 more.
LETTERS. Dm, Mg.
IS IT EMPTY? k3At_mgAll and heldReads_mgAll have no premise.
Compiled with the whole library.


Limits. Dm's fields are parameters: that Dm.digitsPart is the lookups' sentence is asked, not shown.
K3AtLive (the two sentences on the name "frame.liveIs") does NOT hold at this term: the name is
struck from its list.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Look.K3At
import Johnson.Desc.First.Look.K3FillDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning pubAll pubAll_lookIn pubAll_lookOut)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **AT K3's OWN ITEMS AND FIELDS THE COMPOSED MEANING SAYS WHAT THE LOOKUPS' LAYER SAYS.** -/
theorem k3At_mgAll : K3At X Dm.sent Dm.l3 (mgAll Dm Mg) := by
  have hw : ∃ f, (mgAll Dm Mg).worth = worthK3 X Dm.sent Dm.l3 f := by
    rw [mgAll_worth]
    unfold fillK3Both
    exact ⟨_, fillAll_worth X Dm.sent Dm.l3 _⟩
  refine ⟨fun m dg a => ?_, fun m dg a => ?_, fun m a => rfl, fun m a => rfl, fun m a => rfl,
    fun m a => ?_, fun m a => ?_, hw⟩
  · rw [mgAll_pub, pubAll_lookIn Dm.pubD Mg.pub m _ dg (sort_at X m dg) a]
    rfl
  · rw [mgAll_pub, pubAll_lookOut Dm.pubD Mg.pub m _ dg (sort_at X m dg) a]
    rfl
  · rw [mgAll_pubP]
    rfl
  · rw [mgAll_pubP]
    rfl

/-- "Held" at the term reads the statement and the book alone. -/
theorem heldReads_mgAll : HeldReads (mgAll Dm Mg) := by
  intro j k z s t hst hbk
  rw [mgAll_held]
  dsimp only
  rw [hst, hbk]

/-- "In order" at the term reads what Mg's own reads. -/
theorem inOrderReads_mgAll (h : InOrderReads Mg) : InOrderReads (mgAll Dm Mg) := by
  intro z s t hst hck hrq
  rw [mgAll_inOrder_at, mgAll_inOrder_at, h z s t hst hck hrq]

/-- **hdigF at the term.** -/
theorem digPart_mgAll (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3) (l : ℕ)
    (a : P × Desc.First.S) (y : Desc.Strs) (w : Desc.Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll Dm Mg).constr l .lookDigits a y w = digitsPartK3 X Dm.sent Dm.l3 l a y w := by
  rw [mgAll_constr]
  unfold P5J.constrQAt
  rw [if_pos rfl, hD]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3At_mgAll
#print axioms VerifiableInference.OnPublicFiles.heldReads_mgAll
#print axioms VerifiableInference.OnPublicFiles.inOrderReads_mgAll
#print axioms VerifiableInference.OnPublicFiles.digPart_mgAll
