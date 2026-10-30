-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03PubAt.lean: THE KIND "LOOKUP" (K3): TWO TERMS ON THE COMPOSED MEANING's PUBLIC TESTS: pubFree · pubSent: fields of what is left at the lookups (ObjShortR, Johnson/P5J/K03ObjAt.lean; DigShortR, Johnson/P5J/K03DigAt.lean). (The name pubFree_mgAllAt: Johnson/Desc/Sound/MgAt/K3DigitsFree.lean bears the name pubFree_mgAll.) A joining: by calls and one case split.

 GENERAL IN THE PARAMETERS:
  freeAbove_two     the table's own "free above, with n slots" (Desc.First.freeAboveB) and the attention caller's door's (H2K5.Door.freeAboveB) are one function.
  pubFree_mgAllAt     where the built segment l has n slots: an accept of the composed meaning's public test at freeAbove l gives the door's freeAboveB n. (mgAll_pub · pubAll_freeAbove · freeAbove_two.)
  pubSent_mgAll     an accept at "frame.sentIs" l gives sentIsB Dm.pubD.dS l. (mgAll_pub · pubAll_more_sentIs, Johnson/Desc/First/PubAllAt.lean: it goes through a lemma on the attention caller's layer: no unfolding.)
 AT THE CONSTANT (h : AtMgA OnBytes.secondHashFunction …; 𝔇 := h.toAtMg.𝔇 h.𝔇):
  k03_pubFree_calls   ObjShortR's field pubFree to the letter, l < 24, at lookAt's place x (k03_slots_look: the built segment's number of slots is the place's).
  k03_pubSent_calls   ObjShortR's field pubSent to the letter, at lookAt's place, EVERY l · k03_pubSent_head: at headAt's place (segment 24).
  k03_pubFree_digits  DigShortR's field pubFree AT n := y.ns, y the CALLS' place of the same segment (one ledger a segment), l < 24.
NOT PAID: pubFree AT SEGMENT 24 (calls and digits): it wants "the built segment 24 has x.ns slots": typed by nobody (the law that lies speaks of the LAST built segment): pubFree_mgAllAt takes it as its premise. (Where this and lean/THEOREM.md differ, the page holds.)
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03SlotsAt
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Desc.Sound.MgAt.K3HeadR
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Flat
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub Meaning moreItem)
open VerifiableInference.Desc.First.FillSent (sentIsB sentName)

/-- The table's own text and the door's are one function. -/
theorem freeAbove_two (n : ℕ) (s : Desc.First.S) :
    Desc.First.freeAboveB n s = H2K5.Door.freeAboveB n s := by
  unfold Desc.First.freeAboveB H2K5.Door.freeAboveB H2K5.Door.freeFromB
  cases s.fork? with
  | none => rfl
  | some G => exact Bool.and_comm _ _

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

theorem pubFree_mgAllAt (l n : ℕ) (hn : (Dm.built[l]?).map (·.ns) = some n) :
    ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB n s = true := by
  intro z s h
  rw [mgAll_pub, Desc.First.pubAll_freeAbove] at h
  have e : Dm.pubD.nsOf l = some n := hn
  rw [e] at h
  rw [← freeAbove_two]
  exact h

theorem pubSent_mgAll (l : ℕ) :
    ∀ (z : P) s, (mgAll Dm Mg).pub (moreItem (sentName l)) (z, s) = true →
      sentIsB Dm.pubD.dS l s = true := by
  intro z s h
  rw [mgAll_pub] at h
  exact (Desc.First.pubAll_more_sentIs Dm.pubD Mg.pub l (z, s)).symm.trans h

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (moreItem)
open VerifiableInference.Desc.First.FillSent (sentIsB sentName)
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **ObjShortR's field pubFree, at the 24 lookups on a segment's calls.** -/
theorem k03_pubFree_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {x : Place} (hx : lookAt (At.X Zp) l false = some x) :
    ∀ (z : ProofFile.InstPub) s, (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB x.ns s = true :=
  pubFree_mgAllAt (h.toAtMg.𝔇 h.𝔇) mgBase l x.ns (k03_slots_look h hl hx)

/-- **ObjShortR's field pubSent, at lookAt's place, every segment.** -/
theorem k03_pubSent_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ}
    {x : Place} (hx : lookAt (At.X Zp) l false = some x) :
    ∀ (z : ProofFile.InstPub) s,
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (moreItem (sentName l)) (z, s) = true →
      sentIsB (h.toAtMg.𝔇 h.𝔇).pubD.dS x.link s = true := by
  rw [VerifiableInference.OnPublicFiles.lookAt_link hx]
  exact pubSent_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase l

/-- The like at the output head's own place. -/
theorem k03_pubSent_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {x : Place} (hx : VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some x) :
    ∀ (z : ProofFile.InstPub) s,
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (moreItem (sentName 24)) (z, s) = true →
      sentIsB (h.toAtMg.𝔇 h.𝔇).pubD.dS x.link s = true := by
  rw [(headAt_link hx).trans (headLink_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne)]
  exact pubSent_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase 24

/-- **DigShortR's field pubFree at n := the calls' place's number of slots.** -/
theorem k03_pubFree_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 24)
    {y : Place} (hy : lookAt (At.X Zp) l false = some y) :
    ∀ (z : ProofFile.InstPub) s, (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB y.ns s = true :=
  k03_pubFree_calls h hl hy

end P5J

#print axioms VerifiableInference.OnPublicFiles.freeAbove_two
#print axioms VerifiableInference.OnPublicFiles.pubFree_mgAllAt
#print axioms VerifiableInference.OnPublicFiles.pubSent_mgAll
#print axioms P5J.k03_pubFree_calls
#print axioms P5J.k03_pubSent_calls
#print axioms P5J.k03_pubSent_head
#print axioms P5J.k03_pubFree_digits
