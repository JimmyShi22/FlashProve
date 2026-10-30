-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/MoreAtOpening.lean: THE PREMISE hmore OF THE TIE AT THE
FIRST SEGMENT's OPENING IS A THEOREM AT THE WIDER FILLING `plusG D d dk Mg`
(BridgeG.lean): whatever comes at the opening beside the five
items of `madeSix` is one of First.FillSent's two names at segment 0, "frame.sentIs" and
"ledger.treesAre", and the opening makes both. One statement with its proof. WHY IT IS NO PREMISE.
As a premise it would be bound at every state of the wider promise, and nothing in that
promise pins the frame's groups or what is kept: it would have, by our reading, no member. The wider
filling's own "in order" holds `frontB`: with it the three facts on the frame in front follow
(`frontG`, Johnson/Desc/AtSeats/FrontG.lean). `hmore_plusG`: WHAT IT ASKS: `MgGC`'s line at "nothing
  is sent yet"; that item open in front; hmk: what comes is of the five or one of the two (a test
  on the door); TWO EQUATIONS ON Mg's LETTERS at the two names (First.FillSent's tests at its own
  term `sentDataAt`) and `pubP`'s silence there; THREE FACTS ON THE LIST OF ROUNDS: no message is
  counted in front of segment 0; the built segment 0's planned ledger is the opening's.
  `hown_plusG`: the premise hown likewise: as it is bound (every state of the
  wider promise) it hangs on the frame's link, which nothing else pins; `frontB`
  pins it: so hown follows from one test on the list of rounds.
What is not claimed. These. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.FrontG
import Johnson.Desc.K13.Law.BridgeG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Law (openLayZero_ok)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers)
open VerifiableInference.Desc.First.FillSent (sentDataAt baseAt sentIsB treesAreB)
open VerifiableInference.Desc.First.Look (K3Data)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13 (noneSentC)
open VerifiableInference.Desc.K13.Law

/-- First.FillSent's two names at segment 0. -/
def sentItem0 : Pub := .more (some 0) "frame.sentIs"
def treesItem0 : Pub := .more (some 0) "ledger.treesAre"

/-- **hmore, at the wider filling.** -/
theorem hmore_plusG {Pp W Cl : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data)
    {N : Numbers} {Mg : Meaning Pp W} {nsOf : ℕ → Option ℕ} {dg : Bool}
    (hGC : MgGC N Mg nsOf dk dg) (links : List ModelPart) (ps : List Place)
    (built : Array Stages.LinkH) (Q : List Pub) (p : Option Place) (hm : Pub.noneSent ∈ Q)
    (mk : List Pub) (hmk : ∀ i ∈ mk, i ∈ madeSix ∨ i = sentItem0 ∨ i = treesItem0)
    (hSent : ∀ x, Mg.pub sentItem0 x = sentIsB (sentDataAt D.shape N links ps built) 0 x.2)
    (hTrees : ∀ x, Mg.pub treesItem0 x = treesAreB (sentDataAt D.shape N links ps built) 0 x.2)
    (hSP : ∀ x, Mg.pubP sentItem0 x) (hTP : ∀ x, Mg.pubP treesItem0 x)
    (hb0 : baseAt N links ps 0 = 0) {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} (Y : Stages.LinkH) (hY : built[0]? = some Y)
    (hYF : Y.Fp = X.X.Fp) :
    ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' →
      (∀ q' ∈ Q, (plusG D d dk Mg).pub q' x = true) → First.bookAt N p x.2 = true →
      (plusG D d dk Mg).inOrder x = true → i ∈ mk → i ∉ madeSix →
      (plusG D d dk Mg).pub i x' = true ∧ (plusG D d dk Mg).pubP i x' := by
  intro x x' i hst hQ _ hio hi hn
  obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
  have hio' : ((Mg.inOrder x && frontB x.2) &&
      inOrderK13 D.codes D.shape D.layout x.2) = true := hio
  rw [Bool.and_eq_true, Bool.and_eq_true] at hio'
  obtain ⟨⟨_, hfr⟩, hk13⟩ := hio'
  obtain ⟨hg, hl, hkp⟩ := (frontB_iff _).1 hfr
  have hsh : x.2.check.frame.shape = D.shape := by
    unfold inOrderK13 at hk13
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk13
    exact hk13.1.2
  have hns : noneSentC N x.2 = true :=
    (hGC.noneSent x).symm.trans ((plusG_hand D d dk Mg _ rfl x).symm.trans (hQ _ hm))
  have h0 : x.2.st.oracles.size = 0 := by
    rw [noneSentC_eq, Bool.and_eq_true, Bool.and_eq_true] at hns
    have h1 := hns.1.1
    unfold K1.noneSentB at h1
    rw [Bool.and_eq_true] at h1
    exact Array.size_eq_zero_iff.2 (Array.isEmpty_iff.1 h1.1)
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid hd
  obtain ⟨g, mask, e, _, hlt⟩ := K1.firstAtS_frame q gp x.2 s₁ r₁ r₂ g₁ h1
  obtain ⟨hb, hk, ho⟩ := frontG q gp D.shape N links ps built x.2 h0 hsh hl hg hkp hb0
    (Nat.le_of_lt hlt)
  rcases hmk i hi with h | rfl | rfl
  · exact absurd h hn
  · refine ⟨?_, hSP x'⟩
    rw [plusG_hand D d dk Mg _ rfl, hSent]
    exact openingZero_sentIs hd _ hb hk ho
  · refine ⟨?_, hTP x'⟩
    rw [plusG_hand D d dk Mg _ rfl, hTrees]
    exact openingZero_treesAre hd _ (trees_zero D.shape N links ps built X.X X.ns Y hY hYF)

/-- **hown, at the wider filling**: the own seats' test at every state of that filling's promise,
from
ONE TEST ON THE LIST OF ROUNDS: the wider "in order" pins the frame's shape and its link, so how
many
messages it expects at moment 0; the promise's test on the book pins the number of trees. -/
theorem hown_plusG {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data)
    (N : Numbers) (Mg : Meaning Pp W) (O : List First.Item) (p : Option Place) (P' : K1.Par)
    (hB : K1.ownSeatsB N O P'
      (((D.shape.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
      (N.treesAt p) = true) :
    ∀ x, (plusG D d dk Mg).inOrder x = true → First.bookAt N p x.2 = true →
      K1.ownSeatsB N O P' (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true := by
  intro x hio hbk
  have hio' : ((Mg.inOrder x && frontB x.2) &&
      inOrderK13 D.codes D.shape D.layout x.2) = true := hio
  rw [Bool.and_eq_true, Bool.and_eq_true] at hio'
  obtain ⟨⟨_, hfr⟩, hk13⟩ := hio'
  obtain ⟨_, hl, _⟩ := (frontB_iff _).1 hfr
  have hsh : x.2.check.frame.shape = D.shape := by
    unfold inOrderK13 at hk13
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk13
    exact hk13.1.2
  have ht : x.2.book.trees.size = N.treesAt p := by
    unfold First.bookAt at hbk
    rw [Bool.and_eq_true, Bool.and_eq_true] at hbk
    exact eq_of_beq hbk.1.1
  rw [atMoment_zero _ D.shape hsh hl, ht]
  exact hB

end HashBuild
