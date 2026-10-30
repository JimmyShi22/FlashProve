-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormBehind.lean: THE KIND K1's FIFTY LATER SENDINGS (every
link's reads and digits): WHAT STANDS BEHIND A MEMBER's ACCEPTING STEP OF THE TABLE's PROMISE ON THE
VERIFIER's STATE, AT ONE STATE IN FRONT. No thread, no prover and no string occurs. General in the
numbers N, the meaning Mg and the public part z. Statements and proofs.

  epub_eq: the two tests that IM.BK leaves out, as Johnson/Desc/AtSeats/HandsMore.lean spells them
    (EPub) and as Johnson/P1K2R/TieTwo.lean does (P1K2.EQ), are one.
  handsPt_later_pub: WHAT ONE SUB-PROTOCOL OWES AT ONE STATE IN FRONT (IM.HandsPt,
    Johnson/IMR/HandsPoint.lean), ALL SIX FIELDS, AT THE TEST EPub. The library has the like at
    every state in front (hands_later_pub, Johnson/Desc/K1/Law/HandsPubAtFifty.lean), where the
    premise on the link's frame's group ranges over all states; a file that is not in this library
    has it at one state at the narrower test without "in order" (handsPt_later,
    Johnson/Desc/AtSeats/HearAtFiftyR.lean [not in this library; so here read: not proved in this
    library]). The proof is that one's, with one arm more (hOrd) and one premise fewer.
  xk_later_at: so the six tests at the next border behind an accepting step, at P1K2.EQ, from the
    six in front: no fence, and no premise that ranges over states. xk_later_seated: at a member
    that is seated alone over the lot's sub-protocol.
  held_later: the samples are held behind, from: they are held in front · a sample held in front is
    held behind · the samples of the place's own messages are held behind. By the table's row
    (RowL.sampled, Johnson/Desc/K1/Law/KeepAtLater.lean).
  leftOn_later_yes: the sentence of the public item leftOn m over an accepting step: by leftOn_blkL
    (Johnson/Desc/K1/Law/ALeftOf.lean).

Limits. NOT ONE PREMISE IS SHOWN AT ANY NUMBERS OR MEANING: four on the numbers (hinj, trees, msgs,
hP) · the open link's frame's group at the state in front (hg) · three arms on the meaning's public
tests (hOrd, hRide, hNew) · in held_later the two on the samples. At the written list of links and
places alone. Nothing on the first segment's opening or on W's sending. That a member accepts
anywhere is not shown. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.HandsPubAtFifty
import Johnson.Desc.K1.Law.ALeftOf
import Johnson.Desc.K1.Law.RowLFull
import Johnson.Desc.AtSeats.HandsPointG
import Johnson.Desc.AtSeats.HandsBridge
import Johnson.P1K2R.TieTwo
import Johnson.IMR.HandsPoint
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Numbers Meaning flatPlacesOf ledgerB
  samplesHeld sampledIn)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1 (blkL parL noL momL tiedL YesOf InB laterSeatsB layOf)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open OnBytes.Model.Stages (LinkH)
open HashBuild (EPub epub_of xk_swap handsPt_of_all)

variable {Pp W : Type}

/-- **The two spellings of the two further tests are one.** -/
theorem epub_eq (z : Pp) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) :
    EPub z Mg links ps = P1K2.EQ Mg links ps z := rfl

/-- **WHAT ONE LATER SENDING OWES, AT ONE STATE IN FRONT, AT THE TEST WITH "in order".** -/
theorem handsPt_later_pub (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (c : Block S ProofFile.Cl) (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (s₀ : S)
    (hg : s₀.failed = none → ∀ L, s₀.link? = some L → L.check.frame.group = N.groupAt l)
    (hOrd : ∀ x', YesOf (blkL Z G l d X arrs) (z, s₀) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s₀) → Mg.inOrder x' = true)
    (hRide : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s₀) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s₀) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true)
    (hNew : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s₀) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s₀) →
      q ∈ tiedL Mg.more l d → Mg.pub q x' = true) :
    IM.HandsPt N linksFull (flatPlacesOf linksFull true)
      (EPub z Mg linksFull (flatPlacesOf linksFull true)) ft (noL l d) c s₀ := by
  have hpubs : ∀ q ∈ (First.pubSets Mg.more linksFull
        (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        q ∈ tiedL Mg.more l d := by
    cases d with
    | true => exact (K1.rowL_digits_full N Mg.more l hl _ _ hinj trees msgs).pubs
    | false => exact (K1.rowL_reads_full N Mg.more l hl _ _ hinj trees msgs).pubs
  refine handsPt_of_all s₀ fun E₀ h1 h2 =>
    K1.hands_later N E₀ ft Z G l hl d X arrs c hu hinj trees msgs hP
      (fun s h0 hx => ?_) fun s s' hy h0 _ hx => ?_
  · obtain ⟨rfl, _⟩ := h1 s (IM.xk_parts hx).2.2.2.2
    exact hg h0
  · obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
    have hY : YesOf (blkL Z G l d X arrs) (z, s) (z, s') := K1.yesOf_of_yes hu hy z
    have hI : InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) :=
      ⟨xk_swap hx he, h0⟩
    rw [h2]
    have key : ∀ q ∈ (First.pubSets Mg.more linksFull
        (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
        Mg.pub q (z, s') = true := by
      intro q hq
      rcases hpubs q hq with hq' | hq'
      · exact hRide _ q hY hI hq' hq
      · exact hNew _ q hY hI hq'
    exact epub_of (hOrd _ hY hI) (fun q hq => key q (List.mem_append_left _ hq))
      fun q hq => key q (List.mem_append_right _ hq)

/-- **THE SIX TESTS AT THE NEXT BORDER, BEHIND AN ACCEPTING STEP**: from the six in front and facts
at that one state. -/
theorem xk_later_at (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (c : Block S ProofFile.Cl) (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (s s' : S)
    (hg : s.failed = none → ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hOrd : ∀ x', YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) → Mg.inOrder x' = true)
    (hRide : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true)
    (hNew : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) →
      q ∈ tiedL Mg.more l d → Mg.pub q x' = true)
    (hy : IM.Yes ft c s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksFull (flatPlacesOf linksFull true)
      (P1K2.EQ Mg linksFull (flatPlacesOf linksFull true) z) (noL l d) s = true) :
    IM.XK N linksFull (flatPlacesOf linksFull true)
      (P1K2.EQ Mg linksFull (flatPlacesOf linksFull true) z) (noL l d + 1) s' = true := by
  rw [← epub_eq] at hx ⊢
  have H := handsPt_later_pub N Mg z ft Z G l hl d X arrs c hu hinj trees msgs hP s hg hOrd hRide
    hNew
  unfold IM.XK IM.BK
  rw [H.shape s' hy h0 h1 hx, H.rows s' hy h0 h1 hx, H.members s' hy h0 h1 hx,
    H.book s' hy h0 h1 hx, H.more s' hy h0 h1 hx]
  rfl

/-- The same at a member that is seated alone over the lot's sub-protocol. -/
theorem xk_later_seated (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (b : Block S ProofFile.Cl) {name : String} {a : Place}
    (hla : IM.LaidAlone ProofFile.sameReply b ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl) name a)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (s s' : S)
    (hg : s.failed = none → ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hOrd : ∀ x', YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) → Mg.inOrder x' = true)
    (hRide : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true)
    (hNew : ∀ x' q, YesOf (blkL Z G l d X arrs) (z, s) x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) →
      q ∈ tiedL Mg.more l d → Mg.pub q x' = true)
    (hy : IM.Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksFull (flatPlacesOf linksFull true)
      (P1K2.EQ Mg linksFull (flatPlacesOf linksFull true) z) (noL l d) s = true) :
    IM.XK N linksFull (flatPlacesOf linksFull true)
      (P1K2.EQ Mg linksFull (flatPlacesOf linksFull true) z) (noL l d + 1) s' = true :=
  xk_later_at N Mg z ft Z G l hl d X arrs b (IM.alone_underR hla) hinj trees msgs hP s s' hg hOrd
    hRide hNew hy h0 h1 hx

/-- **THE SAMPLES ARE HELD BEHIND**: the old ride, the place's own are laid. nT, nM: by how many
the two counts go on. -/
theorem held_later (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (l : ℕ) (hl : l < 25) (d : Bool)
    (nT nM : ℕ)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + nT)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + nM)
    (s s' : S)
    (hin : samplesHeld N Mg (IM.openAt linksFull (flatPlacesOf linksFull true) (noL l d)) (z, s) =
      true)
    (old : ∀ u ∈ sampledIn N (IM.openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      Mg.held u.1 u.2 (z, s) = true → Mg.held u.1 u.2 (z, s') = true)
    (new : ∀ u ∈ N.sent l (momL d), Mg.held u.1 u.2 (z, s') = true) :
    samplesHeld N Mg (IM.openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) (z, s') =
      true := by
  have hs : ∀ x ∈ sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      x ∈ sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        x ∈ N.sent l (momL d) := by
    cases d with
    | true => exact (K1.rowL_digits_full N Mg.more l hl nT nM hinj trees msgs).sampled
    | false => exact (K1.rowL_reads_full N Mg.more l hl nT nM hinj trees msgs).sampled
  unfold samplesHeld at hin ⊢
  refine List.all_eq_true.2 fun u hu => ?_
  rcases hs u hu with h | h
  · exact old u h (List.all_eq_true.1 hin u h)
  · exact new u h

/-- **The sentence of the public item leftOn m over an accepting step** of a member under the lot's
sub-protocol. -/
theorem leftOn_later_yes (X3 : OnBytes.Model.Verify.Public) (m : ℕ) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (c : Block S ProofFile.Cl)
    (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl)) (s s' : S)
    (hy : IM.Yes ft c s s') (hz : ledgerB s = true) (h0 : k3LeftOnItemAt X3 m s) :
    k3LeftOnItemAt X3 m s' := by
  obtain ⟨-, rs, gs, -, hd⟩ := K1.yesOf_of_yes hu hy ()
  exact K1.leftOn_blkL X3 m Z G l d X arrs s s' _ gs hd hz h0

end ProofFile.Honest.K1
