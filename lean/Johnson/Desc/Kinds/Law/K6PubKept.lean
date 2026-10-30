-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubKept.lean: WHICH PUBLIC TESTS ARE OPEN BEHIND THE SUB-PROTOCOL AT THE
OUTPUT HEAD, BY NAME; AND FIVE OF THEM, OTHER PARTS', THAT IT KEEPS.

Why. The bill for that sub-protocol asks "every public test that is open behind holds
there" as one premise over a list (K6DueAt.pubBehind). At the closed list of extra public tests
(Johnson/Desc/Sound/MgAllAt.lean: mgMore) that list is a written one: fifteen items. Nine of them
are open in front as well (ledger 24, linkFresh 24, freeAbove 24, the two names at 24, lookOut 24 3,
indexIs, indexThere, formsInT 24 3 "objects").

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  open342: THE FIFTEEN, at the full chain: by evaluation in the kernel. open341: the twelve in
      front.
  k6_sameOn: an accepting step of the piece leaves five of the seven readers of the
      verifier's state (Johnson/Desc/First/PubFoot.lean: the statement; what goes on to the later
      chains; the frame between segments; the open segment's link context; its parameters of the
      approximate range proof): it writes the ledger, what is heard and the squares' sumcheck alone.
  kept_four: SO linkFresh 24, "frame.sentIs" at 24, indexIs and indexThere stay true (by
      rides_of_B; its test on the two lists by the kernel), WHERE THE INNERMOST MEANING's PUBLIC
      TESTS DO NOT READ WHERE THE CHAIN STANDS (hPub: that rule's premise on the base test).
  kept_trees: "ledger.treesAre" at 24 stays true: that test reads the ledger, which the step writes:
      by hand: the step leaves the ledger's trees (blockOf_trees).

Every letter under "there is": none.
What it does not say. lookOut 24 3 and formsInT 24 3 "objects", which are open on both sides too,
are not booked in that rule: NOT KEPT HERE. What the sub-protocol makes (lookIn 24 8; four
items formsInT): not here. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6HeardOfLookOut
import Johnson.Desc.Kinds.Law.K6LedgerAt
import Johnson.Desc.Kinds.Law.KeepsTrees
import Johnson.Desc.First.PubFoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub Rdr SameOn pubOfItems)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll pubQ openQ linksFull)

/-- **The fifteen public tests that are open at border 342 of the full chain.** -/
theorem open342 : pubQ Sound.mgMore linksFull (First.flatPlacesOf linksFull true) 342 ++
      pubOfItems (openQ linksFull (First.flatPlacesOf linksFull true) 342) =
    [.ledger 24, .linkFresh 24, .freeAbove 24, .more (some 24) "frame.sentIs",
      .more (some 24) "ledger.treesAre", .lookOut 24 3, .lookIn 24 8, .leftOn 24, .indexIs,
      .indexThere, .formsInT 24 3 "objects", .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join", .formsInT 24 4 "weights"] := by
  decide +kernel

/-- The twelve that are open at border 341. -/
theorem open341 : pubQ Sound.mgMore linksFull (First.flatPlacesOf linksFull true) 341 ++
      pubOfItems (openQ linksFull (First.flatPlacesOf linksFull true) 341) =
    [.tokenSmall, .ledger 24, .linkFresh 24, .freeAbove 24, .more (some 24) "frame.sentIs",
      .more (some 24) "ledger.treesAre", .lookOut 24 3, .look 24, .left 24, .indexIs, .indexThere,
      .formsInT 24 3 "objects"] := by
  decide +kernel

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **What an accepting step leaves.** -/
theorem k6_sameOn (Dp : First.PubData) (H : Seated Wp fld Fr q l bef B bS)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (h : q.ior.red.out a τ = some b) :
    SameOn Dp [.st, .out, .frame, .link, .tl] a.1.2 b.1.2 := by
  obtain ⟨o, F1, X, Q, ho, _, _, e⟩ := k6_behind H a b τ h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · show b.1.2.st = a.1.2.st
    rw [e]
  · show b.1.2.out = a.1.2.out
    rw [e]
  · show b.1.2.check.frame = a.1.2.check.frame
    rw [e]
  · show b.1.2.link? = a.1.2.link?
    rw [e]
    unfold First.S.link?
    rw [ho]
  · show b.1.2.tl? = a.1.2.tl?
    rw [e]
    unfold First.S.tl?
    rw [ho]

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {l : ℕ} {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **Four of other parts' tests stay true.** -/
theorem kept_four (H : Seated Wp fld Fr q l bef B bS)
    (hPub : ∀ (j : Pub) (z : P) (t : S) h, Mg.pub j (z, { t with here := h }) = Mg.pub j (z, t))
    (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) (i : Pub)
    (hi : i ∈ [Pub.linkFresh 24, .more (some 24) "frame.sentIs", .indexIs, .indexThere])
    (ht : (mgAll D Mg).pub i a.1 = true) : (mgAll D Mg).pub i b.1 = true := by
  obtain ⟨o, F1, X, Q, _, _, _, e⟩ := k6_behind H a b τ h
  have e1 : b.1 = (a.1.1, b.1.2) := by rw [e]
  rw [Sound.mgAll_pub] at ht ⊢
  rw [e1]
  exact First.rides_of_B D.pubD Mg.pub [.st, .out, .frame, .link, .tl] _ rfl a.1.1 a.1.2
    b.1.2 (k6_sameOn D.pubD H a b τ h) (fun j _ => by rw [e]; exact hPub j a.1.1 a.1.2 _) i hi ht

/-- **The test on the ledger's trees stays true.** -/
theorem kept_trees (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (ht : (mgAll D Mg).pub (.more (some 24) "ledger.treesAre") a.1 = true) :
    (mgAll D Mg).pub (.more (some 24) "ledger.treesAre") b.1 = true := by
  rw [Sound.mgAll_pub, First.pubAll_more_treesAre] at ht ⊢
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  have et := blockOf_trees Wp l b6 h6 a.1.2 b.1.2 rs gs hd'
  obtain ⟨F1, hF1⟩ := fork_behind H a b τ h
  unfold First.FillSent.treesAreB at ht ⊢
  cases hF : a.1.2.fork? with
  | none =>
    rw [hF] at ht
    cases ht
  | some F =>
    rw [hF] at ht et
    rw [hF1] at et ⊢
    have et' : F1.trees = F.trees := et
    show Decidable.decide (F1.trees.toList.map _ = _) = true
    rw [et']
    exact ht

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.open342
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.open341
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_sameOn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_four
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_trees
