-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsMean.lean: as to (i), smpIs and hread are
shown at no filling. (Where this and
lean/THEOREM.md differ, the page holds.)
The lookup on the digits of a link's smallness test AT THE TABLE OF JOINTS:
FOUR MORE OF THE ROW's PREMISES (k3_digits_seatLaws: hsmp, hS, hH, hSeat), in that theorem's own
binders' form.
  (i) digits_reader: hsmp ∧ hS ∧ hH AT THE MEANT READER OF SAMPLES: where the row's smp is the
  table's smpT at the link's own list (smpIs) and smpT reads of the record st and book alone
  (hread). General in the piece's number and in the kind's parameters; blockVia's planOk is not
  spent.
  (ii) digitsOpenB links ps k m: A Bool ON THE TABLE ALONE: in front of block k the three pins of
  segment m (moments 2, 0, 1) are among the open items. digits_open_of: its law. digits_hSeat:
  hSeat, from it and «every seat of the list is a tenant that segment m sends at one of its three
  moments» (DigSits.sent).
  digitsAtB links m: the Bool at the index's own number of the digits' lookup's address ⟨1, some m,
  7 + shift sub, .K3⟩. digitsAt_small | digitsAt_full: IT SAYS YES AT ALL 5 | 25 SEGMENTS of the two
  written lists (Johnson/Desc/Sound/AtDriver.lean: linksSmall, linksFull): by Lean's own evaluation
  (decide).
  digitsK l := 14 l + i + 2 (i := 6; 7 at the head's link) · digitsBorder_full: the index's own
  number of the address IS digitsK l · digitsOpen_full: the Bool at linksFull, flatPlacesOf
  linksFull true and digitsK l: THE LETTERS OF THE FIELD hSeat OF DigMean
  (K3Means.lean: PS; k3K l true: K3Base.lean), if IM.k3Ix l true is 6, and 7 at the head: NOT HELD
  HERE (that constant: Johnson/IMR/K3Seat.lean).
  calls_reader: the like of hsmp at the seat of the lookup on the calls, for every reader that hangs
  on st and book alone.
  THE CONTROLS, SO THAT THE Bool CAN SAY NO: digitsOpen_next: at the NEXT segment's number it says
  no (its messages are not yet sent) · digitsOpen_start: at border 0 it says no · digitsAt_wrong: at
  a piece at which no block of the kind stands it says no.
OBJECT: First.openSets | start | borderAt | flatPlaces (Johnson/Desc/First/Borders.lean) at two
written lists of segments · K3.Law.blockVia at the digits' seat. USER: digMeanR_of_rest
(K3DigitsRestR.lean) calls digits_reader, digits_open_of and digits_hSeat; digitsOpenB stands in
K3DigitsClosed.lean and Johnson/Desc/Sound/MgAt/K3Owed.lean. No other file calls calls_reader,
digitsAddr, digitsAtB, digitsK or an evaluation at them (digitsAt_small … digitsAt_wrong).
LETTERS: (i): z₀, smp, smpT, f, claim, piece, p · (ii): links, ps, k, m, N, seatT.
Limits. (i) z₀: the public part's type must have a member. (ii) The evaluation stands at
flatPlacesOf links true, at two lists: that these are a description's own index and links is not
said here. Nothing on soundness, completeness or hiding.
Read for this comment in a state that need not be this library's:
Johnson/Desc/Block.lean · First/State.lean ·
First/Borders.lean · Sound/MeaningSig.lean ·
Sound/BordersFill.lean · Sound/TiedSeat.lean ·
Look/K3Caller.lean · Look/K3OwnIs.lean ·
Look/K3QuietLaws.lean · Look/K3ReplyLeaves.lean · Top/H/K3PieceHears.lean.
Compiled with the whole library.
-/
import Johnson.Desc.First.Look.K3DigitsSig
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (digList digSg)
open VerifiableInference.Desc.First (S ModelPart Item Numbers openSets start sampledIn flatPlacesOf
  borderAt shift)

/-! ## (i) The three premises on the reader of samples, at the meant reader -/

section
variable {P Cl : Type} {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {seatT : Fin (digList x D rad).length → ℕ × ℕ}
  {smpT : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp}
  {smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp}

theorem digits_reader (z₀ : P)
    (smpIs : ∀ (z : P) (s : S) i, smp s i = smpT (z, s) (digSending x D rad seatT) i)
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf D.codes s.l).om i).Smp)
    (hread : ∀ z s, smpT (z, s) = f z (s.st, s.book))
    (claim : Aff → Cl) (piece : ℕ) (p : Desc.First.Look.P) :
    (∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) piece laid sent p []).planOk =
        true →
      ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) piece laid sent p
        []).decide s rs cols = .ok s' → smp s' = smp s) ∧
    (∀ s Gk, smp (S.putFork s Gk) = smp s) ∧
    (∀ (s : S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s) := by
  have key : ∀ s t : S, (t.st, t.book) = (s.st, s.book) → smp t = smp s := by
    intro s t e
    funext i
    rw [smpIs z₀ t i, smpIs z₀ s i, hread, hread, e]
  refine ⟨fun sent laid _ s rs cols s' H => key s s' ?_, fun s Gk => key s _ ?_,
    fun s a c _ => key s _ rfl⟩
  · obtain ⟨g, G, rfl⟩ := Desc.K3.blockVia_put _ piece laid sent p [] H
    exact reads_digits_put (fun s : S => (s.st, s.book)) stBook_outside claim s g G
  · exact reads_putFork (fun s : S => (s.st, s.book)) stBook_outside s Gk

end

/-- The like of hsmp at the seat of the lookup ON THE CALLS, for every reader that hangs on st and
book alone (so for a reader of a stored table's sample too). -/
theorem calls_reader {Cl β : Type} (smp : S → β)
    (key : ∀ s t : S, (t.st, t.book) = (s.st, s.book) → smp t = smp s)
    (claim : Aff → Cl) (piece : ℕ) (p : Desc.First.Look.P) :
    ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent p []).planOk =
        true →
      ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid sent p
        []).decide s rs cols = .ok s' → smp s' = smp s := by
  intro sent laid _ s rs cols s' H
  obtain ⟨g, G, rfl⟩ := Desc.K3.blockVia_put _ piece laid sent p [] H
  exact key s _ (reads_calls_put (fun s : S => (s.st, s.book)) stBook_outside claim s g G)

/-! ## (ii) The seats are among the sampled tenants whose pins are open -/

/-- In front of block k the three pins of segment m are among the open items. -/
def digitsOpenB (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  [2, 0, 1].all fun t => ((openSets links ps (start links))[k]?.getD []).contains (.pin m t)

theorem digits_open_of {links : List ModelPart} {ps : List Place} {k m : ℕ}
    (h : digitsOpenB links ps k m = true) :
    ∀ t ∈ [2, 0, 1], Item.pin m t ∈ (openSets links ps (start links))[k]?.getD [] := by
  intro t ht
  have h1 := List.all_eq_true.1 h t ht
  simpa using h1

/-- **hSeat.** -/
theorem digits_hSeat {links : List ModelPart} {ps : List Place} {k m : ℕ} (N : Numbers) {ι : Type}
    (seatT : ι → ℕ × ℕ) (sent : ∀ i, ∃ t ∈ [2, 0, 1], seatT i ∈ N.sent m t)
    (hopen : ∀ t ∈ [2, 0, 1], Item.pin m t ∈ (openSets links ps (start links))[k]?.getD []) :
    ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []) := by
  intro i
  obtain ⟨t, ht, hm⟩ := sent i
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨_, hopen t ht, hm⟩

/-- The digits' lookup's address at segment m. -/
def digitsAddr (links : List ModelPart) (m : ℕ) : Place :=
  ⟨1, some m, 7 + shift (links.getD m .layers), .K3⟩

/-- The Bool at the index's own number of the address. -/
def digitsAtB (links : List ModelPart) (m : ℕ) : Bool :=
  ((borderAt (flatPlacesOf links true) (digitsAddr links m)).map fun k =>
    digitsOpenB links (flatPlacesOf links true) k m).getD false

theorem digitsAt_small : (List.range 5).all (digitsAtB linksSmall) = true := by decide +kernel

theorem digitsAt_full : (List.range 25).all (digitsAtB linksFull) = true := by decide +kernel

/-- The number of link l's lookup on the digits in the full size's list of places, written out:
14 l + i + 2, i := 6, and 7 at the head's link. -/
def digitsK (l : ℕ) : ℕ := 14 * l + (if l == 24 then 7 else 6) + 2

/-- **The index's own number of the address IS that number**, at all 25 links. -/
theorem digitsBorder_full : (List.range 25).all (fun l =>
    borderAt (flatPlacesOf linksFull true) (digitsAddr linksFull l) == some (digitsK l)) =
      true := by
  decide +kernel

/-- **The three pins are open at that number**, at all 25 links: the Bool in the very letters of the
assembly's field hSeat (linksFull · flatPlacesOf linksFull true · 14 l + i + 2). -/
theorem digitsOpen_full : (List.range 25).all (fun l =>
    digitsOpenB linksFull (flatPlacesOf linksFull true) (digitsK l) l) = true := by decide +kernel

/-! ## Controls: the Bool can say no -/

/-- At the NEXT segment's number it says no. -/
theorem digitsOpen_next : (List.range 4).all (fun m =>
    !((borderAt (flatPlacesOf linksSmall true) (digitsAddr linksSmall m)).map fun k =>
      digitsOpenB linksSmall (flatPlacesOf linksSmall true) k (m + 1)).getD false) = true := by
  decide +kernel

/-- At border 0 it says no. -/
theorem digitsOpen_start : (List.range 5).all (fun m =>
    !digitsOpenB linksSmall (flatPlacesOf linksSmall true) 0 m) = true := by decide +kernel

/-- At a piece at which no block of the kind stands it says no. -/
theorem digitsAt_wrong : (List.range 5).all (fun m =>
    !((borderAt (flatPlacesOf linksSmall true) ⟨1, some m, 99, .K3⟩).map fun k =>
      digitsOpenB linksSmall (flatPlacesOf linksSmall true) k m).getD false) = true := by
  decide +kernel

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digits_reader
#print axioms VerifiableInference.OnPublicFiles.digits_hSeat
#print axioms VerifiableInference.OnPublicFiles.digitsAt_small
#print axioms VerifiableInference.OnPublicFiles.digitsAt_full
#print axioms VerifiableInference.OnPublicFiles.digitsBorder_full
#print axioms VerifiableInference.OnPublicFiles.digitsOpen_full
#print axioms VerifiableInference.OnPublicFiles.calls_reader
#print axioms VerifiableInference.OnPublicFiles.digitsOpen_next
#print axioms VerifiableInference.OnPublicFiles.digitsOpen_start
#print axioms VerifiableInference.OnPublicFiles.digitsAt_wrong
