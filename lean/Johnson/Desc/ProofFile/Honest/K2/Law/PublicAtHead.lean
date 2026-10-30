-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PublicAtHead.lean: the kind "the code switch" (K2): UNDER THE
HEAD `P5J.AtMg` AND THE OPENING IN ITS LETTERS: FIVE OF THE PUBLIC PREMISES THAT THE DEBT "IT PLAYS"
LEAVES AT THE 23 LINKS (`switch_playsS`, Honest/K2/Law/PlaysScript.lean),
EACH IN THAT FILE's OWN TERM: `Sizes.serves` · `Sizes.roomy` · `placeFits`:
at EVERY member of `switchPlaces Zp Bs.G₀` (all 25 places) · the honest sending's number of answers
is the plan's: at every member, at the plan's numbers at its link · every tree that the switch into
a later group reads is stated in front of it, by the frame's own count `treesTo` · AND: the list has
one member alone at a place. Joins of two files: the closed terms under the head, and the kernel's
tests at them. The first three serve wherever a law asks these tests at a member of the plan's list.
Statements with their proofs: calls.

  `serves_at_head`, `roomy_at_head`, `fits_at_head` ∀ p ∈ switchPlaces Zp Bs.G₀: the test says yes
  `numsW_at_head` the plan's numbers at a link are the written plan's
  `answers_at_head` ∀ p ∈ switchPlaces Zp Bs.G₀, at the numbers n that the plan has at p's link: the
                    honest sending's answers are n's
  `link_answers`, `link_opens` the two at a link: i < 23 · q
                    := k2P Zp (switchPlaceAt (i + 1)) nm .link n
  `place_alone` two members of switchPlaces Zp Bs.G₀ at one place are one

By: `places_at_head`, `prep_at_head`, `treesTo_at_head` (Honest/K2/Law/PlacesWritten.lean) ·
`servesW`, `roomyW`, `fitsW`, `answersW`, `opensW`, `spotsW_nodup`
(Honest/K2/Law/PublicAtWritten.lean: each by Lean's kernel; the first five each with a control
there, `spotsW_nodup` with none) · the library's `prepW_some` (Johnson/Desc/K1/Law/SitsSwitch.lean).

Limits. THEY SAY THAT PUBLIC TESTS PASS: nothing on what a prover sends, nothing on a run. CLOSED
FACTS BY LEAN's KERNEL LIE BENEATH, REPLAYED BY NO INDEPENDENT CHECKER. THE HEAD IS SHOWN MET BY
NOBODY HERE. The closing's test (`closingOk`) is another file's. OF THE SIXTEEN PREMISES OF
`switch_playsS` (Honest/K2/Law/PlaysScript.lean) THESE ARE FIVE (hs, hr, hf, hA, hopens); nothing is
joined to it here (the join: `switch_playsS_at`, Honest/K2/Law/PlaysAtArms.lean, which spends four
of these five). `Sizes.roomy` calls the
verifier's own test at stand-ins (Honest/K2/Part.lean says what that leaves). The full size alone;
the format's second hash function alone. It stands on files of this folder:
PublicAtWritten.lean and others beneath it, among them PlacesCount.lean,
PlanAsks.lean and PlaysAtPlan.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtWritten
import Johnson.Desc.K1.Law.SitsSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt)
open Johnson.AtFull.Desc (spotsWritten)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- At every member of the plan's list the test `Sizes.serves` says yes. -/
theorem serves_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.sizes.serves = true := by
  rw [places_at_head h O]
  exact List.all_eq_true.1 servesW

/-- At every member of the plan's list the test `Sizes.roomy` says yes. -/
theorem roomy_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.sizes.roomy = true := by
  rw [places_at_head h O]
  exact List.all_eq_true.1 roomyW

/-- At every member of the plan's list the test `placeFits` says yes. -/
theorem fits_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, placeFits p = true := by
  rw [places_at_head h O]
  exact List.all_eq_true.1 fitsW

/-- The plan's numbers at a link are the written plan's. -/
theorem numsW_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} (hP : prepOf Zp Bs.G₀ = some Pp) (l : Option Nat) : numsW l = numsAt Pp l := by
  unfold numsW
  rw [(prep_at_head h O).symm.trans hP]
  rfl

/-- **The honest sending's number of answers is the plan's, at every place.** -/
theorem answers_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} (hP : prepOf Zp Bs.G₀ = some Pp) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n : Nums, numsAt Pp p.place.link = some n →
      (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers = n.answers := by
  intro p hp n hn
  rw [places_at_head h O] at hp
  have t : (numsW p.place.link).any (fun n => answersFit p n) = true :=
    List.all_eq_true.1 answersW p hp
  rw [numsW_at_head h O hP, hn] at t
  exact beq_iff_eq.1 t

/-- The same at a link's place, `switchPlaceAt (i + 1)`. -/
theorem link_answers (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hpp : p.place = switchPlaceAt (i + 1)) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (i + 1)) = some n) :
    (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers =
      (k2P Zp (switchPlaceAt (i + 1)) nm .link n).answers :=
  answers_at_head h O hP p hp n (by rw [hpp]; exact hn)

/-- **Every tree that the switch into a later group reads is stated in front of it.** -/
theorem link_opens (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (h23 : i < 23) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (i + 1)) = some n) :
    ∀ t ∈ (k2P Zp (switchPlaceAt (i + 1)) nm .link n).read,
      t.1 < treesTo cF.blocksInOrder (14 * (i + 1) + 2) := by
  intro t ht
  rw [treesTo_at_head h O]
  have a : (numsW (some (i + 1))).any (fun n => n.read.all fun t =>
      decide (t.1 < treesTold toldFull (14 * (i + 1) + 2 - 0))) = true :=
    List.all_eq_true.1 opensW i (List.mem_range.2 h23)
  rw [numsW_at_head h O hP, hn] at a
  exact of_decide_eq_true (List.all_eq_true.1 a t ht)

/-- **One member alone at a place.** -/
theorem place_alone (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ p' ∈ switchPlaces Zp Bs.G₀, p.place = p'.place → p = p' := by
  rw [places_at_head h O]
  obtain ⟨Pw, hw⟩ := Option.isSome_iff_exists.1 VerifiableInference.Desc.K1.prepW_some
  unfold placesW
  rw [hw]
  intro p hp p' hp' e
  obtain ⟨sp, hs, rfl⟩ := List.mem_map.1 hp
  obtain ⟨sp', hs', rfl⟩ := List.mem_map.1 hp'
  have es : sp = sp' := List.inj_on_of_nodup_map spotsW_nodup hs hs' e
  rw [es]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.serves_at_head
#print axioms ProofFile.Honest.K2.Law.roomy_at_head
#print axioms ProofFile.Honest.K2.Law.fits_at_head
#print axioms ProofFile.Honest.K2.Law.numsW_at_head
#print axioms ProofFile.Honest.K2.Law.answers_at_head
#print axioms ProofFile.Honest.K2.Law.link_answers
#print axioms ProofFile.Honest.K2.Law.link_opens
#print axioms ProofFile.Honest.K2.Law.place_alone
