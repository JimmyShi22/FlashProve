-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A law about ProofFile's seat and the kind's block.
/-
Johnson/K11R/Sits.lean: THE STATEMENT K11_sits AT THE PROOF FILE's DESCRIPTION. A JOINING.
THE LETTERS. k11_of (Johnson/IMR/K11Seat.lean) names the lot's own block K11.blkAt Z "H.8.call" G₀ (Johnson/Desc/ProofFile/Lot/K11.lean): so SitsAs takes the lot's letters Z and G; «laid» speaks of blkAt; «plan» is an implication (b's yes on the plan gives the kind's, and that the step that is looked for is in the table); «step», «rounds», «run» speak of the kind's headClaimMergeKind (parOf Z G), by Johnson/Top/H0/MergeLaw/LotIs.lean.
THE STATEMENT's SENTENCE (from the list of what is owed, a text of this project that is not in this repository): «the entry of the description's list of blocks at each place of the kind is the constant of which K0x_law speaks, at the plan's numbers, under the seat's wrappers alone (another name and place; the mark's guard), or its yes gives that law's premise».
WHAT IS SAID.
  step_leaves       the kind's block headClaimMergeKind P, at its step, leaves the mark and the heard reply (by leavesSeven, Johnson/Top/H0/MergeLaw/Law.lean).
  SitsAs b Z G      what the sentence says of one block b: b IS the lot's block under the seat's wrappers alone (IM.LaidAlone: another name and place; the mark's guard; the guard on the heard reply) · its rounds are the kind's block's · its yes on the plan gives that block's · AS A STEP: b's yes is headClaimMergeKind (parOf Z G)'s yes at the same record, rounds and columns, with the same record behind and as many columns taken, AND NO MARK IN FRONT, both ways: so the guards add just «it refuses at a marked record» · its run of claims "the merge" says yes just where the kind's headMergeClaim does, with the same claims and record.
  sitsAs_of_laid    LaidAlone gives SitsAs.
  K11_sits          in scope (VerifierAndGoals.InScope P · readFiles P = .ok pp), where ProofFile.onlineDescription secondHashFunction P.pol lay P.KL = .ok F: F is fileDescBy … c, and c.blocksInOrder[346]? = some b with SitsAs b Z G₀; (K11.parOf Z G₀).link = 24; Z is pubPlain's value at the three files; G₀ the blank ground of Z; G₀.W is publicOf's value.
WHOSE. (I) THE SEAT: seat_open · k11_of · hear_at_flat · flatIx_scope · (II) THE WRAPPERS: LaidAlone · step_alone · claims_lookup · guardRun_yes · alone_rounds | alone_planOk: those of the files of Johnson/IMR/: CALLED. (III) K11's FILES': that behind the wrappers stands the laws' own constant but for one clause of the test on the plan (Johnson/Top/H0/MergeLaw/LotIs.lean); that the guards are idle at an unmarked record (step_leaves; claim_inv).
LIMITS. «onlineDescription returns in scope» is a premise. The reference shape alone (25 links; the number 346). At the hash secondHashFunction. The piece and the numbers: Johnson/K11R/Tied.lean. No soundness. Nothing on hiding.
-/
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Top.H0.MergeLaw.Run
import Johnson.Top.H0.MergeLaw.LotIs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (leavesSeven claim_inv)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide headMergeClaim)
open ProofFile (Cl)

/-- The merge's block leaves the mark and the heard reply: at its step. -/
theorem step_leaves (P : HeadMergeP) {ft : Nat} {s t : S} {k : Nat} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (h : (headClaimMergeKind P).step ft s rs cols = .ok (t, k)) :
    t.failed = s.failed ∧ ProofFile.sameReply s t = true := by
  obtain ⟨_, hd, _⟩ := (VerifiableInference.Desc.step_iff ft (headClaimMergeKind P) s t rs cols k).1 h
  obtain ⟨_, _, _, h4, _, h6, _⟩ := leavesSeven P s _ _ t hd
  refine ⟨h4, ?_⟩
  unfold ProofFile.sameReply
  rw [h6]
  exact beq_self_eq_true _

/-- **What the row says of one block b of a chain's flat list**, Z and G the lot's letters: b is the
lot's block blkAt Z "H.8.call" G under the seat's wrappers alone (another name and place; the mark's
guard and the guard on the heard reply); that block is the kind's headClaimMergeKind at the lot's numbers in
every field but its test on the plan (MergeLaw/LotIs.lean); AS A STEP b is the kind's block at every
record that bears no mark, and refuses at a marked one; its rounds are that block's; its yes on the
plan gives that block's, and that the step that is looked for is in the table; its one run of claims
is the kind's headMergeClaim. -/
structure SitsAs (b : Block S Cl) (Z : ProofFile.Pub) (G : ProofFile.Ground) : Prop where
  laid : IM.LaidAlone ProofFile.sameReply b (blkAt Z "H.8.call" G) b.name IM.k11Place
  rounds : b.rounds = (headClaimMergeKind (parOf Z G)).rounds
  plan : b.planOk = true →
    (headClaimMergeKind (parOf Z G)).planOk = true ∧ (sentAt? Z "H.8.call").isSome = true
  step : ∀ (ft : Nat) (s t : S) (k : Nat) (rs : List Fmt.RoundView)
      (cols : List VerifiableInference.Desc.OpenedColumn),
    b.step ft s rs cols = .ok (t, k) ↔
      (headClaimMergeKind (parOf Z G)).step ft s rs cols = .ok (t, k) ∧ s.failed = none
  run : ∃ r, b.claims.lookup "the merge" = some r ∧ ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y

theorem sitsAs_of_laid {b : Block S Cl} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hla : IM.LaidAlone ProofFile.sameReply b (blkAt Z "H.8.call" G) b.name IM.k11Place) :
    SitsAs b Z G := by
  refine ⟨hla, (IM.alone_rounds hla).trans (blkAt_fields Z G).2.1, fun hp => (blkAt_planOk Z G).1 (by
    rw [← IM.alone_planOk hla]
    exact hp), ?_, ?_⟩
  · intro ft s t k rs cols
    rw [IM.step_alone hla (by decide) ft s t k rs cols, blkAt_step]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h1, by rw [← (step_leaves _ h1).1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [(step_leaves _ h1).1]; exact h2, (step_leaves _ h1).2⟩
  · refine ⟨IM.guardRun ProofFile.sameReply headMergeClaim, ?_, ?_⟩
    · rw [IM.claims_lookup hla]
      rfl
    · intro n t y
      rw [IM.guardRun_yes]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        obtain ⟨a, wo, G', _, _, h3, _⟩ := claim_inv (cls := y.1) (s' := y.2) h
        unfold ProofFile.sameReply
        rw [h3]
        exact beq_self_eq_true _

/-- **K11 SITS, AT THE PROOF FILE's DESCRIPTION's OWN VALUE**: in scope, where
onlineDescription returns F: F is the written description over a first chain c, and entry number 346 (from 0)
of c's flat list of blocks sits as the kind's block at the lot's numbers parOf Z G₀, whose link is 24:
Z: what is public, made of the three files; G₀: the blank ground of Z (a request of zeros), whose
record W is `verify-on-bytes`'s publicOf's value at the same files. -/
theorem K11_sits {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (b : Block S Cl),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧
      OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok G₀.W ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder[346]? = some b ∧ SitsAs b Z G₀ ∧ (parOf Z G₀).link = 24 := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  obtain ⟨Lk, b, e1, e2, hla, hl⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  exact ⟨Z, Bs.G₀, c, A, B, b, O.pub, O.blank, O.public, O.desc, h3, sitsAs_of_laid hla, hl⟩

end K11

#print axioms K11.step_leaves
#print axioms K11.sitsAs_of_laid
#print axioms K11.K11_sits
