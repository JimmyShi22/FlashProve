-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFirstFromLeft.lean: THE LEDGER OF THE KEY FILE's FIRST CHAIN, AS A THEOREM: at the thread Th
(E2E/FirstHSeat.lean), all that MembersS (E2E/KeyAcceptFamilies.lean) asks of the first chain's nineteen members,
FROM A STRUCTURE WHOSE FIELDS ARE THE ROWS THAT ARE STILL UNPAID. Every paid row is discharged inside. So Lean
keeps the table: a later theorem that pays a row strikes a field.

  `FiveAt T Said fall b`: the five debts at one member.
  `seal_plays`: the seal, member 18, plays: no half of the prover stands at its place (a proof taken over within this project).
  `LeftFirst`: WHAT IS LEFT, nine fields:
      playsK3         the two lookups' members 4, 10 play
      keepsKind       behind a step of member 4, 10 or 15 the letter Q.kind₁ holds of the two states
      exchangeK3      what rows 4, 10 owe (forms, worth)
      ridesKind       what rides past 4, 10, 15
      exchangeLayer   what rows 5, 11 owe (rows, kclaims): the layers' exchange
      playsRanges, acceptedRanges   the ranges' test, member 15, plays and is accepted
      pile            what row 16 owes (the item "pile" among it)
      eval            the claim (Eval) behind W's step, member 17
  **`firstFromLeft`**: OwesS Th Said ∧ YesS Th Said fall, at every letter Said and every fall.
  `firstFromLeft_walked`: with SaidNext at every member, at the letter WalkedFrom Th Begun.

PAID INSIDE, AND BY WHAT. 0, 1: rows_idx, rows_msg (E2E/FirstHRows.lean) · 2, 3, 6, 7, 8, 9, 12, 13: fiveQuiet_Th; 5, 11
but for the exchange: fourLayer_Th (E2E/LotQuietFirst.lean) · 14: five14 (E2E/LotMemberFourteenGrows.lean) · 16 but for the
exchange: E2E/FirstHBatt.lean · 17 but for (Eval): E2E/FirstHWRow.lean, seat_w · acceptance at 4, 10: accepted_first
(E2E/KeyShapeFirstAccepted.lean) with halved_first (E2E/LotMemberFourteen.lean) · the form behind 4, 10, 15: form_behind₁ ·
rows 15 and 18 owe nothing · 18: seal_plays (plays_seal₁), behind₁, ridesPast₁, accepted_first.

HOW FINE THE FIELDS ARE. eval is asked from Thr, not from ThrS: exchange_w's own premise to the letter: more than
ExchangeS at 17 needs. pile is the WHOLE cell ExchangeS at 16, though row 16 owes three items, of which pinT is idle at
this thread (pinT_item, E2E/FirstHBatt.lean) and pin 0 was open in front: it is not cut to the item "pile" here. Typed payers
of some fields lie in other files (accepted_15, pile_item, eval_item); yes_first is not in this library.
SaidNext is had at one letter, WalkedFrom, by its constructor.

Limits. AN IMPLICATION. A member of LeftFirst at the laid letters comes by leftFirst_of_struck (E2E/LotFirstFromLeftStruck.lean) and leftStruck_of_join (E2E/LotJoinFirst.lean) from leftJoin_laid (E2E/LotJoinLaid.lean). keepsKind speaks of Q.kind₁, A FREE LETTER of LaterFill: it
is to be proved and ridesKind is to be proved FROM it, so both wait for a term in its place. FirstPublic is a premise.
ThrS in front, the premise inside every debt, is met by nothing here. In scope, at the written sizes. Nothing on the
shared or the last chain, on AtRunS, on any fall's measure. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.FirstHBatt
import E2E.FirstHWRow
import E2E.LotQuietFirst
import E2E.LotMemberFourteen
import E2E.WalkedFrom
import E2E.KeyPlaysQuiet
import E2E.KeyThreadFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces)
open AtPublicFiles.KeyThread (rowsFirst form_behind₁ exchange_of_nil behind₁ ridesPast₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (accepted_first)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- The five debts at one member. -/
def FiveAt {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (fall : Nat → S → List Fmt.Drawn → Option String)
    (b : Nat) : Prop :=
  PlaysS T Said b ∧ BehindS T Said b ∧ ExchangeS T Said b ∧ RidesPastS T Said b ∧
    AcceptedS T Said fall b

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **WHAT IS LEFT AT THE FIRST CHAIN.** A premise's form. leftFirst_of_struck (E2E/LotFirstFromLeftStruck.lean) gives a member from LeftStruck. -/
structure LeftFirst (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) : Prop where
  playsK3 : ∀ b ∈ [4, 10], PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b
  keepsKind : ∀ b ∈ [4, 10, 15], ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk →
    ∀ k s m E ds y cols s', ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E →
      drawsFit blk.rounds ds = true → (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      Q.kind₁ b s s'
  exchangeK3 : ∀ b ∈ [4, 10], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b
  ridesKind : ∀ b ∈ [4, 10, 15], RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b
  playsRanges : PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 15
  acceptedRanges : AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 15
  pile : ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 16
  eval : ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[17]? = some blk → ∀ k s m E ds y cols s',
    Thr (Th Xs N Pl K f Q w₀ rc x) 17 k s m E → drawsFit blk.rounds ds = true →
    (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
    (Th Xs N Pl K f Q w₀ rc x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1)

variable {Xs N Pl K f Q w₀ rc x} {Z : PublicFiles}

/-- **The seal plays**: no half of the prover stands at its place. -/
theorem seal_plays (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop) :
    PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 18 := by
  have hn : ((AtPublicFiles.KeyFile.keyProver K).first.find? fun g =>
      g.place == (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl).first.last.place) = none := by
    rw [List.find?_eq_none]
    intro g hg
    have hm : g.place ∈ (AtPublicFiles.KeyFile.keyProver K).first.map (·.place) := List.mem_map_of_mem hg
    rw [AtPublicFiles.KeyFile.first_places K hp.places] at hm
    have hl : (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl).first.last.place =
        (⟨1, none, 15, .frame⟩ : VerifiableInference.Desc.Place) := rfl
    rw [hl]
    revert hm
    generalize g.place = p
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h := AtPublicFiles.KeyThread.plays_seal₁ (Th Xs N Pl K f Q w₀ rc x) rfl hn
  rw [(AtPublicFiles.KeyThread.lengths scope hs.named).1] at h
  exact playsS_of _ _ h

/-- The five at every member, from what is left. -/
theorem fiveFromLeft (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftFirst Xs N Pl K f Q w₀ rc x Said fall) :
    ∀ b, b < 19 → FiveAt (Th Xs N Pl K f Q w₀ rc x) Said fall b := by
  have quiet := fiveQuiet_Th Xs N Pl K f Q w₀ rc x hs scope Said fall
  have layer := fourLayer_Th Xs N Pl K f Q w₀ rc x hs scope Said fall
  have acc : ∀ b, b < 19 → b ≠ 15 → AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall b :=
    fun b hb h15 => acceptedS_of _ _ (accepted_first hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
      (fun _ _ _ _ _ hbeg => ⟨_, hbeg⟩) fall hb h15
      (fitsAt_of_halved (Th Xs N Pl K f Q w₀ rc x) (halved_first scope hs.named K hp.places) b))
  have form : ∀ b, b < 19 → ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk →
      ∀ k s m E ds y cols s', ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E →
      (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      (Th Xs N Pl K f Q w₀ rc x).Form (b + 1) k s' y.2 :=
    fun b hb blk hblk k s m E ds y cols s' hA hS =>
      form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope hb hblk hA.1 hS
  have sw := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  intro b hb
  interval_cases b
  · exact rows_idx hs scope hp Said fall
  · exact rows_msg hs scope hp Said fall
  · exact quiet 2 (by decide)
  · exact quiet 3 (by decide)
  · exact ⟨left.playsK3 4 (by decide),
      fun blk hblk k s m E ds y cols s' hA hd hS =>
        ⟨form 4 (by decide) blk hblk k s m E ds y cols s' hA hS, trivial,
          left.keepsKind 4 (by decide) blk hblk k s m E ds y cols s' hA hd hS⟩,
      left.exchangeK3 4 (by decide), left.ridesKind 4 (by decide), acc 4 (by decide) (by decide)⟩
  · exact ⟨(layer 5 (by decide)).1, (layer 5 (by decide)).2.1, left.exchangeLayer 5 (by decide),
      (layer 5 (by decide)).2.2.1, (layer 5 (by decide)).2.2.2⟩
  · exact quiet 6 (by decide)
  · exact quiet 7 (by decide)
  · exact quiet 8 (by decide)
  · exact quiet 9 (by decide)
  · exact ⟨left.playsK3 10 (by decide),
      fun blk hblk k s m E ds y cols s' hA hd hS =>
        ⟨form 10 (by decide) blk hblk k s m E ds y cols s' hA hS, trivial,
          left.keepsKind 10 (by decide) blk hblk k s m E ds y cols s' hA hd hS⟩,
      left.exchangeK3 10 (by decide), left.ridesKind 10 (by decide),
      acc 10 (by decide) (by decide)⟩
  · exact ⟨(layer 11 (by decide)).1, (layer 11 (by decide)).2.1,
      left.exchangeLayer 11 (by decide), (layer 11 (by decide)).2.2.1,
      (layer 11 (by decide)).2.2.2⟩
  · exact quiet 12 (by decide)
  · exact quiet 13 (by decide)
  · exact five14 Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_fillH Xs N Pl K f Q x)
      Said fall
  · exact ⟨left.playsRanges,
      fun blk hblk k s m E ds y cols s' hA hd hS =>
        ⟨form 15 (by decide) blk hblk k s m E ds y cols s' hA hS, trivial,
          left.keepsKind 15 (by decide) blk hblk k s m E ds y cols s' hA hd hS⟩,
      exchangeS_of _ _ (exchange_of_nil _ (show (rowsFirst 15).owes = [] by decide)),
      left.ridesKind 15 (by decide), left.acceptedRanges⟩
  · exact ⟨playsS_of _ _ (plays_batt hs scope hp), behindS_of _ _ (behind_batt hs scope hp),
      left.pile, ridesPastS_of _ _ rides_batt, acceptedS_of _ _ (accepted_batt hs scope hp fall)⟩
  · exact ⟨playsS_of _ _ (seat_plays sw), behindS_of _ _ (behind_w hs scope hp),
      exchangeS_of _ _ (exchange_w hs scope hp left.eval), ridesPastS_of _ _ rides_w,
      acceptedS_of _ _ (accepted_send hs scope sw (by decide) (by decide) fall)⟩
  · exact ⟨seal_plays hs scope hp Said,
      behindS_of _ _ (behind₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope 18 (by decide)),
      exchangeS_of _ _ (exchange_of_nil _ (show (rowsFirst 18).owes = [] by decide)),
      ridesPastS_of _ _ (ridesPast₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x
        (readsL_fillH Xs N Pl K f Q x) 18 (by decide)),
      acc 18 (by decide) (by decide)⟩

/-- **THE FIRST CHAIN's MEMBERS, FROM WHAT IS LEFT.** -/
theorem firstFromLeft (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftFirst Xs N Pl K f Q w₀ rc x Said fall) :
    OwesS (Th Xs N Pl K f Q w₀ rc x) Said ∧ YesS (Th Xs N Pl K f Q w₀ rc x) Said fall := by
  have five := fiveFromLeft hs scope hp Said fall left
  have hlen : (Th Xs N Pl K f Q w₀ rc x).bs.length = 19 := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  exact ⟨fun b hb => ⟨(five b (hlen ▸ hb)).1, (five b (hlen ▸ hb)).2.1, (five b (hlen ▸ hb)).2.2.1,
      (five b (hlen ▸ hb)).2.2.2.1⟩,
    fun b hb => (five b (hlen ▸ hb)).2.2.2.2⟩

/-- The same with SaidNext, at the letter "the thread's own steps reach the state from one that begins". -/
theorem firstFromLeft_walked (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Begun : Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftFirst Xs N Pl K f Q w₀ rc x (WalkedFrom (Th Xs N Pl K f Q w₀ rc x) Begun) fall) :
    OwesS (Th Xs N Pl K f Q w₀ rc x) (WalkedFrom (Th Xs N Pl K f Q w₀ rc x) Begun) ∧
      (∀ b, SaidNext (Th Xs N Pl K f Q w₀ rc x) (WalkedFrom (Th Xs N Pl K f Q w₀ rc x) Begun) b) ∧
      YesS (Th Xs N Pl K f Q w₀ rc x) (WalkedFrom (Th Xs N Pl K f Q w₀ rc x) Begun) fall :=
  ⟨(firstFromLeft hs scope hp _ fall left).1, saidNext_walked _ _,
    (firstFromLeft hs scope hp _ fall left).2⟩

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.seal_plays
#print axioms AtPublicFiles.FirstH.Lots.fiveFromLeft
#print axioms AtPublicFiles.FirstH.Lots.firstFromLeft
#print axioms AtPublicFiles.FirstH.Lots.firstFromLeft_walked
