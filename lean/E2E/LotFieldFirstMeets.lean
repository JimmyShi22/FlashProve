-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFieldFirstMeets.lean: E2E/LotFieldFirst.lean CUT TO WHAT IS LEFT, AND ITS MEETING WITH E2E/LotStandFirst.lean AT
BORDER 19 of the key file's first chain.

  plays_of_three           PlaysS at every member of the first chain from PlaysS at the members 4, 10 (the two lookups) and 15 (the
                           ranges' test): the sixteen others are paid, by the payers that fiveFromLeft (E2E/LotFirstFromLeft.lean) calls.
  LotDoorAsksFirstThree, lotDoorAsksFirstThree   what the door asks of the first chain (DoorAsks), with these three alone as the
                           premise on the members.
  LotFirstAtDoor, lotFirstAtDoor   THE MEETING: where ready returns and LeftFirst holds at no fall, at EVERY list that fits the
                           chain's declared rounds: a pair at border 19 that has heard that list at the run's input, whose field is
                           some cols with cols what the thread's columns say; and every pair at border 19 with that input and list
                           has this same verifier's state and this same state of the run. So there DoorAsks' fields one, state and field speak of something.

Limits. AN IMPLICATION. LeftFirst is a premise: a member at the laid letters comes by leftFirst_of_struck and leftStruck_of_join from leftJoin_laid (E2E/LotJoinLaid.lean). «ready returns» is a premise: lotReadyReturnsWhole (E2E/LotReadyWhole.lean) has it. RangeTie,
Q.Rel, FirstPublic, NoStop are premises; three of them are paid at the real value elsewhere. Q stays a letter. Nothing on the
shared chain. Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotFieldFirst
import E2E.LotFirstFromLeft
import E2E.LotStandFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Stops (NoStop)
open AtPublicFiles.LotField (DoorAsks)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- **PlaysS at every member, from PlaysS at 4, 10 and 15.** -/
theorem plays_of_three (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (h : ∀ b ∈ [4, 10, 15], PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b) :
    ∀ b, b < 19 → PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b := by
  have quiet := fiveQuiet_Th Xs N Pl K f Q w₀ rc x hs scope Said fun _ _ _ => none
  have layer := fourLayer_Th Xs N Pl K f Q w₀ rc x hs scope Said fun _ _ _ => none
  have sw := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  intro b hb
  interval_cases b
  · exact (rows_idx hs scope hp Said fun _ _ _ => none).1
  · exact (rows_msg hs scope hp Said fun _ _ _ => none).1
  · exact (quiet 2 (by decide)).1
  · exact (quiet 3 (by decide)).1
  · exact h 4 (by decide)
  · exact (layer 5 (by decide)).1
  · exact (quiet 6 (by decide)).1
  · exact (quiet 7 (by decide)).1
  · exact (quiet 8 (by decide)).1
  · exact (quiet 9 (by decide)).1
  · exact h 10 (by decide)
  · exact (layer 11 (by decide)).1
  · exact (quiet 12 (by decide)).1
  · exact (quiet 13 (by decide)).1
  · exact (five14 Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_fillH Xs N Pl K f Q x)
      Said fun _ _ _ => none).1
  · exact h 15 (by decide)
  · exact playsS_of _ _ (plays_batt hs scope hp)
  · exact playsS_of _ _ (seat_plays sw)
  · exact seal_plays hs scope hp Said

end

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **What the door asks of the first chain, with three members left.** -/
def LotDoorAsksFirstThree : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f → NoStop (keyProver K).first →
    (∀ b ∈ [4, 10, 15],
      PlaysS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b) →
    DoorAsks (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19 ∧
      ∀ k, walkedFirst Xs N Pl K f Q w₀ rc x 0 k (startFirst K (some []) (inFirst w₀ rc x))

theorem lotDoorAsksFirstThree : LotDoorAsksFirstThree K₀ Xs N Pl K f Q w₀ rc x :=
  fun hs scope hK hp hstop h =>
    lotDoorAsksFirst K₀ Xs N Pl K f Q w₀ rc x hs scope hK hp hstop (plays_of_three hs scope hp _ h)

/-- **The first chain's stand and what the door asks of it meet at border 19.** -/
def LotFirstAtDoor : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f → RangeTie Xs K f w₀ → Q.Rel w₀ rc x →
    NoStop (keyProver K).first →
    LeftFirst Xs N Pl K f Q w₀ rc x (walkedFirst Xs N Pl K f Q w₀ rc x) (fun _ _ _ => none) →
    ∀ (k : Coins (keyBook K₀)) R,
      ready (keyFileDescription Xs N Pl) (keyBook K₀) (keyProver K) w₀ rc x k = .ok R →
    ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs 19) ds = true →
      ∃ s m E cols,
        ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19 k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x ∧
        (Th Xs N Pl K f Q w₀ rc x).colsTo 19 m E = .ok cols ∧ m.opened = some cols ∧
        ∀ s' m' E',
          ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19 k s' m' E' →
          m'.st.input = inFirst w₀ rc x → m'.st.heard = ds → s' = s ∧ m' = m

theorem lotFirstAtDoor : LotFirstAtDoor K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope hK hp tie rel hstop left k R hR ds hd
  obtain ⟨s, m, E, hA, hh, hi⟩ :=
    standFirst_to19 hs scope hp tie rel hstop left k R hR 19 (Nat.le_refl 19) ds hd
  have D := (lotDoorAsksFirst K₀ Xs N Pl K f Q w₀ rc x hs scope hK hp hstop
    fun b hb => (fiveFromLeft hs scope hp _ _ left b hb).1).1
  obtain ⟨cols, hc, ho⟩ := (field_iff _ [] _ _ _).1 (D.field k s m E hA)
  exact ⟨s, m, E, cols, hA, hh, hi, hc, ho, fun s' m' E' hA' hi' hh' =>
    ⟨D.state k s' m' E' s m E hA' hA (hi'.trans hi.symm) (hh'.trans hh.symm),
      D.one k m' m hA'.2 hA.2 (hi'.trans hi.symm) (hh'.trans hh.symm)⟩⟩

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.plays_of_three
#print axioms AtPublicFiles.FirstH.Lots.lotDoorAsksFirstThree
#print axioms AtPublicFiles.FirstH.Lots.lotFirstAtDoor
