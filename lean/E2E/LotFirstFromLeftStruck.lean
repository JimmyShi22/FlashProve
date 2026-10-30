-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFirstFromLeftStruck.lean: THE LEDGER OF THE KEY FILE's FIRST CHAIN (E2E/LotFirstFromLeft.lean), WITH TWO ROWS STRUCK:
at member 15, the ranges' test, what the step keeps and what rides past it, where the letter Q.kind₁ at 15 is the
test's own yes (RngYes, Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesRides.lean).

  `smOnly_baseH`, `arrOk_baseH`: two premises of ridesPastS_rng on the reading, at the thread's own reading baseH.
  `LeftStruck`: what is left: LeftFirst's nine fields, with keepsKind and ridesKind at 4 and 10 alone.
  **`leftFirst_of_struck`**: LeftFirst from it, under hk15 : Q.kind₁ 15 = RngYes Xs N.
  `firstFromStruck`: so OwesS and YesS at Th.
  `cellsFirst`, `cellsStruck`, `cells_count`: the unpaid cells (member, debt) of the two structures as two written lists,
    and their counts BY EVALUATION: 16 and 14 of 95. The lists are written beside the structures: nothing but a
    reading ties them to the fields.

WHICH TEXT OF RangesRides.lean. The one whose two debts ask of kind₁ at 15 that the step's yes gives it and that it keeps what the
riders read (hkind, hkept): both are drawn here from hk15. Over the elder text, which asked the equation itself, this file is red.

Limits. Those of E2E/LotFirstFromLeft.lean. hk15 IS A PREMISE ON THE LETTER Q: it is met by whoever lays Q as a term. An
implication. leftStruck_of_join (E2E/LotJoinFirst.lean) gives a member of LeftStruck from LeftJoin; leftJoin_laid (E2E/LotJoinLaid.lean) is a member of that.
-/
import E2E.LotFirstFromLeft
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesRides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces ArrOk)
open Johnson.RunOne.KeyRows23 (atSix)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12.AtKey (RngYes rng_keeps behindS_rng ridesPastS_rng)

/-- The thread's reading reads of a message's record whether it is sampled, and nothing else. -/
theorem smOnly_baseH (one : OnBytes.Params.OneTime) : (baseH one).SmOnly := by
  intro c o y y' _ hsam _
  show (if y'.sampled = true then some () else none) = (if y.sampled = true then some () else none)
  rw [hsam]

/-- The seats of messages 0, 1, 2 are the messages' own. -/
theorem arrOk_baseH (one : OnBytes.Params.OneTime) : ArrOk (baseH one).h₁ atSix [0, 1, 2] := by
  intro k hk
  have h : ∀ k ∈ [0, 1, 2], arrH (atSix k).1 (atSix k).2 = k := by decide
  exact h k hk

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **WHAT IS LEFT AT THE FIRST CHAIN**, with member 15's keeping and riding struck. A premise's form. -/
structure LeftStruck (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) : Prop where
  playsK3 : ∀ b ∈ [4, 10], PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b
  keepsK3 : ∀ b ∈ [4, 10], ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk →
    ∀ k s m E ds y cols s', ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E →
      drawsFit blk.rounds ds = true → (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      Q.kind₁ b s s'
  exchangeK3 : ∀ b ∈ [4, 10], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b
  ridesK3 : ∀ b ∈ [4, 10], RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b
  playsRanges : PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 15
  acceptedRanges : AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 15
  pile : ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 16
  eval : ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[17]? = some blk → ∀ k s m E ds y cols s',
    Thr (Th Xs N Pl K f Q w₀ rc x) 17 k s m E → drawsFit blk.rounds ds = true →
    (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
    (Th Xs N Pl K f Q w₀ rc x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1)

variable {Xs N Pl K f Q w₀ rc x} {Z : PublicFiles}

/-- **The two rows at 15 are struck**, where Q.kind₁ at 15 is the test's own yes. -/
theorem leftFirst_of_struck (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hk15 : Q.kind₁ 15 = RngYes Xs N) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftStruck Xs N Pl K f Q w₀ rc x Said fall) :
    LeftFirst Xs N Pl K f Q w₀ rc x Said fall where
  playsK3 := left.playsK3
  keepsKind := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact left.keepsK3 4 (by decide)
    · exact left.keepsK3 10 (by decide)
    · exact fun blk hblk k s m E ds y cols s' hA hd hS =>
        (behindS_rng Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x _ _ hs scope
          (fun a a' h => by
            show Q.kind₁ 15 a a'
            rw [hk15]
            exact h) Said blk hblk k s m E ds y cols s' hA hd hS).2.2
  exchangeK3 := left.exchangeK3
  ridesKind := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact left.ridesK3 4 (by decide)
    · exact left.ridesK3 10 (by decide)
    · exact ridesPastS_rng Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x _ _ hs scope
        (fun a a' h => by
          have h' : Q.kind₁ 15 a a' := h
          rw [hk15] at h'
          exact rng_keeps hs h')
        (smOnly_baseH _) rfl (arrOk_baseH _) rfl Said
  exchangeLayer := left.exchangeLayer
  playsRanges := left.playsRanges
  acceptedRanges := left.acceptedRanges
  pile := left.pile
  eval := left.eval

/-- So the first chain's members, from what is left. -/
theorem firstFromStruck (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (hk15 : Q.kind₁ 15 = RngYes Xs N)
    (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftStruck Xs N Pl K f Q w₀ rc x Said fall) :
    OwesS (Th Xs N Pl K f Q w₀ rc x) Said ∧ YesS (Th Xs N Pl K f Q w₀ rc x) Said fall :=
  firstFromLeft hs scope hp Said fall (leftFirst_of_struck hs scope hk15 Said fall left)

end

/-- The unpaid cells of LeftFirst: member and debt. A written list. -/
def cellsFirst : List (Nat × String) :=
  [(4, "PlaysS"), (4, "BehindS: keeps"), (4, "ExchangeS"), (4, "RidesPastS"),
    (10, "PlaysS"), (10, "BehindS: keeps"), (10, "ExchangeS"), (10, "RidesPastS"),
    (5, "ExchangeS"), (11, "ExchangeS"),
    (15, "PlaysS"), (15, "BehindS: keeps"), (15, "RidesPastS"), (15, "AcceptedS"),
    (16, "ExchangeS"), (17, "ExchangeS: (Eval)")]

/-- The unpaid cells of LeftStruck. -/
def cellsStruck : List (Nat × String) :=
  cellsFirst.filter fun c => !(c.1 == 15 && (c.2 == "BehindS: keeps" || c.2 == "RidesPastS"))

/-- The counts, by evaluation: of 19 × 5 = 95 cells. -/
theorem cells_count : cellsFirst.length = 16 ∧ cellsStruck.length = 14 ∧
    19 * 5 - cellsFirst.length = 79 ∧ 19 * 5 - cellsStruck.length = 81 := by decide

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.smOnly_baseH
#print axioms AtPublicFiles.FirstH.Lots.arrOk_baseH
#print axioms AtPublicFiles.FirstH.Lots.leftFirst_of_struck
#print axioms AtPublicFiles.FirstH.Lots.firstFromStruck
#print axioms AtPublicFiles.FirstH.Lots.cells_count
