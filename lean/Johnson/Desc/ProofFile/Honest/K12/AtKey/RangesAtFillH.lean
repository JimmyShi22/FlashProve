-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesAtFillH.lean: the five statements at the key file's
test on the ranges, at the thread of the honest prover's first chain (Th, at the letter fillH and
the tables tbH, E2E/FirstHFill.lean).

  smOnly_baseH, arrOk_baseH   two closed facts of the reading baseH
  five_at_fill   the five at member 15
  row15_at_fill  the row of OwesS at member 15; YesS at Th is yes_first [not in this library]
  owesS_at_fill  OwesS at Th, from the other eighteen rows: the row in OwesS's own form
  keptAt15       any later letters with kind₁ at 15 the value RngKept
  five_at_kept   the five there: no premise on the letter

The premises. hs, scope, hK: the source, scope, the written book. hp: what is public at the sendings
(FirstPublic). hrng: the parts' rng is the test's half. hq₁, hq₂: the letter kind₁ at 15, which
LaterFill leaves free, lies between the test's own yes and what the riders read. RngKept is met by
the value that says just this.

By what. playsS_rng, behindS_rng, exchangeS_rng, ridesPastS_rng (RangesPlays.lean, RangesRides.lean);
accepted_15, tb_is_sent (E2E/FirstHAccepted15.lean, E2E/FirstHRangeLots.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: all five have the pair ThrS as a premise.
- five_at_kept stands at keptAt15 Q, a letter that this file lays, and not at Q: it speaks of the
  thread of LaterFill's owner where that owner lays this value at 15.
- That the pair holds at any run is not said here.
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import E2E.FirstHAccepted15
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces ArrOk)
open Johnson.RunOne.KeyRows23 (atSix)
open AtPublicFiles.FirstH (baseH arrH fillH tbH Th Fl LaterFill FirstPublic accepted_15 tb_is_sent)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open VerifierAndGoals (InScope)

/-- The sample of baseH reads that a message is sampled, and no more. -/
theorem smOnly_baseH (one : OnBytes.Params.OneTime) : (baseH one).SmOnly := by
  intro c o y y' _ e _
  show (if y'.sampled = true then some () else none) = (if y.sampled = true then some () else none)
  rw [e]

/-- The seats of the first three messages. -/
theorem arrOk_baseH (one : OnBytes.Params.OneTime) : ArrOk (baseH one).h₁ atSix [0, 1, 2] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> rfl

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : VerifierAndGoals.PublicFiles}

/-- **The five at member 15 of the honest prover's first chain.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_at_fill (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0))
    (hq₁ : ∀ s s', RngYes Xs N s s' → Q.kind₁ 15 s s')
    (hq₂ : ∀ s s', Q.kind₁ 15 s s' → RngKept s s')
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (Th Xs N Pl K f Q w₀ rc x) Said fall 15 := by
  have hhalf := find_rng K Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 hp.places hrng
  refine ⟨?_, ?_, ?_, ?_, accepted_15 hs scope hK hp hrng Said fall⟩
  · refine playsS_rng Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 (Fl Xs N Pl K f Q x) w₀ rc x
      (keyProver K).first (tbH Xs N Pl K f Q) hK hs scope Said hhalf
      (fun k _ m _ _ => tb_is_sent hp k m) K.own₀ fun τ hτ => ?_
    have h3 : τ = 0 ∨ τ = 1 ∨ τ = 2 := by omega
    rcases h3 with rfl | rfl | rfl <;> rfl
  · exact behindS_rng Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x _ _ hs scope hq₁ Said
  · exact exchangeS_rng Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x _ _ Said
  · exact ridesPastS_rng Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x _ _ hs scope hq₂
      (smOnly_baseH _) rfl (arrOk_baseH _) rfl Said

/-- **Member 15's row of OwesS at the honest prover's first chain**: the four that say nothing of a
fall, in the order of OwesS. NOT IN FRONT OF A LAW OVER COINS. -/
theorem row15_at_fill (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0))
    (hq₁ : ∀ s s', RngYes Xs N s s' → Q.kind₁ 15 s s')
    (hq₂ : ∀ s s', Q.kind₁ 15 s s' → RngKept s s')
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop) :
    PlaysS (Th Xs N Pl K f Q w₀ rc x) Said 15 ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said 15 ∧
      ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said 15 ∧
      RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said 15 :=
  have h := five_at_fill (w₀ := w₀) (rc := rc) (x := x) hs scope hK hp hrng hq₁ hq₂ Said
    fun _ _ _ => none
  ⟨h.plays, h.behind, h.exchange, h.rides⟩

/-- **OwesS at the honest prover's first chain from its other eighteen rows.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem owesS_at_fill (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0))
    (hq₁ : ∀ s s', RngYes Xs N s s' → Q.kind₁ 15 s s')
    (hq₂ : ∀ s s', Q.kind₁ 15 s s' → RngKept s s')
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop)
    (others : ∀ b, b < (Th Xs N Pl K f Q w₀ rc x).bs.length → b ≠ 15 →
      PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b ∧ BehindS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b ∧
        RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b) :
    OwesS (Th Xs N Pl K f Q w₀ rc x) Said := by
  intro b hb
  by_cases e : b = 15
  · subst e
    exact row15_at_fill hs scope hK hp hrng hq₁ hq₂ Said
  · exact others b hb e

/-- **The later letters with kind₁ at 15 laid.** -/
def keptAt15 (Q : LaterFill (keyBook K₀) W₀ Rc) : LaterFill (keyBook K₀) W₀ Rc :=
  { Q with kind₁ := fun b => if b = 15 then RngKept else Q.kind₁ b }

/-- **The five with no premise on the letter.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem five_at_kept (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0))
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Five (Th Xs N Pl K f (keptAt15 Q) w₀ rc x) Said fall 15 :=
  five_at_fill hs scope hK hp hrng
    (fun _ _ h => by
      show (if (15 : Nat) = 15 then RngKept else Q.kind₁ 15) _ _
      rw [if_pos rfl]
      exact rng_keeps hs h)
    (fun _ _ h => by
      have h' : (if (15 : Nat) = 15 then RngKept else Q.kind₁ 15) _ _ := h
      rw [if_pos rfl] at h'
      exact h')
    Said fall

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.smOnly_baseH
#print axioms ProofFile.Honest.K12.AtKey.arrOk_baseH
#print axioms ProofFile.Honest.K12.AtKey.five_at_fill
#print axioms ProofFile.Honest.K12.AtKey.row15_at_fill
#print axioms ProofFile.Honest.K12.AtKey.owesS_at_fill
#print axioms ProofFile.Honest.K12.AtKey.five_at_kept
