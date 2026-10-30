-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12SeatsHeld.lean: THE SEAT's SENTENCE (Johnson/Desc/K12/Coin/Over.lean: Over) GOES ON THROUGH THE TWO DRESSES IN WHICH A FILE's RULE OF COMPOSITION HOLDS A BLOCK: behind the test that every word shown is below the prime (Johnson/Desc/Sound/ChainRule.lean: below), and lifted over what was handed to the chain (Block.lift Prod.snd …: the state P × S). Statements with proofs.
OBJECT. The same four blocks as in Johnson/RunOne/Law/K12SeatsLaw.lean, as `held P B`: the form in which a maker's piece holds a block of a description's blocksInOrder list. At the last chain the term bears the stamp of its place (`Third.ownAt`), as the description lays it.
USER. Johnson/RunOne/Law/K12AtField.lean (over_held).
LETTERS. Those of K12SeatsLaw.lean; P (what was handed to the chain) is free.
  over_below: Over p B R R' gives Over p (below B) R R'.
  over_lift: Over p B R R' gives Over p (B lifted to P × S), at R read at the second half, and R' with "the first half stands".
  held P B: the block as a maker's piece holds it: Chain.blocksInOrder's dress, below the prime's test, lifted.
  over_held: Over p B R R' gives Over p (held P B) ….
  law_rng_held, law_U_held, law_O_held, law_own_held: the law of the proximity test in the plain form (Coin/LawY.lean) at the four blocks of a key file's description IN THAT DRESS. All premises of that law stay.
Limits. Only one direction is used and shown: a yes of the dressed block's step gives a yes of the block's. Whether a maker's piece holds just this term is the maker's text's to show. Nothing on soundness.

-/
import Johnson.RunOne.Law.K12SeatsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12SeatsHeld
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open Johnson.RunOne.Law.K12SeatsLaw

variable {S T A Cl W P : Type} {C : PQ.CK} {F : Frame}

theorem step_below (B : Block S A) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ)
    (h : (below B).step ft s rs cols = .ok (s', k)) : B.step ft s rs cols = .ok (s', k) := by
  obtain ⟨f1, f2, f3⟩ := RngOver.form_over (below B) B rfl ft rs cols
  rw [step_iff, f1, f2, f3] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine (step_iff _ _ _ _ _ _ _).2 ⟨h1, ?_, h3⟩
  have h2' : (if viewWordsBelowPrime ⟨rs.map noDigest, ((B.shown ft rs cols).flatMap id).map fun c => (0, c.1, c.2)⟩ then
      B.decide s (rs.map noDigest) (B.shown ft rs cols) else .error "a word is not below the prime") = .ok s' := h2
  split at h2'
  · exact h2'
  · cases h2'

theorem over_below (p : Piece C F T Cl W) {B : Block S A} {R : S → T → Prop} {R' : S → T → S → Prop}
    (hO : Over p B R R') : Over p (below B) R R' where
  rounds := hO.rounds
  step := fun s rs cols s' k hs => hO.step s rs cols s' k (step_below B _ _ _ _ _ _ hs)
  one := hO.one

theorem step_lift (B : Block S A) (ft : ℕ) (a a' : P × S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ)
    (h : (B.lift Prod.snd fun (t : P × S) s => (t.1, s)).step ft a rs cols = .ok (a', k)) :
    B.step ft a.2 rs cols = .ok (a'.2, k) ∧ a'.1 = a.1 := by
  obtain ⟨f1, f2, f3⟩ := RngOver.form_over (B.lift Prod.snd fun (t : P × S) s => (t.1, s)) B rfl ft rs cols
  rw [step_iff, f1, f2, f3] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : (B.decide a.2 (rs.map noDigest) (B.shown ft rs cols)).map (fun s => (a.1, s)) = .ok a' := h2
  obtain ⟨s', hs, rfl⟩ := (Except.map_eq_ok _ _ _).1 h2'
  exact ⟨(step_iff _ _ _ _ _ _ _).2 ⟨h1, hs, h3⟩, rfl⟩

theorem over_lift (p : Piece C F T Cl W) {B : Block S A} {R : S → T → Prop} {R' : S → T → S → Prop}
    (hO : Over p B R R') :
    Over p (B.lift Prod.snd fun (t : P × S) s => (t.1, s)) (fun a t => R a.2 t)
      (fun a t' a' => R' a.2 t' a'.2 ∧ a'.1 = a.1) where
  rounds := hO.rounds
  step := fun a rs cols a' k hs => by
    obtain ⟨h1, h2⟩ := step_lift B _ _ _ _ _ _ hs
    obtain ⟨t, t', g1, g2, g3⟩ := hO.step a.2 rs cols a'.2 k h1
    exact ⟨t, t', g1, g2, g3, h2⟩
  one := fun a t₁ t₂ h₁ h₂ => hO.one a.2 t₁ t₂ h₁ h₂

/-- The block as a maker's piece holds it. -/
def held (P : Type) (B : Block S A) : Block (P × S) A :=
  (below { B with planOk := B.planOk && B.hasNoClaimsAndNothingAfter }).lift Prod.snd fun t s => (t.1, s)

theorem over_held (p : Piece C F T Cl W) {B : Block S A} {R : S → T → Prop} {R' : S → T → S → Prop}
    (hO : Over p B R R') :
    Over p (held P B) (fun a t => R a.2 t) (fun a t' a' => R' a.2 t' a'.2 ∧ a'.1 = a.1) :=
  over_lift p (over_below p (over_same p (seated_bare B) hO))

section
variable (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (Nn : ConclK F)

/-- **The ranges' test, as a maker's piece holds it.** -/
theorem law_rng_held (one : OneTime) (N : H2U.PlaceNums)
    (hA : AtPlace F (rangesParams N) num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W (rangesParams N) base dB dt e₀ εt)
        (held P (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim))).ior.red.Leads
      (fun a => ∀ t, enterAndAsk (Key.enterRanges one) (rangesParams N) a.1.2 = .ok t →
        FirstOpens (rangesParams N) num no base t ∧ BatAtY F W (rangesParams N) no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', enterAndAsk (Key.enterRanges one) (rangesParams N) a.1.2 = .ok t ∧
        (Key.leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧ QN (rangesParams N) Nn (t, a.2))
      (Coin.«over» (pieceT F W (rangesParams N) base dB dt e₀ εt)
        (held P (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim))).err :=
  law_over (rangesParams N) num no L mC mS mW rad rd base dB dt e₀ εt Nn _ _ _
    (over_held _ (RngOverCoin.over_keyD one N _ rfl)) hA

/-- **The folded row's test.** -/
theorem law_U_held (π : P12) (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Seat.onGu (proximityTestKind guardedProximityTestParts π)) : Block _root_.Desc.K14.St Key.Claim))).ior.red.Leads
      (fun a => ∀ t, Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t →
        FirstOpens π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Seat.onGu (proximityTestKind guardedProximityTestParts π)) : Block _root_.Desc.K14.St Key.Claim))).err :=
  law_over π num no L mC mS mW rad rd base dB dt e₀ εt Nn _ _ _
    (over_held _ (over_same _ (seated_recl _) (over_inside (pieceT F W π base dB dt e₀ εt) _ _))) hA

/-- **Omega's test.** -/
theorem law_O_held (π : P12) (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Seat.onGomega (proximityTestKind guardedProximityTestParts π)) : Block _root_.Desc.K14.St Key.Claim))).ior.red.Leads
      (fun a => ∀ t, Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t →
        FirstOpensOwn π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Seat.onGomega (proximityTestKind guardedProximityTestParts π)) : Block _root_.Desc.K14.St Key.Claim))).err :=
  law_overO π num no L mC mS mW rad rd base dB dt e₀ εt Nn _ _ _
    (over_held _ (over_same _ (seated_recl _) (over_inside (pieceT F W π base dB dt e₀ εt) _ _))) hA

/-- **The own group's test.** -/
theorem law_own_held (π : P12) (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Third.ownAt (Seat.onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) : Block VerifiableInference.Desc.Third.S₃ Key.Claim))).ior.red.Leads
      (fun a => ∀ t, Seat.enterOwn a.1.2 = .ok t →
        FirstOpens π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enterOwn a.1.2 = .ok t ∧
        (Seat.leaveOwn a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt)
        (held P (Block.retype (Cl := Unit) (Third.ownAt (Seat.onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) : Block VerifiableInference.Desc.Third.S₃ Key.Claim))).err :=
  law_over π num no L mC mS mW rad rd base dB dt e₀ εt Nn _ _ _
    (over_held _ (over_same _ ((seated_ownAt _).trans (seated_recl _)) (over_inside (pieceT F W π base dB dt e₀ εt) _ _))) hA

end

end Johnson.RunOne.Law.K12SeatsHeld

#print axioms Johnson.RunOne.Law.K12SeatsHeld.over_below
#print axioms Johnson.RunOne.Law.K12SeatsHeld.over_lift
#print axioms Johnson.RunOne.Law.K12SeatsHeld.over_held
#print axioms Johnson.RunOne.Law.K12SeatsHeld.law_rng_held
#print axioms Johnson.RunOne.Law.K12SeatsHeld.law_U_held
#print axioms Johnson.RunOne.Law.K12SeatsHeld.law_O_held
#print axioms Johnson.RunOne.Law.K12SeatsHeld.law_own_held
