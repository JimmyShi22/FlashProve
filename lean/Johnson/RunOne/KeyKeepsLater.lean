-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyKeepsLater.lean: THEOREMS. **THE KEY FILE's TWO LATER CHAINS KEEP «A STATEMENT ONLY GROWS»: WITH NO PREMISE.** The proximity test's own block is k12_grows (no premise but the yes).
OBJECT. Key.sharedChain c N · Key.thirdChain c N (Johnson/Desc/Key/Chains23.lean) and their forms at another type of claims (Chain.retype), as Key.descriptionFromSource lays them. USER. KeyCodesLater.lean. LETTERS. R with GroundKeeps R in the parts; c · N.
BENEATH, CALLED, NOT TYPED AGAIN: Johnson/Desc/K14/Keeps.lean (the page's eight functions) · K1/Keeps.lean (sendOwn_keeps) · Third/Law/Keeps.lean (takeOver_inv · k14Second_inv · takenSources_same) · ChainEndExact.lean · BlockKeeps.lean (inside_decides) · Johnson/Desc/K12/Law/GrowsTest.lean
(H2K.Out.k12_grows; with GrowsK.lean and SendGrows.lean beneath).
THE THREE SEATS: Johnson/Desc/K12/Seat/Core.lean (onGu_keeps | onGomega_keeps | onOwn_keeps, at a relation on statement · book · roots) over its Desc/CoreKeeps.lean, CALLED.
A TWIN, KNOWN: blocks_keep | blocksOr_keep stand, at another form of K14's blocks (sendU | sendOmega, without K1's own block seated there), in K14/BlockGrows.lean [not in this library]: typed here at the library's blocks.
  sendAt_keeps · blocks_keep · blocksOr_keep      K14's eight blocks, for every GroundKeeps R
  end_keeps'          a chains' end hands the record on
  k12_decides         the proximity test's own block: Decides (By Grows (·.st)): at every place
  onGu_grows · onGomega_grows · onOwn_grows
  shared_grows        **ChainKeeps (By Grows (·.st)) (Key.sharedChain c N)** · third_grows   **… (Key.thirdChain c N)**
  retype_keeps        a chain keeps at another type of claims what it keeps (Chain.retype lets the links fall)
What is not claimed. NOTHING ON ROWS. Nothing on soundness.

-/
import Johnson.Desc.Key.Chains23
import Johnson.Desc.K14.Keeps
import Johnson.Desc.K1.Keeps
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.ChainEndExact
import Johnson.Desc.BlockKeeps
import Johnson.Desc.K12.Seat.Core
import Johnson.Desc.K12.Law.GrowsTest

set_option autoImplicit false

namespace Johnson.RunOne.KeyKeeps

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open VerifiableInference.Desc (Block Chain Grows named)
open VerifiableInference.Desc.Ground (GroundKeeps By groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps named_ok ebind_ok emap_ok)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Third (S₃)
open _root_.Desc.K14 (St P14)

variable {R : Statement → Statement → Prop}

/-- The statement in the shared chain's record. -/
abbrev st₂ : St → Statement := fun d => d.st
/-- The statement in the last chain's record. -/
abbrev st₃ : S₃ → Statement := fun s => s.st

theorem why_ok {l : VerifiableInference.Desc.Ground.Clauses} {x : Option St} {d : St} (h : _root_.Desc.K14.why l x = .ok d) : x = some d := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- A sending at the shared chain's state. -/
theorem sendAt_keeps (H : GroundKeeps R) (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St) (hb : ∀ d d' ids, behind d ids = some d' → R d.st d'.st) :
    Decides (By R st₂) (_root_.Desc.K14.sendAt P n Q inFront groups behind) := by
  intro d rs gs d' h
  obtain ⟨t', h2, h3⟩ := ebind_ok h
  have g1 := VerifiableInference.Desc.K1.Rel.sendOwn_keeps (Cl := Unit) H Q _ rs gs t' h2
  exact H.trans g1 (hb _ _ _ (named_ok h3))

theorem blocks_keep (H : GroundKeeps R) (P : P14) (l : List (Block St Unit)) (h : _root_.Desc.K14.blocks P = some l) : ∀ b ∈ l, Decides (By R st₂) b := by
  unfold _root_.Desc.K14.blocks at h
  obtain ⟨w, _, h⟩ := _root_.Desc.Plain.obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun d rs _ d' hd => _root_.Desc.K14.linPoint_keeps H _ d d' rs (why_ok hd)
  · exact sendAt_keeps H _ _ _ _ _ _ fun d d' ids hd => _root_.Desc.K14.behindU_keeps H _ d d' ids hd
  · exact fun d rs _ d' hd => _root_.Desc.K14.laysRec_keeps H _ d d' rs (why_ok hd)
  · exact fun d rs gs d' hd => _root_.Desc.K14.loc_keeps H _ d d' rs gs (why_ok hd)
  · exact sendAt_keeps H _ _ _ _ _ _ fun d d' ids hd => _root_.Desc.K14.behindOmega_keeps H _ d d' ids hd
  · exact fun d rs _ d' hd => _root_.Desc.K14.joins_keeps H _ d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => _root_.Desc.K14.linZeta_keeps H d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => _root_.Desc.K14.split_keeps H _ d d' rs (why_ok hd)

theorem blocksOr_keep (H : GroundKeeps R) (P : P14) : ∀ b ∈ _root_.Desc.K14.blocksOr P, Decides (By R st₂) b := by
  unfold _root_.Desc.K14.blocksOr
  cases h : _root_.Desc.K14.blocks P with
  | some l => exact blocks_keep H P l h
  | none =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · intro d _ _ d' hd
      cases hd
      exact H.refl _
    · cases hb

/-- A chains' end hands the record on as it is. -/
theorem end_keeps' {S Cl : Type} (hr : ∀ T, R T T) (st : S → Statement) (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound) (ask : S → VerifiableInference.Desc.ChainEnd.Clauses) :
    Decides (By R st) (VerifiableInference.Desc.ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront ask) := by
  intro a rs gs a' hd
  obtain ⟨hx, _⟩ := (VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff chain piece sealed inFront ask a a' rs gs).1 hd
  subst hx
  exact hr _

/-- **The proximity test's own block only grows the statement**: k12_grows: no premise but the yes. -/
theorem k12_decides (p : P12) : Decides (By Grows fun t : T12 => t.st) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) :=
  fun t rs gs t' h => H2K.Out.k12_grows p t t' rs gs h

/-- «A statement only grows», read at the three (statement · book · roots) of Johnson/Desc/CoreKeeps.lean. -/
abbrev GrowsC : VerifiableInference.Desc.Ground.Core → VerifiableInference.Desc.Ground.Core → Prop := fun a b => Grows a.st b.st

/-- The three seats: onGu_keeps | onGomega_keeps | onOwn_keeps (Johnson/Desc/K12/Seat/Core.lean), CALLED at GrowsC. -/
theorem onGu_grows (b : Block T12 Unit) (hb : Decides (By Grows fun t : T12 => t.st) b) : Decides (By Grows st₂) (VerifiableInference.Desc.K12.Seat.onGu b) :=
  VerifiableInference.Desc.K12.Seat.onGu_keeps (R := GrowsC) b hb

theorem onGomega_grows (b : Block T12 Unit) (hb : Decides (By Grows fun t : T12 => t.st) b) : Decides (By Grows st₂) (VerifiableInference.Desc.K12.Seat.onGomega b) :=
  VerifiableInference.Desc.K12.Seat.onGomega_keeps (R := GrowsC) b hb

theorem onOwn_grows (b : Block T12 Unit) (hb : Decides (By Grows fun t : T12 => t.st) b) : Decides (By Grows st₃) (VerifiableInference.Desc.K12.Seat.onOwn b) :=
  VerifiableInference.Desc.K12.Seat.onOwn_keeps (R := GrowsC) b hb

/-- **The shared chain keeps «a statement only grows».** -/
theorem shared_grows (c : Model.Verify.Chains) (N : LaterPlaces) : ChainKeeps (By Grows st₂) (sharedChain c N) := by
  refine ⟨fun d _ _ d' hd => ?_, fun b hb => (by cases hb), fun L hL => (by cases hL), fun b hb => ?_, end_keeps' Grows.refl _ _ _ _ _ _⟩
  · cases hd
    exact Grows.refl _
  · rcases List.mem_append.1 hb with hb | hb
    · exact blocksOr_keep groundKeeps_grows _ b hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact onGu_grows _ (k12_decides _)
        · cases hb
      · obtain ⟨nO, _, rfl⟩ := List.mem_map.1 hb
        exact onGomega_grows _ (k12_decides _)

/-- K14's second part, for every relation that the ground's plain functions keep. -/
theorem k14Second_keeps (H : GroundKeeps R) {Cl : Type} (p : VerifiableInference.Desc.Third.P₁₄) : Decides (By R st₃) (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Cl) p) := by
  intro s rs gs s' h
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := VerifiableInference.Desc.Third.Law.k14Second_inv p s s' rs gs h
  obtain ⟨_, _, _, a₁, d₁, _, _, _, h1, _, h2, h3⟩ := VerifiableInference.Desc.Third.Law.takeOver_inv _ _ _ _ _ ha
  subst e
  exact H.trans (H.trans (H.trans (H.adopt _ _ _ _ _ h1) (H.elsewhere _ _ _ _ _ h2)) (H.join _ _ _ _ _ h3)) (H.addRow _ _ _ _ hb)

/-- **The last chain keeps «a statement only grows».** -/
theorem third_grows (c : Model.Verify.Chains) (N : LaterPlaces) : ChainKeeps (By Grows st₃) (thirdChain c N) := by
  refine ⟨k14Second_keeps groundKeeps_grows _, fun b hb => (by cases hb), fun L hL => (by cases hL), fun b hb => ?_, end_keeps' Grows.refl _ _ _ _ _ _⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · intro s rs gs s' h
    rw [VerifiableInference.Desc.Third.Law.takenSources_same _ s s' rs gs h]
    exact Grows.refl _
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact onOwn_grows _ (k12_decides _)
    · cases hb

/-- A chain keeps at another type of claims what it keeps: every block's decide is unturned; the links fall. -/
theorem retype_keeps {S Cl Cl' : Type} {Q : S → S → Prop} {c : Chain S Cl} (h : ChainKeeps Q c) : ChainKeeps Q (c.retype (Cl' := Cl')) := by
  obtain ⟨h1, hf, _, hk, h9⟩ := h
  refine ⟨h1, fun b hb => ?_, fun L hL => (by cases hL), fun b hb => ?_, h9⟩
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact hf b' hb'
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact hk b' hb'

end Johnson.RunOne.KeyKeeps

#print axioms Johnson.RunOne.KeyKeeps.blocksOr_keep
#print axioms Johnson.RunOne.KeyKeeps.k12_decides
#print axioms Johnson.RunOne.KeyKeeps.shared_grows
#print axioms Johnson.RunOne.KeyKeeps.k14Second_keeps
#print axioms Johnson.RunOne.KeyKeeps.third_grows
#print axioms Johnson.RunOne.KeyKeeps.retype_keeps
