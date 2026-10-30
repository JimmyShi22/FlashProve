-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedSixGood.lean: the second clause of the field `good` of `OwedRest`
(E2E/OfflineClauses.lean) at six of the eight rows of the offline prover's shared chain: "LIN point",
the sending of the folded row, "LOC", the sending of Omega, "LIN zeta", "SPLIT". A join: `Good` at
these rows is AtFullSide/K14/Sim/AtKey.lean's `six_good_key`; here it is laid at the offline file's
rows (`offlineRows`, E2E/OfflineSides.lean).

  `SixPlace`           a place is one of the six
  `SharedSixLetters`   at the six places the rows' letters On and bud are the six rows' own
  `shared_row_is`      a half of the six beside what is laid at its place is the row
  `six_good_sourced`   `six_good_key` at a sourced description, in scope: the plan's two premises paid
  `shared_six_goodAt`, `shared_six_good_mute`   `goodAt` at the six muted rows; the same in the form of
                       the field's second clause
  `keyRows_places`     the six rows stand at the six places, each with one part

Premises that stay. `KeySendersAtTheDescription K`: the letters' sendings and shape are the written
ones. `K.AtAll`. Three on the book: `OwnClear`, and the two owners' tests `maskOwner`, `spOwner`, at the
description's order (paid at the written book: E2E/OfflineSharedSixBook.lean). `SharedSixLetters`.

Limits. `A` and `B` are false at a muted row, so `plays` and `acc` are vacuous. Not the two proximity
tests' rows. What a part shows is not all that a run shows of its messages and coins: the two
proximity tests behind these rows are handed these coins. `exact` at "SPLIT" takes its coin as
uniform: the owner's sentence is `fresh` at that coin's owner, by the written book the sending of Omega
(`split_stretch_full`, E2E/OfflineSharedSixBook.lean). Nothing on any property.
-/
import AtFullSide.K14.Sim.AtKeyBud
import AtFullSide.K14.Sim.AtOfflineRows
import E2E.OfflineSides
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedPar beforeSharedPoint)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver randK14)
open AtPublicFiles.KeyBook (pointPlace foldedPlace locPlace omegaPlace zetaPlace splitPlace foldedTestPlace
  omegaTestPlace)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK par_sourced plan2_full)
open VerifierAndGoals (PublicFiles InScope)

section Lists
variable {W₀ Rc X₀ X Wk : Type}

/-- A place is one of the six. -/
def SixPlace (p : Place) : Prop :=
  p = pointPlace ∨ p = foldedPlace ∨ p = locPlace ∨ p = omegaPlace ∨ p = zetaPlace ∨ p = splitPlace

/-- **A half of the six beside what is laid at its place is the row.** -/
theorem shared_row_is (K : KeyParts W₀ Rc X₀ X Wk) (sims : Place → List (Sim TableKey))
    (h : SimsAtSix K sims) (hS : K.lin.S.sharedSplitNeeded = true) :
    ∀ r ∈ keyRows K, partsBeside r.half.parts (sims r.place) = r.row := by
  intro r hr
  rcases List.mem_append.1 (keyRows_mem K r hr) with g | g
  · unfold ownRows at g
    rcases List.mem_append.1 g with g | g
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
      rcases g with rfl | rfl | rfl
      · show partsBeside _ (sims (place 1)) = _
        rw [h.linPoint]
        rfl
      · show partsBeside _ (sims (place 4)) = _
        rw [h.locColumns]
        rfl
      · show partsBeside _ (sims (place 7)) = _
        rw [h.linZeta]
        rfl
    · rw [if_pos hS] at g
      obtain rfl := List.mem_singleton.1 g
      show partsBeside _ (sims (place 8)) = _
      rw [h.split]
      rfl
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl
    · show partsBeside _ (sims (sendPlace 2)) = _
      rw [h.foldedRowSending]
      rfl
    · show partsBeside _ (sims (sendPlace 5)) = _
      rw [h.omegaSending]
      rfl

/-- The six rows stand at the six places, each with one part. -/
theorem keyRows_places (K : KeyParts W₀ Rc X₀ X Wk) (hS : K.lin.S.sharedSplitNeeded = true) :
    (keyRows K).map (fun r => (r.place, r.row.length)) =
      [(pointPlace, 1), (foldedPlace, 1), (locPlace, 1), (omegaPlace, 1), (zetaPlace, 1),
        (splitPlace, 1)] := by
  unfold keyRows ownRows
  rw [if_pos hS]
  rfl

end Lists

section Letters
variable {W₀ Rc Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **At the six places the rows' letters On and bud are the six rows' own.** -/
structure SharedSixLetters {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) : Prop where
  each : ∀ r ∈ keyRows K,
    (c.shared r.place).atPart = r.On ∧ (c.shared r.place).positions = r.bud

/-- **At a sourced description, in scope: at every row of the six at the written parameters, a side
and `Good`.** What stays: the book's three tests. -/
theorem six_good_sourced {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (d : Data) (hd : d.S = QK.S) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (fs : List (Fall Desc.K14.St)) (Bk : ProverCoinCounts) (ord : List Place) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨QK, 0⟩).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨QK, 0⟩).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc TableKey) Unit TableKey)
    (hr : r ∈ simRows d ⟨QK, 0⟩ weights rand) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∃ σ, Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder r.place r.row fs = some σ ∧
      Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud := by
  have e := par_sourced hs scope
  obtain ⟨layO, hP⟩ := plan2_full
  obtain ⟨B⟩ := hP.eight
  exact six_good_key Xs N Pl (b1 := B.b1) (b2 := B.b2) (b3 := B.b3) (b4 := B.b4) (b5 := B.b5)
    (b6 := B.b6) (b7 := B.b7) (b8 := B.b8) (by rw [e]; exact B.made) (by rw [e]; exact key_fit_full)
    d (by rw [e]; exact hd) weights rand fs Bk ord hB (by rw [e]; exact okU) (by rw [e]; exact okO)
    r (by rw [e]; exact hr) pre

/-- **`goodAt` at the six muted rows of the shared chain.** -/
theorem shared_six_goodAt {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll)
    (hQ : KeySendersAtTheDescription K) (S : OfflineSimulators)
    (hS : SimsAtSix K S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters K c) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 5, 0⟩ = true) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, SixPlace L.place →
      (L.mute.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 1) .shared (keyFileDescription Xs N Pl).shared.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 1 0 [] := by
  intro L hL hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL
  have hp' : SixPlace h.place := hp
  rw [keyRows_half] at hh
  rcases List.mem_append.1 hh with g | g
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 g
    refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder r.place
        (partsBeside r.half.parts (S.byChain.shared r.place)) [] = some σ := hσ
    rw [shared_row_is K _ hS hA.splits r hr] at hσ'
    obtain ⟨σ', h1, h2⟩ := six_good_sourced hs scope K.lin hQ.lin K.weights
      (fun c => randK14 (K.rand c)) [] Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) hB okU okO r
      (keyRows_mem_QK K hQ r hr)
      (preOf 1 0 (earlierOf (keyFileDescription Xs N Pl) 1) (keyFileDescription Xs N Pl).shared.blocksInOrder r.place)
    obtain rfl : σ' = σ := Option.some.inj (h1.symm.trans hσ')
    show Good _ _ _ _ _ _ _ _ _ (c.shared r.place).atPart (c.shared r.place).positions
    rw [(hc.each r hr).1, (hc.each r hr).2]
    exact h2
  · exfalso
    have apart : ∀ p : Place, p.kind = .K12 → ¬ SixPlace p := by
      intro p hk hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl
    · exact apart _ (by rw [hA.onU]; rfl) hp'
    · exact apart _ (by rw [hA.onOmega]; rfl) hp'

/-- **The six rows in the form of `OwedRest.good`'s second clause.** -/
theorem shared_six_good_mute {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll)
    (hQ : KeySendersAtTheDescription K) (S : OfflineSimulators)
    (hS : SimsAtSix K S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters K c) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 5, 0⟩ = true) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, SixPlace L.place →
      (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 1) .shared (keyFileDescription Xs N Pl).shared.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 1 0
        (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.falls₂ := by
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact shared_six_goodAt hs scope K hA hQ S hS c hc hB okU okO L' hL' hp

end Letters

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shared_row_is
#print axioms AtPublicFiles.OfflineRows.keyRows_places
#print axioms AtPublicFiles.OfflineRows.six_good_sourced
#print axioms AtPublicFiles.OfflineRows.shared_six_goodAt
#print axioms AtPublicFiles.OfflineRows.shared_six_good_mute
