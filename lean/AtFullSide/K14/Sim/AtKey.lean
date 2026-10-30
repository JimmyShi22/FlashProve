-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtKey.lean: K14's SIX ROWS AT THE KEY FILE's SHARED CHAIN: the offline twin of `kind_clause_at_return`.

  `flatOf_key`     the key file's shared chain, carried, has the form `FlatOf`, where the maker makes the eight
  `six_good_key`   at the key's description: at each of the six rows a side and `Good`
  `k14_at_key`     **the shared clause of `KindPays` at the key file**, at every list of sides, with one premise on them
  `key_fit_full`, `k14_at_key_sourced`   **the same at a sourced description, in scope**: the plan's two premises paid
  `weaveRows`, `keyRows`, `keyRows_half`, `keyRows_mem`   the six rows in the order of the key's places; **the key prover's shared list is their halves and its two tests**

The kind κ of `k14_at_key` is free: the six rows are of two kinds: four of K14, and the two sendings at K1's places.

Limits. THREE NAMED PREMISES ON THE BOOK (`OwnClear`, the two owners' tests): not paid here; TWO ON THE PLAN (`blocks` returns, `sendingsFit`): of `k14_at_key`, paid by `k14_at_key_sourced`. Nothing of a run. K.onU and K.onOmega are K12's. At
A := False `plays` and `acc` are met for nothing. No property of the protocol is claimed.
-/
import E2E.KeyProver
import E2E.KeyProtocolOverDescription
import E2E.KeyShapeSharedTies
import Johnson.Desc.ProofFile.Honest.K14.Sim.AtFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedChain sharedPar beforeSharedPoint sharedFront sharedTests)
open Desc.K14 (St P14 blocks)
open Desc.K14.Honest (FlatOf)
open AtPublicFiles.KeyFile (KeyParts keyProver sharedChainProverSidesInOrder randK14)
open AtPublicFiles.AtFiles (keyFileDescription)

variable {Cl : Type} {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- **The key file's shared chain, carried, has the form `FlatOf`.** -/
theorem flatOf_key (c : OnBytes.Model.Verify.Chains) (N : LaterPlaces)
    (hb : blocks (sharedPar c (beforeSharedPoint N)) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    FlatOf ((sharedChain c N).retype (Cl' := Cl)).blocksInOrder c b1 b2 b3 b4 b5 b6 b7 b8 := by
  have hc : sharedChain c N =
      { first := sharedFront c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ sharedTests N
        last := VerifiableInference.Desc.K12.Seat.last
          ([b1, b2, b3, b4, b5, b6, b7, b8] ++ sharedTests N) } := by
    simp [sharedChain, Desc.K14.blocksOr, hb]
  rw [hc]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

variable {W₀ Rc Tr X₀ X : Type}

/-- **At the key's description: at every row of the six, a side and `Good`.** -/
theorem six_good_key (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (hb : blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hfit : sendingsFit (sharedPar Xs.chains (beforeSharedPoint Pl)) = true)
    (d : Data) (hd : d.S = (sharedPar Xs.chains (beforeSharedPoint Pl)).S)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts)
    (ord : List Place) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)
    (hr : r ∈ simRows d ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩ weights rand)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∃ σ, Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder r.place r.row fs = some σ ∧
      Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud :=
  six_good_flat (flatOf_key Xs.chains Pl hb) hb hfit d hd weights rand fs Bk ord hB okU okO r hr pre

/-- **THE SHARED CLAUSE OF `KindPays` AT THE KEY FILE.** `rows` is the one premise on the sides. -/
theorem k14_at_key (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (hb : blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hfit : sendingsFit (sharedPar Xs.chains (beforeSharedPoint Pl)) = true)
    (d : Data) (hd : d.S = (sharedPar Xs.chains (beforeSharedPoint Pl)).S)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (Bk : ProverCoinCounts) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩).ok Bk
      (orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩).ok Bk
      (orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 5, 0⟩ = true)
    (G : Sides (keyFileDescription Xs N Pl) Bk W₀ Rc OnBytes.TableKey Tr X₀ X)
    (κ : VerifiableInference.Desc.KindName)
    (rows : ∀ L ∈ G.shared, L.place.kind = κ →
      ∃ r ∈ (simRows d ⟨sharedPar Xs.chains (beforeSharedPoint Pl), 0⟩ weights rand :
          List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf (keyFileDescription Xs N Pl) 1) (keyFileDescription Xs N Pl).shared.blocksInOrder L.place)
        .shared σ Bk (orderOf (keyFileDescription Xs N Pl)) 1 0 A' B' L.On L.bud := by
  intro L hL hk σ hσ
  obtain ⟨r, hr, c1, c2, c3, c4⟩ := rows L hL hk
  obtain ⟨σ', h1, h2⟩ := six_good_key Xs N Pl hb hfit d hd weights rand G.falls₂ Bk _ hB okU okO r hr
    (preOf 1 0 (earlierOf (keyFileDescription Xs N Pl) 1) (keyFileDescription Xs N Pl).shared.blocksInOrder L.place)
  have e : σ' = σ := by
    unfold Lettered.side at hσ
    rw [c1, c2] at hσ
    exact Option.some.inj (h1.symm.trans hσ)
  subst e
  rw [c3, c4]
  exact ⟨_, _, h2⟩

/-- The six rows in the order of the key's places. -/
def weaveRows (own send : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)) :
    List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey) :=
  match own, send with
  | p1 :: p4 :: rest, [s2, s5] => p1 :: s2 :: p4 :: s5 :: rest
  | a, b => a ++ b

variable {Wk : Type}

/-- The key prover's six rows. -/
def keyRows (K : KeyParts W₀ Rc X₀ X Wk) :
    List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey) :=
  weaveRows (ownRows K.lin K.weights) (sendingRows K.send K.weights fun c => randK14 (K.rand c))

/-- Halves in the key's order. -/
theorem weave_half : ∀ (own send : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)),
    sharedChainProverSidesInOrder (own.map (·.half)) (send.map (·.half)) = (weaveRows own send).map (·.half)
  | [], b => by simp [sharedChainProverSidesInOrder, weaveRows]
  | [_], b => by simp [sharedChainProverSidesInOrder, weaveRows]
  | _ :: _ :: _, [] => by simp [sharedChainProverSidesInOrder, weaveRows]
  | _ :: _ :: _, [_] => by simp [sharedChainProverSidesInOrder, weaveRows]
  | _ :: _ :: _, [_, _] => rfl
  | _ :: _ :: _, _ :: _ :: _ :: _ => by simp [sharedChainProverSidesInOrder, weaveRows]

/-- Rows in the key's order are the rows. -/
theorem mem_weaveRows : ∀ (own send : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey))
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey),
    r ∈ weaveRows own send → r ∈ own ++ send
  | [], _, _, h => by simpa [weaveRows] using h
  | [_], _, _, h => by simpa [weaveRows] using h
  | _ :: _ :: _, [], _, h => by simpa [weaveRows] using h
  | _ :: _ :: _, [_], _, h => by simpa [weaveRows] using h
  | _ :: _ :: _, [_, _], _, h => by
    simp only [weaveRows, List.mem_cons, List.cons_append, List.mem_append, List.not_mem_nil,
      or_false] at h ⊢
    tauto
  | _ :: _ :: _, _ :: _ :: _ :: _, _, h => by simpa [weaveRows] using h

/-- **The key prover's shared list is the six rows' halves and its two tests.** -/
theorem keyRows_half (K : KeyParts W₀ Rc X₀ X Wk) :
    (keyProver K).shared = (keyRows K).map (·.half) ++ [K.onU, K.onOmega] := by
  show sharedChainProverSidesInOrder (proverSidesOfSharedRounds K.lin K.weights) (proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++
    [K.onU, K.onOmega] = _
  rw [← ownRows_half (Pb := OnBytes.TableKey) K.lin K.weights,
    ← sendingRows_half (Pb := OnBytes.TableKey) K.send K.weights (fun c => randK14 (K.rand c)), weave_half]
  rfl

/-- Where the shape splits they are six. -/
theorem keyRows_length (K : KeyParts W₀ Rc X₀ X Wk) (hS : K.lin.S.sharedSplitNeeded = true) :
    (keyRows K).length = 6 := by
  simp [keyRows, weaveRows, ownRows, sendingRows, hS]

/-- They are the six rows. -/
theorem keyRows_mem (K : KeyParts W₀ Rc X₀ X Wk)
    (r : Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey) (hr : r ∈ keyRows K) :
    r ∈ simRows K.lin K.send K.weights fun c => randK14 (K.rand c) :=
  mem_weaveRows _ _ r hr

open AtPublicFiles.AtFiles.Full (QK par_sourced plan2_full)
open AtPublicFiles.AtFiles (KeySourced)

/-- The shapes' test at the written key. -/
theorem key_fit_full : sendingsFit QK = true := by decide +kernel

/-- **AT A SOURCED KEY DESCRIPTION, IN SCOPE: THE SHARED CLAUSE OF `KindPays`**: the plan's two premises are paid: the parameters are the written value `QK`. What stays: the book's three tests and `rows`. -/
theorem k14_at_key_sourced {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) (d : Data) (hd : d.S = QK.S)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (Bk : ProverCoinCounts) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨QK, 0⟩).ok Bk (orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨QK, 0⟩).ok Bk (orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 5, 0⟩ = true)
    (G : Sides (keyFileDescription Xs N Pl) Bk W₀ Rc OnBytes.TableKey Tr X₀ X)
    (κ : VerifiableInference.Desc.KindName)
    (rows : ∀ L ∈ G.shared, L.place.kind = κ →
      ∃ r ∈ (simRows d ⟨QK, 0⟩ weights rand :
          List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf (keyFileDescription Xs N Pl) 1) (keyFileDescription Xs N Pl).shared.blocksInOrder L.place)
        .shared σ Bk (orderOf (keyFileDescription Xs N Pl)) 1 0 A' B' L.On L.bud := by
  have e := par_sourced hs scope
  obtain ⟨layO, hP⟩ := plan2_full
  obtain ⟨B⟩ := hP.eight
  exact k14_at_key Xs N Pl (b1 := B.b1) (b2 := B.b2) (b3 := B.b3) (b4 := B.b4) (b5 := B.b5)
    (b6 := B.b6) (b7 := B.b7) (b8 := B.b8) (by rw [e]; exact B.made) (by rw [e]; exact key_fit_full)
    d (by rw [e]; exact hd) weights rand Bk hB (by rw [e]; exact okU) (by rw [e]; exact okO) G κ
    (by rw [e]; exact rows)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.key_fit_full
#print axioms ProofFile.Honest.K14.k14_at_key_sourced
#print axioms ProofFile.Honest.K14.flatOf_key
#print axioms ProofFile.Honest.K14.six_good_key
#print axioms ProofFile.Honest.K14.k14_at_key
#print axioms ProofFile.Honest.K14.keyRows_half
#print axioms ProofFile.Honest.K14.keyRows_length
#print axioms ProofFile.Honest.K14.keyRows_mem
