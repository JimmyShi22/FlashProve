-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtTerm.lean: K14's SIMULATORS AT THE TERM: at the online prover (E2E/TheHonestProver.lean): where its maker returns and
the library's head stands at the files: the term's shared sides BEGIN WITH the six rows' halves, at the term's own readers: the matrix's reader of
the index and the object's randomness read by `tableCoins`; and at the term's book and order of places each of these six rows has a side off
the description's shared list, and `Good` holds of it as one term.

  `online_shared_six`  **`onlineFilling`'s shared field begins with the six rows' halves**
  `term_rows`      the six rows at the term's readers
  `k14_at_term`    **the statement**
  `online_prover_at_head`   **`onlineProver` is the one made from that return**: so these are the parts of the online prover's term
  `kind_clause_at_term`   **the shared clause of `KindPays` at the term**, at K14 and at K1's two
  `lettered_at_term`   the clause at every row with letters that has the place, parts, On and bud of one of the six, at any list of falls: the form
                    of `KindPays`, at A' := False

So the part of the term at each of K14's six places is the part of the row, and its simulator is the row's.

Limits. THE ONLINE PROVER ALONE: the key file's shared chain holds K14's places too, and has no row here: that is the offline proof's. TWO OF THE SIX STAND
AT K1's PLACES (sendPlace 2 and 5): they pay K1's clause at the shared chain, and the other four K14's. That a filling's sides hold no other row of
these kinds is a premise of whoever joins the kinds. UNDER THE HEAD, AND WHERE THE MAKER RETURNS: premises; the head's member is shown at two named sets alone. AT A := False: plays and acc are
met for nothing: fits, exact and fresh alone say something. Owed's fields: AtFullSide/K14/Sim/Debts.lean, whose on₂ stands on the frame's sentence.
What stands behind the six in the shared field are the two proximity tests' sides, which are not this kind's. The value that the statement on zero knowledge reads is the term
under its refusal: that wrapper is not treated here. What a part shows is not all that a run shows. One request. No property of the protocol is
claimed: nothing on its soundness, completeness, binding or hiding.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K14.Sim.Through
import Johnson.Desc.ProofFile.Honest.K14.Sim.AtPure
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain)
open Desc.K14 (St)
open ProofFile.Honest.K14
open ProofFile.Honest.K12.AtProof (halfU halfO sharedWithUO)

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The six rows at the term's readers. -/
noncomputable def termRows (files : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) :
    List (Unlettered Empty (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit TableKey) :=
  simRows (simData Zp Np) (simPub Zp Np) (matrixInput.weights Zp)
    (randNow (qAt Zp Np) ∘ tableCoins files)

/-- **`onlineFilling`'s shared field begins with the six rows' halves.** -/
theorem online_shared_six (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : Ground) :
    ∃ rest, (onlineFilling files).shared Zp G = (termRows files Zp Np).map (·.half) ++ rest := by
  have hs := simRows_now (Pb := TableKey) h (matrixInput.weights Zp)
  refine ⟨_, six_in_through (Pb := TableKey) h (matrixInput.weights Zp) id (tableCoins files)
    matrixInput.dummy (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest)
    G _ (halfU (matrixInput.weights Zp)
        (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp ++
      halfO (matrixInput.weights Zp) Zp) hs ?_⟩
  show sharedWithUO matrixInput Zp = _
  unfold sharedWithUO
  rw [hs]
  simp only [List.append_assoc]

/-- **K14 AT THE TERM.** -/
theorem k14_at_term (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    {returned : OnlineReturn files} (hA : onlineMaker files = .ok returned) :
    returned.Z = Zp ∧ returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ OwnClear returned.B ∧
      (∃ rest, returned.H.shared = (termRows files Zp Np).map (·.half) ++ rest) ∧
      ∀ (fs : List (Fall St)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
        (r : Unlettered Empty (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit TableKey),
        r ∈ termRows files Zp Np →
        ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
          Good pre .shared σ returned.B (orderOf returned.F) 1 0 (fun _ _ _ _ => False)
            (fun _ _ _ _ => False) r.On r.bud := by
  obtain ⟨eZ, eF, hc, hall⟩ := six_at_atPure h hA
  obtain ⟨-, -, -, -, -, -, -, -, hS, -⟩ := atPure_ok hA
  refine ⟨eZ, eF, hc, ?_, fun fs pre r hr => hall _ _ _ _ _ _ fs r pre hr⟩
  obtain ⟨rest, e⟩ := online_shared_six h returned.G
  refine ⟨rest, ?_⟩
  rw [hS, eZ]
  exact e

/-- **The clause at every row with letters that has the place, parts, On and bud of one of the six.** -/
theorem lettered_at_term (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    {returned : OnlineReturn files} (hA : onlineMaker files = .ok returned)
    (r : Unlettered Empty (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit TableKey)
    (hr : r ∈ termRows files Zp Np)
    (L : Lettered returned.B St ProofFile.Cl Empty (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit TableKey)
    (c1 : L.place = r.place) (c2 : L.row = r.row) (c3 : L.On = r.On) (c4 : L.bud = r.bud)
    (fs : List (Fall St)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (σ : Side St ProofFile.Cl Empty (Common FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey) Unit TableKey)
    (hσ : L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ) :
    Good pre .shared σ returned.B (orderOf returned.F) 1 0 (fun _ _ _ _ => False)
      (fun _ _ _ _ => False) L.On L.bud := by
  obtain ⟨-, -, -, -, hall⟩ := k14_at_term h hA
  obtain ⟨σ', h1, h2⟩ := hall fs pre r hr
  have e : σ' = σ := by
    unfold Lettered.side at hσ
    rw [c1, c2] at hσ
    exact Option.some.inj (h1.symm.trans hσ)
  subst e
  rw [c3, c4]
  exact h2

/-- **The online prover is the one made from that return**: under the head, where the maker returns, `onlineProver` takes its first arm, at the
head's places and first chain: so it is `onlineProversOfCommitter` at `returned.H`, whose shared sides `k14_at_term` speaks of. -/
theorem online_prover_at_head (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    {returned : OnlineReturn files} (hA : onlineMaker files = .ok returned) :
    onlineProver files = onlineProverAt returned Np cF := by
  obtain ⟨eZ, -⟩ := k14_at_term h hA
  have pl : H2U.placesOfMade returned.Z.made = .ok Np := by
    rw [eZ]
    exact h.laid.places
  have ch : ProofFile.onlineFirstChainAt returned.Z = .ok cF := by
    rw [eZ]
    exact h.laid.chain
  unfold onlineProver
  simp only [hA, pl, ch]

/-- **THE SHARED CLAUSE OF `KindPays` AT THE TERM**: `kind_clause_at_return` at the term's readers. -/
theorem kind_clause_at_term (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    {returned : OnlineReturn files} (hA : onlineMaker files = .ok returned) {Tr X : Type}
    (G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Tr Unit X)
    (κ : VerifiableInference.Desc.KindName)
    (rows : ∀ L ∈ G.shared, L.place.kind = κ → ∃ r ∈ termRows files Zp Np,
      L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side returned.F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf returned.F 1) returned.F.shared.blocksInOrder L.place) .shared σ
        returned.B (orderOf returned.F) 1 0 A' B' L.On L.bud :=
  kind_clause_at_return h hA _ _ G κ rows

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.kind_clause_at_term
#print axioms ProofFile.Honest.Term.online_prover_at_head
#print axioms ProofFile.Honest.Term.lettered_at_term
#print axioms ProofFile.Honest.Term.online_shared_six
#print axioms ProofFile.Honest.Term.k14_at_term
