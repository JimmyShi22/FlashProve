-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/KindPaysK1.lean: the shared "sending" (the kind K1): **KindPays G .K1, BY THAT NAME**
(VerifiableInference.Compilation.KindPays, Johnson/T3/OwedOfKinds.lean: what one kind pays, in each of the three chains), AT WHAT THE
MAKER onlineProverFromPublicFiles RETURNS, in scope, where the gate accepts, at any filling, under the head at the return as a DATUM
(h : HeadAtReturn Z A, Honest/Thread/TheFirstThread.lean: its places are h.places: bound by no ∃), at sides G over the
returned description and book. Three premises on G, one a chain, each on WHICH rows G's lists at places of the kind K1 bear:

  rows₁   each list of G.first at a place of the kind K1 has the place, row, On and bud of one of our 52 rows
  rows₂   each list of G.shared at a place of the kind K1 has the place, row, On and bud of one of the shared chain's two
          sendings' rows sendingRows (simPub A.Z h.places) weights rand (Honest/K14/ExactRows.lean,
          Honest/K14/Sim/Good.lean)
  none₃   no list of G.second stands at a place of the kind K1

  shared_of_six         the shared chain's clause at a kind, from "a side and Good at each row of a list R" and "G's lists
                        of that kind bear R's rows": at a description that equals the head's
  kindPays_K1_of_rows   THE STATEMENT. Clause 1: k1_pays_first (KindPaysFirst.lean) · clause 2: six_at_atPure
                        (Honest/K14/Sim/AtPure.lean: Good at the shared chain's six rows at A.B, the book's tests paid
                        there), called at the two sendings' rows · clause 3: from none₃: nothing to show

Limits. The three premises are where the prover enters: that G's lists are the prover's own, beside these simulators, is
for whoever lays G to show. weights and rand are letters in rows₂: at the real G they must be those of A.H.shared's own
halves (at the base filling: I.weights A.Z and randNow (qAt A.Z h.places)): whoever pays rows₂ picks them. IDLE WHERE G HAS
NO LIST OF THE KIND: the guards: that G's prover is A.H, with k1_halves_at_base (52 halves) and sendingRows_half (two). Good is had at predicates that never hold: plays and acc are met for nothing. Clause 2 is
another house's law, called: its limits travel (these two rows' On is pointApart: owed at the run). All limits of
KindPaysFirst.lean. No property of the protocol is claimed.
-/
import AtFullSide.K1.KindPaysFirst
import Johnson.Desc.ProofFile.Honest.K14.Sim.AtPure
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.T3.OwedOfKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Compilation (KindPays)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open ProofFile.Honest.K14 (sendingRows simRows simPub simData six_at_atPure)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open Desc.K14 (St)

variable {W₀ W₀' Rc' : Type}

/-- **The shared chain's clause at a kind**, at a description that equals the head's. -/
theorem shared_of_six {Tr X₀ X : Type} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {F : FileDescription Inst} (e : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀' Rc' OnBytes.TableKey Tr X₀ X) (κ : KindName)
    (R : List (Unlettered Empty (Common W₀' Rc' OnBytes.TableKey) X₀ OnBytes.TableKey))
    (hall : ∀ (fs : List (Fall St)) (pre : List (Nat × Nat × List Fmt.DeclaredRound)), ∀ r ∈ R,
      ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
        Good pre .shared σ Bk (orderOf F) 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
          r.bud)
    (rows : ∀ L ∈ G.shared, L.place.kind = κ →
      ∃ r ∈ R, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud := by
  subst e
  intro L hL hk σ hσ
  obtain ⟨r, hr, c1, c2, c3, c4⟩ := rows L hL hk
  obtain ⟨σ', h1, h2⟩ := hall G.falls₂ (preOf 1 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 1)
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder L.place) r hr
  have e' : σ' = σ := by
    unfold Lettered.side at hσ
    rw [c1, c2] at hσ
    exact Option.some.inj (h1.symm.trans hσ)
  subst e'
  rw [c3, c4]
  exact ⟨_, _, h2⟩

/-- **KindPays G .K1.** -/
theorem kindPays_K1_of_rows {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (h : HeadAtReturn Z A)
    (G : Sides A.F A.B W₀' Rc' OnBytes.TableKey Cells Unit Unit)
    (weights : W₀' → Weights) (rand : Rc' → TableRand)
    (rows₁ : ∀ L ∈ G.first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud)
    (rows₂ : ∀ L ∈ G.shared, L.place.kind = .K1 →
      ∃ r ∈ (sendingRows (simPub A.Z h.places) weights rand :
          List (Unlettered Empty (Common W₀' Rc' OnBytes.TableKey) Unit OnBytes.TableKey)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud)
    (none₃ : ∀ L ∈ G.second, L.place.kind ≠ .K1) : KindPays G .K1 := by
  obtain ⟨-, eF, -, hall⟩ := six_at_atPure h.head hA
  refine ⟨k1_pays_first hS hL I g rd S O hA G rows₁, ?_, fun L hL' hk => absurd hk (none₃ L hL')⟩
  exact shared_of_six eF G .K1 _ (fun fs pre r hr =>
    hall W₀' Rc' OnBytes.TableKey Unit weights rand fs r pre (List.mem_append_right _ hr)) rows₂

end AtFullSide.K1

#print axioms AtFullSide.K1.shared_of_six
#print axioms AtFullSide.K1.kindPays_K1_of_rows
