-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/KindPaysFirst.lean: the shared "sending" (the kind K1): THE FIRST CHAIN's CLAUSE OF "KindPays" AT
THE KIND K1 (the rule's premise hand₁, Johnson/Desc/ProofFile/Honest/Thread/Rows.lean, cut by the place's
kind), AT WHAT THE MAKER onlineProverFromPublicFiles RETURNS, AT ANY FILLING: at sides G over the returned description and book
whose first list, at places of the kind K1, holds our rows: at every such list L and every side of it there
are A', B' with Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder L.place) .own σ A.B (orderOf A.F) 0 0 A' B'
L.On L.bud. Letters: the types, the filling, the readers, the sizes, the open functions, G. Two theorems; no
definition.

  good_seated_at_return   Good at the side that Side.seated returns for a job's row, at the row's own On and
                    bud: good_all_at_return without a thread's letters
  k1_pays_first     THE CLAUSE. "rows" is its one premise on the sides: each list of G.first at a place of
                    the kind K1 has the place, row, On and bud of one of our 52 rows

Limits. All limits of GoodAtReturn.lean: A', B' never hold; fresh has content at two rows. "rows" is where
the prover enters: that G's first list is the prover's own is k1_halves_at_base | _through
(Honest/K1/Sim/HalvesAtReturn.lean) for the halves, and whoever lays G for the simulators, On and bud. The
kind's two places on the shared chain fall under the shared clause, which is another file's. No property
of the protocol is claimed.
-/
import AtFullSide.K1.GoodAtReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst Pub Ground)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ W₀' Rc' : Type}

/-- **Good at the side that Side.seated returns for a job's row**, at the row's own On and bud. -/
theorem good_seated_at_return {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} {Z : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (I : WiderIn W₀) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (φ : Face (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Inst) (chain ft : Nat)
    (fs : List (Fall A.F.S₁)) :
    ∀ r ∈ rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O],
      ∀ σ, Side.seated A.F.first.blocksInOrder r.place r.row fs = some σ →
        Good pre₀ φ σ A.B (orderOf A.F) chain ft (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
          r.bud := by
  intro r hr σ hσ
  rw [rows_eq] at hr
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  have hB := clear_all hS hL S O hA J hJ
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG] at hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  obtain ⟨-, h⟩ := fieldsAtLots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Op φ (witAt I g rd A.Z)
    (lotNo OnBytes.secondHashFunction A.Z) D chain ft fs J hD
  obtain ⟨hf, he, -⟩ := h σ hσ
  exact good_of_fields hf he (freshAtLots_of_spenders Op φ (witAt I g rd A.Z)
    (lotNo OnBytes.secondHashFunction A.Z) D hD hσ A.B (orderOf A.F) hB)

/-- **THE FIRST CHAIN's CLAUSE OF KindPays AT THE KIND K1.** -/
theorem k1_pays_first {Ky X₀ : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (G : Sides A.F A.B W₀' Rc' Ky Cells X₀ Unit)
    (rows : ∀ L ∈ G.first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [lotS I g rd OnBytes.secondHashFunction S, wS I g rd OnBytes.secondHashFunction O],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.first, L.place.kind = .K1 → ∀ σ, L.side A.F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder L.place) .own σ A.B (orderOf A.F) 0 0
        A' B' L.On L.bud := by
  intro L hL' hk σ hσ
  obtain ⟨r, hr, c1, c2, c3, c4⟩ := rows L hL' hk
  unfold Lettered.side at hσ
  rw [c1, c2] at hσ
  rw [c3, c4]
  exact ⟨_, _, good_seated_at_return hS hL I g rd S O hA .own 0 0 G.falls₁ r hr σ hσ⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.good_seated_at_return
#print axioms AtFullSide.K1.k1_pays_first
