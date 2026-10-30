-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysShared.lean: the shared chain's two proximity tests pay. Under the library's head,
at the book and description that onlineProverFromPublicFiles returns at any filling, the pair on G_u and the pair on
G_omega behind the guard fit, at every reader of the index. At onlineProverPartsInUse I no other side of
the shared chain stands at a place of the kind K12.

  testOnU_fits         each side of halfU fits
  testOnOmega_fits     each side of halfO fits
  testOnU_lends, testOnOmega_lends   so the frame lends each of these sides, at every run's coins
  sharedTests_fit      every side of the kind K12 in sharedWithUO fits, at any filling's book
  sharedTests_pay      every side of the kind K12 in the prover's shared chain pays: that kind's
                       share of the field pays₂ of ReadyDebts

By what. realU_bare, realO_bare (K12/AtProof/HalfU.lean, HalfO.lean): a job has the bare job's
parameters, members and word on the fresh table; fourU_written, fourO_written, lays_at_head
(PaysAtHead.lean); laysB_congr (K12/StepsAtKey.lean); SideFits.guarded, which stands for the step
that chainSteps_guarded (K12/FieldGuardLift.lean) makes at a list of one block; six_places
(K14/NoStray.lean).

Limits.
- Conditional on the head and on onlineProverFromPublicFiles's return.
- The laws at halfU and halfO read public fields alone: wt and enc are free, and nothing is said of
  the rows that a part lays or of what is handed.
- Where a job is not made its list is empty and the law says nothing of it. halfO_made_at_head says
  that the pair on G_omega is there; of the pair on G_u no law says so yet.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.PaysAtHead
import AtFullSide.K12.PaysRoundsU
import AtFullSide.K12.PaysRoundsO
import AtFullSide.K12.ReadyTestsW
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey
import Johnson.Desc.ProofFile.Honest.K14.NoStray

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piUFull piOFull)
open P5J (AtMgA TS)
open AtFullSide.K14 (bookWhole_returns_written_ahead)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X W₁ : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Each side of halfU fits** at onlineProverFromPublicFiles's book and description, at every reader of the index. -/
theorem testOnU_fits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (wt : W₁ → Weights)
    (enc : W₁ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) :
    ∀ g ∈ halfU wt enc Zp, SideFits A.B 1 A.F.shared.blocksInOrder g := by
  intro g hg
  unfold halfU at hg
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
  obtain ⟨J₀, h0, e1, e2, e3⟩ := realU_bare wt enc Zp J (Option.mem_toList.1 hJ)
  unfold bareU at h0
  obtain ⟨F, hF, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain rfl : F = fourOf Np :=
    Option.some.inj (hF.symm.trans (ProofFile.Honest.K12.Light.stages_at_head h.toAtMg).1)
  obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.1 h0
  have hp : J.p = ({ piUFull with place := placeU } : P12) :=
    e1.trans (fourU_written h.toAtMg)
  obtain ⟨lU, -⟩ := lays_at_head h.toAtMg (sendPub_plan h.toAtMg hA')
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  have hl : laysB A.B 1 J = true := by
    rw [book_of_atPure h hA h₀, book_is_written h₀,
      laysB_congr bookW 1 J (bareJob ({ piUFull with place := placeU } : P12) (membersU A') freshU :
        TestJob Unit Unit) hp e2 e3]
    exact lU
  obtain ⟨-, sh2, -⟩ := planOk_all (atPure_planOk h.laid hA)
  exact fits_at_numbers A.B 1 (Or.inr rfl) J _ hp two_stages_U hl
    (fun b hb => (shaped_parts (sh2 b hb).2).1)
    (rounds_of_alike (alike_at_atPure h hA).shared rounds_at_U)

/-- **Each side of halfO fits** at onlineProverFromPublicFiles's book and description, behind the guard. -/
theorem testOnOmega_fits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (wt : W₁ → Weights) :
    ∀ g ∈ halfO wt Zp, SideFits A.B 1 A.F.shared.blocksInOrder g := by
  intro g hg
  unfold halfO at hg
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
  obtain ⟨J₀, h0, e1, e2, e3⟩ := realO_bare wt Zp J (Option.mem_toList.1 hJ)
  unfold bareO at h0
  obtain ⟨F, hF, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain rfl : F = fourOf Np :=
    Option.some.inj (hF.symm.trans (ProofFile.Honest.K12.Light.stages_at_head h.toAtMg).1)
  obtain ⟨p, hpO, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.1 h0
  have hp : J.p = ({ piOFull with place := placeO } : P12) :=
    e1.trans (fourO_written h.toAtMg hpO)
  obtain ⟨-, lO⟩ := lays_at_head h.toAtMg (sendPub_plan h.toAtMg hA')
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  have hl : laysB A.B 1 J = true := by
    rw [book_of_atPure h hA h₀, book_is_written h₀,
      laysB_congr bookW 1 J (bareJob ({ piOFull with place := placeO } : P12) (membersO A') freshO :
        TestJob Unit Unit) hp e2 e3]
    exact lO
  obtain ⟨-, sh2, -⟩ := planOk_all (atPure_planOk h.laid hA)
  exact SideFits.guarded (fits_at_numbers A.B 1 (Or.inr rfl) J _ hp two_stages_O hl
    (fun b hb => (shaped_parts (sh2 b hb).2).1)
    (rounds_of_alike (alike_at_atPure h hA).shared rounds_at_O))

/-- **The frame lends each side of halfU**, at every run's coins, at onlineProverFromPublicFiles's book. -/
theorem testOnU_lends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (wt : W₁ → Weights)
    (enc : W₁ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) :
    ∀ g ∈ halfU wt enc Zp, ∀ k : Coins A.B,
      ∃ c, lendRow A.B (A.B.rowsOf 1) (k.look 1) placeU g.parts 0 = .ok c := by
  intro g hg k
  have hp := halfU_place wt enc Zp g hg
  have p2 := written_places_all.2.1
  rw [VerifiableInference.Desc.alike₂_place _ _ (alike_at_atPure h hA).shared, ← hp] at p2
  have q := lends_of_fits (testOnU_fits h hA wt enc g hg) p2 k
  rw [hp] at q
  exact q

/-- **The frame lends each side of halfO**, at every run's coins, at onlineProverFromPublicFiles's book. -/
theorem testOnOmega_lends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (wt : W₁ → Weights) :
    ∀ g ∈ halfO wt Zp, ∀ k : Coins A.B,
      ∃ c, lendRow A.B (A.B.rowsOf 1) (k.look 1) placeO g.parts 0 = .ok c := by
  intro g hg k
  have hp := halfO_place wt Zp g hg
  have p3 := written_places_all.2.2.1
  rw [VerifiableInference.Desc.alike₂_place _ _ (alike_at_atPure h hA).shared, ← hp] at p3
  have q := lends_of_fits (testOnOmega_fits h hA wt g hg) p3 k
  rw [hp] at q
  exact q

/-- **Every side of the kind K12 in sharedWithUO fits**, at the book and description of any
filling. -/
theorem sharedTests_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (I : WiderIn W₁) :
    ∀ g ∈ sharedWithUO I Zp, g.place.kind = KindName.K12 →
      SideFits A.B 1 A.F.shared.blocksInOrder g := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)
  intro g hg hk
  rw [sharedWithUO_ok I h6, sharedWithU_ok I h6] at hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · have q := ProofFile.Honest.K14.six_places _ _ _ _ g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at q
      rcases q with e | e | e | e | e | e | e | e <;>
        (rw [e] at hk; exact absurd hk (by decide))
    · exact testOnU_fits h hA _ _ g hg
  · exact testOnOmega_fits h hA _ g hg

/-- **At the filling every side of the kind K12 in the shared chain pays.** -/
theorem sharedTests_pay {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared .K12 := by
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, e2, -⟩ := atPure_ok hA
  have es : A.H.shared = sharedWithUO I Zp := by
    rw [e2, hZ] <;> rfl
  intro g hg hk
  rw [es] at hg
  exact sidePays_of_fits (sharedTests_fit h hA I g hg hk)

end AtFullSide.K12

#print axioms AtFullSide.K12.testOnU_fits
#print axioms AtFullSide.K12.testOnOmega_fits
#print axioms AtFullSide.K12.testOnU_lends
#print axioms AtFullSide.K12.testOnOmega_lends
#print axioms AtFullSide.K12.sharedTests_fit
#print axioms AtFullSide.K12.sharedTests_pay
