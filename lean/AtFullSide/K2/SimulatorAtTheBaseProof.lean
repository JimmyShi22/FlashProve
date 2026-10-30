-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SimulatorAtTheBaseProof.lean: the proof of SimulatorAtTheBase
(AtFullSide/K2/SimulatorAtTheBase.lean).

  lot_is_the_fillings   with the simulators forgotten, the lot is the base filling's second
  sides_are_the_rows    the base prover's sides of this kind are the rows' sides
  simulatorAtTheBase    the statements, at public files that the library's test accepts

By: P5J.head_exists_at_name and P5J.owed_of_live (the head exists where the files pass), its field
laid.opened (the opening), AtFullSide.K14.makers_book_one (the maker's book and description),
atPure_ok, good_at_place, bud_at_place, book_at_place, first_kind_base, switchSLot_toHLot.

Limits. Statements on the kind K2 at the base filling and at any filling. It says nothing of what this kind plays or
of the verifier's answer. All limits of the files named hold.
-/
import AtFullSide.K2.SimulatorAtTheBase
import AtFullSide.K2.GoodAtPlace
import AtFullSide.K2.BookAtPlace
import AtFullSide.K14.MakersBookOne
import AtFullSide.K2.HalvesAtFilling
import AtFullSide.K2.KindOtherChains
import AtFullSide.K2.KindSpends
import Johnson.Desc.ProofFile.Honest.K2.Law.KindPlaces
import Johnson.Desc.ProofFile.Honest.K2.Law.ShowsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import Johnson.HonestTrace.U3Fit.ReadsDebt3
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesCount
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open VerifiableInference.Desc (Chain)
open P5J (AtMgA F0T TS)

section
variable {W₀ Rc X : Type}

/-- The lot's sides with the simulators forgotten. -/
theorem lot_toHLot (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins) :
    (switchSimLotAt (X := X) weights coins).toHLot =
      HLot.byPub weights fun wt =>
        HLot.byRows (widerRows OnBytes.HonestTrace.Sz.ref) fun D =>
          switchLot D fun w => ⟨w.trace, wt w.w₀, coins w.rc⟩ := by
  unfold switchSimLotAt
  rw [SLot.byPub_toHLot]
  congr 1
  funext wt
  rw [SLot.byRows_toHLot]
  congr 1
  funext D
  exact switchSLot_toHLot D _

/-- A row of the lot is the kind's row at a place. -/
theorem row_at_place {weights : ProofFile.Pub → W₀ → Weights} {coins : Rc → IndexCommitterCoins} {Zp : ProofFile.Pub}
    {G : ProofFile.Ground} {r' : Unlettered (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X
            ProofFile.Inst}
    (hr : r' ∈ (switchSimLotAt (X := X) weights coins).rows Zp G) :
    ∃ p ∈ switchPlaces Zp G, r'.place = p.place ∧ r'.On = (fun _ _ _ _ => True) ∧
      r'.bud = switchBud p ∧
      r'.row = switchRow (coreSender freshTable) (widerRows OnBytes.HonestTrace.Sz.ref Zp G)
        (fun w => ⟨w.trace, weights Zp w.w₀, coins w.rc⟩) (lotClosing Zp G) p
        (publicOk (widerRows OnBytes.HonestTrace.Sz.ref Zp G) G.first.layout p
          ((segmentsOf Zp G).take p.link)) (roundsAt Zp G p.place) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  exact ⟨p, hp, rfl, rfl, rfl, rfl⟩

end

/-- **No part of a row stops.** -/
theorem noPartStops : NoPartStops := by
  intro W₀ Rc X weights coins Z G r hr x hx
  obtain ⟨p, -, -, -, -, e⟩ := row_at_place hr
  rw [e] at hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  obtain rfl := List.mem_singleton.1 hP
  exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **With the simulators forgotten it is the base filling's second lot.** -/
theorem lot_is_the_fillings : LotIsTheFillings := by
  unfold LotIsTheFillings
  rw [lot_toHLot]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The sides of this kind at the base filling are the rows' sides.** -/
theorem sides_are_the_rows (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) : SidesAreTheRows Z := by
  intro A hA
  refine ⟨?_, others_no_kind h hA⟩
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := atPure_ok hA
  rw [h8, first_kind_base]
  have e : (baseSimLot.rows A.Z A.G).map (·.half) = baseSimLot.toHLot.halves A.Z A.G := rfl
  rw [e, lot_toHLot]
  rfl

/-- What the head gives of a return of the maker, at any filling. -/
theorem return_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.Z = Zp ∧ A.G = Bs.G₀ ∧ A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) Johnson.G.proofSendsFull.1
        Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
        (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, -, hB, -, -, hAll⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨eB, eF⟩ := hAll _ _ _ _ _ P A hA
  obtain ⟨h1, h2, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (h1.symm.trans O.pub)
  refine ⟨eZ, ?_, eF, by rw [eB]; exact hB⟩
  rw [eZ] at h2
  exact Option.some.inj (h2.symm.trans O.blank)

/-- **The statements at public files that the library's test accepts.** -/
theorem simulatorAtTheBase : SimulatorAtTheBase := by
  refine ⟨noPartStops, lot_is_the_fillings, fun Z scope live => ?_⟩
  obtain ⟨pp, read⟩ := H2K.Sizes.inScope_readFiles scope
  obtain ⟨Zp, Np, cF, x₀, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨sides_are_the_rows h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W₀ Rc X₀ X P A hA
    obtain ⟨eZ, eG, eF, -⟩ := return_at_head h O hA
    obtain ⟨Za, Ga, Fa, Ba, Ha, ra, da⟩ := A
    dsimp only at eZ eG eF ⊢
    subst eZ eG eF
    have hP := ProofFile.Honest.K2.Law.places_at_head h.toAtMg O
    refine ⟨?_, ?_, fun p hp => ?_, fun b hb hk => ?_⟩
    · rw [hP]
      exact ProofFile.Honest.K2.Law.placesW_count
    · rw [hP]
      exact ProofFile.Honest.K2.Law.places_nodup_kind
    · rw [hP] at hp
      exact ProofFile.Honest.K2.Law.kind_of_written hp
    · obtain ⟨p, hp, e⟩ := ProofFile.Honest.K2.Law.block_has_place scope read O hb hk
      exact ⟨p, hP ▸ hp, e⟩
  · intro W₀ Rc X₀ X P A hA weights coins r' hr fs
    obtain ⟨eZ, eG, eF, hB⟩ := return_at_head h O hA
    obtain ⟨Za, Ga, Fa, Ba, Ha, ra, da⟩ := A
    dsimp only at eZ eG eF hB hr ⊢
    subst eZ eG eF
    obtain ⟨p, hp, e1, e2, e3, e4⟩ := row_at_place hr
    obtain ⟨σ, hs, hG⟩ := good_at_place (X := X) h O hp
      (book_at_place h O hB hp) (widerRows OnBytes.HonestTrace.Sz.ref _ _)
      (fun w : Local W₀ Rc ProofFile.Inst Cells => ⟨w.trace, weights _ w.w₀, coins w.rc⟩) fs
    refine ⟨σ, ?_, fun pre => ?_⟩
    · rw [e1, e4]
      exact hs
    · rw [e2, e3]
      exact hG pre
  · intro W₀ Rc X₀ X P A hA weights coins r' hr σ hσ u hu pre t n hcut hn ρ hρ
    obtain ⟨eZ, eG, eF, -⟩ := return_at_head h O hA
    obtain ⟨Za, Ga, Fa, Ba, Ha, ra, da⟩ := A
    dsimp only at eZ eG eF hr hσ hcut hρ ⊢
    subst eZ eG eF
    obtain ⟨p, hp, e1, -, e3, e4⟩ := row_at_place hr
    rw [e1, e4] at hσ
    rw [e3]
    exact bud_at_place scope live O (ProofFile.Honest.K2.Law.places_at_head h.toAtMg O ▸ hp) hσ u hu pre t
      n hcut hn ρ hρ
  · intro W₀ Rc X₀ X P A hA weights coins r' hr fs σ hσ u hu c m ds asks hd hq
    obtain ⟨eZ, eG, eF, -⟩ := return_at_head h O hA
    obtain ⟨Za, Ga, Fa, Ba, Ha, ra, da⟩ := A
    dsimp only at eZ eG eF hr hσ hq ⊢
    subst eZ eG eF
    obtain ⟨p, hp, e1, -, -, e4⟩ := row_at_place hr
    rw [e1, e4] at hσ
    exact ProofFile.Honest.K2.Law.shows_at_head h O hp _ _ _ fs hσ u hu c m ds asks hd (hq p hp e1.symm)
  · intro W₀ Rc X₀ X P A hA ξ hx p hp
    obtain ⟨eZ, eG, eF, -⟩ := return_at_head h O hA
    obtain ⟨Za, Ga, Fa, Ba, Ha, ra, da⟩ := A
    dsimp only at eZ eG eF hx hp ⊢
    subst eZ eG eF
    exact ProofFile.Honest.K2.Law.publicOk_of_reads h O
      (OnBytes.HonestTrace.U3.Fit.readsLight_of_att h O hx
        (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O)) p hp
  · intro W₀ Rc Tr X₀ X P A hA e he ho hk
    obtain ⟨B, -, -, -, ha, hAll⟩ := AtFullSide.K14.makers_book_one h
    obtain ⟨eB, -⟩ := hAll _ _ _ _ _ P A hA
    rw [eB, ha] at he
    have t := List.all_eq_true.1 noKindSpends e he
    simp [ho, hk] at t

end AtFullSide.K2

#print axioms AtFullSide.K2.noPartStops
#print axioms AtFullSide.K2.lot_is_the_fillings
#print axioms AtFullSide.K2.sides_are_the_rows
#print axioms AtFullSide.K2.simulatorAtTheBase
