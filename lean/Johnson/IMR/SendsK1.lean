-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsK1.lean: hearSpotsFit · hear_spots_fit BEAR THESE NAMES BECAUSE Johnson/IMR/TableW.lean declares IM.hearFit, at another type. FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): THE DEBT SendsAt (Johnson/IMR/SendsFold.lean) AT KIND K1's 52 PLACES, AT THE TERM snAt (Johnson/Desc/K12/Door/SentAtPlace.lean): K1's first sending (number 2) · its fifty later sendings ·
W's commitment (356). THESE LEMMAS OF K1's AND K13's FILES ARE CALLED: K1.firstAtS_seated · K1.commitAtS_seated (K1/Law/SeatedAtRecord.lean) · K13.Law.atM4_seated (K13/Law/SeatedM4.lean) · K1.step_ok (K1/Law/AtRecord.lean) · K1.roundsFit_two (K1/Law/Step.lean). Compiled with the whole library.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
AT EVERY STATE (SendsAt, not only SendsOn): K1's decisions read what is sent off their own parameter, not off the state.

  two_rounds        a step's accepting at a sub-protocol with just two declared rounds holds the decision's on two rounds. (A joining of K1.step_ok and K1.roundsFit_two; K1's files have the like at their own Step relations: StepG.decide · StepM4.decide.)
  sends_firstAtS · sends_laterAt · sends_k1Reads · sends_atM4   the law at the four makers.
  hear_spots_fit · hear_placeW · place_356   the closed facts, by the kernel: which place of the written list stands at a number in front of a batching; at 356.
  sends_K1_link · sends_K1_back   SendDebts' debts at K1's 52 places, at sn := snAt Z Bs.G₀ placesW, codes := Z.first.codes: AT EVERY STATE · AT EVERY o · NO PREMISE ON SCOPE.

What is not claimed. K2's 25 · K12's 1 · the batching and behind it (50). The plan's side. No soundness.
-/
import Johnson.IMR.SendsPaid
import Johnson.IMR.SendsBridge
import Johnson.IMR.K1Seat
import Johnson.IMR.SeatKeeps
import Johnson.Desc.Sound.Gather
import Johnson.Desc.K1.Law.Step
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K13.Law.SeatedM4
import Johnson.Desc.K13.Keeps

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S kindsBeforeBatching backKinds)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

/-- A step's accepting at a sub-protocol with just two declared rounds holds the decision's on two rounds. -/
theorem two_rounds {C : Type} {b : Block S C} {a c : Fmt.DeclaredRound} (hr : b.rounds = [a, c]) {ft : ℕ}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) : ∃ r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' := by
  obtain ⟨h1, gs, h2⟩ := VerifiableInference.Desc.K1.step_ok ft b s s' rs cols n hy
  rw [hr] at h1
  obtain ⟨r₁, r₂, rfl⟩ := VerifiableInference.Desc.K1.roundsFit_two a c rs h1
  exact ⟨_, _, gs, h2⟩

/-- K1's first sending. -/
theorem sends_firstAtS (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (ft : ℕ) :
    SendsAt ft q.codes [(VerifiableInference.Desc.K1.firstPar q gp).sent]
      ((VerifiableInference.Desc.K1.firstSegmentOpening q gp : Block S Unit).retype : Block S Cl) := by
  refine sends_of_seatedBy (P := VerifiableInference.Desc.K1.firstPar q gp) rfl fun s s' rs cols n hy => ?_
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K1.firstSegmentOpening q gp : Block S Unit).decide s [r₁, r₂] gs = .ok s' := hd
  exact ⟨((Meaning.K2.firstAtS_grows (Cl := Unit) q gp).1 s _ _ s' hd').1,
    VerifiableInference.Desc.K1.firstAtS_seated q gp s s' r₁ r₂ gs hd'⟩

/-- A later sending. -/
theorem sends_laterAt (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) (ft : ℕ) :
    SendsAt ft q.codes [(VerifiableInference.Desc.K1.parLater q gp link piece moment).sent]
      ((VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).retype : Block S Cl) := by
  refine sends_of_seatedBy (P := VerifiableInference.Desc.K1.parLater q gp link piece moment) rfl
    fun s s' rs cols n hy => ?_
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).decide s [r₁, r₂] gs =
      .ok s' := hd
  exact ⟨((Meaning.K2.laterAt_grows (Cl := Unit) q gp link piece moment arrays).1 s _ _ s' hd').1,
    VerifiableInference.Desc.K1.commitAtS_seated _ link moment arrays s s' r₁ r₂ gs hd'⟩

/-- The reads' place's sub-protocol: K1's later sending with the quiet sub-protocol joined behind it. -/
theorem sends_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : OnBytes.Model.Stages.LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (ft : ℕ) :
    SendsAt ft G.first.codes
      [(VerifiableInference.Desc.K1.parLater G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1).sent]
      ((k1Reads Z G l X pr reads).retype : Block S Cl) := by
  refine sends_of_seatedBy
    (P := VerifiableInference.Desc.K1.parLater G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1) rfl
    fun s s' rs cols n hy => ?_
  obtain ⟨h1, gs, h2⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hlen := VerifiableInference.Desc.Sound.roundsFit_len _ _ h1
  obtain ⟨u, hk, hq⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (x := (VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1 reads :
      Block S Unit).decide s ((rs.map VerifiableInference.Desc.noDigest).take 2) _) h2
  have h2le : 2 ≤ rs.length := by
    rw [hlen]
    show 2 ≤ (_ :: _ :: _ : List Fmt.DeclaredRound).length
    simp
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, (rs.map VerifiableInference.Desc.noDigest).take 2 = [r₁, r₂] := by
    rcases rs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at h2le
    · simp at h2le
    · exact ⟨_, _, rfl⟩
  rw [e] at hk
  have Q := (Meaning.K2.orLoud_whole (R := Meaning.K2.Quiet)
    fun b hb => Meaning.K2.readsQuietAt_quiet hb).1 u _ _ s' hq
  have hs := VerifiableInference.Desc.K1.commitAtS_seated _ l 1 reads s u r₁ r₂ _ hk
  have hg := ((Meaning.K2.laterAt_grows (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
    reads).1 s _ _ u hk).1
  rw [Q.1.1, Q.1.2.2.1, Q.1.2.2.2]
  exact ⟨hg, hs⟩

/-- W's commitment. -/
theorem sends_atM4 (p : VerifiableInference.Desc.K13.Where) (P' : VerifiableInference.Desc.K1.Par) (ft : ℕ) :
    SendsAt ft P'.codes [P'.sent]
      ((VerifiableInference.Desc.K13.atM4 p (VerifiableInference.Desc.K1.sendAtS P') : Block S Unit).retype :
        Block S Cl) := by
  refine sends_of_seatedBy (P := P') rfl fun s s' rs cols n hy => ?_
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K13.atM4 p (VerifiableInference.Desc.K1.sendAtS P') :
      Block S Unit).decide s [r₁, r₂] gs = .ok s' := hd
  exact ⟨(VerifiableInference.Desc.K13.atM4_keeps
      VerifiableInference.Desc.Ground.groundKeeps_grows.quiet p _
      (VerifiableInference.Desc.K1.Rel.sendAtS_keeps VerifiableInference.Desc.Ground.groundKeeps_grows P')
      s _ _ s' hd').1, VerifiableInference.Desc.K13.Law.atM4_seated hd'⟩

/-- THE CLOSED FACT: the written list's place in front of a batching, by its number. (Its like
stands as hear_numbers | hear_number_at in Johnson/IMR/TableW.lean.) -/
def hearSpotsFit : Bool :=
  (List.range 25).all fun l => (List.range (nAt l)).all fun i =>
    placesW[14 * l + i + 2]? == ((kindsBeforeBatching (subAt l) (l == 0))[i]?).map fun k =>
      ({ chain := 1, link := some l, piece := i + 1, kind := k } : Place)

set_option maxRecDepth 1000000 in
theorem hear_spots_fit : hearSpotsFit = true := by decide +kernel

theorem hear_placeW {l i : ℕ} {k : KindName} (hl : l < 25)
    (hk : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k) :
    placesW[14 * l + i + 2]? = some { chain := 1, link := some l, piece := i + 1, kind := k } := by
  have hi : i < nAt l := by
    have h1 := (List.getElem?_eq_some_iff.1 hk).1
    have h2 : ∀ l < 25, (kindsBeforeBatching (subAt l) (l == 0)).length = nAt l := by decide
    rw [h2 l hl] at h1
    exact h1
  have h := hear_spots_fit
  unfold hearSpotsFit at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h l hl i hi, hk]
  rfl

set_option maxRecDepth 1000000 in
theorem place_356 : placesW[356]? = some { chain := 1, link := none, piece := 4, kind := .K1 } := by
  decide +kernel

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K1's places inside the links, the first sending among them**: the lot's own sub-protocol at (1, some l, i + 1, K1) pays the debt at the named term: at every state; at every o; no premise on scope. -/
theorem sends_K1_link (O : Open o pol lay KL F Z Bs base c A B) {ft : ℕ} {l i : ℕ} (hl : l < 25)
    (hk : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K1) {b' : Block S Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := .K1 }) :
    SendsAt ft Z.first.codes (snAt Z Bs.G₀ placesW (14 * l + i + 2)) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K1 hL hb' (by rw [hp]) (l := l) (by rw [hp])
  have hW := hear_placeW hl hk
  rw [← O.first]
  rcases k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, -, hn, rfl | rfl⟩
  · have e : (⟨1, some 0, 1, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l = 0 ∧ i = 0 := by
      injection e with _ e2 e3 _
      exact ⟨(Option.some.inj e2).symm, by omega⟩
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_first Z Bs.G₀ placesW _ 0 hW]
    exact sends_firstAtS _ _ ft
  · have e : (⟨1, some l', pr, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pr = i + 1 := by
      injection e with _ e2 e3 _
      exact ⟨Option.some.inj e2, e3⟩
    have h5 : i + 1 ≤ 5 ∧ i + 1 ≠ 1 := by rcases numbers_pieces hn with ⟨a, -⟩ | ⟨a, -⟩ <;> omega
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_later Z Bs.G₀ placesW _ l' (i + 1) hW h5.2,
      if_pos h5.1]
    exact sends_k1Reads Z Bs.G₀ l' X (i + 1) reads ft
  · have e : (⟨1, some l', pd, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pd = i + 1 := by
      injection e with _ e2 e3 _
      exact ⟨Option.some.inj e2, e3⟩
    have h5 : ¬ (i + 1 ≤ 5) ∧ i + 1 ≠ 1 := by rcases numbers_pieces hn with ⟨-, a⟩ | ⟨-, a⟩ <;> omega
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_later Z Bs.G₀ placesW _ l' (i + 1) hW h5.2,
      if_neg h5.1]
    exact sends_laterAt _ _ l' (i + 1) 2 digits ft

/-- **W's commitment (356)**: the lot's own sub-protocol at (1, none, 4, K1). -/
theorem sends_K1_back (O : Open o pol lay KL F Z Bs base c A B) {ft : ℕ} {b' : Block S Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := none, piece := 4, kind := .K1 }) :
    SendsAt ft Z.first.codes (snAt Z Bs.G₀ placesW 356) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨-, w, hw, rfl⟩ := lot_M4 hL hb' (by rw [hp]) (by rw [hp])
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  rw [VerifiableInference.Desc.K12.Door.snAt_w Z Bs.G₀ placesW 356 4 place_356, O.first, hm]
  exact sends_atM4 _ _ ft

end

end IM

#print axioms IM.sends_atM4
#print axioms IM.hear_spots_fit
#print axioms IM.hear_placeW
#print axioms IM.sends_K1_link
#print axioms IM.sends_K1_back
#print axioms IM.sends_k1Reads
#print axioms IM.two_rounds
#print axioms IM.sends_firstAtS
#print axioms IM.sends_laterAt
