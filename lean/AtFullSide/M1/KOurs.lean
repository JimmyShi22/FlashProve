-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- a value of `KindRows` at our rows.
/-
AtFullSide/M1/KOurs.lean: `kOurs`, a value of `KindRows` (E2E/TheSides.lean) at the base filling: our four
lots on the first chain, on the shared chain the six, the test on G_u and the test on G_omega by place,
on the last chain the request's own test. NINE LOTS STAY BARE: this is not the K of the zero-knowledge
theorem. At `theG hd T kOurs` the kinds K1, K10, K14 pay with no premise on K. No property of the protocol
is claimed here.
-/
import AtFullSide.M1.KindAtTheG
import AtFullSide.K14.Sim.AtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open ProofFile.Honest.K12.Sim2 (lotU rowsW)
open ProofFile.Honest.K12.AtProof (rowsAtOmega)
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

section Generic
variable {V W Y Pb : Type}

/-- A row of a list whose places are apart is named by its half. -/
theorem named_of_map {hs : List (Placed V W Y)} {rs : List (Unlettered V W Y Pb)}
    (e : rs.map (·.half) = hs) : ∀ r ∈ rs, hs.any (fun h => h.place == r.place) = true := by
  intro r hr
  subst e
  exact List.any_eq_true.2 ⟨r.half, List.mem_map.2 ⟨r, hr, rfl⟩, beq_self_eq_true _⟩

/-- Where the places are apart, the row found at a side's place has that half. -/
theorem fit_of_map {hs : List (Placed V W Y)} {rs : List (Unlettered V W Y Pb)}
    (e : rs.map (·.half) = hs) (ha : (rs.map (·.place)).Nodup) :
    ∀ h ∈ hs, ∀ r, (rs.find? fun r => r.place == h.place) = some r → r.half = h := by
  intro h hh r hf
  subst e
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hh
  have hm := List.mem_of_find?_eq_some hf
  have hp : r.place = r₀.half.place :=
    beq_iff_eq.1 (List.find?_some (p := fun r : Unlettered V W Y Pb => r.place == r₀.half.place) hf)
  have : r = r₀ := List.inj_on_of_nodup_map ha hm hr₀ hp
  rw [this]

/-- **Laying rows by place over their own halves gives them back.** -/
theorem overlay_self {hs : List (Placed V W Y)} {rs : List (Unlettered V W Y Pb)}
    (e : rs.map (·.half) = hs) (ha : (rs.map (·.place)).Nodup) : hs.map (overlayRow rs) = rs := by
  subst e
  rw [List.map_map]
  refine (List.map_congr_left fun r hr => ?_).trans (List.map_id _)
  show overlayRow rs r.half = r
  have hf : (rs.find? fun x => x.place == r.half.place) = some r :=
    OnBytes.SendSim.Seat.find_of_nodup (fun x : Unlettered V W Y Pb => x.place) rs ha r hr
  unfold overlayRow
  rw [hf]

theorem apart_of_short {l : List (Unlettered V W Y Pb)} (h : l.length ≤ 1) :
    (l.map (·.place)).Nodup := by
  match l, h with
  | [], _ => exact List.nodup_nil
  | [_], _ => exact List.nodup_singleton _

end Generic

theorem rowsU_short (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((lotU .shared matrixInput.weights encOf).rows Z G).length ≤ 1 := by
  show ((ProofFile.Honest.K12.AtProof.realU (matrixInput.weights Z) (encOf Z) Z).toList.map _).length ≤ 1
  cases ProofFile.Honest.K12.AtProof.realU (matrixInput.weights Z) (encOf Z) Z <;> simp

theorem rowsO_short (Z : ProofFile.Pub) :
    (rowsAtOmega (matrixInput.weights Z) Z).length ≤ 1 := by
  unfold rowsAtOmega
  generalize ((ProofFile.Honest.K12.AtProof.four Z).bind _) = o
  cases o <;> simp

theorem rowsW_short (Z : ProofFile.Pub) (G : ProofFile.Ground) : (secondOurs Z G).length ≤ 1 := by
  unfold secondOurs rowsW
  split
  · generalize (ProofFile.Honest.K12.AtProof.realW _ _ _ _ _ _ _ _ _ _) = o
    cases o <;> simp
  · simp

/-- **The shared rows' places are apart.** -/
theorem shared_apart {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : ProofFile.Ground) :
    ((sharedOurs Zp Np G).map (·.place)).Nodup := by
  unfold sharedOurs
  rw [List.map_append, List.map_append]
  have eU : ((lotU .shared matrixInput.weights encOf).rows Zp G).map (·.half) =
      ProofFile.Honest.K12.AtProof.halfU (matrixInput.weights Zp) (encOf Zp) Zp :=
    ProofFile.Honest.K12.Sim2.lotU_halves .shared matrixInput.weights encOf Zp G
  have eO := ProofFile.Honest.K12.AtProof.rowsAtOmega_half (matrixInput.weights Zp) Zp
  refine List.nodup_append.2 ⟨ProofFile.Honest.Term.base_apart (files := files) h, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨apart_of_short (rowsU_short Zp G), apart_of_short (rowsO_short Zp), ?_⟩
    intro a ha b hb e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
    have e1 := AtFullSide.K12.halfU_place _ _ _ r.half (eU ▸ List.mem_map.2 ⟨r, hr, rfl⟩)
    have e2 := AtFullSide.K12.halfO_place _ _ r'.half (eO ▸ List.mem_map.2 ⟨r', hr', rfl⟩)
    exact absurd (e1.symm.trans (e.trans e2)) (by decide)
  · intro a ha b hb e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    have hk := rest_k12 Zp G
    rcases List.mem_append.1 hb with h1 | h1
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h1
      exact ProofFile.Honest.Term.base_not_K12 (files := files) h r hr
        ((congrArg Place.kind e).trans (hk r' (List.mem_append_left _ hr')))
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h1
      exact ProofFile.Honest.Term.base_not_K12 (files := files) h r hr
        ((congrArg Place.kind e).trans (hk r' (List.mem_append_right _ hr')))

/-- **The value at our rows.** -/
noncomputable def kOurs {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit)
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀) : KindRows baseFill A₀.Z A₀.G where
  lots := mineOurs
  named := mine_named
  apart := mine_apart
  lots_fit := mine_hm _ _
  shared := sharedOurs A₀.Z Np A₀.G
  shared_named := named_of_map (shared_fit h _)
  shared_apart := shared_apart h _
  shared_fit := fit_of_map (shared_fit h _) (shared_apart h _)
  second := secondOurs A₀.Z A₀.G
  second_named := named_of_map (second_fit _ _)
  second_apart := apart_of_short (rowsW_short _ _)
  second_fit := fit_of_map (second_fit _ _) (apart_of_short (rowsW_short _ _))

section
variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- The slots' shared rows are ours, in order. -/
theorem kOurs_shared (hd : HeadAtReturn files A₀) :
    (kOurs A₀ hd.head).slots.shared = sharedOurs A₀.Z hd.places A₀.G :=
  overlay_self (shared_fit hd.head _) (shared_apart hd.head _)

/-- The slots' last rows are ours. -/
theorem kOurs_second (hd : HeadAtReturn files A₀) :
    (kOurs A₀ hd.head).slots.second = secondOurs A₀.Z A₀.G :=
  overlay_self (second_fit _ _) (apart_of_short (rowsW_short _ _))

/-- **At `theG` at our rows the kinds K1, K10, K14 pay, no premise on K.** -/
theorem kOurs_pays (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) :
    VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K14 := by
  refine ⟨kindPays_K1_theG hd hS hL made T _ ?_ ?_ ?_,
    kindPays_K10_theG hd hS hL made T _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
    kindPays_K14_theG hd hS hL made T _ ?_ ?_⟩
  · exact OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mineOurs mine_apart _
      (List.mem_cons_self ..)
  · exact OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mineOurs mine_apart _
      (by simp [mineOurs])
  · rw [kOurs_shared]
    exact rows_of_shared _ _ _ KindName.K1 (by decide)
  · rw [kOurs_shared]
    exact rows_of_shared _ _ _ KindName.K14 (by decide)
  · rw [kOurs_second]
    intro r hr hk
    have h2 := second_k12 _ _ r hr
    rw [hk] at h2
    cases h2

/-- **The same at the description that the return holds.** -/
theorem kOurs_pays_ofReturn (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) :
    VerifiableInference.Compilation.KindPays (theGOfReturn made hd T (kOurs A₀ hd.head)) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theGOfReturn made hd T (kOurs A₀ hd.head)) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theGOfReturn made hd T (kOurs A₀ hd.head)) KindName.K14 := by
  obtain ⟨a, b, c⟩ := kOurs_pays hd hS hL made T
  exact ⟨castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K1) _ a,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K10) _ b,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K14) _ c⟩

end

/-- **At three public files.** The head is bound under ∃ here: a caller with a head of its own takes
`kOurs_pays` or `kOurs_pays_ofReturn`. -/
def KOursAt (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (hd : HeadAtReturn files A₀),
    ProofFile.Honest.Term.baseMaker files = .ok A₀ ∧ ∀ (Wt : Type) (T : ThreadParts A₀ Wt),
      VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (kOurs A₀ hd.head)) KindName.K14

/-- **At the named files, under no premise.** Nine lots are bare at this K: not the K of the
zero-knowledge theorem. -/
theorem kOurs_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : KOursAt files := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named files hZ
  have live := AtFullSide.K14.live_named files hZ
  have hS : VerifierAndGoals.InScope files = true := by
    rcases hZ with rfl | rfl
    · exact AtFullSide.Tie.premises_zFull.1
    · exact AtFullSide.Tie.premises_zGap.1
  obtain ⟨A, hA, -, -, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest ProofFile.Honest.Term.range_matrixInput
  obtain ⟨hZp, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZp.symm.trans h.laid.pub)
  subst eZ
  exact ⟨A, ⟨⟨_, hA⟩, Np, cF, x₀, h⟩, hA, fun Wt T => kOurs_pays ⟨⟨_, hA⟩, Np, cF, x₀, h⟩ hS live hA T⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.kOurs
#print axioms AtFullSide.M1.kOurs_pays
#print axioms AtFullSide.M1.kOurs_named
#print axioms AtFullSide.M1.kOurs_pays_ofReturn
