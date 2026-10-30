-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowFree.lean: the measure of the private stops with no premise on a run.

The set of an online prover whose halves are pinned lies inside the set of the thin prover
(Johnson/FrontRoad/ThinProverSpec.lean), which has the twenty-five pinned halves alone: where a
combination leaves its window at a member, the thin prover stops by its second stop, since it has
no first stop. The thin prover's measure is proved with no premise on a run. So the prover's
preparation need not return at any input.

  stopAt_only_hid, row_only_hid, chain_only_hid   a list of parts with no first stop stops by a
                        second stop alone
  parOwn_congr          parOwn at two lists of matrices that agree below 25
  hid_sub_thin          the set lies inside the thin prover's
  window_free_of_pin    the measure at 2 ^ (-174)

Limits. The thin prover is no honest prover: it serves here as a set of messages alone. The bound
holds of the prover's set, and it says nothing of what the prover plays.
-/
import Johnson.P1K8R.WindowOfPin
import Johnson.P1K8R.WindowsHold
import Johnson.FrontRoad.ThinProver
import Johnson.FrontRoad.PinPublic

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace P1K8
open Iop Prob AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open OnBytes.FrontRoad
open OnBytes.HonestTrace (cellsC matsOf)
open VerifiableInference.Desc (Block Place KindName)
open ProofFile.Honest (Prover ProverCoinCounts Sides Cells chainStopAt drawsLo Placed Part rowStopAt Why Local)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open FlashProve (dataAtFiles)
open OnBytes.Maker (WholeD)
open P5J

attribute [-instance] Inst.Model.Scl.ref

local instance (priority := high) nonemptyPadZ_windowFree : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyOfInhabited_windowFree {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

section
variable {V W Y S Cl : Type}

/-- A part with no first stop stops by a second stop alone. -/
theorem stopAt_only_hid (p : Part V W Y) (hb : ∀ l o, p.bad l o = none) (v : Option V)
    (loc ds : List Fmt.Drawn) {y : Why} (h : p.stopAt v loc ds = some y) : y = Why.hid := by
  unfold ProofFile.Honest.Part.stopAt at h
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some h
  rw [hb] at hj
  simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hj
  split at hj
  · exact (Option.some.inj hj).symm
  · cases hj

/-- So does a list of such parts. -/
theorem row_only_hid (v : Option V) :
    ∀ (ps : List (Part V W Y)), (∀ p ∈ ps, ∀ l o, p.bad l o = none) →
      ∀ (loc ds : List Fmt.Drawn) {y : Why}, rowStopAt v ps loc ds = some y → y = Why.hid
  | [], _, _, _, _, h => by cases h
  | p :: ps, hb, loc, ds, y, h => by
    have e : rowStopAt v (p :: ps) loc ds = (p.stopAt v loc (ds.take p.moves.length)).or
      (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length)) := rfl
    rw [e] at h
    cases hs : p.stopAt v loc (ds.take p.moves.length) with
    | some z =>
      rw [hs] at h
      obtain rfl : z = y := by simpa using h
      exact stopAt_only_hid p (hb p List.mem_cons_self) v loc _ hs
    | none =>
      rw [hs] at h
      exact row_only_hid v ps (fun q hq => hb q (List.mem_cons_of_mem _ hq)) _ _ (by simpa using h)

/-- And a chain whose halves hold such parts. -/
theorem chain_only_hid (v : Option V) (hs : List (Placed V W Y))
    (hb : ∀ x ∈ hs, ∀ p ∈ x.parts, ∀ l o, p.bad l o = none) (bs : List (Block S Cl))
    (loc ds : List Fmt.Drawn) {y : Why} (h : chainStopAt v bs hs loc ds = some y) :
    y = Why.hid := by
  obtain ⟨A, b, B, -, -, h₁⟩ := (chainStop_iff v hs y bs loc ds).1 h
  unfold memberStop at h₁
  cases hg : hs.find? (fun x => x.place == b.place) with
  | none =>
    rw [hg] at h₁
    cases h₁
  | some g =>
    rw [hg] at h₁
    exact row_only_hid v g.parts (hb g (List.mem_of_find?_eq_some hg)) _ _ h₁

end

/-- parOwn at two lists of matrices that agree below 25, at a ground of 25 links. -/
theorem parOwn_congr {Zp : ProofFile.Pub} {mats mats' : ℕ → List (ℕ × String × ℕ)}
    {a : Place} {P : VerifiableInference.Desc.First.K8.Par × List (ℕ × String × ℕ)}
    (hs : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → G₀.built.size = 25)
    (hM : ∀ l < 25, mats l = mats' l) (h : parOwn Zp mats a = some P) :
    parOwn Zp mats' a = some P := by
  obtain ⟨hk, l, G₀, Xl, hl, hG, hX, rfl⟩ := parOwn_some Zp mats a P h
  have h25 : l < 25 := hs G₀ hG ▸ (Array.getElem?_eq_some_iff.1 hX).1
  unfold parOwn
  rw [if_pos hk, hl]
  show ((ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
    (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats' l)) = _
  rw [hG]
  show (G₀.built[l]?).map (fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats' l)) = _
  rw [hX, hM l h25]
  rfl

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Cells X₀ Xh)

/-- **The set lies inside the thin prover's.** -/
theorem hid_sub_thin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ)) (hM : ∀ l < 25, mats l = matsOf Zp.p.X l)
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) :
    ((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
        (x, (protocolAtFiles Z).recOf i ρ e) ⊆
      ((famG Z Zp Np cF run₂ run₃ (thinB Zp Np cF) (thinG Zp Np cF id H)
        (thinAt Zp (cellsC Zp.p.X) H)).at n).Hid (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) := by
  intro τ hτ
  obtain ⟨tr, ht, A, b, C, P, d, e₁, -, hp, hd, hl⟩ :=
    (hid_iff_of_pin Z Zp Np cF run₂ run₃ B H scope hr L hn mats h₁ h₃ n i ρ e x τ).1 hτ
  have hsz : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → G₀.built.size = 25 :=
    fun G₀ hG => (IM.ground_gets scope hr L.pub hG).1
  have hp' := parOwn_congr hsz hM hp
  have hpub := public_first Z Zp Np cF scope hr L
  have hpinT := thin_halves Z Zp Np cF scope hr L (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst)
    (X := Xh) (id : Cells → Cells)
  have hfit : ∀ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, ∀ P,
      parOwn Zp (matsOf Zp.p.X) b.place = some P →
      ProofFile.Honest.K8.smallFits P = true ∧ b.rounds.length = 1 := by
    intro b hb P hP
    have h := hpub b hb
    rw [hP] at h
    exact ⟨h.1, by rw [h.2]; rfl⟩
  have hlast : ∀ a, (descZ Zp Np cF).first.blocksInOrder.getLast? = some a →
      ((thinFirst Zp (id : Cells → Cells) :
        List (Placed (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells) Xh)).find?
        fun h => h.place == a.place) = none ∧ parOwn Zp (matsOf Zp.p.X) a.place = none := by
    intro a ha
    have hk : a.place.kind = KindName.frame := by
      have h := (k8_places_front Z Zp Np cF scope hr L).2
      rw [ha] at h
      exact Option.some.inj h
    refine ⟨?_, parOwn_other Zp _ a.place (by rw [hk]; decide)⟩
    cases hf : (thinFirst Zp (id : Cells → Cells) :
        List (Placed (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells)
          Xh)).find? (fun h => h.place == a.place) with
    | none => rfl
    | some g =>
      have hg := List.mem_of_find?_eq_some hf
      have hb' := List.find?_some hf
      have hq : g.place = a.place := eq_of_beq hb'
      have := thin_no_frame Zp (id : Cells → Cells) g hg
      rw [hq, hk] at this
      cases this
  have hbad : ∀ g ∈ (thinFirst Zp (id : Cells → Cells) :
      List (Placed (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells) Xh)),
      ∀ p ∈ g.parts, ∀ l o, p.bad l o = none := by
    intro g hg p hp l o
    obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hg
    obtain ⟨P', -, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl := List.mem_singleton.1 hp
    rfl
  refine (mem_hid_famG Z Zp Np cF run₂ run₃ _ _ _ n _ _ τ).2 ?_
  have hpf : (thinP Z Zp Np cF (id : Cells → Cells) (cellsC Zp.p.X) H).first =
      thinFirst Zp (id : Cells → Cells) := (bare_forgets _ _ _ _).1
  have htr : (thinP Z Zp Np cF (id : Cells → Cells) (cellsC Zp.p.X) H).trace i
      (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e)) = some tr := by
    rw [← ht, hT]
    rfl
  unfold ProofFile.Honest.hidB
  show Option.any _ ((thinP Z Zp Np cF (id : Cells → Cells) (cellsC Zp.p.X) H).trace i
    (LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e))) = true
  rw [htr, hpf]
  simp only [Option.any_some, Bool.or_eq_true, beq_iff_eq]
  left
  cases hS : chainStopAt (some (⟨i, ρ, LPFD.Full.instanceAsPlainRecord (x, (protocolAtFiles Z).recOf i ρ e), tr⟩ :
      Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Cells)) (descZ Zp Np cF).first.blocksInOrder
      (thinFirst Zp (id : Cells → Cells)) []
      (drawsLo (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (Iop.Rho.lo _ τ)).1 with
  | none =>
    have hw := windows_hold (cells := id) (Zp := Zp) (mats := matsOf Zp.p.X) _
      (descZ Zp Np cF).first.blocksInOrder _ hpinT hfit hlast [] _ hS A C b e₁ P hp' d hd
    have : (VerifiableInference.Desc.First.K8.Honest.leaves P.1
        (ProofFile.Honest.K8.cellsAtOf tr P.2) d.trits.toArray).isSome = false := by
      have h' := hw
      simp only [id] at h'
      rw [h']
      rfl
    rw [this] at hl
    cases hl
  | some y =>
    have hy := chain_only_hid _ _ hbad _ _ _ hS
    subst hy
    exact hS

/-- **The measure, with no premise on a run.** -/
theorem window_free_of_pin (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (mats : ℕ → List (ℕ × String × ℕ)) (hM : ∀ l < 25, mats l = matsOf Zp.p.X l)
    (h₁ : RowsPinned (parOwn Zp mats) id H.first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) id H.second (descZ Zp Np cF).second.blocksInOrder)
    (hT : H.trace = modelAt Zp.p.X (cellsC Zp.p.X))
    (n : ℕ) (i : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (x : LPFD.Full.XF) (hx : RyesZ Z i x) :
    prRho (((onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P H).at n).Hid (i, ρ, e)
      (x, (protocolAtFiles Z).recOf i ρ e)) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := by
  have hS := sessionStops_at_thin Z Zp Np cF run₂ run₃ H scope hr live L (id : Cells → Cells)
    (cellsC Zp.p.X) (readsAs_cells Zp.p.X) (RyesZ Z) (fun _ => True) (fun _ => True)
  have hY := validYes Z Zp Np cF run₂ run₃ (thinB Zp Np cF) (thinG Zp Np cF id H)
    (thinAt Zp (cellsC Zp.p.X) H) (Yes := RyesZ Z) (fun _ _ h => h)
    (AtPublicFiles.AtZero.itemsZero_of_data L.data) n i ρ e x trivial trivial hx
  have hb := hS n (i, ρ, e) (x, (protocolAtFiles Z).recOf i ρ e) ⟨trivial, trivial, hY⟩
  rw [add_zero] at hb
  have hw : windowBound Zp = ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) := window_number scope hr L
  refine le_trans (pr_mono _ (hid_sub_thin Z Zp Np cF run₂ run₃ B H scope hr L hn mats hM h₁ h₃ hT
    n i ρ e x)) ?_
  rw [← hw]
  exact hb

end

end P1K8

#print axioms P1K8.stopAt_only_hid
#print axioms P1K8.chain_only_hid
#print axioms P1K8.parOwn_congr
#print axioms P1K8.hid_sub_thin
#print axioms P1K8.window_free_of_pin
