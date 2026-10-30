-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ParOwn.lean: the function parOwn, which names at a place of the kind K8 the
description's own parameters of the smallness test at that place's link (k8Par,
Johnson/Desc/ProofFile/Lot/K8.lean), and none at a place of another kind. With it,
sessionStops_of_pinned (Johnson/FrontRoad/SessionStopsOfPinned.lean) and sessionStops_of_tiedOwn
(Johnson/FrontRoad/SessionStopsOfTrace.lean) at par := parOwn Zp mats (sessionStops_of_pinned_own,
sessionStops_of_tiedOwn_own): there the parameters are no variable: Zp, which parOwn reads, is the
public part computed from Z's three files (the field pub of LaidAt, Johnson/P5J/LaidOpens.lean). The
lists of matrices, mats, are free.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  parOwn   at a place a of the kind K8 with the link l, where the segments' structures without a
      request can be computed (blankBy, Johnson/Desc/ProofFile/Pub.lean) and have an entry Xl at l:
      the pair (k8Par Zp G₀ Xl l, mats l). None elsewhere. parOwn_other: none at a place of another
      kind. parOwn_some: what it names is of that form.
  draw_place_at_flat   at public files in scope that can be read, at an opening of the description's
      maker (IM.Open, Johnson/IMR/SeatOpen.lean), at each link l ≤ 24: the member number ixOf l of
      the first chain (Johnson/P1K8R/Tied.lean) has the one round round (k8Par Z G₀ Xl l) and the
      place with chain 1, link l and the kind K8. It is draw_at_flat (Johnson/P1K8R/PieceAtRow.lean)
      with the place beside the round: by k8_alone (Johnson/IMR/K8Seat.lean).
  parOwn_at_draw   a control: at public files in scope that can be read, under LaidAt, at each link
      l ≤ 24: at the member number ixOf l of the first chain cF (it is (descZ Zp Np cF).first, by
      definition), parOwn Zp mats names (k8Par Zp G₀ Xl l, mats l), the member is of the kind K8,
      and its rounds are [round (k8Par Zp G₀ Xl l)]. So the clause of the pin on the member's round
      is met at the description's own twenty-five members, at parOwn.
  sessionStops_of_pinned_own   sessionStops_of_pinned at par := parOwn Zp mats. cells and mats are
      free; l, oneTime, columnsFirst and batches are free. sessionStops_of_tiedOwn_own:
      sessionStops_of_tiedOwn at par := parOwn Zp mats: the reader of cells is cellsC Zp.p.X, and
      the premise on the trace is TraceOwn (Johnson/FrontRoad/TracePremises.lean).

How it fits. In sessionStops_of_pinned the values that par names are free: the pin (RowsPinned,
Johnson/FrontRoad/SessionStopsPinned.lean) holds the parameters against a member by the number of
entries that its round draws alone. Here they are k8Par at the place's own link, by definition. That
the description's member number ixOf l is the kind's sub-protocol at just these parameters, with
nothing beside it, is k8_alone (Johnson/IMR/K8Seat.lean); draw_place_at_flat keeps of that the round
and the place. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean. A definition, a control and two instances; not one of the
release's goal statements.

Limits.
  mats is free: the list P.2 is held against nothing but its length, as in sessionStops_of_pinned.
      That mats l is the list of the matrices that the description's test covers at the link l is
      not asked here.
  parOwn_at_draw speaks of the first chain's whole flat list. That the twenty-five members stand in
      the list without its last member, at which sessionStops_of_pinned asks the pin, is by
      inspection, not proved (the numbers ixOf l are at most 343; the list has 358 members:
      Meaning.Carry.flat_len, Johnson/IMR/RootsWhole.lean). That they are all members of the kind K8
      is not proved here (the library has the flat list's places as an explicit list, places_scope,
      Johnson/IMR/PlacesScope.lean, and where the kind stands in such a list, k8_places_full,
      Johnson/P1K8R/Tied.lean; they are not joined here); the pin at parOwn fails at any other
      member of that kind at whose link parOwn names none.
  That the checks of these parameters (checksOfPars, Johnson/FrontRoad/SharesLePlanner.lean) are
      those that the verifier gives the planner is not proved here. Nor that the planner's test
      passes at them at any l: at parOwn the list of checks is a function of the public files, and
      the test is missed at every l if one matrix in it has no row or no column.
  All limits of Johnson/FrontRoad/SessionStopsOfPinned.lean and
      Johnson/FrontRoad/SessionStopsOfTrace.lean hold, but for the one on the values that par names,
      as far as the parameters go.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SessionStopsOfTrace
import Johnson.P1K8R.PieceAtRow

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place KindName)
open VerifiableInference.Desc.First.K8 (Par round)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Cells)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_parOwn : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_parOwn {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- **The description's own parameters of the smallness test, by place**: at a place of the kind K8
with the link l, the pair of k8Par Zp G₀ Xl l and mats l, where G₀ holds the segments' structures
without a request and Xl is its entry at l; none elsewhere. Of the place it reads the kind and the
link alone. mats is free. -/
def parOwn (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) (a : Place) :
    Option (Par × List (ℕ × String × ℕ)) :=
  if a.kind = KindName.K8 then
    a.link.bind fun l => (ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
      (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)
  else none

/-- parOwn names none at a place of another kind. -/
theorem parOwn_other (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) (a : Place)
    (h : a.kind ≠ KindName.K8) : parOwn Zp mats a = none := by
  unfold parOwn
  rw [if_neg h]

/-- What parOwn names is the description's own, at the place's link. -/
theorem parOwn_some (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) (a : Place)
    (P : Par × List (ℕ × String × ℕ)) (h : parOwn Zp mats a = some P) :
    a.kind = KindName.K8 ∧ ∃ l G₀ Xl, a.link = some l ∧
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      P = (ProofFile.k8Par Zp G₀ Xl l, mats l) := by
  unfold parOwn at h
  by_cases hk : a.kind = KindName.K8
  · rw [if_pos hk] at h
    refine ⟨hk, ?_⟩
    cases hl : a.link with
    | none =>
      rw [hl] at h
      cases h
    | some l =>
      rw [hl] at h
      cases hG : ProofFile.blankBy ProofFile.pureRoad.links Zp with
      | none =>
        have h' : ((ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
          (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = some P := h
        rw [hG] at h'
        cases h'
      | some G₀ =>
        have h' : ((ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
          (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = some P := h
        rw [hG] at h'
        have h'' : ((G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = some P := h'
        cases hX : G₀.built[l]? with
        | none =>
          rw [hX] at h''
          cases h''
        | some Xl =>
          rw [hX] at h''
          exact ⟨l, G₀, Xl, rfl, rfl, hX, (Option.some.inj h'').symm⟩
  · rw [if_neg hk] at h
    cases h

/-- At an opening of the description's maker, at each link l ≤ 24: the member number ixOf l of the
first chain has the draw's one round at the description's own parameters, and the place with chain
1, link l and the kind K8. -/
theorem draw_place_at_flat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l ≤ 24) :
    ∃ b Xl, c.blocksInOrder[P1K8T.ixOf l]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      b.rounds = [round (ProofFile.k8Par Z Bs.G₀ Xl l)] ∧
      b.place =
        { chain := 1, link := some l, piece := (if l = 24 then 5 else 4) + 1, kind := .K8 } := by
  obtain ⟨Lk, b, Xl, e1, e2, e3, -, hla⟩ := IM.k8_alone O l (IM.subAt l)
    (IM.subs_scope hS hR O l (Nat.lt_succ_of_le hl)) (if l = 24 then 5 else 4)
    (P1K8T.k8_kind_full l hl) (by split <;> decide)
  refine ⟨b, Xl, ?_, e3, (IM.alone_rounds hla).trans rfl, IM.alone_place hla⟩
  have h := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O hl] at h
  have e : P1K8T.ixOf l = 14 * l + (if l = 24 then 5 else 4) + 2 := by
    unfold P1K8T.ixOf
    split
    · subst_vars
      rfl
    · rfl
  rw [e]
  exact h

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- A control; it counts as no goal. **At public files in scope that can be read, under LaidAt, at
each link l ≤ 24: at the member number ixOf l of the first chain, parOwn names the description's own
parameters, the member is of the kind K8, and its rounds are the one round at these parameters.** -/
theorem parOwn_at_draw (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (mats : ℕ → List (ℕ × String × ℕ)) {l : ℕ} (hl : l ≤ 24) :
    ∃ b G₀ Xl, cF.blocksInOrder[P1K8T.ixOf l]? = some b ∧
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      b.place.kind = KindName.K8 ∧
      parOwn Zp mats b.place = some (ProofFile.k8Par Zp G₀ Xl l, mats l) ∧
      b.rounds = [round (ProofFile.k8Par Zp G₀ Xl l)] := by
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨b, Xl, eb, eX, er, ep⟩ := draw_place_at_flat scope hr O hl
  refine ⟨b, Bs.G₀, Xl, eb, O.blank, eX, by rw [ep], ?_, er⟩
  unfold parOwn
  rw [ep, if_pos rfl]
  show ((ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
    (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = _
  rw [O.blank]
  show ((Bs.G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp Bs.G₀ Xl l, mats l)) = _
  rw [eX]
  rfl

variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **sessionStops_of_pinned at par := parOwn Zp mats: the parameters of the smallness test are the
description's own, at each member's own link; at a place of another kind none are named.** cells and
mats are free; l, oneTime, columnsFirst and batches are free: tied to nothing here. All else that
the docstring of sessionStops_of_pinned says holds here too. -/
theorem sessionStops_of_pinned_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (mats : ℕ → List (ℕ × String × ℕ)) (cells : Tr → Cells)
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned (parOwn Zp mats) cells (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) cells (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
        parOwn Zp mats b.place).map (·.1))) oneTime columnsFirst batches = false)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr →
        CellsSmallAt (parOwn Zp mats) cells (descZ Zp Np cF).first.blocksInOrder.dropLast
          ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_pinned Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes (parOwn Zp mats)
    cells l oneTime columnsFirst batches h₁ h₃ hm hP ok Gs

section AtTheTrace
variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey OnBytes.HonestTrace.Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey OnBytes.HonestTrace.Tr X₀ Xh)

/-- **sessionStops_of_tiedOwn (Johnson/FrontRoad/SessionStopsOfTrace.lean) at par := parOwn Zp
mats.** The reader of cells is cellsC Zp.p.X; the parameters are the description's own; the premise
on the trace is TraceOwn. mats is free; l, oneTime, columnsFirst and batches are free: tied to
nothing here. All else that the docstring of sessionStops_of_tiedOwn says holds here too. -/
theorem sessionStops_of_tiedOwn_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey OnBytes.HonestTrace.Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (mats : ℕ → List (ℕ × String × ℕ))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned (parOwn Zp mats) (OnBytes.HonestTrace.cellsC Zp.p.X)
      (provG Z Zp Np cF B G H).first (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (OnBytes.HonestTrace.cellsC Zp.p.X)
      (provG Z Zp Np cF B G H).second (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
        parOwn Zp mats b.place).map (·.1))) oneTime columnsFirst batches = false)
    (hO : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_tiedOwn Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes (parOwn Zp mats) l
    oneTime columnsFirst batches h₁ h₃ hm hO ok Gs

end AtTheTrace

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_parOwn
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_parOwn
#print axioms OnBytes.FrontRoad.parOwn
#print axioms OnBytes.FrontRoad.parOwn_other
#print axioms OnBytes.FrontRoad.parOwn_some
#print axioms OnBytes.FrontRoad.draw_place_at_flat
#print axioms OnBytes.FrontRoad.parOwn_at_draw
#print axioms OnBytes.FrontRoad.sessionStops_of_pinned_own
#print axioms OnBytes.FrontRoad.sessionStops_of_tiedOwn_own
