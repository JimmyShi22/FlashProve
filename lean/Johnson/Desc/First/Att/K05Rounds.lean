-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Rounds.lean: kind K5: its rounds have the proved chain's shape, and the
chain's
error at each round is a function of that round's entry.

Main names:
  `rounds_attList`: the kind's `rounds p`, as entries, are the library's closed list attList p.work
    p.own,
    in every field, at all p.
  `errOf z e`: the chain's error at a round, by the round's entry: 1 at "PSC epsilon"; the scalars
    sent at
    "PSC round" and "PSC Y"; 0 at "PSC values"; rows - 1 at "BAT-sigma"; z at "ZERO".
  `K05_rounds`: for letters with the plan's numbers (OwnFits): (1) the reduction's shape is an
    instance of
    the kind's rounds; (2) the chain's list of errors is errOf over them, entry for entry; (3) at z
      := the
    point's number of coordinates errOf gives the library's list attNums, the numerators of the
      bounds
    that the planner hands to its accounting.
  `K05_price`: a corollary of (2) and no more: the errors are at most any price that is at least
    errOf.
  `fits_of_own`: OwnFits gives the numbers that Att/K5Data.lean asks.

Each error is a count of draws among its own round's draws: at "PSC Y" among |E| - 1, at "ZERO"
among
|E|^(coordinates), else among |E|.
Limits. K05_price names no price of the plan's accounting: that comparison is not shown in this file
or in what it imports. At "ZERO" clause (2) has the chain's count of bad points among all points,
clause (3) the
coordinates' number; the two are tied at the library's letters alone (Att/K05Condition.lean).
Sources: OnBytes/Tie/Pv/Att/PlanOwn.lean, PlanOwnW.lean, PlanNums.lean, OwnShape.lean,
ChainShape.lean,
PlanJoin.lean; OnBytes/Params/SubRounds.lean; ShapeIs; Cb/G6/Cut.lean (errList). The
planner's
monad is not reached.
Nothing is claimed on completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.OwnShape
import Johnson.Desc.First.Att.K5Data
import Johnson.Desc.First.Att.K5Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Params Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (OwnFits UnitsFit SumFits own_fit own_nums numsZ nP)
open OnBytes.Tie.Pv.Att.Plan
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

/-! ## K5's ROUNDS are the library's closed list -/

/-- A round that draws bears the policy's work. -/
def withWork (w : Nat) (e : Fmt.Entry) : Fmt.Entry := if e.drawE == 0 then e else { e with work := w }

theorem rounds_entries (p : Par) : (rounds p).map (·.entry) = (entriesOf 0 (script p.own)).map (withWork p.work) := by
  unfold rounds
  rw [List.map_map]
  rfl

/-- A sumcheck's size. -/
def sizeOf (vs : List Var) (e : Ends) : PscSize := { degree := vs.map (·.d), degreeY := e.dY, values := e.n }

theorem entries_lPsc (w lead : Nat) (vs : List Var) (e : Ends) :
    (MaskedSum.entries ⟨lead, vs, some e⟩).map (withWork w) = lPsc w (24 * lead) (sizeOf vs e) := by
  simp [MaskedSum.entries, MaskedSum.entry, withWork, lPsc, eDraw, eY, eValues, sizeOf, Function.comp_def,
    Nat.mul_add]

theorem size_products (n m : Nat) : sizeOf (List.replicate n (.plain 4)) ⟨2, 2 * m⟩ = attentionSc3 n m := by
  simp [sizeOf, attentionSc3, Var.d]

theorem size_key (x : AttentionRounds) :
    sizeOf ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map .plain)
      ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩ = attentionScd x.lt x.lgk x.pairs x.Lam := by
  simp [sizeOf, attentionScd, Var.d]

theorem entriesOf_takes (l : List Stage) : ∀ (k lead : Nat),
    entriesOf lead (List.replicate k (.scalars 3) ++ l) = entriesOf (lead + 3 * k) l
  | 0, _ => rfl
  | k + 1, lead => by
    rw [List.replicate_succ, List.cons_append]
    show entriesOf (lead + 3) _ = _
    rw [entriesOf_takes l k]
    congr 1
    omega

/-- The scalars that still wait behind the units. -/
def leadLeft (lead : Nat) : List (Nat × Nat) → Nat
  | [] => lead
  | _ :: _ => 0

theorem entriesOf_units (w : Nat) (l : List Stage) : ∀ (us : List (Nat × Nat)) (lead : Nat),
    (entriesOf lead ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ l)).map (withWork w) =
      unitsL w (24 * lead) us ++ (entriesOf (leadLeft lead us) l).map (withWork w)
  | [], _ => rfl
  | u :: us, lead => by
    rw [List.flatMap_cons]
    show (MaskedSum.entries ⟨lead + 7, _, some _⟩ ++
      entriesOf 0 ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ l)).map (withWork w) = _
    rw [List.map_append, entries_lPsc, size_products, entriesOf_units w l us 0]
    simp only [unitsL, unitL, List.append_assoc, Nat.mul_add, Nat.mul_zero]
    cases us <;> rfl

theorem leftOpen_lead (k : Nat) (us : List (Nat × Nat)) : leftOpen (24 * k) us = 24 * leadLeft k us := by
  cases us <;> rfl

/-- **K5's ROUNDS are the library's closed list.** -/
theorem rounds_attList (p : Par) : (rounds p).map (·.entry) = attList p.work p.own := by
  rw [rounds_entries, script_eq, entriesOf_takes, entriesOf_units]
  have ht : ∀ lead, (entriesOf lead (tailStages p.own)).map (withWork p.work) =
      lPsc p.work (24 * lead + 24 * (5 + p.own.lt + 2)) (attentionSc3 p.own.e p.own.pairs) ++
      (eBat p.work 0 2 :: (lPsc p.work (24 * 2) (attentionSc3 p.own.valueM p.own.pairs) ++
      (lPsc p.work 0 (attentionSc3 p.own.valueD p.own.pairs) ++
      (eDraw "ZERO" p.work 0 (2 * p.own.lgk + 2 * p.own.lt + 4) :: eBat p.work (24 * p.own.pairs) p.own.pairs ::
      (lPsc p.work 0 (attentionSc3 p.own.attained p.own.pairs) ++ (eBat p.work 0 p.own.pairs ::
      (lPsc p.work 0 (attentionScd p.own.lt p.own.lgk p.own.pairs p.own.Lam) ++ (eBat p.work 0 p.own.pairs ::
      lPsc p.work 0 (attentionSc3 p.own.bits p.own.pairs))))))))) := by
    intro lead
    have hk := size_key p.own
    simp only [tailStages, entriesOf, products, keyStage, List.map_append (f := withWork p.work), List.map_cons,
      entries_lPsc, size_products, hk, List.append_nil]
    simp [withWork, eBat, eDraw, MaskedSum.entry, Nat.mul_add, Nat.add_assoc]
  rw [ht]
  simp only [attList, scoreL, aE, batV, aVM, aVD, zeroFH, batF, aF, batD, aD, OnBytes.Tie.Pv.Att.Plan.batH, aH, planeBytes, Nat.zero_add,
    leftOpen_lead, List.append_assoc, List.cons_append, List.nil_append]

/-! ## The errors, as a function of the entry -/

/-- The proved chain's error at a round, as a function of the round's entry. z: the count at the
draw of the point. -/
def errOf (z : Nat) (e : Fmt.Entry) : Nat :=
  if e.name = "PSC epsilon" then 1
  else if e.name = "PSC round" ∨ e.name = "PSC Y" then e.msg / 24
  else if e.name = "BAT-sigma" then e.rows - 1
  else if e.name = "ZERO" then z
  else 0

theorem errOf_lPsc (z w b : Nat) (x : PscSize) (h : x.withY = true) : (lPsc w b x).map (errOf z) = nP x := by
  show _ = OnBytes.Tie.Pv.Att.Plan.numsOf (OnBytes.Tie.Pv.Att.Plan.qPsc 0 x)
  rw [OnBytes.Tie.Pv.Att.Plan.nums_psc, h]
  simp [lPsc, h, errOf, eDraw, eY, eValues, Function.comp_def]

theorem errOf_units (z w : Nat) : ∀ (us : List (Nat × Nat)) (b : Nat), (unitsL w b us).map (errOf z) =
    OnBytes.Tie.Pv.Att.Plan.numsOf (us.map fun u => OnBytes.Tie.Pv.Att.Plan.qPsc 0 (attentionSc3 u.1 u.2)).flatten
  | [], _ => rfl
  | u :: us, b => by
    simp only [unitsL, unitL, List.map_append, List.map_cons, List.flatten_cons,
      OnBytes.Tie.Pv.Att.Plan.numsOf_append]
    rw [errOf_units z w us 0, errOf_lPsc z w _ _ rfl]

/-- The library's list of the plan's numerators, with z at the draw of the point, is errOf of the
library's list of entries. -/
theorem errOf_attList (z w : Nat) (x : AttentionRounds) : (attList w x).map (errOf z) = numsZ z x := by
  simp only [attList, scoreL, aE, batV, aVM, aVD, zeroFH, batF, aF, batD, aD, OnBytes.Tie.Pv.Att.Plan.batH, aH,
    List.map_append, errOf_units, errOf_lPsc _ _ _ _ (rfl : (attentionSc3 _ _).withY = true),
    errOf_lPsc _ _ _ _ (rfl : (attentionScd _ _ _ _).withY = true), numsZ, List.append_assoc, List.append_nil]
  simp [errOf, eBat, eDraw]

/-- **K05_rounds.** -/
theorem K05_rounds {K : Type} [Field K] [Fintype K] {M X : Type} (A : AttOwn K M X) (p : Par)
    (h : OwnFits A p.own) (Ex : ExtSpec) :
    OnBytes.G4.ShapeIs K (A.ch.R Ex).shape ((rounds p).map (·.entry)) ∧
    errList (A.ch.eps Ex) = ((rounds p).map (·.entry)).map (errOf A.tail.eZ) ∧
    ((rounds p).map (·.entry)).map (errOf (2 * p.own.lgk + 2 * p.own.lt + 4)) =
      OnBytes.Tie.Pv.Att.Plan.attNums p.own := by
  rw [rounds_attList]
  exact ⟨OnBytes.Tie.Pv.Att.Ch.shapeIs_R Ex A.ch _ (own_fit A p.own h p.work),
    by rw [errOf_attList]; exact own_nums A p.own h Ex,
    by rw [errOf_attList]; exact OnBytes.Tie.Pv.Att.numsZ_att p.own⟩

/-- So the chain's errors are, entry for entry, at most any price that is at least errOf. -/
theorem K05_price {K : Type} [Field K] [Fintype K] {M X : Type} (A : AttOwn K M X) (p : Par)
    (h : OwnFits A p.own) (Ex : ExtSpec) (price : Fmt.Entry → Nat)
    (hp : ∀ e ∈ (rounds p).map (·.entry), errOf A.tail.eZ e ≤ price e) :
    List.Forall₂ (fun err e => err ≤ price e) (errList (A.ch.eps Ex)) ((rounds p).map (·.entry)) := by
  rw [(K05_rounds A p h Ex).2.1, List.forall₂_map_left_iff]
  exact List.forall₂_same.2 hp

/-! ## One premise on the letters' numbers -/

theorem sizeP_of_fits {K : Type} [Field K] [Fintype K] {M X : Type} (S : SumL K M X) (vs : List Var) (e : Ends)
    (h : S.T.Fits (sizeOf vs e)) (hv : ∀ v ∈ vs, v = .plain v.d ∧ 1 ≤ v.d) : SizeP S (.sum vs e) := by
  refine ⟨e.n, ?_⟩
  have h1 : (vs.map (·.d)).map (· - 1) = List.ofFn S.T.deg := h.degs
  have h2 : e.dY = S.T.DY := h.degY
  rw [← h1, ← h2, List.map_map, List.map_map]
  congr 1
  conv_lhs => rw [← List.map_id vs]
  refine List.map_congr_left fun v hm => ?_
  obtain ⟨a, b⟩ := hv v hm
  show v = Var.plain (v.d - 1 + 1)
  rw [Nat.sub_add_cancel b]
  exact a

theorem sizeP_products {K : Type} [Field K] [Fintype K] {M X : Type} (S : SumL K M X) (n m : Nat)
    (h : S.T.Fits (attentionSc3 n m)) : SizeP S (products n m) :=
  sizeP_of_fits S _ _ (by rw [size_products]; exact h) fun v hv => by
    rw [List.eq_of_mem_replicate hv]
    exact ⟨rfl, by show 1 ≤ 4; omega⟩

theorem sizeP_key {K : Type} [Field K] [Fintype K] {M X : Type} (S : SumL K M X) (x : AttentionRounds)
    (h : S.T.Fits (attentionScd x.lt x.lgk x.pairs x.Lam)) : SizeP S (keyStage x) :=
  sizeP_of_fits S _ _ (by rw [size_key]; exact h) fun v hv => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    refine ⟨rfl, ?_⟩
    show 1 ≤ d
    simp only [List.mem_append, List.mem_replicate] at hd
    omega

theorem unitsFits_of {K : Type} [Field K] [Fintype K] {M X : Type} :
    ∀ (us : List (SumL K M (Seen K X))) (ps : List (Nat × Nat)) (k : Nat), UnitsFit us ps (24 * k) →
      UnitsFits us ps k
  | [], [], _, _ => trivial
  | u :: us, p :: ps, k, ⟨a, b⟩ =>
    ⟨sizeP_products u _ _ a.fits, by have := a.bytes; omega, unitsFits_of us ps 0 b⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- **OwnFits (OnBytes/Tie/Pv/Att/OwnShape.lean) gives the numbers that K5's law asks.** -/
theorem fits_of_own {K : Type} [Field K] [Fintype K] {M X : Type} (A : AttOwn K M X) (x : AttentionRounds)
    (h : OwnFits A x) (hne : x.score ≠ []) :
    UnitsFits A.units x.score (3 * x.planeMessages) ∧ TailFits A.tail x := by
  have hl : leftOpen (planeBytes x) x.score = 0 := by
    cases hs : x.score with
    | nil => exact absurd hs hne
    | cons _ _ => rfl
  exact ⟨unitsFits_of _ _ _ h.units,
    { zE := sizeP_products _ _ _ h.sE.fits
      nE := by have := h.sE.bytes; rw [hl] at this; omega
      zM := sizeP_products _ _ _ h.sVM.fits
      nM := by have := h.sVM.bytes; omega
      zVD := sizeP_products _ _ _ h.sVD.fits
      nVD := by have := h.sVD.bytes; omega
      nz := h.nz
      np := h.np
      zF := sizeP_products _ _ _ h.sF.fits
      nF := by have := h.sF.bytes; omega
      zD := sizeP_key _ _ h.sD.fits
      nD := by have := h.sD.bytes; omega
      zH := sizeP_products _ _ _ h.sH.fits
      nH := by have := h.sH.bytes; omega }⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.rounds_attList
#print axioms VerifiableInference.Desc.First.Att.P.K05_rounds
#print axioms VerifiableInference.Desc.First.Att.P.K05_price
#print axioms VerifiableInference.Desc.First.Att.P.fits_of_own
