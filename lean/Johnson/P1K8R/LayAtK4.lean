-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LayAtK4.lean: THE SMALLNESS TEST: ONE MORE THEOREM AT THE FOLD,
AT A LAYERS' LINK THE SEVEN FIELDS OF THE LINK'S OWN PLANNED VALUE STAND
ALREADY IN FRONT OF THE SUB-PROTOCOL OF KIND K4 (ENTRY 28 g + 4). NO SOUNDNESS.

`k8LaidOwn` (P1K8R/FrontAtSeat.lean) says it in front of the draw (28 g + 6), behind the step that
lays the smallness test's part anew. The wider table opens its public name for these seven fields
earlier. Here: behind the link's opening (28 g + 3) the part IS the planned one (`lay_tl_at_fold`,
Johnson/P1L20R/FrameFold.lean); the one entry between, the first sub-protocol of the
lookups, leaves the seven fields (`theStated_leaves_tl`); the planner's element's group number is g
(`zipped_g`); the planned value is the built link's own (`IM.ground_tails`).
  `lay7_at_k4`: along the fold from the first state: `lay7B Xl.tl` says yes, at the built link Xl.
  `lay7_fill_at_k4`: the same in the spelling of the table's public data
    (`FillP1.tlAt`, Johnson/Top/H0/Fill/D1At.lean).
  `lay7_reached`: **at every state that is reached at 28 g + 4 by the flat list's own steps.**
  `lay7_reachedR`: at `RchAt`.
Limits. From an accepting fold alone. AT `OnBytes.secondHashFunction` ALONE. Layers' links alone. Nothing on
soundness.

-/
import Johnson.P1K8R.FrontAtSeat
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7B)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_fold rchAt_fold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Along the fold from the first state.** -/
theorem lay7_at_k4 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {ft : ℕ} {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (f : foldBlocks ft (c.blocksInOrder.take (28 * g + 4)) s₀ R C = .ok out) :
    ∃ Xl, Bs.G₀.built[2 * g]? = some Xl ∧ lay7B Xl.tl out.1 = true := by
  have e4 : 28 * g + 4 = 14 * (2 * g) + 3 + 1 := by omega
  rw [e4] at f
  obtain ⟨hN, _⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨Xl, _, e3, hk, hXg, _⟩ := hN g hg
  obtain ⟨Lk, b1, b1', eL, e1, k3, la1⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have ix1 : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  rw [ix1] at e1
  have i1 : c.blocksInOrder[14 * (2 * g) + 3]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega) 1] at k
  obtain ⟨t₂, R₂, C₂⟩ := out
  obtain ⟨t₁, R₁, C₁, f₁⟩ := Meaning.K2.fold_back (k := 14 * (2 * g) + 3) f
  obtain ⟨rs1, gs1, d1⟩ := Meaning.K2.fold_next i1 f₁ f
  have ha : IM.subAt (2 * g) = ModelPart.layers := by
    unfold IM.subAt
    rw [if_neg (by omega), if_pos (by omega)]
  obtain ⟨X, hp, eX, _, eq, ht1⟩ := P1L20.lay_tl_at_fold hS hR O (l := 2 * g) (by omega) ha f₁
  have hg' : X.g = g := by
    obtain ⟨ls, _, _, eB, _⟩ := IM.blank_ground O.blank
    have e3' := e3
    rw [eB] at e3'
    obtain ⟨b', hb', hbg⟩ := zipped_g e3'
    obtain rfl : b' = X := Option.some.inj (hb'.symm.trans eX)
    rw [hbg]
    exact hXg
  rw [hg', ← O.W] at eq
  have eT : hp.tl = Xl.tl :=
    planAt_built hS hR O e3 (Or.inr (Or.inl ⟨g, hp, hg, rfl, eq, rfl⟩))
  have h1 : lay7 t₁ = some (seven hp.tl) := by
    unfold lay7
    rw [ht1]
    rfl
  have h2 : lay7 t₂ = lay7 t₁ :=
    leaves_of_under (IM.alone_underR la1).2 (theStated_leaves_tl keeps4_seven k3) _ _ _ _ d1
  refine ⟨Xl, e3, lay7B_of_lay7 ?_⟩
  rw [← eT]
  exact h2.trans h1

/-- In the spelling of the table's public data. -/
theorem lay7_fill_at_k4 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {ft : ℕ} {s₀ : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (f : foldBlocks ft (c.blocksInOrder.take (28 * g + 4)) s₀ R C = .ok out) :
    ((VerifiableInference.Desc.First.FillP1.tlAt Z (2 * g)).any fun t => lay7B t out.1) = true := by
  obtain ⟨Xl, e3, h⟩ := lay7_at_k4 hS hR O hg f
  unfold VerifiableInference.Desc.First.FillP1.tlAt
  rw [O.blank]
  show ((Bs.G₀.built[2 * g]?).map (·.tl)).any (fun t => lay7B t out.1) = true
  rw [e3]
  exact h

/-- **AT EVERY STATE THAT IS REACHED AT 28 g + 4.** -/
theorem lay7_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 4) (z, s)) :
    ((VerifiableInference.Desc.First.FillP1.tlAt Z (2 * g)).any fun t => lay7B t s) = true := by
  obtain ⟨_, rs, cols, f⟩ := reach_fold.1 h
  exact lay7_fill_at_k4 hS hR O hg f

/-- At the description's own "reached". -/
theorem lay7_reachedR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (28 * g + 4) a) :
    ((VerifiableInference.Desc.First.FillP1.tlAt Z (2 * g)).any fun t => lay7B t a.1.2) = true := by
  obtain ⟨_, rs, cols, f⟩ := rchAt_fold h
  exact lay7_fill_at_k4 hS hR O hg f

end P1K8S

#print axioms P1K8S.lay7_at_k4
#print axioms P1K8S.lay7_fill_at_k4
#print axioms P1K8S.lay7_reached
#print axioms P1K8S.lay7_reachedR
