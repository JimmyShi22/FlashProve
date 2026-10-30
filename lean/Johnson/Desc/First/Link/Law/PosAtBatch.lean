-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PosAtBatch.lean: THE CLAUSE "pos" OF WHAT IS FIXED IN FRONT OF A
BATCHING ("every entry that a read names lies inside its table's vector's array") AT EVERY STATE
REACHED THERE,
AT ALL 25 SEGMENTS, FROM ONE CLOSED SENTENCE ON THE BUILT SEGMENT. In the goals' scope.
One definition, statements and proofs.

  `PosPlan tl Fp sh`: THE CLOSED SENTENCE: every table of the skeleton sh on a matrix of tl, with at
    least one stretch of rows and one column, ends inside the array of the third vector:
    start + k * (m / len) ≤ the array's columns.
  `posRead tl`: (NM, mats, ix.U): what the clause reads of the structure. `planned_pos`: a `Planned`
    reading (PlannedAtDraw.lean). `posRead_blank`: none of the fourteen written fields.
  `mem_reads`: what a member of `readsList` is.
  `pos_core`: **the clause's body**, from `PosPlan`, the skeleton, "every table lies on the third
    vector", the reading and the columns.
  `PosAt π q`: the clause, in the letters of the field pos of `OkCore` and of `OkCoreLeft`
    (OkOne.lean and CoreAtBatch.lean, which are not imported here).
  `pos_at`: at what is fixed at a state.
  `pos_layers`, `pos_att`, `pos_head`: **reached (`RchAt`) in front of the batching; `PosPlan` at
    the built segment and the plan's skeleton ⊢ the clause at `fixed9 φ a.1.2`.**
The stones: the skeleton in front of the batching (FunsAtBatch.lean, AttSkelAtBatch.lean,
HeadSkel.lean); the structure's planned fields (`planned_batch_rch`); the
snapshot's arrays have the looks of the built segment's planned ledger (`part_at_batch`,
AtBatchOpen.lean).
Limits. `PosPlan` IS A PREMISE: shown of no plan here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.AttSkelAtBatch
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.WidthAtReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf uOf posOf colsU)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open Johnson.Desc.First.Walk.Tied (RchAt Reach rchAt_raw)
open ProofFile (Cl)

/-- **THE CLOSED SENTENCE.** -/
def PosPlan (tl : HTailF2) (Fp : Fork) (sh : List Tab) : Prop :=
  ∀ t ∈ sh, t.mat < tl.NM → 0 < (tl.mats.getD t.mat {}).m / t.len →
    0 < (tl.mats.getD t.mat {}).k →
    t.start + (tl.mats.getD t.mat {}).k * ((tl.mats.getD t.mat {}).m / t.len) ≤
      colsU Fp ((tl.ix.U.getD 2 none).getD 0)

/-- What the clause reads of the structure. -/
def posRead (tl : HTailF2) := (tl.NM, tl.mats, tl.ix.U)

theorem posRead_blank (u tl : HTailF2) : posRead (blank u tl) = posRead tl := rfl

theorem planned_pos : Planned posRead :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- What a member of the list of reads is. -/
theorem mem_reads {tl : HTailF2} {funs : Array HFun} {x : HFun × ℕ} (h : x ∈ readsList tl funs) :
    x.1 ∈ funs.toList ∧ x.1.mat < tl.NM ∧ x.2 < (tl.mats.getD x.1.mat {}).m / x.1.len := by
  unfold readsList at h
  obtain ⟨mu, hmu, h⟩ := List.mem_flatMap.1 h
  obtain ⟨un, _, h⟩ := List.mem_flatMap.1 h
  obtain ⟨Fn, hFn, h⟩ := List.mem_flatMap.1 h
  unfold segsOf at h
  split at h
  · rename_i hc
    obtain ⟨sg, hsg, rfl⟩ := List.mem_map.1 h
    have hm : Fn.mat = mu := by
      have hc' : Fn.mat = mu ∧ Fn.tree = un := by simpa using hc
      exact hc'.1
    subst hm
    exact ⟨hFn, List.mem_range.1 hmu, List.mem_range.1 hsg⟩
  · exact nomatch h

/-- **THE CLAUSE's BODY.** -/
theorem pos_core {tlb tlP : HTailF2} {Fp G : Fork} {funs : Array HFun} {sh : List Tab}
    (H : PosPlan tlP Fp sh) (hr : posRead tlb = posRead tlP) (hs : shapesOf funs = sh)
    (h2 : ∀ Fn ∈ funs.toList, Fn.tree = 2) (hc : ∀ t, colsU G t = colsU Fp t) :
    ∀ x ∈ readsList tlb funs, ∀ d, d < (tlb.mats.getD x.1.mat {}).k →
      posOf tlb x.1 x.2 d < colsU G (uOf tlb x.1) := by
  intro x hx d hd
  obtain ⟨m1, m2, m3⟩ := mem_reads hx
  have e1 : tlb.NM = tlP.NM := congrArg (·.1) hr
  have e2 : tlb.mats = tlP.mats := congrArg (·.2.1) hr
  have e3 : tlb.ix.U = tlP.ix.U := congrArg (·.2.2) hr
  have hlen : x.1.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at m3
    exact absurd m3 (Nat.not_lt_zero _)
  have hp : posOf tlb x.1 x.2 d =
      x.1.start + d * ((tlb.mats.getD x.1.mat {}).m / x.1.len) + x.2 := by
    unfold posOf HTailF2.tabAt
    rw [if_pos (by simp [m2, hlen])]
    dsimp only
    rw [if_pos (by
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hd, decide_eq_true m3⟩)]
    rfl
  have hmem : (⟨x.1.mat, x.1.len, x.1.start⟩ : Tab) ∈ sh := by
    rw [← hs]
    unfold shapesOf
    exact List.mem_map.2 ⟨x.1, m1, rfl⟩
  have K := H _ hmem (by show x.1.mat < tlP.NM; rw [← e1]; exact m2)
    (by show 0 < (tlP.mats.getD x.1.mat {}).m / x.1.len; rw [← e2]; omega)
    (by show 0 < (tlP.mats.getD x.1.mat {}).k; rw [← e2]; omega)
  have K' : x.1.start + (tlb.mats.getD x.1.mat {}).k * ((tlb.mats.getD x.1.mat {}).m / x.1.len) ≤
      colsU Fp ((tlb.ix.U.getD 2 none).getD 0) := by
    rw [e2, e3]
    exact K
  have hu : uOf tlb x.1 = (tlb.ix.U.getD 2 none).getD 0 := by
    unfold uOf
    rw [h2 x.1 m1]
  rw [hp, hu, hc]
  have hmul : (d + 1) * ((tlb.mats.getD x.1.mat {}).m / x.1.len) ≤
      (tlb.mats.getD x.1.mat {}).k * ((tlb.mats.getD x.1.mat {}).m / x.1.len) :=
    Nat.mul_le_mul_right _ hd
  rw [Nat.succ_mul] at hmul
  omega

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **The clause.** -/
def PosAt (q : α × Option Pub9) : Prop :=
  ∀ tlb funs v, π q.1 = (some tlb, some funs) → q.2 = some v → ∀ x ∈ readsList tlb funs,
    ∀ d, d < (tlb.mats.getD x.1.mat {}).k → posOf tlb x.1 x.2 d < colsU v.F (uOf tlb x.1)

/-- At what is fixed at a state. -/
theorem pos_at (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (s : S) (tlP : HTailF2) (Fp : Fork)
    (sh : List Tab) (h1 : ∀ tl, s.tl? = some tl → posRead tl = posRead tlP)
    (h2 : ∀ p, atS.get? s = some p →
      (pubOf p).F.trees.toList.map look = Fp.trees.toList.map look)
    (h3 : ∀ funs, s.funs? = some funs → shapesOf funs = sh ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (H : PosPlan tlP Fp sh) : PosAt π (fixed9 φ s) := by
  intro tlb funs v e1 e2
  have e1' : (s.tl?.map (blank u), s.funs?) = (some tlb, some funs) := (hπ s).symm.trans e1
  obtain ⟨a1, a2⟩ := Prod.mk.inj e1'
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 a1
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? s).map pubOf = some v from e2)
  obtain ⟨s1, s2⟩ := h3 funs a2
  have hl : (pubOf p).F.trees.map look = Fp.trees.map look := by
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_map]
    exact h2 p hp
  exact pos_core H ((posRead_blank u tl).trans (h1 tl htl)) s1 s2 (colsU_of_looks hl)

end

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The join, at a written stretch. -/
theorem pos_at_stretch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (sh : List Tab)
    (h3 : ∀ funs, a.1.2.funs? = some funs →
      shapesOf funs = sh ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (H : PosPlan Xl.tl Xl.Fp sh) : PosAt π (fixed9 φ a.1.2) :=
  pos_at π φ u hπ a.1.2 Xl.tl Xl.Fp sh
    (of_readTl (planned_batch_rch planned_pos hS hR O hx e3 a h))
    (fun p hp => (part_at_batch hS hR O hx e3 a h p hp).2) h3 H

/-- **AT THE LAYERS' SEGMENTS.** -/
theorem pos_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (28 * g + 9) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (H : PosPlan Xl.tl Xl.Fp (layShapes Bs.G₀.W.layers g)) : PosAt π (fixed9 φ a.1.2) := by
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have e : 14 * (2 * g) + 4 + 3 + 2 = 28 * g + 9 := by omega
  obtain ⟨funs, f1, f2, f3⟩ := funsSkel_at_batch hS hR O hg
    (z := a.1.1) (s' := a.1.2) (rchAt_raw h)
  have h' : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (2 * g) + 4 + 3 + 2) a := by
    rw [e]
    exact h
  refine pos_at_stretch hS hR O hx e3 a h' π φ u hπ _ (fun funs' hf => ?_) H
  obtain rfl : funs = funs' := Option.some.inj (f1.symm.trans hf)
  exact ⟨f2, f3⟩

/-- **AT THE ATTENTION SEGMENTS.** -/
theorem pos_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (2 * g + 1) + 9) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (H : ∀ p, Bs.G₀.W.A[g]? = some p → PosPlan Xl.tl Xl.Fp (attShapes p.S (nScores p.S))) :
    PosAt π (fixed9 φ a.1.2) := by
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  obtain ⟨p, funs, p1, f1, f2, f3⟩ := attSkel_at_batch hS hR O hg
    (z := a.1.1) (s' := a.1.2) (rchAt_raw h)
  refine pos_at_stretch hS hR O hx e3 a h π φ u hπ _ (fun funs' hf => ?_) (H p p1)
  obtain rfl : funs = funs' := Option.some.inj (f1.symm.trans hf)
  exact ⟨f2, f3⟩

/-- **AT THE HEAD.** -/
theorem pos_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs)) : PosAt π (fixed9 φ a.1.2) := by
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  obtain ⟨funs, t0, f1, f0, f2, f3⟩ := headSkel_at_batch hS hR O
    (z := a.1.1) (s' := a.1.2) (rchAt_raw h)
  refine pos_at_stretch hS hR O hx e3 a h π φ u hπ _ (fun funs' hf => ?_) (H t0 f0)
  obtain rfl : funs = funs' := Option.some.inj (f1.symm.trans hf)
  exact ⟨f2, f3⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.posRead_blank
#print axioms VerifiableInference.Desc.LinkJoin.planned_pos
#print axioms VerifiableInference.Desc.LinkJoin.mem_reads
#print axioms VerifiableInference.Desc.LinkJoin.pos_core
#print axioms VerifiableInference.Desc.LinkJoin.pos_at
#print axioms VerifiableInference.Desc.LinkJoin.pos_at_stretch
#print axioms VerifiableInference.Desc.LinkJoin.pos_layers
#print axioms VerifiableInference.Desc.LinkJoin.pos_att
#print axioms VerifiableInference.Desc.LinkJoin.pos_head
