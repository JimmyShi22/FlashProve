-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsHeadAt.lean: `TabsBelow` AT WHAT IS FIXED AT
EVERY STATE REACHED IN FRONT OF THE HEAD's BATCHING, FROM THE CLOSED SENTENCE `PosPlan`; THE PREMISE
hU THERE; AND SO THE TWO CLAUSES "entsK6" AND "entsJoin" WITH TWO PREMISES FEWER. In the goals'
scope. Statements and proofs: a join.

  `seen_tabs`: what the head's readers see as t is the state's `tabs?`.
  `tree_of_unit`: an array whose look passes `unitLook` is there.
  `hU_head`: **reached (`RchAt`) at 347; the plan's structure names iU3 for the third vector ⊢ so
    does the fixed structure.**
  `tabsBelow_at_347`: **reached at 347; `PosPlan` at the built segment and the plan's skeleton; the
    plan names iU3; the snapshot's ledger has array iU3 ⊢ `TabsBelow iU3 y w.F ‹that array's
    width›`** at what kap shows and the snapshot.
  `entsK6_at_347`, `entsJoin_at_347`: **the two clauses** (EntsHead.lean), without hT and hU.
The stones: TabsStay.lean (the state holds the text's own return); HeadSkel.lean's `tables_skel`;
TabsBelowOfPos.lean; `IM.ground_tails` (the built segment's structure is the plan's);
`k6_NM` (NM = NHf + 4); `part_at_batch` (the snapshot's arrays look as the built segment's
planned ledger's).
PREMISES THAT STAY: hok, hsz (on the plan); hk (`K6Ready`); for the join hb; hs (the static clause)
and hthere (the structure is there); h0; H (`PosPlan`); hi (the plan names iU3); hkap (on the
letters).
Limits. These are shown of no state and no plan here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsHead
import Johnson.Desc.First.Link.Law.TabsStay
import Johnson.Desc.First.Link.Law.TabsBelowOfPos
import Johnson.Desc.Kinds.Law.HeadPlanesTie
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (colsU)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open ProofFile (Cl)

/-- What the head's readers see as t is the state's. -/
theorem seen_tabs {s : S} {y : Seen} (h : seenOf s = some y) : y.t = s.tabs? := by
  unfold seenOf at h
  unfold S.tabs?
  split at h
  · rename_i o ho
    obtain rfl := Option.some.inj h
    rw [ho]
  · exact nomatch h

/-- An array whose look passes the test is there. -/
theorem tree_of_unit {F : Fork} {t : ℕ} (h : unitLook (F.trees.toList.map look) t = true) :
    ∃ tr, F.trees[t]? = some tr := by
  unfold unitLook at h
  split at h
  · rename_i x hx
    rw [List.getElem?_map] at hx
    obtain ⟨tr, htr, _⟩ := Option.map_eq_some_iff.1 hx
    exact ⟨tr, by rw [← Array.getElem?_toList]; exact htr⟩
  · exact nomatch h

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem stretch_24 : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
  List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩

/-- **hU AT THE HEAD.** -/
theorem hU_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {iU3 : ℕ}
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    ∀ tlb, (π (fixed9 φ x.1.2).1).1 = some tlb → tlb.ix.U.getD 2 none = some iU3 := by
  obtain ⟨Xl, hX, ht, _⟩ := (IM.ground_tails hS hR O.pub O.blank).2
  have hr := of_readTl (planned_batch_rch planned_pos hS hR O stretch_24 hX x h)
  intro tlb e1
  have e1' : x.1.2.tl?.map (blank u) = some tlb := (congrArg Prod.fst (hπ x.1.2)).symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  have e : posRead (blank u tl) = posRead Xl.tl := (posRead_blank u tl).trans (hr tl htl)
  have eU : (blank u tl).ix.U = Xl.tl.ix.U := congrArg (·.2.2) e
  rw [eU, ht]
  exact hi

/-- **`TabsBelow` AT WHAT IS FIXED IN FRONT OF THE HEAD's BATCHING.** -/
theorem tabsBelow_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {iU3 : ℕ}
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    {α : Type} (φ : S → α) (kap : α → Option Seen) (hkap : ∀ e, kap (φ e) = seenOf e) :
    ∀ y w tr, kap (fixed9 φ x.1.2).1 = some y → (fixed9 φ x.1.2).2 = some w →
      w.F.trees[iU3]? = some tr → TabsBelow iU3 y w.F tr.K := by
  intro y w tr hy hw htr
  obtain ⟨Xl', hX, ht, _⟩ := (IM.ground_tails hS hR O.pub O.blank).2
  obtain rfl : Xl = Xl' := Option.some.inj (e3.symm.trans hX)
  refine ⟨⟨tr, htr, rfl⟩, fun tt htt z hz => ?_⟩
  obtain ⟨cov, xh, tt', a1, a2⟩ := tabs_at_batch hS hR O (z := x.1.1) (s' := x.1.2) (rchAt_raw h)
  have hy' : seenOf x.1.2 = some y := (hkap x.1.2).symm.trans hy
  obtain rfl : tt = tt' := Option.some.inj ((htt.symm.trans (seen_tabs hy')).trans a1)
  obtain ⟨t0, k1, k2, _⟩ := tables_skel _ _ _ cov xh tt a2
  have HP : PosPlan Xl.tl Xl.Fp (shapesOf tt.funs) := by
    rw [k2]
    exact H t0 k1
  have hE := endsIn_of_pos HP
  rw [ht] at hE
  have hNM : Bs.G₀.W.H.tl.NM = Bs.G₀.W.hS.NHf + 4 := k6_NM (IM.ground_publicK O.pub O.blank)
  have K := tables_below_of _ _ _ cov xh tt a2 hNM hE z hz
  rw [hi] at K
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1
    (show (atS.get? x.1.2).map pubOf = some w from hw)
  have hl : (pubOf p).F.trees.map look = Xl.Fp.trees.map look := by
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_map]
    exact (part_at_batch hS hR O stretch_24 hX x h p hp).2
  have hc : colsU (pubOf p).F iU3 = tr.K := by
    unfold colsU
    rw [htr]
    rfl
  rw [← hc, colsU_of_looks hl iU3]
  exact K

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
  (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : Par) (kap : α → Option Seen)

/-- What both clauses share: hT of EntsHead.lean. -/
theorem hT_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (hkap : ∀ e, kap (φ e) = seenOf e)
    {nU : Array ℕ} (h0 : 0 < nU.getD 2 0)
    (hthere : ((π (fixed9 φ x.1.2).1).1).isSome = true)
    (hs : ∀ tlb v, (π (fixed9 φ x.1.2).1).1 = some tlb → (fixed9 φ x.1.2).2 = some v →
      StaticOk tlb v.F) :
    ∀ y w, kap (fixed9 φ x.1.2).1 = some y → (fixed9 φ x.1.2).2 = some w →
      ∃ K3, TabsBelow iU3 y w.F K3 := by
  intro y w hy hw
  obtain ⟨tlb, htl⟩ := Option.isSome_iff_exists.1 hthere
  have T := tableAt_of_static (nU := nU) (hs tlb w htl hw)
    (hU_head hS hR O hi x h π φ u hπ tlb htl) h0
  obtain ⟨tr, htr⟩ := tree_of_unit T.2.2.2.2.2
  exact ⟨tr.K, tabsBelow_at_347 hS hR O hi e3 H x h φ kap hkap y w tr hy hw htr⟩

/-- **THE CLAUSE entsK6 AT 347, AT EVERY NAME.** -/
theorem entsK6_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (hkap : ∀ e, kap (φ e) = seenOf e)
    {nU : Array ℕ} (h0 : 0 < nU.getD 2 0)
    (hthere : ((π (fixed9 φ x.1.2).1).1).isSome = true)
    (hs : ∀ tlb v, (π (fixed9 φ x.1.2).1).1 = some tlb → (fixed9 φ x.1.2).2 = some v →
      StaticOk tlb v.F)
    (hok : p6.ok = true) (hsz : p6.sizes = sizesOf hh)
    (hk : ∀ y w, kap (fixed9 φ x.1.2).1 = some y → (fixed9 φ x.1.2).2 = some w →
      K6Ready hh iU3 p6 y w.F) (name : String) :
    ∀ l, fsK6 hh iU3 p6 kap name (fixed9 φ x.1.2) = some l → EntsAt π nU (fixed9 φ x.1.2) l :=
  entsK6_of π hh iU3 p6 kap hok hsz hk
    (hT_at_347 π φ u iU3 kap hS hR O hi e3 H x h hπ hkap h0 hthere hs) hs
    (hU_head hS hR O hi x h π φ u hπ) h0 name

/-- **THE CLAUSE entsJoin AT 347.** -/
theorem entsJoin_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (hkap : ∀ e, kap (φ e) = seenOf e)
    {nU : Array ℕ} (h0 : 0 < nU.getD 2 0)
    (hthere : ((π (fixed9 φ x.1.2).1).1).isSome = true)
    (hs : ∀ tlb v, (π (fixed9 φ x.1.2).1).1 = some tlb → (fixed9 φ x.1.2).2 = some v →
      StaticOk tlb v.F)
    (hok : p6.ok = true) (hsz : p6.sizes = sizesOf hh)
    (hk : ∀ y w, kap (fixed9 φ x.1.2).1 = some y → (fixed9 φ x.1.2).2 = some w →
      K6Ready hh iU3 p6 y w.F)
    (hb : ∀ y g, kap (fixed9 φ x.1.2).1 = some y → y.lookHeard = some g → g.cEnd.ents = #[]) :
    ∀ l, fsJoin hh iU3 p6 kap (fixed9 φ x.1.2) = some l → EntsAt π nU (fixed9 φ x.1.2) l :=
  entsJoin_of π hh iU3 p6 kap hok hsz hk
    (hT_at_347 π φ u iU3 kap hS hR O hi e3 H x h hπ hkap h0 hthere hs) hb hs
    (hU_head hS hR O hi x h π φ u hπ) h0

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seen_tabs
#print axioms VerifiableInference.Desc.LinkJoin.tree_of_unit
#print axioms VerifiableInference.Desc.LinkJoin.stretch_24
#print axioms VerifiableInference.Desc.LinkJoin.hU_head
#print axioms VerifiableInference.Desc.LinkJoin.tabsBelow_at_347
#print axioms VerifiableInference.Desc.LinkJoin.hT_at_347
#print axioms VerifiableInference.Desc.LinkJoin.entsK6_at_347
#print axioms VerifiableInference.Desc.LinkJoin.entsJoin_at_347
