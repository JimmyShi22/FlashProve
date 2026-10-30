-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9PosLayPaid.lean: AT THE TWELVE LAYERS' SEGMENTS EVERY TABLE THAT CAN
BE LAID ENDS INSIDE THE ARRAY OF THE THIRD VECTOR: the second conjunct of the test `posPlanB`
(Johnson/Desc/First/Link/K9PosAsk.lean), at every list that `layTriples` returns: a
theorem in the goals' scope alone, BY THE MAKE OF THE PLAN: no entry test, no head, no opening of
the maker, no numeral but "twelve groups". Statements with their proofs; nothing is evaluated.

IT IS NOT THE TEST's YES. `posPlanB` asks two things more at a layers' segment: that
`Layer.layTables` returns (it refuses a family without entries) and that the list is not empty.
Neither is shown here. The sentence `PosPlan` at the plan's skeleton, which other files' laws spend,
follows from what is shown (by `layTriples_is` and `all_gives`,
Johnson/Desc/First/Link/Law/K9PosAskLaw.lean): where layTables refuses, the skeleton is empty.

How. The library's laying ends each table at or below its first free entry (`layTables_below`). That
entry is the end of the fold of `K8.tabs` (`tabs_of_layTables`, `asks_layers`,
Johnson/Desc/First/K8/LawShapes.lean). That end is at most the plan's nU[2]:
`end_lay` and `planG_nU2` (Johnson/Road/K4/Plan/TabsEndLay.lean), whose lines for their premises
are taken over from U3ColsLay.lean there. nU[2] is the array's number of columns (`public_G_K3`,
Johnson/Goal/Meaning/PlanPort.lean).

  `layParts_below`, `layTables_below`   the law on the library's laying
  `posTables_lay`   **MAIN**

What is not claimed. That a table can be laid. Nothing on tiling. Nothing on soundness.

-/
import Johnson.Desc.First.Link.K9PosAsk
import Johnson.Desc.First.Link.Law.K9NuPaid
import Johnson.Road.K4.Plan.TabsEndLay
import Johnson.Desc.First.K8.LawShapes
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH LinkH)
open OnBytes.Model.Layer (matIx)
open OnBytes.Road (matsR)
open OnBytes.Road.K4.Plan (end_lay planG_nU2 filled_of_layout pair_of ks_at ms_at)
open VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed (Third)

/-! ## 1 The library's laying of tables: each table ends at or below the first free entry -/

theorem layParts_below (mats : Array (ℕ × ℕ)) (a : Layer.TableAsk) : ∀ (n p : ℕ),
    p ≤ (Layer.layParts mats a n p).2 ∧ ∀ y ∈ (Layer.layParts mats a n p).1,
      y.2 + (mats.getD y.1 (0, 0)).2 * ((mats.getD y.1 (0, 0)).1 / a.L) ≤
        (Layer.layParts mats a n p).2
  | 0, p => ⟨Nat.le_refl _, fun y hy => by cases hy⟩
  | n + 1, p => by
    simp only [Layer.layParts]
    obtain ⟨h1, h2⟩ := layParts_below mats a n
      (p + (mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).2 *
        ((mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).1 / a.L))
    refine ⟨by omega, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact h2 y hy

theorem layTables_below (mats : Array (ℕ × ℕ)) : ∀ (asks : List Layer.TableAsk) (p : ℕ)
    (x : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ),
    Layer.layTables mats asks p = some x →
    p ≤ x.2.2 ∧ ∀ f ∈ x.2.1, ∀ y ∈ f.2,
      y.2 + (mats.getD y.1 (0, 0)).2 * ((mats.getD y.1 (0, 0)).1 / f.1.L) ≤ x.2.2
  | [], p, x, h => by
    simp only [Layer.layTables, Option.some.injEq] at h
    subst h
    exact ⟨Nat.le_refl _, fun f hf => by cases hf⟩
  | a :: rest, p, x, h => by
    simp only [Layer.layTables] at h
    split at h
    · cases h
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨g1, g2⟩ := layTables_below mats rest _ r hr
      obtain ⟨q1, q2⟩ := layParts_below mats a a.parts p
      refine ⟨q1.trans g1, fun f hf y hy => ?_⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact (q2 y hy).trans g1
      · exact g2 f hf y hy

/-! ## 2 The clause -/

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **At each of the twelve layers' segments every table that can be laid ends inside the array of
the third vector.** -/
theorem posTables_lay (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) {g : ℕ} (hg : g < 12) :
    ∃ X, Z.p.built.links[2 * g]? = some X ∧ ∀ ts, layTriples Z.p.X.layers g = some ts →
      ts.all (tableIn X.tl (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0))) = true := by
  obtain ⟨k4, kN, _, hAll⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4, kN] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨_, hat⟩ := OnBytes.L5.LinksOrder.declareLinks_at _ _ _ _ _ hd
  obtain ⟨a, ha, _⟩ := hAll g hg
  obtain ⟨hp, hgp⟩ := _root_.Meaning.planG_there hpub C hg
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨q0, _⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, har⟩ := hat (2 * g) _ q0
  have h3 : Third hp.tl := thirdG Z.p.X.layers g _ hp (Fo.Pub.public_G hpub g hp hgp)
  have hK : colsB hp.Fp 0 = hp.nU.getD 2 0 := _root_.Meaning.Plan.public_G_K3 hpub g hp hgp h3
  -- the layers' layout, the reads, the plan: U3ColsLay.lean's lines
  obtain ⟨hy, -, -, hrd, -⟩ := _root_.Meaning.P34.pub34_public hS hR hpub
  have L := OnBytes.Road.laid2_of_layout hy
  have F := filled_of_layout hy
  have hgN : g < Z.p.X.y.NGr := by
    have e : Z.p.X.y.NGr = 12 := kN
    omega
  have htm := (_root_.Meaning.P34.tails_of_public hpub hgp).1
  have hn := planG_nU2 _ _ _ _ (Fo.Pub.public_G hpub g hp hgp)
  have tXI := OnBytes.Road.tails_pair Z.p.X.y hgN (mat := 4) (p := 0) (by decide) Nat.zero_lt_one
  rw [← htm, pair_of] at tXI
  obtain ⟨x1, x2⟩ := Prod.mk.inj tXI
  have x1' : (hp.tl.mats.getD (matIx Z.p.X.layers.y).iXI {}).m = Z.p.X.y.mxb := x1
  have x2' : (hp.tl.mats.getD (matIx Z.p.X.layers.y).iXI {}).k = Z.p.X.y.kxb := x2
  rw [x1', x2'] at hn
  let p : First.K8.Par :=
    { link := 0, piece := 0, ks := hp.tl.mats.toList.map (·.k), tau := 0
      ms := hp.tl.mats.toList.map (·.m), asks := First.K8.Asks.layers Z.p.X.y Z.p.X.layers.rd g
      matsIn := [], readsIn := [] }
  have hk : ∀ M, p.ks.getD M 0 = ((matsR Z.p.X.y g).getD M (0, 0)).2 := by
    intro M
    show (hp.tl.mats.toList.map (·.k)).getD M 0 = _
    rw [ks_at, ← htm, pair_of]
  have hm : ∀ M, p.ms.getD M 0 = ((matsR Z.p.X.y g).getD M (0, 0)).1 := by
    intro M
    show (hp.tl.mats.toList.map (·.m)).getD M 0 = _
    rw [ms_at, ← htm, pair_of]
  have hE := end_lay L F hrd hgN p rfl hk hm
  refine ⟨_, har, fun ts hts => ?_⟩
  show ts.all (tableIn hp.tl (colsB hp.Fp ((hp.tl.ix.U.getD 2 none).getD 0))) = true
  rw [show hp.tl.ix.U.getD 2 none = some 0 from h3]
  show ts.all (tableIn hp.tl (colsB hp.Fp 0)) = true
  rw [hK]
  unfold layTriples at hts
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hts
  rw [_root_.Meaning.P34.mats_of_public hpub g] at hx
  have hx' : Layer.layTables (matsR Z.p.X.y g)
      (Layer.tableAsks Z.p.X.y Z.p.X.layers.rd g) 0 = some x := hx
  have hT := First.K8.tabs_of_layTables p (matsR Z.p.X.y g) hk hm _ [] 0 x hx'
  rw [First.K8.asks_layers] at hT
  have hEnd : x.2.2 ≤ hp.nU.getD 2 0 := by
    have e : (p.asks.foldl (fun x a => let z := First.K8.layFamily p a x.2; (x.1 ++ z.1, z.2))
        ([], 0)).2 = x.2.2 := by
      show ((First.K8.Asks.layers Z.p.X.y Z.p.X.layers.rd g).foldl _ ([], 0)).2 = _
      rw [hT]
    rw [e] at hE
    rw [hn]
    exact hE
  obtain ⟨_, hb⟩ := layTables_below _ _ _ _ hx'
  refine List.all_eq_true.2 fun t ht => ?_
  obtain ⟨f, hf, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨y, hy', rfl⟩ := List.mem_map.1 ht
  have hb' := hb f hf y hy'
  rw [← htm, pair_of] at hb'
  unfold tableIn
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  refine .inr ?_
  exact hb'.trans hEnd

end

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.layParts_below
#print axioms VerifiableInference.Desc.K9Asks.layTables_below
#print axioms VerifiableInference.Desc.K9Asks.posTables_lay
