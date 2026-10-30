-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9NuPaid.lean: THE TEST `nuPosB` (Johnson/Desc/First/Link/K9NuAsk.lean:
the plan's length of the third vector at a segment is not 0) ACCEPTS AT ALL 25
SEGMENTS: a theorem, in the goals' scope, where the request's layout is the written one; and so
from the shared head, at every o for the second hash. The end is the sentence `NuAsked Z` of
Johnson/Desc/First/Link/Law/K9NuAskLaw.lean, WRITTEN OUT, letter for letter: this file does not
import that one. Definitions (one test) and statements with their proofs; one closed fact by Lean's
kernel, looked at with the evaluator first, with its negative test.

How. At segment l the plan's nU[2] IS the number of columns of the planned ledger's array of the
third vector: the head: `public_array` (Johnson/Desc/Kinds/Law/ReadsArray.lean); the layers:
`public_G_K3` (Johnson/Goal/Meaning/PlanPort.lean); attention: `ofPlan_u3_tree`
(Johnson/Desc/First/Att/Claims/OfPlan.lean) with the seam's own line nU := #[0, 0, nU3]. That
number IS the columns of the layout's array (l, "U3"): `reads_room_of_built`
(Johnson/Desc/K1/Law/ReadsRoomAtAny.lean), general in the segment. The written layout's 25 arrays
"U3" each have a column: the kernel.

  `u3ColB`, `u3Col_written`, `u3Col_bites`   the test on the layout; the kernel's fact; at number
      25, where there is no segment, it rejects
  `thirdG`   a feed-forward plan numbers its third vector as array 0. THE SAME SENTENCE stands as
      `planG_third` in Johnson/Desc/AtSeats/LayKAt.lean, whose proof this is, line by line: typed
      again so that this file imports no law on the sub-protocol K1
  `thirdA`   the like for an attention plan (as `planA_third`,
      Johnson/Desc/K1/Law/SecAtAllPaid.lean); and its seam's third length is nW
  `nuAsked_in_scope`   **MAIN**. That a segment stands at l, with its kind and group:
      `listLinksH_with`, `built_declared`, `declareLinks_at`: no opening of the maker is asked
  `nuAsked_of_head`   **from the head**: the layout is the written one by `layout_in_scope` under
      the entry tests' first comparison, which the head gives (`pins_of_laid`)

What is not claimed. No member of the head. Without the written layout: nothing: the planners
refuse no array without columns. Nothing on soundness.

-/
import Johnson.Desc.First.Link.K9NuAsk
import Johnson.Desc.K1.Law.ReadsRoomAtAny
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Kinds.Law.ReadsArray
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Road.K4.Names.NamesAtLinks
import Johnson.P5J.MgAtAll
import Johnson.Goal.Meaning.PlanPort
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Model.Stages (SubPlanH LinkH)
open Fo.BatRows (bindE_ok ite_ok)
open VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed (Third made_third public_third)
open VerifiableInference.Desc.First.Att.P (planIs_public)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Desc.K1.Only (reads_room_of_built)
open Johnson.G (layoutFull)

/-- The layout's array "U3" of segment l has a column. -/
def u3ColB (lay : ReqLayout) (l : ℕ) : Bool :=
  (OnBytes.reqArray lay l "U3").any fun A => decide (0 < A.sizeC)

set_option maxRecDepth 1000000 in
/-- **The kernel's fact on the written layout.** -/
theorem u3Col_written : ((List.range 25).all fun l => u3ColB layoutFull l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: where there is no segment. -/
theorem u3Col_bites : u3ColB layoutFull 25 = false := by
  decide +kernel

/-- A feed-forward plan numbers its third vector as array 0. -/
theorem thirdG (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Third hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact made_third hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact made_third hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- An attention plan numbers its third vector as array 0; its seam's third length is nW. -/
theorem thirdA (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    Third P.seam.tl ∧ P.seam.nU.getD 2 0 = P.nW := by
  obtain ⟨seam0, h0, h1, -⟩ := Fo.BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := Fo.ZPlan.seamShape_lit h0
  obtain ⟨T, hA⟩ := Fo.ZPlan.seamPlan_cut h1
  refine ⟨made_third hS hA (Fo.SameP.refl _), ?_⟩
  unfold Attention.Seam.plan at h1
  dsimp only at h1
  obtain ⟨⟨tl1, Fp, T1⟩, _, h1⟩ := bindE_ok h1
  dsimp only at h1
  split at h1
  · obtain ⟨_, hx, _⟩ := bindE_ok h1
    cases hx
  · obtain ⟨_, _, h1⟩ := bindE_ok h1
    obtain ⟨Tp, _, h1⟩ := bindE_ok h1
    rw [← Except.ok.inj h1]
    rfl

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **The sentence NuAsked Z** (Johnson/Desc/First/Link/Law/K9NuAskLaw.lean), written out. -/
theorem nuAsked_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X)
    (hlay : Z.p.chains.proof.first.layout = layoutFull) :
    ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ nuPosB Z.p.X X = true := by
  obtain ⟨k4, kN, _, hAll⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4, kN] at h₀
  obtain ⟨_, _, _, p0, p24⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨_, hat⟩ := OnBytes.L5.LinksOrder.declareLinks_at _ _ _ _ _ hd
  -- what every sort ends in
  have fin : ∀ (l : ℕ) (Y : LinkH) (n : ℕ), l < 25 → l₀[l]? = some Y →
      Y.tl.ix.U.getD 2 none = some 0 → (∀ tr, Y.Fp.trees[0]? = some tr → tr.K = n) →
      (∀ ar, (nuB Z.p.X { Y with arrayOf := ar }).getD 2 0 = n) →
      ∃ X, Z.p.built.links[l]? = some X ∧ nuPosB Z.p.X X = true := by
    intro l Y n hl hY hU hK hn
    obtain ⟨ar, har⟩ := hat l Y hY
    obtain ⟨tr, A, g1, g2, _, g4⟩ := reads_room_of_built hB hY hU
    have hw := List.all_eq_true.1 u3Col_written l (List.mem_range.2 hl)
    unfold u3ColB at hw
    rw [hlay] at g2
    rw [g2, Option.any_some] at hw
    refine ⟨_, har, ?_⟩
    unfold nuPosB
    rw [hn ar, ← hK tr g1, ← g4]
    exact hw
  intro l hl
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨h0, hK, -⟩ := Kinds.Head.Law.ReadsArray.public_array hpub
    refine fin 24 _ (Z.p.X.H.nU.getD 2 0) hl p24 (public_third hpub) (fun tr htr => ?_)
      (fun _ => rfl)
    have e : Z.p.X.H.Fp.trees[0]? = some (Z.p.X.H.Fp.trees.getD 0 {}) := by
      rw [Array.getElem?_eq_getElem h0]
      simp [Array.getD, h0]
    have htr' : Z.p.X.H.Fp.trees[0]? = some tr := htr
    rw [Option.some.inj (htr'.symm.trans e)]
    exact hK
  · have hg : l / 2 < 12 := by omega
    obtain ⟨a, ha, _⟩ := hAll (l / 2) hg
    obtain ⟨hp, hgp⟩ := _root_.Meaning.planG_there hpub C hg
    have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
        ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[l / 2]? =
        some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, hgp]
      rfl
    have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
        ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[l / 2]? =
        some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, ha]
      rfl
    obtain ⟨q0, q1⟩ := p0 (l / 2) _ _ s0 t0
    by_cases hev : l % 2 = 0
    · have el : 2 * (l / 2) = l := by omega
      rw [el] at q0
      have h3 : Third hp.tl := thirdG Z.p.X.layers (l / 2) _ hp (public_G hpub (l / 2) hp hgp)
      refine fin l _ (hp.nU.getD 2 0) hl q0 h3 (fun tr htr => ?_) (fun _ => ?_)
      · have hk := _root_.Meaning.Plan.public_G_K3 hpub (l / 2) hp hgp h3
        have htr' : hp.Fp.trees[0]? = some tr := htr
        rw [htr'] at hk
        exact hk
      · show (((Z.p.X.G[l / 2]?).map (·.nU)).getD #[]).getD 2 0 = _
        rw [hgp]
        rfl
    · have el : 2 * (l / 2) + 1 = l := by omega
      rw [el] at q1
      obtain ⟨A0, pf, h0, e⟩ := planIs_public hpub (l / 2) a ha
      obtain ⟨h30, hnU⟩ := thirdA _ _ _ A0 h0
      obtain ⟨i0, T, hT, _, hK, _⟩ := _root_.K5Law.ofPlan_u3_tree ⟨_, _, _, A0, pf, h0, e⟩
      have h3 : a.seam.tl.ix.U.getD 2 none = some 0 := by
        rw [e]
        exact h30
      have hn : a.seam.nU.getD 2 0 = a.nW := by
        rw [e]
        exact hnU
      refine fin l _ (a.seam.nU.getD 2 0) hl q1 h3 (fun tr htr => ?_) (fun _ => ?_)
      · have htr' : a.seam.Fp.trees[0]? = some tr := htr
        rw [i0] at hT
        rw [Option.some.inj (htr'.symm.trans hT), hK, hn]
      · show (((Z.p.X.A[l / 2]?).map (·.seam.nU)).getD #[]).getD 2 0 = _
        rw [ha]
        rfl

end

/-- **From the head.** -/
theorem nuAsked_of_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain First.S ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ l < 25, ∃ X, Zp.p.built.links[l]? = some X ∧ nuPosB Zp.p.X X = true :=
  nuAsked_in_scope h.scope h.reads h.laid.pub h.pubOne
    (VerifiableInference.PlanWritten.Joined.layout_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1)

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.u3Col_written
#print axioms VerifiableInference.Desc.K9Asks.u3Col_bites
#print axioms VerifiableInference.Desc.K9Asks.thirdG
#print axioms VerifiableInference.Desc.K9Asks.thirdA
#print axioms VerifiableInference.Desc.K9Asks.nuAsked_in_scope
#print axioms VerifiableInference.Desc.K9Asks.nuAsked_of_head
