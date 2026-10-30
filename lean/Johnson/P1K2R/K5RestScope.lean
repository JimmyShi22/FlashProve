-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/K5RestScope.lean: code switching (K2): THE REST OF THE NAMED TEST k5PlanB
(k5RestB: Johnson/P1K2R/K5PlanCut.lean) IS A THEOREM IN SCOPE, WHERE THE VALUE IS LAID, at
the twelve written attention links.
  att_u3       an attention plan of the public record: its vector of reads is array number 0, with
               one row and nW columns; its record names the third vector alone: Att.P.public_plan
               (Johnson/Desc/First/Att/GuardPublic.lean) · K5Law.plan_u3_tree | plan_U
               (Johnson/Desc/First/Att/Claims/PlanU3.lean)
  u3Moment_full    BY LEAN's KERNEL, at the written layout and shape: at the twelve links the array
               "U3" is laid in a message of moment 1 · u3Moment_bent: a bent twin that rejects
               (the same link's array "ZZ") · u3Moment_bent_there: that twin is not idle
  k5RestB_in_scope (hZ : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt …) (hl : l ∈ attW) :
               k5RestB Zp (At.X Zp) Zp.first.shape Zp.first.layout l = true
HOW. The built links are buildLinksH's with the routines blanked (ProofFile.Law.pub_builtOf); the list
that
it is handed has attention's link at l (listLinksH_with); reads_named_at (Johnson/P1K2R/
ReadsRoomAtAny.lean) names the array and sizes it by the plan's tree; att_u3 sizes the tree. The
written layout and shape: at_written (K2Ties/WrittenAt.lean) at pins_of_laid: this spends LaidAt's
entry tests (its field asks).
LIMITS. Joins, a law's call and one closed fact by the kernel. hZ and LaidAt are not shown met: no
example. No soundness is claimed.
-/
import Johnson.P1K2R.ReadsRoomAtAny
import Johnson.P1K2R.K5PlanCut
import Johnson.P1K2R.BuiltLinkAt
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Desc.First.Att.Claims.PlanU3
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model.Stages

/-! ## Attention's plan in the public record -/

/-- **An attention plan of the public record**: its vector of reads is array number 0, with one row
and nW columns; its record names the third vector alone. -/
theorem att_u3 {pol KL : ByteArray} {layout : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL layout = .ok X) {g : ℕ} {a : Attention.Plan}
    (hg : X.A[g]? = some a) :
    a.iU3 = 0 ∧ a.seam.tl.ix.U.getD 2 none = some 0 ∧
      ∃ T : Model.HTree, a.seam.Fp.trees[0]? = some T ∧ T.R = 1 ∧ T.K = a.nW := by
  obtain ⟨A0, pf, hp, e⟩ := VerifiableInference.Desc.First.Att.P.public_plan h g a hg
  obtain ⟨i0, T, hT, hR, hK, -⟩ := K5Law.plan_u3_tree hp
  have hU := K5Law.plan_U hp
  rw [i0] at hT
  rw [e]
  refine ⟨i0, ?_, T, hT, hR, hK⟩
  show A0.seam.tl.ix.U.getD 2 none = some 0
  rw [hU]
  rfl

/-! ## A closed fact at the written layout and shape -/

set_option maxRecDepth 1000000 in
/-- **By the kernel**: at the twelve written attention links the array "U3" is laid in a message of
moment 1. -/
theorem u3Moment_full : attW.all (fun l => (reqArray Johnson.G.layoutFull l "U3").any fun Ar =>
    match (VerifiableInference.PlanWritten.proofSizedFull.request.link[l]?).bind
      fun k => k.messages[Ar.message]? with
    | some x => x.moment == 1
    | none => false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A bent twin that rejects: another array of the same link, which is laid at a later moment. -/
theorem u3Moment_bent : ((reqArray Johnson.G.layoutFull 1 "ZZ").any fun Ar =>
    match (VerifiableInference.PlanWritten.proofSizedFull.request.link[1]?).bind
      fun k => k.messages[Ar.message]? with
    | some x => x.moment == 1
    | none => false) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- That twin is not idle: the array is laid. -/
theorem u3Moment_bent_there : (reqArray Johnson.G.layoutFull 1 "ZZ").isSome = true := by
  decide +kernel

/-! ## k5RestB in scope -/

section
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Ties (at_written)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

set_option maxHeartbeats 2000000 in
/-- **k5RestB IS A THEOREM IN SCOPE**, at the twelve written attention links. -/
theorem k5RestB_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l ∈ attW) :
    k5RestB Zp (P5J.At.X Zp) Zp.first.shape Zp.first.layout l = true := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  have hX := public_at_laid L
  obtain ⟨hq, hN, -, hAll⟩ := Meaning.scope_plans hZ hR hX
  have Aw := at_written hZ L (P5J.pins_of_laid hZ L).1
  -- l is odd and below 24
  have hl' : l < 24 ∧ l % 2 = 1 := by
    unfold attW at hl
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hl
    have h3 := List.mem_range'_1.1 h1
    have h4 : IM.subW l = .attention := of_decide_eq_true h2
    refine ⟨by omega, ?_⟩
    unfold IM.subW at h4
    by_contra c
    rw [if_neg (by omega), if_pos (by omega)] at h4
    cases h4
  obtain ⟨h24, hodd⟩ := hl'
  obtain ⟨a, hA, -⟩ := hAll (l / 2) (by omega)
  obtain ⟨i0, hU, T, hT, hTR, hTK⟩ := att_u3 hX hA
  -- the built links
  obtain ⟨b, hb, eb⟩ := ProofFile.Law.pub_builtOf
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp from L.pub)
  unfold Model.Verify.builtOf at hb
  obtain ⟨l₀, h₀, hB⟩ := OnBytes.L5.LinksOrder.ok_bind hb
  unfold Model.Verify.linksOf at h₀
  rw [hq, hN] at h₀ hB
  obtain ⟨gs, -, -, p0, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have hs := Array.getElem?_eq_getElem (i := l / 2) (by rw [gs]; omega)
  have hAs : (Zp.p.X.A.map Model.Verify.attentionPlanOf)[l / 2]? =
      some (Model.Verify.attentionPlanOf a) := by rw [Array.getElem?_map, hA]; rfl
  have hY := (p0 (l / 2) _ _ hs hAs).2
  rw [show 2 * (l / 2) + 1 = l by omega] at hY
  obtain ⟨⟨bl, hbl, harr⟩, tr, Ar, htr, hreq, hI, hC⟩ := reads_named_at hB hY (t := 0) hU
  obtain rfl : T = tr := Option.some.inj (hT.symm.trans htr)
  have hXl : Zp.p.built.links[l]? = some (ProofFile.Law.blank bl) := by
    rw [← eb]
    show (b.links.map ProofFile.Law.blank)[l]? = _
    rw [Array.getElem?_map, hbl]
    rfl
  obtain ⟨ar, hbl'⟩ := (Meaning.built_at hB).2 l _ hY
  obtain rfl := Option.some.inj (hbl.symm.trans hbl')
  have hlay : Zp.first.layout = Johnson.G.layoutFull := Aw.layout
  have hsh : Zp.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request := Aw.shape
  have km := List.all_eq_true.1 u3Moment_full l hl
  have hreq' : reqArray Zp.first.layout l "U3" = some Ar := hreq
  rw [← hlay, ← hsh, hreq', Option.any_some] at km
  -- the second clause
  have c2 : r2B Zp.first.layout Zp.first.shape l ar a.iU3 a.nW = true := by
    unfold r2B
    rw [i0, show ar[0]? = some (l, "U3") from harr, Option.any_some]
    show ((reqArray Zp.first.layout l "U3").any fun Ar => _) = true
    rw [hreq', Option.any_some]
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨km, by rw [hI, hTR]; omega⟩, by rw [hC, hTK]⟩
  -- the first clause
  have c1 : ((startFork (pubOf (ProofFile.Law.blank
      { OnBytes.L5.LinksOrder.linkA 12 (Model.Verify.attentionPlanOf a) (l / 2) with
        arrayOf := ar })) a.ns).trees[a.iU3]?).any (fun T => T.R == 1 && T.K == a.nW) = true := by
    rw [i0]
    show ((a.seam.Fp.trees.map _)[0]?).any _ = true
    rw [Array.getElem?_map, hT, Option.map_some, Option.any_some]
    show (T.R == 1 && T.K == a.nW) = true
    rw [hTR, hTK]
    simp
  unfold k5RestB
  rw [show (P5J.At.X Zp).A[l / 2]? = some a from hA, hXl]
  show (r2B Zp.first.layout Zp.first.shape l ar a.iU3 a.nW &&
    match Zp.p.X.A[l / 2]? with
    | some p => ((startFork (pubOf (ProofFile.Law.blank
        { OnBytes.L5.LinksOrder.linkA 12 (Model.Verify.attentionPlanOf a) (l / 2) with
          arrayOf := ar })) p.ns).trees[a.iU3]?).any fun T => T.R == 1 && T.K == a.nW
    | none => false) = true
  rw [c2, hA]
  exact c1

end

end P1K2

#print axioms P1K2.att_u3
#print axioms P1K2.u3Moment_full
#print axioms P1K2.u3Moment_bent
#print axioms P1K2.u3Moment_bent_there
#print axioms P1K2.k5RestB_in_scope
