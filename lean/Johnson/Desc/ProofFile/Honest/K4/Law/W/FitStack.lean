-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitStack.lean: CONDITIONAL.

What is here. The honest side's function for the batched sumcheck returns, and what it returns has
the public shape of its call (`stack_fit`): one more of the fifteen clauses of the public test
`k4MakersFit` (Johnson/Desc/ProofFile/Honest/K4/Part.lean), as a law, at every input w, at all
sampled values p whose fields have the sizes named and at all shown values; brought down to returns
of three functions: the one that lays the honest side's common data (Sides.of), its list of placed
panels, and the verifier's own end of that sumcheck over these panels. The data are made by
Johnson/Road/K4/C/StackDataOf.lean. The true end values are made at every list of challenges, and
are as many as the call states (`endsAt_returns`): the verifier's end returns; its two forms are
valued (end_valued); the panel of the down product is found (Johnson/Road/K4/C/DownFound.lean). The
two long tables have 2 ^ lamS entries (Law/SkelStack.lean).

  `endsAt_returns`   the true end values are made, and how many they are.
  `stackJob_fits`   the job of given data has its call's shape.
  `stack_fit`   the whole.

Not shown here. THREE RETURNS: that Sides.of returns (hS': Law/SidesWhole.lean's sides_whole has it
with no return left); that the honest side's list of placed panels returns (hPan); that the
verifier's end returns over these panels at all values of the right sizes (hEnd): hypotheses HERE;
Johnson/Road/K4/C/PanelsOf.lean's panels_return has the last two, and both tests on numbers, from
the public test pansB; Law/W/FitStackPub.lean lays all of these in. TWO TESTS ON NUMBERS: the
panels' places fill lamS bits (hc); the weight claims are as many as the plan says (ho). The
verifier's laying of the tables returns (hl). K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH
THE LIBRARY's ELEVEN SWITCHES). The sizes of p's fields: two weights of the passes (hom); the end
point rt has lt coordinates (hrt). (That the lookup's point is not empty, that its token point has
lt coordinates and that lt is not 0 follow here: from hS' and Johnson/Road/K4/C/PlanLt.lean.) That
all of these hold together: no example is laid here; by the head of Law/W/FitStackPub.lean,
Law/MakersFitHead.lean has them together under the library's hypothesis on the public files. What
the job's tables and end values hold. By a walk of import lines the closure holds no module under
Johnson/RecCompile/, Johnson/Goal/ or Johnson/D/. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelStack
import Johnson.Desc.ProofFile.Honest.K4.Law.SumLevels
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPaid
import Johnson.Road.K4.C.PlanLt
import Johnson.Road.K4.C.StackDataOf
import Johnson.Road.K4.C.DownFound
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.CornerKit
import Johnson.Road.K4.C.NormsPlanOf
import Johnson.Road.K4.C.PlanLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE oneE ceilLog2)
open OnBytes.Model (HTailF2 orderDefault)
open OnBytes.Model.Layer (SBlk StackEnd TableAsk TableAt layTables tableAsks stackEnd)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (sides_fields stackDataOn_returns end_valued down_found named_three
  normsPlan_of_plan planLens_of_plan)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open Inst.Model.FFSeg (Dim)

/-- **THE TRUE END VALUES ARE MADE, AND HOW MANY THEY ARE.** CONDITIONAL: on every hypothesis named.
-/
theorem endsAt_returns {D : StackData} {rs : Array E} {fin : StackEnd}
    (hE : stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om (Array.replicate D.nVirt zeroE)
      (Array.replicate D.S.opens.size zeroE) zeroE zeroE = some fin)
    (hA : affFits D.S.v D.R fin.Alin = true) (hB : affFits D.S.v D.R fin.Blin = true)
    (h0 : D.S.v.y.h.ll + D.S.v.y.lPf ≠ 0) :
    ∃ e, D.endsAt rs = some e ∧ e.length = 2 + (1 + D.S.v.y.LamM) + D.S.opens.size := by
  obtain ⟨dn, hdn⟩ := down_found hE h0
  have vA : ∃ z, D.val fin.Alin = some z := by
    unfold StackData.val
    rw [if_pos hA]
    exact ⟨_, rfl⟩
  have vB : ∃ z, D.val fin.Blin = some z := by
    unfold StackData.val
    rw [if_pos hB]
    exact ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ := vA
  obtain ⟨B0, hB0⟩ := vB
  refine ⟨_, Option.bind_eq_some_iff.mpr ⟨fin, hE, Option.bind_eq_some_iff.mpr ⟨A0, hA0,
    Option.bind_eq_some_iff.mpr ⟨B0, hB0, Option.bind_eq_some_iff.mpr ⟨dn, hdn, rfl⟩⟩⟩⟩, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [Array.length_toList, afoldl_size, Array.size_replicate]
  · omega
  · intro V b
    cases b.v0 with
    | none => rfl
    | some v0 =>
      dsimp only
      split
      · exact Array.size_setIfInBounds ..
      · exact foldl_size (fun _ _ => Array.size_setIfInBounds ..) _ V

/-- **THE JOB OF GIVEN DATA HAS ITS CALL's SHAPE.** CONDITIONAL: on the three hypotheses. -/
theorem stackJob_fits {D : StackData} {n : ℕ} (h1 : D.SA.size = 2 ^ D.S.Q.hp.lamS)
    (h2 : D.SB.size = 2 ^ D.S.Q.hp.lamS)
    (he : ((D.endsAt (List.replicate D.S.Q.hp.lamS zeroE).toArray.reverse).getD []).length = n) :
    k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 n) (jobStackOn D) = true := by
  have hfit : (jobStackOn D).cube.fits = true := by
    refine fits_of _ ?_ ?_ ?_ ?_ ?_
    · show (orderDefault D.S.Q.hp.lamS).length = D.S.Q.hp.lamS
      simp [orderDefault]
    · intro v hv
      show v ∈ orderDefault D.S.Q.hp.lamS
      simpa [orderDefault] using hv
    · intro t ht
      have ht' : t ∈ [D.SA, D.SB] := ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl
      · exact h1
      · exact h2
    · intro x hx
      have hx' : x ∈ [((oneE, 0, 1) : E × ℕ × ℕ)] := hx
      rw [List.mem_singleton] at hx'
      rw [hx']
      exact ⟨by show 0 < 2; norm_num, by show 1 < 2; norm_num⟩
    · intro r hr
      cases hr
  have he' : ((jobStackOn D).ends (List.replicate D.S.Q.hp.lamS zeroE)).length = n := he
  unfold k4JobFits
  rw [hfit]
  simp [k4PlainShape, jobStackOn, VerifiableInference.Desc.Part.MaskedSum.Var.d] at he' ⊢
  exact he'

variable {Q : K4Pub} {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2}
  {D : Dim} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **THE BATCHED SUMCHECK's JOB IS MADE AND HAS ITS CALL's SHAPE.** CONDITIONAL: on every
hypothesis named. -/
theorem stack_fit (A : K4Plan hS pc Q.P Q.g tl D)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {w : K4In} {p : Pts}
    {shownT : Array E} {S : OnBytes.Desc.First.K4.Honest.Sides} (hS' : Sides.of Q w p = some S)
    {x : Array SBlk × ℕ} (hPan : S.panels shownT = some x) (hc : ceilLog2 x.2 = Q.hp.lamS)
    (hom : p.om.size = 2) (ho : S.opens.size = Q.hp.NCL - (if Q.g == 0 then 1 else 0))
    (hEnd : ∀ (rs om H1 V : Array E) (a b : E), rs.size = Q.hp.lamS → om.size = 2 →
      H1.size = 1 + Q.P.y.LamM → V.size = S.opens.size →
      ∃ fin, stackEnd Q.P.y x.1 rs Q.hp.lamS om H1 V a b = some fin)
    (hrt : p.rt.size = Q.P.y.h.lt) :
    ∃ j, jobStack Q w p shownT = some j ∧
      k4JobFits (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - (if Q.g == 0 then 1 else 0)))) j = true := by
  obtain ⟨eQ, _, efo, hv, ⟨Z, hZ, _⟩, _, _⟩ := sides_fields hS'
  subst eQ
  have ht := OnBytes.Road.K4.C.envOf_tab hv hl
  have ey := OnBytes.Road.K4.C.envOf_y hv
  have Ad := OnBytes.Road.admitted_of_layout A.lay A.sw.p3
  have hT : S.Q.P.y.T = 2 ^ S.Q.P.y.h.lt := by
    rw [(normsPlan_of_plan A).T, (planLens_of_plan A).2.2.1]
  have hla : S.Q.P.y.ls + S.Q.P.y.h.lt = S.Q.P.y.h.la := by
    rw [Ad.shape]
    exact Ad.la.symm
  have h4 := OnBytes.Road.K4.C.lt_of_plan A
  have hlt : S.Q.P.y.h.lt ≠ 0 := by omega
  have hle : S.Q.P.y.h.la ≤ p.fo.zx.size := by
    by_contra hk
    unfold OnBytes.Model.lastOf OnBytes.Model.cutLast at hZ
    rw [if_pos (by omega)] at hZ
    cases hZ
  have h0 : p.fo.zx.isEmpty = false := by
    have : p.fo.zx.size ≠ 0 := by omega
    simpa [Array.isEmpty] using this
  have hzt : (ztOf S.Q p).size = S.Q.P.y.h.lt := ztOf_size_of_le S.Q p (by omega)
  have ep : ({ p with fo := S.fo } : Pts) = p := by rw [efo]
  have H3 := named_three (Q := S.Q) (p := p) hZ h0 hzt hrt hlt hla
  rw [← ep] at H3
  obtain ⟨fin0, hE0⟩ := hEnd (Array.replicate S.Q.hp.lamS zeroE) p.om
    (Array.replicate (1 + S.Q.P.y.LamM) zeroE) (Array.replicate S.opens.size zeroE) zeroE zeroE
    (by rw [Array.size_replicate]) hom (by rw [Array.size_replicate])
    (by rw [Array.size_replicate])
  obtain ⟨R, sides, hR, _, hD⟩ := stackDataOn_returns (p := p) A.reads hl hT hla ht hPan hc hom ho
    hE0 H3
  refine ⟨_, by unfold jobStack stackData; rw [hS']; show (stackDataOn S p shownT).map _ = _
                rw [hD]; rfl, ?_⟩
  obtain ⟨fin, hE⟩ := hEnd (List.replicate S.Q.hp.lamS zeroE).toArray.reverse p.om
    (Array.replicate (1 + S.Q.P.y.LamM) zeroE) (Array.replicate S.opens.size zeroE) zeroE zeroE
    (by simp) hom (by rw [Array.size_replicate]) (by rw [Array.size_replicate])
  obtain ⟨fA, fB⟩ := end_valued A.reads hl hT hla ht hPan hR H3 hE
  obtain ⟨e, he, hlen⟩ := endsAt_returns
    (D := { S := S, R := R, bl := x.1, om := p.om, F := S.weights (OnBytes.Model.eqTab p.rt)
            hZ := S.gatedUnder (OnBytes.Model.eqTab S.zt)
            hR := S.gatedUnder (OnBytes.Model.eqTab p.rt)
            SA := (longTabs S.Q.hp.lamS x.1 sides).1, SB := (longTabs S.Q.hp.lamS x.1 sides).2 })
    (rs := (List.replicate S.Q.hp.lamS zeroE).toArray.reverse) (fin := fin)
    (by
      show stackEnd S.v.y x.1 _ S.Q.hp.lamS p.om (Array.replicate (1 + S.v.y.LamM) zeroE) _ _ _ = _
      rw [ey]
      exact hE) fA fB (by
      show S.v.y.h.ll + S.v.y.lPf ≠ 0
      rw [ey]
      have := Ad.laid.ll
      omega)
  refine stackJob_fits (longTabs_size _ _ _).1 (longTabs_size _ _ _).2 ?_
  rw [he]
  show e.length = _
  rw [hlen]
  show 2 + (1 + S.v.y.LamM) + S.opens.size = _
  rw [ey, ho]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.endsAt_returns
#print axioms ProofFile.Honest.K4.W.stackJob_fits
#print axioms ProofFile.Honest.K4.W.stack_fit
