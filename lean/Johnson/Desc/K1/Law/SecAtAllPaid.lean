-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SecAtAllPaid.lean: THE TEST `secB` (Johnson/Desc/K1/Law/SecAtAll.lean: at each
attention segment, of all entries of the segment's list of arrays only the one at the plan's number
iU3 lies in a message of moment 1, and it has room) ACCEPTS: a theorem, in the goals' scope, under
the entry tests' first comparison (by which the layout and the shape are the written ones).
Definitions (one test) and statements with their proofs; one closed fact by Lean's kernel, looked
at with the evaluator first, with its negative test.

  `momNameB`, `momU3_written`, `momU3_bites`   BY LEAN's KERNEL, at the written layout and shape: at
      each odd segment every array whose message has moment 1 is named "U3"; under the names "ZZ"
      and "M0" the test rejects (so there is such an array)
  `name_of_guard`   so an entry that passes secB's guard is (l, "U3")
  `planA_third`   an attention plan numbers its third vector as array 0: the library's `planA_u`'s
      walk (OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean) with `made_third`
      (Johnson/Desc/Kinds/Law/ReadsNamed.lean)
  `sec_att`   **what secB asks, at an attention segment**: the number by `declared_only`
      (ReadsNameOnly.lean, this folder); the room by `reads_room_of_built` (ReadsRoomAtAny.lean,
      this folder) and `ofPlan_u3_tree` (one row; as many columns as the plan's nW, which is what
      `plannedK` reads). The road from the public part to the planner's list is that of
      `names_tie_att_plain` (Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean), line by line
  `hSecB_atAll`   **the owed field hSecB, in its own type**, at the closed constant (`hA.𝔇`,
      P5J/MgAtAll.lean): from the head, an opening of the maker and the first comparison's accept

What is not claimed. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.SecAtAll
import Johnson.Desc.K1.Law.HeadNumbersAtAll
import Johnson.Desc.K1.Law.ReadsNameOnly
import Johnson.Desc.K1.Law.ReadsRoomAtAny
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Road.K4.Names.NamesAtLinks
import Johnson.Goal.Numbers.MadeInScope
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Stages (SubPlanH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First.Att.P (plannedK planIs_public)
open VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed (Third made_third)
open VerifiableInference.PlanWritten (madePinnedAt)
open Johnson.G (layoutFull)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

/-- Every array of segment l's layout whose message has moment 1 is named nm. -/
def momNameB (lay : ReqLayout) (shp : ReqShape) (l : ℕ) (nm : String) : Bool :=
  ((lay.link[l]?).getD []).all fun Ar => !mom1B shp l (l, Ar.name) Ar || Ar.name == nm

set_option maxRecDepth 1000000 in
/-- **The kernel's fact on the written layout and shape.** -/
theorem momU3_written :
    ((List.range 12).all fun g => momNameB layoutFull shapeFull (2 * g + 1) "U3") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: under another name; and there is such an array. -/
theorem momU3_bites : momNameB layoutFull shapeFull 3 "ZZ" = false ∧
    momNameB layoutFull shapeFull 3 "M0" = false := by
  decide +kernel

theorem sec_odd : ∀ l < 25, (linksFull[l]?).getD .layers = ModelPart.attention →
    2 * (l / 2) + 1 = l ∧ l / 2 < 12 := by decide

/-- An attention plan numbers its third vector as array 0. -/
theorem planA_third (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : Third P.seam.tl := by
  obtain ⟨seam0, h0, h1, -⟩ := Fo.BatRows.planA_rows0 settings i cf P e
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := Fo.ZPlan.seamShape_lit h0
  obtain ⟨T, hA⟩ := Fo.ZPlan.seamPlan_cut h1
  exact made_third hS hA (Fo.SameP.refl _)

/-- An entry that passes secB's guard is (l, nm). -/
theorem name_of_guard {lay : ReqLayout} {shp : ReqShape} {l : ℕ} {nm : String} {cn : ℕ × String}
    {Ar : ReqArray} (hw : momNameB lay shp l nm = true)
    (hr : OnBytes.reqArray lay cn.1 cn.2 = some Ar) (hm : mom1B shp l cn Ar = true) :
    cn = (l, nm) := by
  have e1 : cn.1 = l := by
    unfold mom1B at hm
    rw [Bool.and_eq_true] at hm
    exact eq_of_beq hm.1
  unfold OnBytes.reqArray at hr
  cases hL : lay.link[cn.1]? with
  | none =>
    rw [hL] at hr
    cases hr
  | some arrays =>
    rw [hL] at hr
    have hf : (arrays.find? fun A => A.name == cn.2) = some Ar := hr
    have h1 : (Ar.name == cn.2) = true :=
      List.find?_some (p := fun A : ReqArray => A.name == cn.2) hf
    have h2 : Ar ∈ arrays := List.mem_of_find?_eq_some hf
    unfold momNameB at hw
    rw [← e1, hL] at hw
    have h3 := List.all_eq_true.1 hw Ar h2
    have h4 : mom1B shp cn.1 (cn.1, Ar.name) Ar = true := by
      rw [← e1] at hm
      exact hm
    rw [h4, Bool.not_true, Bool.false_or] at h3
    exact Prod.ext e1 ((eq_of_beq h1).symm.trans (eq_of_beq h3))

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub}

/-- **What secB asks, at an attention segment, in the goals' scope.** -/
theorem sec_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {shp : ReqShape} {g : ℕ}
    (hg : g < 12) (hw : momNameB Z.p.chains.proof.first.layout shp (2 * g + 1) "U3" = true)
    {Ap : Attention.Plan} (hAp : Z.p.X.A[g]? = some Ap) (t : ℕ) (cn : ℕ × String) (Ar : ReqArray)
    (ht : ((Z.p.built.links.map (·.arrayOf)).getD (2 * g + 1) #[])[t]? = some cn)
    (hr : OnBytes.reqArray Z.p.chains.proof.first.layout cn.1 cn.2 = some Ar)
    (hm : mom1B shp (2 * g + 1) cn Ar = true) :
    t = Ap.iU3 ∧ roomB (plannedK Ap) Ap.nW Ar.sizeI Ar.sizeC = true := by
  have hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public hZ
  obtain ⟨k4, kN, _, _⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
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
      some { tl := Ap.seam.tl, Fp := Ap.seam.Fp, Tp := Ap.seam.Tp, ns := Ap.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hAp]
    rfl
  obtain ⟨_, q1⟩ := p0 g _ _ s0 t0
  obtain ⟨A0, pf, h0, e⟩ := planIs_public hpub g Ap hAp
  have h3 : Ap.seam.tl.ix.U.getD 2 none = some 0 := by
    have h30 : Third A0.seam.tl := planA_third _ _ _ A0 h0
    rw [e]
    exact h30
  obtain ⟨i0, T, hT, hR1, hK, _⟩ := _root_.K5Law.ofPlan_u3_tree ⟨_, _, _, A0, pf, h0, e⟩
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨ar, har, hOnly⟩ := Only.declared_only hd q1
  have ecn := name_of_guard hw hr hm
  have elist : (Z.p.built.links.map (·.arrayOf)).getD (2 * g + 1) #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, har]
    rfl
  rw [elist, ecn] at ht
  have ht0 : (some 0 : Option ℕ) = some t := h3.symm.trans (hOnly t _ ht)
  have et : t = 0 := (Option.some.inj ht0).symm
  obtain ⟨tr, A, g1, g2, g3, g4⟩ := Only.reads_room_of_built hB q1 h3
  have etr : tr = T := by
    rw [i0] at hT
    exact Option.some.inj (g1.symm.trans hT)
  have eA : A = Ar := by
    rw [ecn] at hr
    exact Option.some.inj (g2.symm.trans hr)
  have hk : plannedK Ap = T.K := by
    unfold plannedK
    rw [hT]
    rfl
  refine ⟨by rw [et, i0], ?_⟩
  rw [← eA, g3, g4, etr, hR1, hk, ← hK]
  unfold roomB
  simp

end

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA O hP1

/-- **The field hSecB.** -/
theorem hSecB_atAll : secB Zp.made.p.built.links Zp.p.X hA.𝔇.shape hA.𝔇.layout = true := by
  have hlay : hA.𝔇.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope hA.scope hA.laid.pub hP1
  have hshp : hA.𝔇.shape = shapeFull := hDsh_atAll hA O hP1
  unfold secB
  refine List.all_eq_true.2 fun l hl => ?_
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases hs : (linksFull[l]?).getD .layers = ModelPart.attention
  · obtain ⟨e, h12⟩ := sec_odd l hl' hs
    rw [Bool.or_eq_true]
    right
    cases hG : Zp.p.X.A[l / 2]? with
    | none => rfl
    | some Ap =>
      rw [Option.all_some]
      refine List.all_eq_true.2 fun y hy => ?_
      have hy' := List.mem_zipIdx_iff_getElem?.1 hy
      rw [Array.getElem?_toList] at hy'
      cases hr : OnBytes.reqArray hA.𝔇.layout y.1.1 y.1.2 with
      | none => rfl
      | some Ar =>
        rw [Option.all_some]
        cases hm : mom1B hA.𝔇.shape l y.1 Ar with
        | false => rfl
        | true =>
          have hw : momNameB hA.𝔇.layout hA.𝔇.shape (2 * (l / 2) + 1) "U3" = true := by
            rw [hlay, hshp]
            exact List.all_eq_true.1 momU3_written (l / 2) (List.mem_range.2 h12)
          rw [← e] at hy' hm
          obtain ⟨h1, h2⟩ := sec_att hA.scope hA.reads O.pub h12 hw hG y.2 y.1 Ar hy' hr hm
          rw [Bool.not_true, Bool.false_or, h2, Bool.and_true, h1]
          exact beq_self_eq_true _
  · rw [Bool.or_eq_true]
    left
    simpa using hs

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.momU3_written
#print axioms VerifiableInference.Desc.K1.momU3_bites
#print axioms VerifiableInference.Desc.K1.sec_odd
#print axioms VerifiableInference.Desc.K1.planA_third
#print axioms VerifiableInference.Desc.K1.name_of_guard
#print axioms VerifiableInference.Desc.K1.sec_att
#print axioms VerifiableInference.Desc.K1.hSecB_atAll
