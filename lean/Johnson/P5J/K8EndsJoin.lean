-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8EndsJoin.lean: THE SMALLNESS TEST's NAMED TEST ON SIZES AT EVERY BUILT SEGMENT (ProofFile.smallSizesOwnB): THE JOIN OF THREE KINDS' LAWS ON "THE TABLES' END", SO FAR AS IT CAN BE TYPED. One definition, four theorems.
24 OF THE 25 PLACES ARE OPEN: ownSizes_of_cols TAKES THE LAW AT THE TWELVE FEED-FORWARD SEGMENTS (HL) AND AT THE TWELVE ATTENTION SEGMENTS (HA) AS PREMISES: two other kinds' laws; the output head's (24) is called. AND hW : planFitsAllB Zp.p.X = true (the frozen condition's own second conjunct) stays in front. (Where this and lean/THEOREM.md differ, the page holds.)
  K8N.box_of_array    an array of the name with rows and columns enough: the box accepts (sizeBoxOf's own text at a list of one name).
  K8N.ColsAt Z k      THE THREE LAWS' COMMON END: whatever ground, whatever built segment at k: Z's own layout has an array (k, "U3") with a row and at least tabsEnd (ProofFile.k8Par Z G Xl k) columns (Johnson/P5J/K8ThreeBoxes.lean).
  built_lt            under the head a ground's built segment has a number below 25.
  colsAt_head         ColsAt Zp 24: u3_cols_head (Johnson/P2LawR/U3ColsHead.lean), whose end spells the fold out: one term with tabsEnd.
  **ownSizes_of_cols h hW HL HA : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true**: ownSizes_of_ends (Johnson/P5J/K8OwnSizesAt.lean) at the three.
Can the premises be met together? Evaluated at the goals' named full-size set, in a file of evaluations that is not named here: hW: true; ColsAt's inequality is an equality at all 25. Not proved.
Limits. The head is a premise: over the entry tests' asksAt2 and asksAt3. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8OwnSizesAt
import Johnson.P2LawR.U3ColsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.K8N
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc.K9 (sizeBoxOf)

/-- An array of the name with rows and columns enough: the box accepts. -/
theorem box_of_array {lay : Params.ReqLayout} {k : ℕ} {nm : String} {R C : ℕ}
    (h : ∃ A, reqArray lay k nm = some A ∧ R ≤ A.sizeI ∧ C ≤ A.sizeC) :
    sizeBoxOf #[(k, nm)] lay 0 R C = true := by
  obtain ⟨A, e, h1, h2⟩ := h
  show (match (some (k, nm) : Option (ℕ × String)).bind fun b => reqArray lay b.1 b.2 with
    | some A => decide (R ≤ A.sizeI) && decide (C ≤ A.sizeC)
    | none => false) = true
  rw [Option.bind_some, e]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

/-- **The three laws' common end.** -/
def ColsAt (Z : ProofFile.Pub) (k : ℕ) : Prop :=
  ∀ (G : ProofFile.Ground) (Xl : LinkH), ProofFile.blankBy ProofFile.pureRoad.links Z = some G →
    G.built[k]? = some Xl →
    ∃ A, reqArray Z.first.layout k "U3" = some A ∧ 1 ≤ A.sizeI ∧
      tabsEnd (ProofFile.k8Par Z G Xl k) ≤ A.sizeC

end P5J.K8N

namespace P5J
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open VerifiableInference.PlanWritten.Joined (layout_in_scope)
open K8N

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head a ground's built segment has a number below 25. -/
theorem built_lt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) : l < 25 := by
  obtain ⟨links, eB⟩ := Meaning.K2.blank_built hG
  have hsz : Zp.p.built.links.size = 25 := built_size h.toAtMg.scope h.toAtMg.laid
  have a := (Array.getElem?_eq_some_iff.1 e3).1
  rw [eB, Array.size_zipWith] at a
  omega

/-- The law at the output head's segment: another file's (`u3_cols_head`). -/
theorem colsAt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ColsAt Zp 24 :=
  fun _ _ hG e3 => P2Law.K8U.u3_cols_head h.toAtMg.scope h.toAtMg.reads h.toAtMg.laid.pub hG e3

/-- **THE NAMED TEST ON SIZES AT EVERY BUILT SEGMENT, FROM THE HEAD, planFitsAllB AND THE LAW ON THE TABLES'
END AT THE 24 OTHER SEGMENTS.** -/
theorem ownSizes_of_cols (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hW : planFitsAllB Zp.p.X = true) (HL : ∀ g < 12, ColsAt Zp (2 * g))
    (HA : ∀ g < 12, ColsAt Zp (2 * g + 1)) :
    ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true := by
  refine ownSizes_of_ends h hW fun G l Xl hG e3 => ?_
  have hl := built_lt h hG e3
  have hLay : Zp.first.layout = Johnson.G.layoutFull :=
    layout_in_scope h.toAtMg.scope h.toAtMg.laid.pub (pins_of_laid h.toAtMg.scope h.toAtMg.laid).1
  rw [← hLay]
  refine box_of_array ?_
  by_cases h24 : l = 24
  · subst h24
    exact colsAt_head h G Xl hG e3
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact HL g (by omega) G Xl hG e3
    · exact HA g (by omega) G Xl hG e3

end P5J

#print axioms P5J.K8N.box_of_array
#print axioms P5J.built_lt
#print axioms P5J.colsAt_head
#print axioms P5J.ownSizes_of_cols
#print axioms P2Law.K8U.u3_cols_head
