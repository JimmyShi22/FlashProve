-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/RestTiesAtHeadU.lean: the public premises of
`exact_free_trees` (Sim/TreesExact.lean), `PubTiesT` and `OpenTies`, under the library's head
(`P5J.AtMg`), at the place at which the proof file's description seats the test on G_u,
`(fourOf Np).U`: at every job at that place which says that the first fold's fresh table has come
earlier.

Which trees. The list of first trees is the place's own field `first`: the openings that the place's
numbers lay at the first reading round where the fold sends no table of its own (`roundsOfNums`,
Johnson/Desc/K12/TestEntries.lean). Under the head they are two, both the chain's own
(`first_head_U`). What is asked of the simulators' job beyond its place and its flag is one public
equation: it names these trees, each at its declared depth.

  `declared_alike`, `reachTB_alike`   `reachTB` (Sim/TreesReach.lean) reads of a place no more than
                 `Alike` (FrontAtHead.lean) holds
  `rounds_UFull`, `opens_UFull`   two evaluations by Lean's kernel at the written place `piUFull`
  `first_head_U`   the two first trees at the seated place
  `pubTiesT_head_U`   `PubTiesT` at two trees
  `openTies_head_U`   `OpenTies` at the place's own list
  `madeSimsOpen`, `sims_open_there`   a made-up simulators' job, written out, with the three public
                 letters that are asked: so what is asked is not empty by form

By what. `alike_head_U` (FrontAtHead.lean), `planB_head` and `formPubB_head` (AsksAtHead.lean),
`reachT_U_full` (Sim/TreesReach.lean), `facts_head_U` (Sim/FirstAnyAtHeadU.lean), `tablesFitB_eq`
and `nums_head_U` (Sim/FirstPubAtHead.lean), called.

Limits.
- Public premises alone: Booleans, numbers and lists on the place and on two public letters of the
  jobs. No sentence on a member is stated here, and nothing on a run.
- "At every job at the place" says nothing on whether any job there is the prover's.
- The test on G_u alone. At the second chain's own test the same road does not go as typed: `planB`
  (PlanB.lean) reads all seven numbers of a place, its code numbers and two flags, and of these the
  library gives less under the head there.
- The full size alone. No example of the head is shown here. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12)
open Johnson.G (codesFull2)
open H2K.Member (piUFull)
open H2K.JointK (laidOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12 (reachTB reachTL declared reachT_U_full PubTiesT OpenTies stN lenFrom)

/-! ## 1 What `reachTB` reads -/

theorem declared_alike {p q : P12} (A : Alike p q) (i : ℕ) : declared p i = declared q i := by
  have e : ∀ r : P12, declared r i = ((((laidOf r).map (·.1))[i]?).map (·.entry.poss)).getD 0 :=
    fun r => by
      unfold declared
      rw [List.getElem?_map, Option.map_map]
      rfl
  rw [e p, e q, A.decls]

theorem reachTB_alike {p q : P12} (A : Alike p q) : reachTB p = reachTB q := by
  have e : declared p = declared q := funext (declared_alike A)
  unfold reachTB reachTL
  rw [A.nums, e]

/-! ## 2 At the written place -/

theorem rounds_UFull : restLen piUFull.nums.stages =
    2 + lenFrom (stN piUFull) (piUFull.nums.stages.drop 2) := by decide +kernel

theorem opens_UFull :
    ((((laidOf piUFull).map (·.1)).drop (firstLen piUFull.nums.stages))[1]?).map (·.opens) =
      some piUFull.nums.first := by decide +kernel

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W X Pb : Type}

/-- **Under the head: the two first trees of the seated place**, both the chain's own. -/
theorem first_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).U.nums.first =
      [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)] := by
  rw [nums_head_U h]
  rfl

/-- **`PubTiesT` under the head, at every job at the place.** -/
theorem pubTiesT_head_U (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (hs : Js.p = (fourOf Np).U)
    (ho : Js.own = false) : PubTiesT J Js codesFull2 2 := by
  have F := facts_head_U h
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, reachTB_alike (alike_head_U h)]
    exact reachT_U_full
  · rw [hJ]
    exact planB_head h
  · rw [hJ]
    exact F.form
  · rw [hJ]
    exact F.count
  · rw [hJ]
    show restLen (fourOf Np).U.nums.stages =
      2 + lenFrom ((fourOf Np).U.nums.stages.getD 1 default) ((fourOf Np).U.nums.stages.drop 2)
    rw [nums_head_U h]
    exact rounds_UFull
  · rw [tablesFitB_eq, hfr, hJ]
    exact F.tab

/-- **`OpenTies` under the head, at the place's own list of first trees.** -/
theorem openTies_head_U (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = (fourOf Np).U) (chain : ℕ)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain (fourOf Np).U.nums.first := by
  refine ⟨?_, hop⟩
  have e : ((((laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some (fourOf Np).U.nums.first := by
    rw [hJ, (alike_head_U h).decls, nums_head_U h]
    exact opens_UFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-! ## 4 What is asked of the simulators' job is not empty by form -/

/-- A made-up simulators' job at the place p that names the place's own first trees. -/
def madeSimsOpen (Pb : Type) (p : P12) (chain : ℕ) : SimJob Pb :=
  ⟨p, false, fun _ _ => noState,
    p.nums.first.map fun x => ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a)⟩

theorem sims_open_there (Pb : Type) (p : P12) (chain : ℕ) :
    ∃ Js : SimJob Pb, Js.p = p ∧ Js.own = false ∧
      Js.opens = p.nums.first.map fun x => ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a) :=
  ⟨madeSimsOpen Pb p chain, rfl, rfl, rfl⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.declared_alike
#print axioms ProofFile.Honest.K12.Light.reachTB_alike
#print axioms ProofFile.Honest.K12.Light.rounds_UFull
#print axioms ProofFile.Honest.K12.Light.opens_UFull
#print axioms ProofFile.Honest.K12.Light.first_head_U
#print axioms ProofFile.Honest.K12.Light.pubTiesT_head_U
#print axioms ProofFile.Honest.K12.Light.openTies_head_U
#print axioms ProofFile.Honest.K12.Light.madeSimsOpen
#print axioms ProofFile.Honest.K12.Light.sims_open_there
