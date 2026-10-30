-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ObjectsOnKeeps.lean: CONDITIONAL.

What is here. `objects_on` (Law/ObjectsOn.lean: the sentence of the lookup's run of claims
"objects", from the state in front of a step to the state behind it, at the same tables of the
witness) AT K4's OWN CLAUSE OF `keeps` AND THREE TESTS WITH CODE ON THE STATE IN FRONT, at a
segment's own readers. `K4Keeps s s'` (Law/Keeps.lean) gives the step: a feed-forward segment in
front, `Rest`, the later ledger behind and what K4 has heard; and, where the ledger in front has its
sizes, that the arrays which the claims read are as they were and that the slot of the merge's end
value is not below the ledger's next free number in front. `ledgerB` gives the sizes and
`freeAboveB` that nothing is filled from the next free number on (the library's `sized_of_ledgerB`,
`free_of_freeAboveB`, Johnson/Road/K4/Riders/ObjectsAtMeans.lean). `rowsBareB`, the test of the
public name "K4.rowsBare" (Johnson/Desc/First/FillBare.lean), gives at once what the lookup heard
and that its rows name no entry. The readers' two equations are the library's `link_forms` at the
reader in closed form. One statement with its proof: calls. Words: Law/ObjectsOn.lean's head.

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: no example is known to us. THAT THE THREE
TESTS ACCEPT AT A STATE, AND `K4Keeps` AT A STEP: Law/Keeps.lean has the clause wherever the kind's
sub-protocol accepts. fO and oRun (the segment states a run under the name "objects", and it is an
`ObjRun`) and hSt (the stated data's mask row is one at both states) stay hypotheses. Nothing says
that a form is worth 0 anywhere. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach a module under Johnson/Goal/
(Johnson/P5J/MeansQ.lean imports one). No property is claimed.

  `objects_on_keeps`   **the sentence forward, under the clause and the three tests.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ObjectsOn
import Johnson.Desc.ProofFile.Honest.K4.Law.Keeps
import Johnson.Road.K4.Riders.ObjectsAtMeans
import Johnson.Desc.First.FillBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Desc.First.K4 (Rest)
open OnBytes.Desc.First.K4.Riders (ObjRun reader_objects rowsOwn_of_hne)
open OnBytes.Road.K4.Riders (link_forms sized_of_ledgerB free_of_freeAboveB)
open VerifiableInference.Desc (Claim Link K9.readerOf K9.mergeOf K9.Read K9.readersOfLink
  K9.statesOfLink K9.LinkHoles)
open VerifiableInference.Desc.First (S LayOwn ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillBare (rowsBareB)
open VerifiableInference.Desc.Sound (Stated formsTQ MsgQ)

/-- CONDITIONAL: on every hypothesis named. **THE SENTENCE OF "objects" FORWARD OVER A STEP WITH
`K4Keeps`**, where the tests `ledgerB`, `freeAboveB` and `rowsBareB` accept in front. -/
theorem objects_on_keeps {Hh : K9.LinkHoles} {l : Link S Claim} {nO : String}
    {runO : Nat → S → Except String (List Claim × S)} {St : Stated} {own : List (Nat × Nat)}
    {rd : Nat × Nat → MsgQ} {n : Nat} {s s' : S} (K : K4Keeps s s') (hled : ledgerB s = true)
    (hfa : freeAboveB n s = true) (hbare : rowsBareB s = true)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO) (hSt : ∀ D j, (St.at1 s' D).mask j = (St.at1 s D).mask j)
    (h : formsTQ (K9.readersOfLink Hh l) St own 1 "objects" s rd) :
    formsTQ (K9.readersOfLink Hh l) St own 1 "objects" s' rd := by
  obtain ⟨R, a, G, o, ha, hG, ho, L, hk⟩ := K
  have hS : Sized a.F := sized_of_ledgerB ha hled
  obtain ⟨htr, -, hsF, -⟩ := hk hS
  have hfree := free_of_freeAboveB ha hS hfa
  unfold rowsBareB at hbare
  rw [ha] at hbare
  have hb1 : (a.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty) = true := hbare
  cases hlh : a.lookHeard with
  | none =>
    rw [hlh] at hb1
    simp at hb1
  | some g =>
    rw [hlh] at hb1
    have hb2 : (g.rows.toList.all fun f => f.ents.isEmpty) = true := hb1
    have hne : ∀ f ∈ g.rows.toList, f.ents.toList = [] := by
      intro f hf
      have k' : f.ents.isEmpty = true := List.all_eq_true.1 hb2 f hf
      rw [Array.isEmpty_iff] at k'
      rw [k']
    obtain ⟨a', ha', _, _, _, hlh'⟩ := R.here a ha
    have hown' : a'.own = some o := by
      have e : s'.own? = a'.own := by simp only [S.own?, ha']
      rw [← e]
      exact ho
    have hmg : K9.mergeOf s' = some o.wo.sFv := by
      simp only [K9.mergeOf, ha', hown', Option.map_some]
    have rO : K9.readerOf (K9.statesOfLink l) 1 "objects" s =
        some { forms := g.rows.toList, late := [] } := by
      rw [reader_objects fO oRun ha hlh, if_pos (rowsOwn_of_hne a.F hne)]
    have rO' : K9.readerOf (K9.statesOfLink l) 1 "objects" s' =
        some { forms := g.rows.toList, late := [] } := by
      rw [reader_objects fO oRun ha' (hlh'.trans hlh), if_pos (rowsOwn_of_hne a'.F hne)]
    exact objects_on ha R hG L htr fO oRun hlh hne hmg hsF hS hfree (link_forms (by decide) rO)
      (link_forms (by decide) rO') hSt h

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.objects_on_keeps
