-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9PosHeadPaid.lean: THE TEST `posPlanB`
(Johnson/Desc/First/Link/K9PosAsk.lean: every table of a segment's plan ends inside
the array of the third vector) ACCEPTS AT THE OUTPUT HEAD's SEGMENT, number 24: a theorem in the
goals' scope alone: no entry test, no head, no opening of the maker. The end is the clause at
l = 24 of the sentence `PosAsked Z` (Johnson/Desc/First/Link/Law/K9PosAskLaw.lean), written
out. Definitions (three: second texts, each tied by rfl) and statements with their proofs; one
closed fact by Lean's kernel, looked at with the evaluator first, with its negative tests.

How. In scope the sizes of the head's plan are written numbers: its eight matrices, their number
and the length of its third vector (`plan_in_scope`, Johnson/Desc/Kinds/Law/HeadPlanWritten.lean),
and so are the four numbers of the head's shape that the tables read (`hS_in_scope`,
Johnson/Goal/Meaning/HeadShapeScope.lean). The array has as many columns as the third vector is long
(`public_array`, Johnson/Desc/Kinds/Law/ReadsArray.lean). So the test is a function of eight
values, all written.

  `headTabsN`, `tableInN`, `posHeadB`   `headTabs`, `tableIn` and `posPlanB` at 24, each as a
      function of the values that it reads; `headTabsN_is`, `tableIn_is`, `posPlanB_head`: the ties,
      by rfl
  `posHead_written`   BY LEAN's KERNEL: yes at 4, 16, 1024, 15, the written matrices, 8 and 61680
  `posHead_bites`   it is tight: at 61679 columns: no; and where no table can be laid: no
  `posAsked_head`   **MAIN**

The first tie is named `headTabsN_is` because
Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean declares `headTabs_is` for another sentence.

What is not claimed. Nothing on tiling: the test asks that each table END inside. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.K9PosAsk
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Kinds.Law.ReadsArray
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Road.K4.Names.NamesAtLinks
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (SubPlanH LinkH)
open VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed (public_third)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope)

/-- `headTabs`, of the five values that it reads. -/
def headTabsN (N la T lmb : ℕ) (mats : Array TMat) : Option Head.Tables :=
  ([(0, N, 2 ^ la, "hf@Z"), (0, N, 2 ^ la, "hf@phiZ"),
    (N + 1 + 1 + 1, 1, 2 ^ la, "xbL@Z_V"), (N + 1 + 1 + 1, 1, 2 ^ la, "xbL@Y_N"),
    (N, 1, T, "hd@zt_FC"), (N, 1, T, "hd@r_H"),
    (N + 1, 1, T, "hr@zt_ROW"), (N + 1, 1, T, "hr@P_V"),
    (N + 1, 1, T, "hr@r_tV"), (N + 1, 1, T, "hr@rt_N"),
    (N + 1, 1, T, "hr@phiC"), (N + 1, 1, T, "hr@rhoC"),
    (N + 1 + 1, 1, 2 ^ lmb, "bH-bits-0"), (N + 1 + 1, 1, 2 ^ lmb, "bH-bits-1"),
    (N + 1 + 1, 1, 2 ^ lmb, "bH-pin")] : List (Nat × Nat × Nat × String)).foldlM
    (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) {}

theorem headTabsN_is (h : Head.Shape) (hp : Head.HPlanH2) :
    headTabs h hp = headTabsN h.NHf h.la h.T h.lmbH hp.tl.mats := rfl

/-- `tableIn`, of the two values of the structure that it reads. -/
def tableInN (NM : ℕ) (mats : Array TMat) (cols : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  !decide (t.1 < NM) || (mats.getD t.1 {}).m / t.2.1 == 0 || (mats.getD t.1 {}).k == 0 ||
    decide (t.2.2 + (mats.getD t.1 {}).k * ((mats.getD t.1 {}).m / t.2.1) ≤ cols)

theorem tableIn_is (tl : HTailF2) (cols : ℕ) : tableIn tl cols = tableInN tl.NM tl.mats cols := rfl

/-- `posPlanB` at the head's segment, of the values that it reads. -/
def posHeadB (N la T lmb : ℕ) (matsP : Array TMat) (NM : ℕ) (mats : Array TMat) (cols : ℕ) : Bool :=
  match (headTabsN N la T lmb matsP).map fun t =>
      t.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start) with
  | some ts => !ts.isEmpty && ts.all (tableInN NM mats cols)
  | none => false

theorem posPlanB_head (W : Verify.Public) (X : LinkH) :
    posPlanB W 24 X = posHeadB W.hS.NHf W.hS.la W.hS.T W.hS.lmbH W.H.tl.mats X.tl.NM X.tl.mats
      (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0)) := rfl

set_option maxRecDepth 1000000 in
/-- **The kernel's fact at the written values.** -/
theorem posHead_written : posHeadB 4 16 1024 15 matsW 8 matsW 61680 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It is tight: with one column fewer it rejects; and where no table can be laid. -/
theorem posHead_bites : posHeadB 4 16 1024 15 matsW 8 matsW 61679 = false ∧
    posHeadB 4 16 1024 15 #[] 8 matsW 61680 = false := by
  decide +kernel

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **The clause of PosAsked Z at the head's segment**
(Johnson/Desc/First/Link/Law/K9PosAskLaw.lean), written out. -/
theorem posAsked_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) :
    ∃ X, Z.p.built.links[24]? = some X ∧ posPlanB Z.p.X 24 X = true := by
  obtain ⟨k4, kN, _, _⟩ := _root_.Meaning.scope_plans hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4, kN] at h₀
  obtain ⟨_, _, _, _, p24⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨declared, hd⟩ := OnBytes.Road.K4.Names.built_declared hB
  obtain ⟨_, hat⟩ := OnBytes.L5.LinksOrder.declareLinks_at _ _ _ _ _ hd
  obtain ⟨ar, har⟩ := hat 24 _ p24
  have PW := plan_in_scope hS hR hpub
  obtain ⟨h0, hK, -⟩ := Kinds.Head.Law.ReadsArray.public_array hpub
  have eS := _root_.Meaning.HeadS.hS_in_scope hS hR hpub
  have eN : Z.p.X.hS.NHf = 4 := by rw [eS]; rfl
  have eA : Z.p.X.hS.la = 16 := by rw [eS]; rfl
  have eT : Z.p.X.hS.T = 1024 := by rw [eS]; rfl
  have eB : Z.p.X.hS.lmbH = 15 := by rw [eS]; rfl
  have eU : Z.p.X.H.tl.ix.U.getD 2 none = some 0 := public_third hpub
  have eC : colsB Z.p.X.H.Fp 0 = 61680 := by
    unfold colsB
    rw [Array.getElem?_eq_getElem h0]
    have e : Z.p.X.H.Fp.trees.getD 0 {} = Z.p.X.H.Fp.trees[0] := by simp [Array.getD, h0]
    rw [e, PW.nU] at hK
    exact hK
  refine ⟨_, har, ?_⟩
  rw [posPlanB_head, eN, eA, eT, eB, PW.mats]
  show posHeadB 4 16 1024 15 matsW Z.p.X.H.tl.NM Z.p.X.H.tl.mats
    (colsB Z.p.X.H.Fp ((Z.p.X.H.tl.ix.U.getD 2 none).getD 0)) = true
  rw [PW.nm, PW.mats, eU]
  show posHeadB 4 16 1024 15 matsW 8 matsW (colsB Z.p.X.H.Fp 0) = true
  rw [eC]
  exact posHead_written

end

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.headTabsN_is
#print axioms VerifiableInference.Desc.K9Asks.tableIn_is
#print axioms VerifiableInference.Desc.K9Asks.posPlanB_head
#print axioms VerifiableInference.Desc.K9Asks.posHead_written
#print axioms VerifiableInference.Desc.K9Asks.posHead_bites
#print axioms VerifiableInference.Desc.K9Asks.posAsked_head
