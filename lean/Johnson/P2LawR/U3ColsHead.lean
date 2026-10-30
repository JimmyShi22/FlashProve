-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/U3ColsHead.lean: THE KIND K8 (the smallness test's draw), "OWN SIZES", AT THE OUTPUT
HEAD's SEGMENT (k = 24): in the goals' scope, where the public part returns: the request's layout
has an array (24, "U3"); it has a row; and THE FIRST ENTRY BEHIND THE LAST TABLE of K8.tabs at the
segment's own numbers is at most its number of columns. No pin. A JOIN OF OTHER FILES' THEOREMS AND
ONE SMALL EVALUATION BY LEAN's KERNEL.
"THE TABLES' END" STANDS HERE AS THE SECOND COMPONENT OF K8.tabs' OWN FOLD
(Johnson/Desc/First/K8/Hear.lean), WRITTEN OUT: no name is given to it here; by its text
P5J.K8N.tabsEnd (Johnson/P5J/K8ThreeBoxes.lean) is this term: no theorem of this file says so.
THE STONES. reads_named_of_built (Johnson/Desc/Kinds/Law/ReadsRoomOfBuilt.lean: behind an
accept of buildLinksH the layout has the last segment's "U3", with the rows and columns of the
plan's array) · public_third · public_array (that array is number 0: one row, nU[2] columns) ·
plan_in_scope (Johnson/Desc/Kinds/Law/HeadPlanWritten.lean: in scope nU = #[0, 0, 61680] and the
eight matrices are a written list) · from Johnson/IMR/: ground_tails · ground_named ·
ground_publicK · planned_built · plain_built (the ground's segment 24 has the head's plan's tl, and
kind 2) · from OnBytes/Tie/Pv/Keeps/LinksOrder.lean: listLinksH_with.
  end_congr   the tables' end reads ks, ms and asks alone of a place's numbers.
  parW · **end_written**   at the written numbers it is 61680. By the kernel.
  end_control   A NEGATIVE TEST: with one family more it is not at most 61680.
  asks_in_scope   in scope the head's families of tables are the written list.
  **u3_cols_head**   see its statement.
Limits. AT OnBytes.secondHashFunction ALONE. That the public part returns at any files in scope, and that there
is a ground, are premises. THE INEQUALITY IS MET WITH NOTHING TO SPARE: both sides are 61680. The
head's segment alone. The full size alone. Raised limits: maxRecDepth 100000 at the two closed
facts. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.Kinds.Law.ReadsRoomInScope
import Johnson.IMR.K8Seat
import Johnson.Desc.ProofFile.Lot.K8

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K8U
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW)

local notation "K8Par" => VerifiableInference.Desc.First.K8.Par
local notation "layF" => VerifiableInference.Desc.First.K8.layFamily

/-- The tables' end reads ks, ms and asks alone. -/
theorem end_congr {p q : K8Par} (h1 : p.ks = q.ks) (h2 : p.ms = q.ms) (h3 : p.asks = q.asks) :
    (p.asks.foldl (fun x a => let y := layF p a x.2; (x.1 ++ y.1, y.2)) ([], 0)).2 =
      (q.asks.foldl (fun x a => let y := layF q a x.2; (x.1 ++ y.1, y.2)) ([], 0)).2 := by
  have e : layF p = layF q := by
    funext a e
    unfold VerifiableInference.Desc.First.K8.layFamily
    rw [h1, h2]
  rw [h3, e]

/-- The head's families of tables, as written. -/
def asksW : List (ℕ × ℕ × ℕ) :=
  List.replicate 2 (0, 4, 2 ^ 16) ++ List.replicate 2 (4 + 3, 1, 2 ^ 16) ++
    List.replicate 2 (4, 1, 1024) ++ List.replicate 6 (4 + 1, 1, 1024) ++
    List.replicate 3 (4 + 2, 1, 2 ^ 15)

/-- The head's place's numbers, as written; more: families laid behind. -/
def parW (more : List (ℕ × ℕ × ℕ)) : K8Par :=
  { link := 24, piece := 6, ks := matsW.toList.map (·.k), ms := matsW.toList.map (·.m), tau := 128,
    asks := asksW ++ more, matsIn := [], readsIn := [] }

set_option maxRecDepth 100000 in
/-- **At the written numbers the tables' end is 61680.** -/
theorem end_written :
    ((parW []).asks.foldl (fun x a => let y := layF (parW []) a x.2; (x.1 ++ y.1, y.2))
      ([], 0)).2 = 61680 := by decide +kernel

set_option maxRecDepth 100000 in
/-- A NEGATIVE TEST: with one family more (hr's, once more) it is beyond 61680. -/
theorem end_control :
    decide (((parW [(5, 1, 1024)]).asks.foldl
      (fun x a => let y := layF (parW [(5, 1, 1024)]) a x.2; (x.1 ++ y.1, y.2))
      ([], 0)).2 ≤ 61680) = false := by decide +kernel

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}

/-- In scope the head's families of tables are the written list. -/
theorem asks_in_scope {X : Verify.Public} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (h : Verify.publicOf P.pol P.KL (some lay) = .ok X) :
    VerifiableInference.Desc.First.K8.Asks.head X.hS = asksW := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  have hP := OnBytes.Road.Hd.scan_of_scope hS hR h
  have e : X.hS = OnBytes.Model.Verify.headShape
      (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp)) X.layers.y := by
    rw [St.hS, hP]
  have hF : OnBytes.Road.Hd.FullH X.hS := by
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have Nm := OnBytes.Road.Hd.numH_of_layout hF St.head
  have slm : X.hS.lmbH = 15 := by rw [e]; rfl
  unfold VerifiableInference.Desc.First.K8.Asks.head asksW
  dsimp only
  rw [hF.NHf, hF.la, Nm.T, slm]

/-- **K8's "OWN SIZES" AT THE HEAD's SEGMENT: THE VECTOR OF READS HAS ROOM FOR ALL TABLES.** -/
theorem u3_cols_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {Xl : LinkH}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (e3 : G.built[24]? = some Xl) :
    ∃ A, reqArray Z.first.layout 24 "U3" = some A ∧ 1 ≤ A.sizeI ∧
      ((ProofFile.k8Par Z G Xl 24).asks.foldl
        (fun x a => let y := layF (ProofFile.k8Par Z G Xl 24) a x.2; (x.1 ++ y.1, y.2))
        ([], 0)).2 ≤ A.sizeC := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← eW]
    exact IM.ground_publicK hZ hG
  have PW := VerifiableInference.Desc.Kinds.Head.Law.InScope.plan_in_scope hS hR hX
  obtain ⟨k4, kN, -, -⟩ := Meaning.scope_plans hS hR hX
  -- the layout's array
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts P.pol lay P.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨_, _, z, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  rw [kN] at z e
  have T : Z.p.X.H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third hX
  obtain ⟨-, tr, A, c2, c3, c4, c5⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Built.reads_named_of_built hB z e (t := 0) T
  obtain ⟨-, pK, pR, -⟩ := VerifiableInference.Desc.Kinds.Head.Law.ReadsArray.public_array hX
  have c2' : Z.p.X.H.Fp.trees[0]? = some tr := c2
  have etr : Z.p.X.H.Fp.trees.getD 0 {} = tr := by
    rw [Array.getD_eq_getD_getElem?, c2']
    rfl
  rw [etr] at pK pR
  have hC : A.sizeC = 61680 := by
    rw [c5, pK, PW.nU]
    rfl
  -- the segment's own numbers
  obtain ⟨-, l, f, t1, -⟩ := IM.ground_tails hS hR hZ hG
  obtain rfl : l = Xl := Option.some.inj (f.symm.trans e3)
  obtain ⟨-, l', f', k2, -⟩ := IM.ground_named hS hR hZ hG
  obtain rfl : l' = l := Option.some.inj (f'.symm.trans e3)
  have hm : l'.tl.mats = matsW := by rw [t1, eW]; exact PW.mats
  have a1 : (ProofFile.k8Par Z G l' 24).ks = (parW []).ks := by
    show l'.tl.mats.toList.map (·.k) = matsW.toList.map (·.k)
    rw [hm]
  have a2 : (ProofFile.k8Par Z G l' 24).ms = (parW []).ms := by
    show l'.tl.mats.toList.map (·.m) = matsW.toList.map (·.m)
    rw [hm]
  have a3 : (ProofFile.k8Par Z G l' 24).asks = (parW []).asks := by
    show ProofFile.k8Asks G l' = asksW ++ []
    unfold ProofFile.k8Asks
    rw [k2, List.append_nil, eW]
    exact asks_in_scope hS hR hX
  refine ⟨A, c3, ?_, ?_⟩
  · rw [c4, pR]
  · rw [end_congr a1 a2 a3, end_written, hC]

end P2Law.K8U

#print axioms P2Law.K8U.end_congr
#print axioms P2Law.K8U.end_written
#print axioms P2Law.K8U.end_control
#print axioms P2Law.K8U.asks_in_scope
#print axioms P2Law.K8U.u3_cols_head
