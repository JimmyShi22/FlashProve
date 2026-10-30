-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WordsTiedU.lean: `WordsTied` at the test on G_u at the proof
file's shared thread, at a stand: the form that `saysAt_of_items` asks as hw. Beneath it `tie_U`, `tie_O`
(TieAtMembers.lean); the statement's shape comes from `doorUF`'s shape by closed lines: so no fold.

  `doorAt`       the door's shape at a plan: `Desc.K14.Shape.doorU` behind `endOf`
  `codes_U`, `orc_U0`, `orc_U3`, `members_U`, `draw_first`   closed lines at the typed sizes
  `orc_U1_bent`, `members_U_bent`, `draw_second_bent`   controls
  `orc_of_shape`  a state's message shapes are its shape's
  `point_U`      at a stand something is heard, and the first challenge has the point's length
  `words_tied_U`  the statement

Limits.
- At the thread's own words: `witAll` at the holdings `holds2`. That a thread's witness is that is its
  letter's (`get_witL`).
- NOT IN FRONT OF A LAW OVER COINS: a tie of the words to the lent coins, behind `Thr`.
- The job's rows at the members alone: off the members nothing is asked.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TieAtMembers
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle Group)
open OnBytes.Slice (rdE ofE begun)
open OnBytes.Means (tableSize layoutOf Words)
open VerifiableInference.Desc (Block Place Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open Desc.K14 (P14 St first withU blocks)
open Desc.K14.Honest
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.Sh (TestSh testSh)
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP)

/-- The door's shape at a plan. -/
def doorAt (A : SendPub) : TestSh :=
  Desc.K14.Shape.doorU (ProofFile.Honest.K12.Light.endOf A.P (ProofFile.Honest.K12.Light.sentOf A.P.S))

-- Foretold: yes. Controls: no.
#guard realSized.all fun q => (doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.codes == q.2
#guard realSized.all fun q => ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[0]?).map (·.shape) ==
  some (shapeAt (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 0)
#guard realSized.all fun q => ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[3]?).map (·.shape) ==
  some (shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 1)
#guard realSized.all fun q => ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[1]?).map (·.shape) !=
  some (shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 1)
#guard realSized.all fun q => ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.groups[
        (doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).g]?).map (·.members) == some [0, 3]
#guard realSized.all fun q => ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.groups[
        (doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).g + 1]?).map (·.members) != some [0, 3]
#guard realSized.all fun q => (((sharedR.take 9).flatMap (·.1)).head?).map (·.entry.drawE) ==
  some q.1.shape.kCol
#guard realSized.all fun q => ((((sharedR.take 9).flatMap (·.1)).drop 1).head?).map (·.entry.drawE) !=
  some q.1.shape.kCol

theorem codes_U : (realSized.all fun q =>
    (doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.codes == q.2) = true := by decide +kernel

theorem orc_U0 : (realSized.all fun q =>
    ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[0]?).map (·.shape) ==
      some (shapeAt (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 0)) = true := by decide +kernel

theorem orc_U3 : (realSized.all fun q =>
    ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[3]?).map (·.shape) ==
      some (shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 1)) = true := by decide +kernel

/-- Control: message 1 is not o_sp. -/
theorem orc_U1_bent : (realSized.all fun q =>
    ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.oracles[1]?).map (·.shape) !=
      some (shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 1)) = true := by decide +kernel

theorem members_U : (realSized.all fun q =>
    ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.groups[(doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).g]?).map
      (·.members) == some [0, 3]) = true := by decide +kernel

/-- Control: the next group has other members. -/
theorem members_U_bent : (realSized.all fun q =>
    ((doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).core.st.groups[(doorAt (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)).g + 1]?).map
      (·.members) != some [0, 3]) = true := by decide +kernel

theorem draw_first : (realSized.all fun q =>
    (((sharedR.take 9).flatMap (·.1)).head?).map (·.entry.drawE) == some q.1.shape.kCol) = true := by
  decide +kernel

/-- Control: the second round draws otherwise. -/
theorem draw_second_bent : (realSized.all fun q =>
    ((((sharedR.take 9).flatMap (·.1)).drop 1).head?).map (·.entry.drawE) != some q.1.shape.kCol) =
      true := by decide +kernel

theorem orc_of_shape (t : VerifiableInference.Desc.K12.T12) (N : TestSh) (h : testSh t = N) (i : ℕ) :
    (t.st.oracles[i]?).map (·.shape) = (N.core.st.oracles[i]?).map (·.shape) := by
  subst h
  show _ = ((t.st.oracles.toList.map VerifiableInference.Desc.Ground.Sh.orcSh)[i]?).map (·.shape)
  rw [List.getElem?_map, Array.getElem?_toList, Option.map_map]
  rfl

/-- **Read off a state's shape: the members of the group under test.** -/
theorem members_of_shape (t : VerifiableInference.Desc.K12.T12) (N : TestSh) (h : testSh t = N)
    (l : List ℕ) (hm : (N.core.st.groups[N.g]?).map (·.members) = some l) (G : Group)
    (hG : t.st.groups[t.g]? = some G) : G.members.toList = l := by
  subst h
  have e : ((testSh t).core.st.groups[(testSh t).g]?).map (·.members) = some G.members.toList := by
    show ((t.st.groups.toList.map VerifiableInference.Desc.Ground.Sh.grpSh)[t.g]?).map _ = _
    rw [List.getElem?_map, Array.getElem?_toList, hG]
    rfl
  exact Option.some.inj (e.symm.trans hm)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **At a stand something is heard, and the first challenge has the point's length.** -/
theorem point_U (h : P5J.AtMg o Z D r Zp Np cF) (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (hah : T.ahead = []) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E) (ds : List Fmt.Drawn) :
    m.st.heard ≠ [] ∧ (m.st.heard ++ ds).take (0 + 1) = m.st.heard.take (0 + 1) ∧
      (Desc.K14.drawn (firstRv (m.st.heard ++ ds))).length = (K1.qAt Zp Np).par.S.kCol := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hd : drawsFit (T.ahead ++ declsTo T.bs 9) m.st.heard = true := u.2.1
  rw [hah, List.nil_append, decls_rounds, ← rounds_alike hl] at hd
  have hf := draw_first
  rw [hx₀] at hf
  simp only [Option.all_some, beq_iff_eq] at hf
  have hS : (K1.qAt Zp Np).par.S.kCol = x₀.shape.kCol := by rw [qAt_written Wr Np]; rfl
  rw [hS]
  change drawsFit ((sharedR.take 9).flatMap (·.1)) m.st.heard = true at hd
  cases hD : (sharedR.take 9).flatMap (·.1) with
  | nil =>
    rw [hD] at hf
    cases hf
  | cons d tl =>
    rw [hD] at hd hf
    have hdraw : d.entry.drawE = x₀.shape.kCol := Option.some.inj hf
    cases hh : m.st.heard with
    | nil =>
      rw [hh] at hd
      simp [drawsFit] at hd
    | cons x t =>
      rw [hh] at hd
      simp only [drawsFit, Bool.and_eq_true] at hd
      have h1 := hd.1
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
      have hlen : x.elems.length = d.entry.drawE := h1.1.1.1.1.1.1.1
      refine ⟨by simp, by simp, ?_⟩
      show (Desc.K14.drawn (rvOf x)).length = _
      rw [← elems_one x, ← hdraw, ← hlen]
      show (x.elems.map OnBytes.E.ofTriple ++ []).length = _
      simp

/-- **`WordsTied` at the test on G_u, at a stand.** -/
theorem words_tied_U (h : P5J.AtMg o Z D r Zp Np cF) {x₀ : VerifiableInference.Desc.First.Look.Place}
    (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hB : bookWhole (P5J.F0T o Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (hah : T.ahead = [])
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (n2 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E)
    (ds : List Fmt.Drawn)
    (c : (restPart (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨(fourOf Np).U.place, 1⟩
      (restPart (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest : Part Empty _ _) = .ok c) :
    ∀ G, ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st.groups[
        ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g]? = some G →
      WordsTied ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g G
        (witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (holds2 (K1.qAt Zp Np) wts rnd) rest k
          m.st.input (m.st.heard ++ ds))
        (layoutOf ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st G)
        (plainMany (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd) m.st.input (frontOf m)
          (carriedCoins (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest (stretches _ c.2.2))) := by
  intro G hG oM ho pt i hi
  obtain ⟨hne, ht1, hpt⟩ := point_U h T hl hah u ds
  obtain ⟨x₀', hx₀, Wr⟩ := written_at_head h
  obtain ⟨sentU, layO, hQ'⟩ := ProofFile.Honest.K14.plan2_at_head hA
  have hqp : K1.qAt Zp Np = Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np) := rfl
  have hQ : Plan2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO := by
    have hs : sentU = sentOf (K1.qAt Zp Np).S := by
      have e : withU (K1.qAt Zp Np).S = some sentU := hQ'.facts.goes
      show sentU = (withU (K1.qAt Zp Np).S).getD #[]
      rw [e]
      rfl
    rw [← hs, hqp]
    exact hQ'
  have hSh : SendShapes (K1.qAt Zp Np) := sendShapes_head h
  have hu : withU (K1.qAt Zp Np).S = some (sentOf (K1.qAt Zp Np).S) := hQ.facts.goes
  have hsh : testSh ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)) =
      doorAt ⟨K1.qAt Zp Np, 0⟩ := shape_head_UF h bs hb _ _ _ _
  have hdoor : doorAt ⟨K1.qAt Zp Np, 0⟩ = doorAt (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x₀'.shape) := by
    unfold doorAt
    rw [qAt_written Wr Np]
    rfl
  have hsh' := hsh.trans hdoor
  have hcodes : ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st.codes =
      (K1.qAt Zp Np).codes := by
    have k₁ := codes_U
    rw [hx₀] at k₁
    simp only [Option.all_some, beq_iff_eq] at k₁
    have h1 : (testSh ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m))).core.st.codes =
        ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st.codes := rfl
    rw [← h1, hsh', k₁, qAt_written Wr Np]
  have hmem : G.members.toList = [0, 3] := by
    have k₁ := members_U
    rw [hx₀] at k₁
    simp only [Option.all_some, beq_iff_eq] at k₁
    exact members_of_shape _ _ hsh' _ k₁ G hG
  have hmemA : G.members = #[0, 3] := Array.toList_inj.1 hmem
  obtain ⟨hf0, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two
    (layoutOf ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st G) 0 3 (by decide)
    (show G.members = #[0, 3] from hmemA)
  have hts : ∀ o' pt', tableSize (begun ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st
      ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g G) o' pt' =
      tableSize ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st o' pt' :=
    fun o' pt' => by
      unfold tableSize OnBytes.Statement.tableBits
      rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd := (OnBytes.Slice.begun_codes ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st
    ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g G).trans hcodes
  unfold witAll
  have h2 : (sentOf (K1.qAt Zp Np).S).size = 2 := hQ.facts.goesTwo
  have hoo : oM = 0 ∨ oM = 3 := by
    have h' : oM ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl
  · have hy0 : ((begun ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g G).oracles[0]?).map
          (·.shape) = some (shapeAt (jobU ⟨K1.qAt Zp Np, 0⟩) 0) := by
      have k₁ := orc_U0
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy0
    rw [words2_ours (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) _ _ _ _ 0 (Or.inl (by rw [h2]; decide)) pt i]
    exact tie_U (K1.qAt Zp Np) (fourOf Np).U _ wts rnd (sendingsFit_head h) (ells_head h)
      (AtFullSide.K12.bookCutsU_head h hB) (fits_at_head h).2.1 c2 c5 n2 n5 hQ hSh k m.st.input
      (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf0 y hy hys hcd pt i
      (by rw [hts]; exact hi)
  · have hy3 : ((begun ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ m.st.input (frontOf m)).g G).oracles[3]?).map
          (·.shape) = some (shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 1) := by
      have k₁ := orc_U3
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy3
    have hw2 : (Desc.K14.withOmega (K1.qAt Zp Np).S).size = 2 :=
      (Desc.K14.Honest.withOmega_two hQ.facts.two).1
    rw [words2_ours (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) _ _ _ _ 3
      (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_O (K1.qAt Zp Np) (fourOf Np).U _ wts rnd (sendingsFit_head h) (ells_head h)
      (AtFullSide.K12.bookCutsU_head h hB) (fits_at_head h).2.1 c2 c5 n2 n5 hQ hSh k m.st.input
      (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf3 y hy hys hcd pt i
      (by rw [hts]; exact hi)

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.codes_U
#print axioms ProofFile.Honest.K12.AtFile.orc_U0
#print axioms ProofFile.Honest.K12.AtFile.orc_U3
#print axioms ProofFile.Honest.K12.AtFile.orc_U1_bent
#print axioms ProofFile.Honest.K12.AtFile.members_U
#print axioms ProofFile.Honest.K12.AtFile.members_U_bent
#print axioms ProofFile.Honest.K12.AtFile.draw_first
#print axioms ProofFile.Honest.K12.AtFile.draw_second_bent
#print axioms ProofFile.Honest.K12.AtFile.orc_of_shape
#print axioms ProofFile.Honest.K12.AtFile.members_of_shape
#print axioms ProofFile.Honest.K12.AtFile.point_U
#print axioms ProofFile.Honest.K12.AtFile.words_tied_U
