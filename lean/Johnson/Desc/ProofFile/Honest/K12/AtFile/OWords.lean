-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OWords.lean: `WordsTied` at the test on G_omega at the proof file's
shared thread, at a stand: the form that `saysAt_of_items` asks as hw. Beneath it `tie_omega`, `tie_sp` (OTie.lean);
the statement's shape comes from `doorOmegaF`'s shape by closed lines: so no fold.

  `codes_real_O`, `orc_O2`, `orc_O3`, `draw_ten`, `ell_real_O`   closed lines at the typed sizes
  `orc_O2_bent`, `orc_O3_bent`   controls: the other member's shape
  `ellOmega_head`, `members_head_O`   under the head: the code's length; the members 2 and 3
  `kinds_of_shape`   read off a state's shape: the rows and the members of the group under test
  `point_O`      at a stand something is heard, and the first challenge has the point's length
  `words_tied_O` the statement

Limits.
- At the thread's own words: `witAll` at the holdings `holds2`. That a thread's witness is that is its letter's
  (`get_witL`).
- NOT IN FRONT OF A LAW OVER COINS: a tie of the words to the lent coins, behind `Thr`.
- The job's rows at the members alone: off the members nothing is asked.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OTie
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WordsTiedU
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OAccepted

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
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (P14 St first withU blocks)
open Desc.K14.Honest
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.Sh (TestSh testSh)
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP)

-- Foretold: yes. Controls: no.
#guard realSized.all fun q => (omegaShape q).core.st.codes == q.2
#guard realSized.all fun q => ((omegaShape q).core.st.oracles[2]?).map (·.shape) ==
  some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 0)
#guard realSized.all fun q => ((omegaShape q).core.st.oracles[3]?).map (·.shape) ==
  some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 1)
#guard realSized.all fun q => ((omegaShape q).core.st.oracles[2]?).map (·.shape) !=
  some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 1)
#guard realSized.all fun q => ((omegaShape q).core.st.oracles[3]?).map (·.shape) !=
  some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 0)
#guard realSized.all fun q => (((sharedR.take 10).flatMap (·.1)).head?).map (·.entry.drawE) ==
  some q.1.shape.kCol
#guard realSized.all fun q => ellOmegaB (Light.planOf q.2 q.1.shape)

theorem codes_real_O : (realSized.all fun q => (omegaShape q).core.st.codes == q.2) = true := by
  decide +kernel

theorem orc_O2 : (realSized.all fun q => ((omegaShape q).core.st.oracles[2]?).map (·.shape) ==
    some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 0)) = true := by decide +kernel

theorem orc_O3 : (realSized.all fun q => ((omegaShape q).core.st.oracles[3]?).map (·.shape) ==
    some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 1)) = true := by decide +kernel

/-- Control: message 2 is not o_sp. -/
theorem orc_O2_bent : (realSized.all fun q => ((omegaShape q).core.st.oracles[2]?).map (·.shape) !=
    some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 1)) = true := by decide +kernel

/-- Control: message 3 is not o_omega. -/
theorem orc_O3_bent : (realSized.all fun q => ((omegaShape q).core.st.oracles[3]?).map (·.shape) !=
    some (shapeAt (jobOmega (Light.planOf q.2 q.1.shape)) 0)) = true := by decide +kernel

theorem draw_ten : (realSized.all fun q =>
    (((sharedR.take 10).flatMap (·.1)).head?).map (·.entry.drawE) == some q.1.shape.kCol) = true := by
  decide +kernel

theorem ell_real_O : (realSized.all fun q => ellOmegaB (Light.planOf q.2 q.1.shape)) = true := by
  decide +kernel

/-- **Read off a state's shape: the rows and the members of the group under test.** -/
theorem kinds_of_shape (t : VerifiableInference.Desc.K12.T12) (N : TestSh) (h : testSh t = N)
    (l : Nat × List Nat) (hm : (N.core.st.groups[N.g]?).map rowsMembers = some l) (G : Group)
    (hG : t.st.groups[t.g]? = some G) : (G.rows.toList.length, G.members.toList) = l := by
  subst h
  have e : ((testSh t).core.st.groups[(testSh t).g]?).map rowsMembers =
      some (G.rows.toList.length, G.members.toList) := by
    show ((t.st.groups.toList.map VerifiableInference.Desc.Ground.Sh.grpSh)[t.g]?).map _ = _
    rw [List.getElem?_map, Array.getElem?_toList, hG]
    simp only [Option.map_some, rowsMembers, VerifiableInference.Desc.Ground.Sh.grpSh, List.length_map]
  exact Option.some.inj (e.symm.trans hm)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}

theorem ellOmega_head (h : P5J.AtMg o Z D r Zp Np cF) : ellOmegaB ⟨K1.qAt Zp Np, 0⟩ = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := ell_real_O
  rw [hx] at k
  have k' : ellOmegaB (Light.planOf Johnson.G.codesFull2 x.shape) = true := k
  have e : ellOmegaB ⟨K1.qAt Zp Np, 0⟩ =
      ellOmegaB (Light.planOf (K1.qAt Zp Np).codes (K1.qAt Zp Np).S) := rfl
  rw [e, qAt_written Wr Np]
  exact k'

/-- **The group under test has one open row, and the members 2 and 3**, at a state of the door's shape. -/
theorem group_at_stand (h : P5J.AtMg o Z D r Zp Np cF) (t : VerifiableInference.Desc.K12.T12)
    (ht : testSh t = headShape Zp Np) (G : Group) (hG : t.st.groups[t.g]? = some G) :
    G.rows.toList.length = 1 ∧ G.members.toList = [2, 3] := by
  have e := kinds_of_shape t _ ht _ (group_head_O h) G hG
  exact ⟨congrArg (·.1) e, congrArg (·.2) e⟩

/-- **At a stand something is heard, and the first challenge has the point's length.** -/
theorem point_O (h : P5J.AtMg o Z D r Zp Np cF) (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (hah : T.ahead = []) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E) (ds : List Fmt.Drawn) :
    m.st.heard ≠ [] ∧ (m.st.heard ++ ds).take (0 + 1) = m.st.heard.take (0 + 1) ∧
      (Desc.K14.drawn (firstRv (m.st.heard ++ ds))).length = (K1.qAt Zp Np).par.S.kCol := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hd : drawsFit (T.ahead ++ declsTo T.bs 10) m.st.heard = true := u.2.1
  rw [hah, List.nil_append, decls_rounds, ← rounds_alike hl] at hd
  have hf := draw_ten
  rw [hx₀] at hf
  simp only [Option.all_some, beq_iff_eq] at hf
  have hS : (K1.qAt Zp Np).par.S.kCol = x₀.shape.kCol := by rw [qAt_written Wr Np]; rfl
  rw [hS]
  change drawsFit ((sharedR.take 10).flatMap (·.1)) m.st.heard = true at hd
  cases hD : (sharedR.take 10).flatMap (·.1) with
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

set_option maxHeartbeats 1000000 in
/-- **`WordsTied` at the test on G_omega, at a stand.** -/
theorem words_tied_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    {x₀ : VerifiableInference.Desc.First.Look.Place} (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hB : bookWhole (P5J.F0T o Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (hah : T.ahead = [])
    (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E)
    (ds : List Fmt.Drawn)
    (c : (restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨pO.place, 1⟩
      (restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part Empty _ _) = .ok c) :
    ∀ G, ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st.groups[
        ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g]? = some G →
      WordsTied ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g G
        (witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (holds2 (K1.qAt Zp Np) wts rnd) rest k
          m.st.input (m.st.heard ++ ds))
        (layoutOf ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st G)
        (plainMany (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd) m.st.input (frontOf m)
          (carriedCoins (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest (stretches _ c.2.2))) := by
  intro G hG oM ho pt i hi
  obtain ⟨hne, ht1, hpt⟩ := point_O h T hl hah u ds
  obtain ⟨x₀', hx₀, Wr⟩ := written_at_head h
  obtain ⟨x', hx', eS, -, -⟩ := omegaShape_head h
  obtain rfl : x₀' = x' := congrArg Prod.fst (Option.some.inj (hx₀.symm.trans hx'))
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
  have hsh : testSh ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)) =
      headShape Zp Np := by
    rw [rec_door]
    exact shape_head_OmegaF h bs hb _ _ _ _
  have hsh' := hsh.trans eS
  have hcodes : ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st.codes =
      (K1.qAt Zp Np).codes := by
    have k₁ := codes_real_O
    rw [hx₀] at k₁
    simp only [Option.all_some, beq_iff_eq] at k₁
    have h1 : (testSh ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m))).core.st.codes =
        ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st.codes := rfl
    rw [← h1, hsh', k₁, qAt_written Wr Np]
  have hmem : G.members.toList = [2, 3] := (group_at_stand h _ hsh G hG).2
  have hmemA : G.members = #[2, 3] := Array.toList_inj.1 hmem
  obtain ⟨hf2, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two
    (layoutOf ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st G) 2 3 (by decide)
    (show G.members = #[2, 3] from hmemA)
  have hts : ∀ o' pt', tableSize (begun ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st
      ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g G) o' pt' =
      tableSize ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st o' pt' :=
    fun o' pt' => by
      unfold tableSize OnBytes.Statement.tableBits
      rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd := (OnBytes.Slice.begun_codes ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st
    ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g G).trans hcodes
  have hcuts := bookCutsOmega_head h hO hB
  have hw2 : (Desc.K14.withOmega (K1.qAt Zp Np).S).size = 2 :=
    (Desc.K14.Honest.withOmega_two hQ.facts.two).1
  unfold witAll
  have hoo : oM = 2 ∨ oM = 3 := by
    have h' : oM ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl
  · have hy2 : ((begun ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g G).oracles[2]?).map
          (·.shape) = some (shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 0) := by
      have k₁ := orc_O2
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy2
    rw [words2_ours (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) _ _ _ _ 2
      (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_omega (K1.qAt Zp Np) pO _ wts rnd (sendingsFit_head h) (ellOmega_head h) hcuts c5 n5 hQ
      hSh k m.st.input (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf2 y hy
      hys hcd pt i (by rw [hts]; exact hi)
  · have hy3 : ((begun ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st
        ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g G).oracles[3]?).map
          (·.shape) = some (shapeAt (jobOmega ⟨K1.qAt Zp Np, 0⟩) 1) := by
      have k₁ := orc_O3
      rw [hx₀] at k₁
      simp only [Option.all_some, beq_iff_eq] at k₁
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh', k₁, qAt_written Wr Np]
      rfl
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy3
    rw [words2_ours (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) _ _ _ _ 3
      (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_sp (K1.qAt Zp Np) pO _ wts rnd (sendingsFit_head h) (ells_head h) hcuts c5 n5 hQ hSh k
      m.st.input (frontOf m) (m.st.heard ++ ds) (by simp [hne]) ht1.symm c hlp hpt _ _ hf3 y hy hys hcd
      pt i (by rw [hts]; exact hi)

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.codes_real_O
#print axioms ProofFile.Honest.K12.AtFile.orc_O2
#print axioms ProofFile.Honest.K12.AtFile.orc_O3
#print axioms ProofFile.Honest.K12.AtFile.orc_O2_bent
#print axioms ProofFile.Honest.K12.AtFile.orc_O3_bent
#print axioms ProofFile.Honest.K12.AtFile.draw_ten
#print axioms ProofFile.Honest.K12.AtFile.ell_real_O
#print axioms ProofFile.Honest.K12.AtFile.kinds_of_shape
#print axioms ProofFile.Honest.K12.AtFile.ellOmega_head
#print axioms ProofFile.Honest.K12.AtFile.group_at_stand
#print axioms ProofFile.Honest.K12.AtFile.point_O
#print axioms ProofFile.Honest.K12.AtFile.words_tied_O
