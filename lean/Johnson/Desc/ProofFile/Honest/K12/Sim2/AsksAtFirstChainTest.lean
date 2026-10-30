-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two clauses at the first chain's last test, from the verifier's record.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/AsksAtFirstChainTest.lean: AsksAtStand (ListAtRun.lean) at a
stand of jobL, where the state that stands in is the record T. A corollary of frontAsksD_at_L
(AtFile/ClosingFront.lean) and dataFront_L (AtFile/ClosingData.lean) by shapeAsksD_of_first and
dataAsks_of_first (AsksFromFront.lean).

  asksAtStand_of_front   the statement

What stays a premise. hr, he: the record is the way in at a state reached at border 354: reach_below
(Thread/SaidOk.lean) gives hr from the thread. h5, hc: the public test at the record's shape and the
test on the open rows. hE, hst, FP, hplan, hfits: public. hheard: FiveAt's clause. hR: the sender's
text returns. hs: THE CLAUSE ON VALUES: the rows that the group takes in say their claims of these
words. It reads the targets. No property of the protocol is claimed.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). This
file's ground. First kind: hr, he, h5, hfits, hheard, hR, hs: at a record and a stand that a run makes: they read k, ρ, rc. Made terms and lemmas that
lift the bar: none: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.AsksFromFront
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingFront
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12 P12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Sh (testSh claimsB)
open H2K.First (Plain Seat1)
open H2K.Member (codesFull)
open OnBytes (TreeLay)
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh

variable {W₀ Rc Tr : Type}

/-- **The two clauses, from the verifier's record.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem asksAtStand_of_front {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Y : Type} (q : P12)
    (door : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hJ : J = jobL q door D readers closing pl)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (T : T12) (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hP₁ : patch m.st.input (restFront J m) T m.st.input (restFront J m) = T)
    {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) (he : enterFinish s = .ok T)
    (hE : J.p.early = true) (h5 : frontFiveB J.p codesFull (testSh T) = true)
    (hc : claimsB T = true) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (FP : FormPub J.p a next rest)
    (hheard : drawsFit (((H2K.JointK.laidOf J.p).take (2 + a.k)).map (·.1))
      (m.st.lately (firstLen J.p.nums.stages)) = true)
    (hos : os.length = 1) (hplan : planB J.p codesFull 1 = true)
    (hfits : ∀ Dp : Plain, FrontAsksD { J with rec₀ := (patch m.st.input (restFront J m) T) }
        m.st.input (restFront J m) codesFull Dp →
      ∃ (s' : Seat1) (u : ℕ) (Ly : TreeLay), FitsAtL J.p pl Dp s' u Ly)
    {R : Johnson.Prover.Send.Rows}
    (hR : carryRows D readers closing pl m.st.input (heardL (restFront J m))
      (carriedCoins J mem).mem = .ok R)
    (hs : ∀ G, T.st.groups[T.g]? = some G →
      AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G)
          (plainL R (J.first m.st.input (restFront J m) (carriedCoins J mem))))) :
    AsksAtStand J patch T codesFull os mem m := by
  subst hJ
  have hT : ({ jobL q door D readers closing pl with
      rec₀ := (patch m.st.input (restFront (jobL q door D readers closing pl) m) T) } :
      TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).rec₀ m.st.input
      (restFront (jobL q door D readers closing pl) m) = T := hP₁
  obtain ⟨Dp, Sf⟩ := frontAsksD_at_L h _ _ _ hr he hT hE h5 hc
  obtain ⟨s', u, Ly, H⟩ := hfits Dp Sf
  have hl : Dp.ts.length = 1 := by
    rw [H.ts]
    rfl
  have hP : planB q codesFull Dp.ts.length = true := by
    rw [hl]
    exact hplan
  obtain ⟨fb, ff⟩ := bat_fold_of_heard { jobL q door D readers closing pl with
      rec₀ := (patch m.st.input (restFront (jobL q door D readers closing pl) m) T) }
    m.st.input (restFront (jobL q door D readers closing pl) m)
    (carriedCoins (jobL q door D readers closing pl) mem)
    (m.st.lately (firstLen q.nums.stages)) a next rest hst FP hheard
  have Dt := dataFront_L q (patch m.st.input (restFront (jobL q door D readers closing pl) m) T)
    D readers closing pl m.st.input (restFront (jobL q door D readers closing pl) m)
    (carriedCoins (jobL q door D readers closing pl) mem) hR H (by
      intro G
      have e : patch m.st.input (restFront (jobL q door D readers closing pl) m) T m.st.input
          (restFront (jobL q door D readers closing pl) m) = T := hP₁
      rw [e]
      exact hs G)
  exact ⟨Dp, _, _, hl.trans hos.symm,
    shapeAsksD_of_first _ _ _ _ _ _ _ hP Sf fb ff,
    dataAsks_of_first _ _ _ _ _ _ _ _ _ hP Sf fb Dt⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.asksAtStand_of_front
