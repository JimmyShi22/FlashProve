-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OWordAtW.lean: Omega's words at the own test's member, with the premises of
`omega_word_rows` (K12/AtProof/WordsTiedAtW.lean) paid: the hypothesis hO of `sent_at_W`, at the sending's own job, state
and coins: `jobOmega` at the reader's input, the challenges of the shared chain and the coins that the book lends.

  `point_of_fit`   a list that fits rounds whose first draws the point's length is not empty, and its first challenge has
                 that length
  `omega_word_paid`   the statement
  `omega_word_fit`   the same, the challenges' premises from a fit
  `omega_word_at`   the same at the sending read at challenge n
  `omega_member_plan`   the public premises of `tied_at_fill` at Omega's member

The premises. hP, hSh: the plan and the shapes of the sendings (`plan2_at_head`, `sendShapes_head`). own, hcut, n5: the coins
cut at the sending, and the book's row there (`covers_head`).

Limits. At the words alone. NOT IN FRONT OF A LAW OVER COINS where a stand gives the fit. Nothing on completeness of the
chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsTiedAtW
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TieAtMembers
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open OnBytes (E TableKey)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (P14)
open Desc.K14.Honest
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (omegaWord omega_word_rows)
open ProofFile.Honest.FirstThread (HeadAtReturn IndexReaders)

/-- **A list that fits rounds whose first draws the point's length**: it is not empty and its first challenge has
that length. -/
theorem point_of_fit (dl : List Fmt.DeclaredRound) (n : ℕ) (hf : (dl.head?).map (·.entry.drawE) = some n)
    (l : List Fmt.Drawn) (hd : drawsFit dl l = true) :
    l ≠ [] ∧ (Desc.K14.drawn (firstRv l)).length = n := by
  cases hD : dl with
  | nil =>
    rw [hD] at hf
    cases hf
  | cons d tl =>
    rw [hD] at hd hf
    have hdraw : d.entry.drawE = n := Option.some.inj hf
    cases hh : l with
    | nil =>
      rw [hh] at hd
      simp [drawsFit] at hd
    | cons x t =>
      rw [hh] at hd
      simp only [drawsFit, Bool.and_eq_true] at hd
      have h1 := hd.1
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
      have hlen : x.elems.length = d.entry.drawE := h1.1.1.1.1.1.1.1
      refine ⟨by simp, ?_⟩
      show (Desc.K14.drawn (rvOf x)).length = _
      rw [← elems_one x, ← hdraw, ← hlen]
      show (x.elems.map OnBytes.E.ofTriple ++ []).length = _
      simp

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Omega's words at the sending's rows, at the book's coins.** -/
theorem omega_word_paid (h : HeadAtReturn files A) (reads : ProofFile.Honest.FirstThread.IndexReaders W₀ Rc)
    (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) {layO}
    (hP : Plan2 (K1.qAt A.Z h.places) (sentOf (K1.qAt A.Z h.places).S) layO)
    (hSh : SendShapes (K1.qAt A.Z h.places))
    (own : Cs (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes)
    (hcut : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes.e)
    (hl : heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length ≠ [])
    (hpt : (Desc.K14.drawn (firstRv (heard.drop (declsTo h.description.first.blocksInOrder
        h.description.first.blocksInOrder.length).length))).length = (K1.qAt A.Z h.places).par.S.kCol)
    (pt : OnBytes.Part) (i : ℕ) :
    omegaWord h reads k w heard pt i =
      rdE.val (wordsOf (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q.sent
        ((jobOmega ⟨K1.qAt A.Z h.places, 0⟩).rows
          { input := askR (K1.qAt A.Z h.places) reads.weights reads.rand
              ⟨w.w₀, w.rc, A.H.key w.x⟩
            heard := heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
            own := () } (coinsE own).toArray) 0 pt i) := by
  have nO : (k.look 1 ⟨sendPlace 5, 0⟩).1.e =
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes.e := by
    rw [AtPublicFiles.KeyBook.look_due k 1 ⟨sendPlace 5, 0⟩]
    exact n5
  have hw : (Desc.K14.withOmega (K1.qAt A.Z h.places).S).size = 2 ∧
      (Desc.K14.withOmega (K1.qAt A.Z h.places).S)[0]? =
        some ⟨(K1.qAt A.Z h.places).S.omega, (K1.qAt A.Z h.places).S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega (K1.qAt A.Z h.places).S)[1]? =
        some ⟨(K1.qAt A.Z h.places).S.sharedSplit, (K1.qAt A.Z h.places).S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q.sent = Desc.K14.withOmega (K1.qAt A.Z h.places).S :=
    Desc.K14.Law.parK1_sent (K1.qAt A.Z h.places) 5 _ _
  have hs0O : ((jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q.sent.getD 0 default).shape =
      (K1.qAt A.Z h.places).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q 0
      ⟨(K1.qAt A.Z h.places).par.S.omega, (K1.qAt A.Z h.places).par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hs1O : ((jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q.sent.getD 1 default).shape =
      (K1.qAt A.Z h.places).par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q 1
      ⟨(K1.qAt A.Z h.places).par.S.sharedSplit, (K1.qAt A.Z h.places).par.S.sharedSplitLeafClass⟩
      (by rw [sOs]; exact hw.2.2)).1
  have mO := fun n => msg_eq k (jobOmega ⟨K1.qAt A.Z h.places, 0⟩) (sendPlace 5) n own hcut nO
  have H₀ := omega_word_rows h reads k w heard
    (askR (K1.qAt A.Z h.places) reads.weights reads.rand ⟨w.w₀, w.rc, A.H.key w.x⟩)
    (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)
    (coinsE own).toArray (by rw [sOs, hw.1]) hs0O hs1O hSh.omega (sp_noMain hP)
    (first_read _ _ hl) hpt (fun _ _ => rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 0) = _
      rw [mO 0]
      rfl)
    (by
      show readCoins _ _ (coinsOfMsg k _ _ 1) = _
      rw [mO 1]
      rfl) pt i
  exact H₀

/-- **The same, the challenges' premises from a fit.** dl: rounds that the shared chain's challenges fit, whose first
draws the point's length. -/
theorem omega_word_fit (h : HeadAtReturn files A) (reads : ProofFile.Honest.FirstThread.IndexReaders W₀ Rc)
    (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) {layO}
    (hP : Plan2 (K1.qAt A.Z h.places) (sentOf (K1.qAt A.Z h.places).S) layO)
    (hSh : SendShapes (K1.qAt A.Z h.places))
    (own : Cs (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes)
    (hcut : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes.e)
    (dl : List Fmt.DeclaredRound)
    (hf : (dl.head?).map (·.entry.drawE) = some (K1.qAt A.Z h.places).par.S.kCol)
    (hd : drawsFit dl (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) = true)
    (pt : OnBytes.Part) (i : ℕ) :
    omegaWord h reads k w heard pt i =
      rdE.val (wordsOf (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).Q.sent
        ((jobOmega ⟨K1.qAt A.Z h.places, 0⟩).rows
          { input := askR (K1.qAt A.Z h.places) reads.weights reads.rand
              ⟨w.w₀, w.rc, A.H.key w.x⟩
            heard := heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
            own := () } (coinsE own).toArray) 0 pt i) := by
  obtain ⟨hl, hpt⟩ := point_of_fit dl _ hf _ hd
  exact omega_word_paid h reads k w heard hP hSh own hcut n5 hl hpt pt i

/-- **Omega's words at the sending read at challenge n**: where it hears what the sending at the head hears. -/
theorem omega_word_at (h : HeadAtReturn files A) (reads : ProofFile.Honest.FirstThread.IndexReaders W₀ Rc)
    (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) {layO}
    (hP : Plan2 (K1.qAt A.Z h.places) (sentOf (K1.qAt A.Z h.places).S) layO)
    (hSh : SendShapes (K1.qAt A.Z h.places))
    (own : Cs (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes)
    (hcut : (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt A.Z h.places, 0⟩)).takes.e)
    (hl : heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length ≠ [])
    (hpt : (Desc.K14.drawn (firstRv (heard.drop (declsTo h.description.first.blocksInOrder
        h.description.first.blocksInOrder.length).length))).length = (K1.qAt A.Z h.places).par.S.kCol)
    (n : ℕ) (hd' : List Fmt.Drawn)
    (hh : heardFrom (⟨askR (K1.qAt A.Z h.places) reads.weights reads.rand ⟨w.w₀, w.rc, A.H.key w.x⟩,
        hd', ()⟩ : State Ask Unit) n 1 =
      heardFrom (⟨askR (K1.qAt A.Z h.places) reads.weights reads.rand ⟨w.w₀, w.rc, A.H.key w.x⟩,
        heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length,
        ()⟩ : State Ask Unit) 0 1)
    (pt : OnBytes.Part) (i : ℕ) :
    omegaWord h reads k w heard pt i =
      rdE.val (wordsOf (jobOmega ⟨K1.qAt A.Z h.places, n⟩).Q.sent
        ((jobOmega ⟨K1.qAt A.Z h.places, n⟩).rows
          { input := askR (K1.qAt A.Z h.places) reads.weights reads.rand
              ⟨w.w₀, w.rc, A.H.key w.x⟩
            heard := hd', own := () } (coinsE own).toArray) 0 pt i) := by
  have e : (jobOmega ⟨K1.qAt A.Z h.places, n⟩).rows
        { input := askR (K1.qAt A.Z h.places) reads.weights reads.rand ⟨w.w₀, w.rc, A.H.key w.x⟩
          heard := hd', own := () } (coinsE own).toArray =
      (jobOmega ⟨K1.qAt A.Z h.places, 0⟩).rows
        { input := askR (K1.qAt A.Z h.places) reads.weights reads.rand ⟨w.w₀, w.rc, A.H.key w.x⟩
          heard := heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length
          own := () } (coinsE own).toArray :=
    funext fun j => ProofFile.Honest.K12.AtProof.omega_rows_same _ n _ _ hd' _ j hh
  rw [e]
  exact omega_word_paid h reads k w heard hP hSh own hcut n5 hl hpt pt i

/-- **Omega's member at the plan, at any challenge**: the public premises of `tied_at_fill`. -/
theorem omega_member_plan {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg o Z D r Zp Np cF) {layO}
    (hP : Plan2 (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) layO) (hSh : SendShapes (K1.qAt Zp Np)) (n : ℕ) :
    sendingsFit (K1.qAt Zp Np) = true ∧ 0 < (jobOmega ⟨K1.qAt Zp Np, n⟩).Q.sent.size ∧
      (jobOmega ⟨K1.qAt Zp Np, n⟩).sort 0 = .plain (K1.qAt Zp Np).S.omegaRowsHigh ∧
      shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0 = (K1.qAt Zp Np).par.S.omega ∧
      (0 < (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).mainRows →
        ((jobOmega ⟨K1.qAt Zp Np, n⟩).Q.codes.base.getD
          (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).code default).ell =
        2 ^ ((jobOmega ⟨K1.qAt Zp Np, n⟩).Q.codes.base.getD
          (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).code default).logEll) ∧
      (0 < (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).maskRows →
        ((jobOmega ⟨K1.qAt Zp Np, n⟩).Q.codes.mask.getD
          (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).maskCode default).ell =
        2 ^ ((jobOmega ⟨K1.qAt Zp Np, n⟩).Q.codes.mask.getD
          (shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0).maskCode default).logEll) := by
  have hw : (Desc.K14.withOmega (K1.qAt Zp Np).S).size = 2 ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[0]? =
        some ⟨(K1.qAt Zp Np).S.omega, (K1.qAt Zp Np).S.omegaLeafClass⟩ ∧
      (Desc.K14.withOmega (K1.qAt Zp Np).S)[1]? =
        some ⟨(K1.qAt Zp Np).S.sharedSplit, (K1.qAt Zp Np).S.sharedSplitLeafClass⟩ :=
    Desc.K14.Honest.withOmega_two hP.facts.two
  have sOs : (jobOmega ⟨K1.qAt Zp Np, n⟩).Q.sent = Desc.K14.withOmega (K1.qAt Zp Np).S :=
    Desc.K14.Law.parK1_sent (K1.qAt Zp Np) 5 _ _
  have hs0 : shapeAt (jobOmega ⟨K1.qAt Zp Np, n⟩) 0 = (K1.qAt Zp Np).par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨K1.qAt Zp Np, n⟩).Q 0
      ⟨(K1.qAt Zp Np).par.S.omega, (K1.qAt Zp Np).par.S.omegaLeafClass⟩
      (by rw [sOs]; exact hw.2.1)).1
  have hE := ellOmega_head h
  unfold ellOmegaB at hE
  rw [beq_iff_eq] at hE
  have eQ : (jobOmega ⟨K1.qAt Zp Np, n⟩).Q = (jobOmega ⟨K1.qAt Zp Np, 0⟩).Q := rfl
  refine ⟨sendingsFit_head h, by rw [sOs, hw.1]; decide, rfl, hs0, fun _ => ?_, fun hpos => ?_⟩
  · unfold shapeAt at hE ⊢
    rw [eQ]
    exact hE
  rw [hs0, hSh.omega.noMask] at hpos
  exact absurd hpos (Nat.lt_irrefl 0)

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.point_of_fit
#print axioms ProofFile.Honest.K12.AtFile.omega_word_paid
#print axioms ProofFile.Honest.K12.AtFile.omega_word_fit
#print axioms ProofFile.Honest.K12.AtFile.omega_word_at
#print axioms ProofFile.Honest.K12.AtFile.omega_member_plan
