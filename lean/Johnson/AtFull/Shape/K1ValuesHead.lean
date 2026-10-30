-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1ValuesHead.lean: THE KIND K1 IN THE TABLE OF STEPS ON SHAPES: THE HEAD's READS (member 342): the debt
ValuesJ of the file's rule at the family "the run on shapes returns the state's shape". The cell's test is midV at S.covered: the
commitment behind the member's front returns, and at the state behind it the covered positions can be made.

What is owed inside. The commitment's return: from the step on the shape (J and the run's yes) and the rounds' fit. The covered
positions: covered_reach_ground at the state in front (reached from the chain's own start: the thread's Made), carried over the
commitment (request: commitAtS_order; reply: commit_keeps).

Premises. hs₀: the thread begins at the chain's own start. hft: at the first tree 0. hfit: the fits at 342 (fitsAt_of_halved gives them).
hyes: the run on shapes. No premise on the request: a state without a mark has it, by the marks' walk back to the start.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K1ValuesFree
import Johnson.AtFull.Shape.ReadsHeadAtHead
import Johnson.AtFull.Shape.ReqReplyReach
import Johnson.AtFull.Shape.ReqReached
import Johnson.Desc.K1.Law.InOrderAtLater
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks noDigest roundsFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Thread Coins Mid ProverCoinCounts ValuesJ FitsAt shapeJ Shape run_front Thr ThrS roundsOf)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- The step's half of a cell, as vals_at_head has the test's. -/
theorem g_at_head (Z : ProofFile.Pub) (G : ProofFile.Ground) (j : Nat) (hj : j < 16) :
    Tab.g Z G (337 + j) = ((Tab.headRow Z G).at j).1 := by
  unfold Tab.g Tab.cells
  rw [table_head _ _ _ _ j hj]

/-- The chain's start bears no mark only where the request passes. -/
theorem start_passes (Zp : ProofFile.Pub) (p : ProofFile.InstPub) (h0 : (ProofFile.startS Zp p).failed = none) :
    (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  unfold ProofFile.startS at h0
  dsimp only at h0
  by_contra hq
  rw [if_neg hq] at h0
  cases h0

/-- A state without a mark, at the end of a fold from the chain's own start: the start has none. -/
theorem start_clean (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y)
    (hm : y.1.failed = none) : (ProofFile.startS Zp p).failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
    (fun _ _ _ => trivial) (plans_at h) k hf
  exact q.2 hm

/-- **(V2) THE HEAD's READS.** -/
theorem k1_valuesJ_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hs₀ : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = ProofFile.startS Zp p)
    (hfit : FitsAt T 342) {a₀ : Johnson.AtFull.Shape.ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) :
    ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall 342 := by
  intro blk hblk k s m E ds y cols hA hJ hd _ _ hMv
  obtain ⟨Bs', Xl, pd, reads, digits, b, eB, eX, eN, eb, erd, -, -, -⟩ := reads_head_at h
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans eB)
  have hblk' : cF.blocksInOrder[342]? = some blk := by rw [← hbs]; exact hblk
  obtain rfl : blk = b := Option.some.inj (hblk'.symm.trans eb)
  -- the step on the shape returns at s
  obtain ⟨t, ht⟩ := run_front (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀ 358 343 (by omega) hyes
  have hg : Tab.g Zp Bs.G₀ 342 (shA s) = .ok t := by
    have ht' : ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run 342 a₀).bind
        ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).g 342) = .ok t := ht
    have hJ' : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run 342 a₀ = .ok (shA s) := hJ
    rw [hJ'] at ht'
    exact ht'
  have eNum : Tab.nums Bs.G₀ 24 = some (5, pd, reads, digits) := by
    unfold Tab.nums
    rw [eX]
    exact eN
  have eG : Tab.g Zp Bs.G₀ 342 = (Tab.readsHead Zp Bs.G₀).1 := g_at_head Zp Bs.G₀ 5 (by omega)
  have eV : Tab.vals Zp Bs.G₀ 342 = (Tab.readsHead Zp Bs.G₀).2 := vals_at_head Zp Bs.G₀ 5 (by omega)
  -- the fits give two rounds
  have hf1 := (hfit blk hblk k m E ds y cols hd hMv).1
  rw [erd] at hf1
  have hf2 := (VerifiableInference.Desc.roundsFit_noDigest _ _).trans hf1
  obtain ⟨r₁, r₂, e2, -, han⟩ := k1_fit hf2
  have hz := Johnson.Prover.Send.factors_of_fit _ r₁ r₂ (e2 ▸ hf2)
  -- the guard gives the commitment
  rw [eG] at hg
  unfold Tab.readsHead at hg
  rw [eNum] at hg
  have hg2 : readsA (readsHeadGS (Tab.k1P Zp Bs.G₀ 24 5 1) reads
      ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩) (Tab.k1P Zp Bs.G₀ 24 5 1) (shA s) = .ok t := hg
  unfold readsA at hg2
  split at hg2
  · rename_i u hu
    have hu' : readsHeadGS (Tab.k1P Zp Bs.G₀ 24 5 1) reads
        ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ (chainSh s) = some u := hu
    unfold readsHeadGS at hu'
    split at hu'
    · cases hu'
    · rename_i hmk
      obtain ⟨mm, hcm, -⟩ := Option.bind_eq_some_iff.1 hu'
      have hclean : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hmk
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      -- the goal: the cell's test
      show Tab.vals Zp Bs.G₀ 342 s _ _ = true
      rw [eV]
      unfold Tab.readsHead
      rw [eNum]
      show midV (Tab.k1P Zp Bs.G₀ 24 5 1) 24 reads _ s _ _ = true
      rw [e2]
      obtain ⟨mS, hd', -⟩ := commit_returns (gs := (blk.shown T.ft (roundsOf y.1) cols).take
        (VerifiableInference.Desc.K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 reads).openings) hcm hz han
      unfold midV
      rw [hd']
      -- the covered positions at the state in front
      have hA1 := hA.1
      unfold Thr ProofFile.Honest.Thread.Made at hA1
      obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩, -, -⟩ := hA1
      obtain ⟨p, rfl⟩ := hs₀ _ _ _ _ hbeg
      rw [hbs, hft] at hfold
      have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 342 (p, s) :=
        reach_of_fold 342 (by rw [flat_len h]; omega) s _ _ _ _ hfold
      have hq := start_passes Zp p (start_clean h 342 0 p _ _ _ hfold hclean)
      obtain ⟨Bs₂, hB₂, hc⟩ := covered_reach_ground h
      obtain rfl : Bs = Bs₂ := Except.ok.inj (hB.symm.trans hB₂)
      obtain ⟨cov, hcov⟩ := hc hr hq (by omega)
      have e₁ := (VerifiableInference.Desc.K1.commitAtS_order _ _ _ _ s mS _ _ hd').2
      have e₂ := congrArg (·.reply) (commit_keeps hd').2
      show (mS.covered _ _).toOption.isSome = true
      rw [covered_congr e₁ e₂, hcov]
      rfl
  · cases hg2

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.g_at_head
#print axioms Johnson.AtFull.Shape.start_passes
#print axioms Johnson.AtFull.Shape.start_clean
#print axioms Johnson.AtFull.Shape.k1_valuesJ_head
