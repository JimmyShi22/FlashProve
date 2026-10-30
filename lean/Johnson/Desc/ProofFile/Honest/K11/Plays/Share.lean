-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Share.lean: the proof of `HeadMergeShare`
(Honest/K11/Plays/ShareStatement.lean), to the letter. Lemmas; none of the library's goals.

How. The member is the kind's block at its seat; the frame's steps for it are the row's: so what was
played is what the row plays (`headMergePlays`, Honest/K11/Plays/Proofs.lean), and a view shows of
it the rounds `headMergeSaid` (`roundsOf_said`, Honest/SumLaw/PlaysSum.lean). The seated block's yes
is the kind's block's yes (the library's `IM.alone_underR`, Johnson/IMR/SeatForm.lean, and
`step_under`, Johnson/Desc/Sound/SeatGuardChain.lean); a step's yes holds the decision's, on the
rounds without the sealed digest (`step_ok_iff`, Johnson/Desc/Sound/RunIsDecide.lean). Then
`headMergeItems` (Honest/K11/Plays/Items.lean), `mergedAtMgSeated`
(Johnson/Desc/K11/Exchange/AtSeat.lean) and `woAtMg` (Johnson/Desc/K11/Exchange/AtMg.lean), and the
two premises on what the items mean.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ShareStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Items
import Johnson.Desc.K11.Exchange.AtSeat
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim step_under)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? formsIn)
open VerifiableInference.Desc.Sound (mgAll seatTab step_ok_iff)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind mergeEntries)
open Johnson.Desc.First.ForkMerge.Exchange (mergedAtMgSeated woAtMg)
open ProofFile.Honest.SumLaw (roundsOf_said saidPlayed)

/-- Where the public test holds the open segment's part is there. -/
theorem seg_of_formsIn {Rd : VerifiableInference.Desc.K9.Readers} {own : List (ℕ × ℕ)} {piece : ℕ}
    {run : String} {s : S} (h : formsIn Rd own piece run s = true) : ∃ a, segAt? s = some a := by
  unfold formsIn at h
  cases ha : segAt? s with
  | none => simp [ha] at h
  | some a => exact ⟨a, rfl⟩

/-- **The merge's share of the thread's debt, at its two items.** -/
theorem headMergeShare : HeadMergeShare := by
  intro Bk W₀ Rc Xi Tr X Pb Pp Tok Xi' rows cols nR Xp T b P claims weights name pl coins i₁ i₂ toP
    toW Dof Mg₀ seg l H
  have core : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cs s', Thr T b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cs s' → ∀ ds',
      (mgAll (Dof y.2.st.input) Mg₀).forms seg 9 "merged" (toP (T.seat k y.2 s').1, s')
          (T.strs (E.add y.1)) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) ∧
        (mgAll (Dof y.2.st.input) Mg₀).wo seg (toP (T.seat k y.2 s').1, s')
          (T.strs (E.add y.1)) (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) := by
    intro blk hblk k s m E ds y cs s' hT hd hS ds'
    have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
      rw [H.member] at hblk
      exact (Option.some.inj hblk).symm
    subst eb
    have hS0 := hS
    obtain ⟨⟨⟨st, hst, hplay⟩, _⟩, hstep⟩ := hS0
    obtain ⟨v, q, rfl⟩ := H.steps k m.st.input st hst
    cases ds with
    | nil => cases hd
    | cons d₀ ds₁ =>
      have hp := headMergePlays W₀ Rc Xi Tr X S Claim
        (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) P claims weights v q (coins k) d₀ ds₁ []
        m rfl rfl hd
      rw [hp] at hplay
      have ey := Except.ok.inj hplay
      subst ey
      have hro : ∀ (nm : String) (p : VerifiableInference.Desc.Place),
          roundsOf ((⟨nm, p, 0, true, [], [], d₀⟩ : Played) ::
            (headMergeSaid P claims weights (coins k) m d₀ ds₁).tail.map
              (saidPlayed nm ⟨p, 1⟩)) = headMergeSaid P claims weights (coins k) m d₀ ds₁ := by
        intro nm p
        show (⟨[], d₀⟩ : Fmt.RoundView) :: roundsOf _ = _
        rw [roundsOf_said]
        rfl
      have h1 := step_under (IM.alone_underR (same := ProofFile.sameReply) (b' := headClaimMergeKind P)
        (name := name) (a := pl) rfl) hstep
      have h2 := ((step_ok_iff T.ft (headClaimMergeKind P) s s' _ cs cs.length).1 h1).2.2.2
      rw [hro] at h2
      obtain ⟨a, claim, x0, b9, f1, f2, f3, f4, f5, f6, f7, f8⟩ := H.front k s m E hT
      have hpub := H.pubTest _ k s m E _ _ cs s' hT hS H.member
      obtain ⟨a9, h9⟩ := seg_of_formsIn hpub
      have hv : T.valid m.st.input := hT.2.2.2.2.2.2
      obtain ⟨cells, idx, t1, t2, t3, t4, t5, t6, t7⟩ :=
        H.ties _ k s m E _ _ cs s' a claim x0 b9 a9 hT hS H.member f1 f2 f3 f4 h9 ds'
      have hI := headMergeItems W₀ Rc Xi Tr X P claims weights (coins k) d₀ ds₁ m s s' a claim x0
        ((Dof m.st.input).N.group seg) _ b9 a9 cells idx ((Dof m.st.input).d1.ncl seg)
        (Dof m.st.input).d1.lin nR (Dof m.st.input).P13.lin.kCol _ hd h2 f1 f2 f3 f5 f6 f7 f8 t1 h9
        t2 t3 f4 t4 hpub (H.colBits _ hv) (H.rowsFit _ hv) t5 t6 t7
      refine ⟨mergedAtMgSeated Xi' Pp Tok rows cols nR Xp (Dof m.st.input) Mg₀ seg l P name pl _ s'
        _ _ (H.head _ hv) (H.link _ hv) H.hears hI.1, ?_⟩
      refine woAtMg Xi' Pp Tok rows cols nR Xp (Dof m.st.input) Mg₀ seg _ s' _ _ ?_
      rw [H.lay _ hv]
      exact hI.2
  refine ⟨?_, ?_⟩
  · intro blk hblk k s m E ds y cs s' hT hd hS ds' i hi
    rw [List.mem_singleton.1 hi]
    exact H.merged _ _ _ _ (core blk hblk k s m E ds y cs s' hT hd hS ds').1
  · intro blk hblk k s m E ds y cs s' hT hd hS ds' i hi
    rw [List.mem_singleton.1 hi]
    exact H.wo _ _ _ _ (core blk hblk k s m E ds y cs s' hT hd hS ds').2

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.seg_of_formsIn
#print axioms ProofFile.Honest.K11.headMergeShare
