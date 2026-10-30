-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandStep.lean: one step of a thread at a letter `Said` of the frame's type: from a border to the next,
at a member where the thread's debts are paid. General in the thread and the letter.

Why. `thr_behind` (Johnson/Desc/ProofFile/Honest/Thread/PaysLaw.lean) takes the move and the step as
given. A stand at a run has to produce them, and to keep hold of which state of the prover's run it
speaks: a bare «there is m» says nothing, since `Thr` does not say that m comes from the prover's parts.
So the step is stated at the pair `ThrS T Said`, with `SaidNext` and the S forms as premises. What it keeps hold
of is what the letter says: at `Said := True`, nothing more than `Thr`.

Main names.
  `step_pair`: one step: the pair at `b`, the member's steps, no stop, a list of challenges that fits, and
    `PlaysS`, `SaidNext`, `AcceptedS`, `BehindS`, `ExchangeS`, `RidesPastS`, `MadeNext` at `b`, give the pair at
    `b + 1`, where the run has heard the list, what the member keeps, and what it moved: the rounds that the step
    returned and the tables that it added.

What stays open. Each premise is a debt of the member's. Nothing here says that any thread stands: the
statements are implications, general in the thread.

NOT IN FRONT OF A LAW OVER COINS: `step_pair` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: `hA` stands at a run's coins `k`, and ties the
thread's letters and the letter `Said`, of the first kind. `hN`, `hP`, `hAc`, `hB`, `hX`, `hR` are bound over all
coins and by themselves pick none. None of these is the term that the committer makes. None: the
bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyStandStep
open ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **One step at the pair.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem step_pair {n b : Nat} {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {l : List (Step W X)} (fall : Nat → S → List Fmt.Drawn → Option String)
    (hfit : T.fits n = true) (hb : b < n) (hblk : T.bs[b]? = some blk)
    (hN : SaidNext T Said b) (hP : PlaysS T Said b) (hAc : AcceptedS T Said fall b)
    (hB : BehindS T Said b) (hX : ExchangeS T Said b) (hR : RidesPastS T Said b) (hM : MadeNext T b)
    (hA : ThrS T Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hstop : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hsteps : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l)
    (hfall : fall b s ds = none) :
    ∃ (s' : S) (m' : Mid W X) (E' : Env), ThrS T Said (b + 1) k s' m' E' ∧
      m'.st.heard = m.st.heard ++ ds ∧ T.keeps b s s' ∧
      ∃ (y : List Played × Mid W X) (cols : List OpenedColumn), T.Moved blk k m E ds y cols ∧
        m' = y.2.took cols ∧ E' = E.add y.1 := by
  obtain ⟨y, cols, hMv, hTr⟩ := hP blk hblk k s m E ds l hA hd hstop hsteps
  obtain ⟨s', hS⟩ := hAc blk hblk k s m E ds y cols hA hd hstop hfall hMv
  obtain ⟨hF, hRd, hK⟩ := hB blk hblk k s m E ds y cols s' hA hd hS
  have hT' : Thr T (b + 1) k s' (y.2.took cols) (E.add y.1) :=
    thr_next_at T hfit hb hblk hA.1 hd hS hTr hF hRd
      (hX blk hblk k s m E ds y cols s' hA hd hS)
      (fun i v h1 h2 h3 h4 => hR k s m E s' y.1 i v hA hK h1 h2 h3 h4) hM
  refine ⟨s', y.2.took cols, E.add y.1, ⟨hT',
    hN blk hblk k s m E ds y cols hA.1 hA.2 hd hMv⟩, ?_, hK, y, cols, hMv, rfl, rfl⟩
  obtain ⟨⟨l', -, hy⟩, -⟩ := hMv
  exact play_heard _ _ _ _ _ hy

end AtPublicFiles.KeyStandStep

#print axioms AtPublicFiles.KeyStandStep.step_pair
