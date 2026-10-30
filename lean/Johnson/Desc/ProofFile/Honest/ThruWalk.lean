-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruWalk.lean: NOT IN FRONT OF A LAW OVER COINS. A thread walked over
several members: from a stand at a border, where each member in the stretch pays the five sentences
and its two letters, the thread stands at the border behind the stretch, and the run has heard the
lists of the stretch in order. General in the thread and the letter.

  MemberPaid           what a member pays at the pair
  step_of_paid         one step
  walk_of_paid         a stretch of members

By what. step_of_paid is step_pair (E2E/KeyStandStep.lean, in the key file's walked pack) with its
premises gathered; thr_next_at (Honest/Thread/PaysS.lean), play_heard (Honest/Thread/PaysLaw.lean).

Limits. Each premise is a debt of the member's. A walk of the thread's steps, not a run of the frame.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **What a member pays at the pair**: the five sentences, at no fall, and its two letters. -/
structure MemberPaid (b : Nat) : Prop where
  next : SaidNext T Said b
  plays : PlaysS T Said b
  accepted : AcceptedS T Said (fun _ _ _ => none) b
  behind : BehindS T Said b
  exchange : ExchangeS T Said b
  rides : RidesPastS T Said b
  made : MadeNext T b

/-- What a member's round asks at a list of challenges, at every state of the prover: it fits, no
part stops and the steps return. -/
structure MemberRuns (k : Coins Bk) (b : Nat) (ds : List Fmt.Drawn) : Prop where
  there : ∃ blk, T.bs[b]? = some blk ∧ drawsFit blk.rounds ds = true ∧
    ∀ m : Mid W X, chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none ∧
      ∃ l, chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
        .ok l

/-- **One step at the pair.** -/
theorem step_of_paid {n b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} (hfit : T.fits n = true) (hb : b < n) (P : MemberPaid T Said b)
    (R : MemberRuns T k b ds) (hA : ThrS T Said b k s m E) :
    ∃ (s' : S) (m' : Mid W X) (E' : Env), ThrS T Said (b + 1) k s' m' E' ∧
      m'.st.heard = m.st.heard ++ ds ∧ T.keeps b s s' ∧
      ∃ blk, ∃ (y : List Played × Mid W X) (cols : List OpenedColumn), T.bs[b]? = some blk ∧
        T.Moved blk k m E ds y cols ∧ m' = y.2.took cols ∧ E' = E.add y.1 := by
  obtain ⟨blk, hblk, hd, hr⟩ := R.there
  obtain ⟨hstop, l, hsteps⟩ := hr m
  obtain ⟨y, cols, hMv, hTr⟩ := P.plays blk hblk k s m E ds l hA hd hstop hsteps
  obtain ⟨s', hS⟩ := P.accepted blk hblk k s m E ds y cols hA hd hstop rfl hMv
  obtain ⟨hF, hRd, hK⟩ := P.behind blk hblk k s m E ds y cols s' hA hd hS
  have hT' : Thr T (b + 1) k s' (y.2.took cols) (E.add y.1) :=
    thr_next_at T hfit hb hblk hA.1 hd hS hTr hF hRd
      (P.exchange blk hblk k s m E ds y cols s' hA hd hS)
      (fun i v h1 h2 h3 h4 => P.rides k s m E s' y.1 i v hA hK h1 h2 h3 h4) P.made
  refine ⟨s', y.2.took cols, E.add y.1, ⟨hT',
    P.next blk hblk k s m E ds y cols hA.1 hA.2 hd hMv⟩, ?_, hK, blk, y, cols, hblk, hMv, rfl, rfl⟩
  obtain ⟨⟨l', -, hy⟩, -⟩ := hMv
  exact play_heard _ _ _ _ _ hy

/-- **A stretch of members.** From a stand at b, over the c members behind it. -/
theorem walk_of_paid {n : Nat} (hfit : T.fits n = true) (b : Nat) (k : Coins Bk)
    (ds : Nat → List Fmt.Drawn) {s : S} {m : Mid W X} {E : Env} (hA : ThrS T Said b k s m E) :
    ∀ c, b + c ≤ n → (∀ j, j < c → MemberPaid T Said (b + j)) →
      (∀ j, j < c → MemberRuns T k (b + j) (ds (b + j))) →
      ∃ (s' : S) (m' : Mid W X) (E' : Env), ThrS T Said (b + c) k s' m' E' ∧
        m'.st.heard = m.st.heard ++ (List.range c).flatMap fun j => ds (b + j)
  | 0, _, _, _ => ⟨s, m, E, hA, by simp⟩
  | c + 1, hn, hP, hR => by
    obtain ⟨s₁, m₁, E₁, u₁, h₁⟩ := walk_of_paid hfit b k ds hA c (by omega)
      (fun j hj => hP j (by omega)) (fun j hj => hR j (by omega))
    obtain ⟨s₂, m₂, E₂, u₂, h₂, -⟩ := step_of_paid T Said (n := n) hfit (by omega) (hP c (by omega))
      (hR c (by omega)) u₁
    refine ⟨s₂, m₂, E₂, u₂, ?_⟩
    rw [h₂, h₁, List.range_succ, List.flatMap_append, List.append_assoc]
    simp

end ProofFile.Honest

#print axioms ProofFile.Honest.MemberPaid
#print axioms ProofFile.Honest.MemberRuns
#print axioms ProofFile.Honest.step_of_paid
#print axioms ProofFile.Honest.walk_of_paid
