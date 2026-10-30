-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/EveryAtS.lean: THE LAW OF EveryAt.lean IN THIS FOLDER, FROM THE
PAIR: a member of a thread that seats a proximity test is accepted in the frame's form that is asked
from the thread TOGETHER WITH WHAT IS SAID OF THE PROVER's RUN (`AcceptedS`,
Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean; `ThrS`, Thread/Said.lean), at every letter for a
fall. WHY A SECOND FORM: what the premise `K12Front` asks of the tables at hand in front of the test
can be had of a thread's tables that are those of the frame's own play only where the run stands
where that play stands; the thread alone does not say so. The law from the pair asks `K12Front` at
fewer stands. A definition, statements and proofs.

  `acceptedS_of_saysYes`   the frame's lemma `accepted_of_saysYes` (Thread/FileRowYes.lean), word
                 for word, at the pair
  `K12SeatedFS`  `K12SeatedF` with its last clause asked at the stands of the pair alone
  `seatedFS_of`  `K12SeatedF` gives it, whatever is said
  **`acceptedS_every`**   `K12SeatedFS` ⟹ `AcceptedS T Said fall b` at every letter fall

Limits. Those of EveryAt.lean: `K12Front` is asked at every stand of the pair, at whatever coins the
book lends; no member of `K12SeatedFS` is given. Nothing on completeness, on soundness or on what is
hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.EveryAt
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- The sixth debt, from the pair, out of the chain's rule's second form. -/
theorem acceptedS_of_saysYes (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} {fall : ℕ → S → List Fmt.Drawn → Option String}
    {fl : S → List Fmt.Drawn → Option String} {A : Coins Bk → S → Mid W X → Env → Prop}
    (hblk : T.bs[b]? = some blk) (h : SaysYes T.φ Bk T.chain T.ft T.hs blk fl A)
    (hA : ∀ k s m E, ThrS T Said b k s m E → A k s m E)
    (hf : ∀ s ds, fall b s ds = none → fl s ds = none) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hThr hd hst hn hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨s', n, hs⟩ := h k s m E ds l y cols (hA k s m E hThr) hd hst (hf s ds hn) hl hy hc
  have hn' : n = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hn'
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hMv, hs⟩

/-- `K12SeatedF`, with its last clause asked at the stands of the pair alone. -/
structure K12SeatedFS (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S) :
    Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g
  stands : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    ThrS T Said b k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    K12Front J enter leave st m E c

theorem seatedFS_of (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (h : K12SeatedF T b J enter leave) : K12SeatedFS T Said b J enter leave :=
  ⟨h.member, h.half, h.stages, fun k st m E c hT hc => h.stands k st m E c hT.1 hc⟩

/-- **It is accepted, from the pair, whatever the letter for a fall says.** -/
theorem acceptedS_every (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    (b : ℕ) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (h : K12SeatedFS T Said b J enter leave)
    (fall : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS T Said fall b := by
  obtain ⟨s, t, rest, hst, hk⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  exact acceptedS_of_saysYes T Said hblk
    (saysYes_seat T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (fall b) (ThrS T Said b) s t rest
      hst hk h.half fun k st m E ds c hT hd _ hc =>
        k12At_every J enter leave st m E c (h.stands k st m E c hT hc) ds hd)
    (fun _ _ _ _ x => x) fun _ _ x => x

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.acceptedS_of_saysYes
#print axioms ProofFile.Honest.K12.seatedFS_of
#print axioms ProofFile.Honest.K12.acceptedS_every
