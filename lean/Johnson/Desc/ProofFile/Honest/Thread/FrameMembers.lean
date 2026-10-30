-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FrameMembers.lean: THE YES AND THE OWES AT MEMBERS THAT BELONG TO
NO KIND: the shared chain's first and last members, and the last chain's members 1 and 3. These
members draw nothing new, and where they say yes they hand on the state as it stood. So their debts
come down to what the thread says of that state.

  `acceptedS_of_runs`, `acceptedS_sealed`   the yes at a sealing member, from `ThrS`
  `step_quiet`, `exchangeS_nil`   a member without a round: its step; no item owed
  `flat_first`   a chain's flat list begins with its first block
  `acceptedS_front`, `acceptedS_end₂`, `acceptedS_takenSources`, `acceptedS_end₃`   at the description's
    own members

What these are. Conditional lemmas on our own definitions. None is one of the library's goals. Two
forms of the yes follow `accepted_of_runs` and `accepted_sealed` line for line, with `ThrS` for `Thr`.
At a member without a round the library's `acceptedS_quiet` and `behindS_quiet` serve
(Honest/Law/NoHouse/Quiet.lean).

Limits.
  * The sentences that each lemma asks of `ThrS` are premises. That a thread's `form` or `rides` gives
    them is not shown here of any letter.
  * `RidesPastS` at these members is not here: it reads the meaning of each open item, which is a
    letter of the thread.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.KeyThreads
import E2E.KeyPlaysQuiet
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Quiet
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Chain)

section General
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- `accepted_of_runs`, from `ThrS`. -/
theorem acceptedS_of_runs {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (h : ∀ k s m E ds l, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
        .ok l →
      ∃ (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S), play l ds [] m = .ok y ∧
        fillCols (readsOf T.chain T.ft (E.add y.1).stored (E.add y.1).tree blk.rounds ds) [] =
          .ok cols ∧ blk.step T.ft s (roundsOf y.1) cols = .ok (s', cols.length)) :
    AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hThr hd _ _ hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨y', cols', s', hy', hc', hs'⟩ := h k s m E ds l hThr hd hl
  have ey : y' = y := Except.ok.inj (hy'.symm.trans hy)
  subst ey
  have ec : cols' = cols := Except.ok.inj (hc'.symm.trans hc)
  subst ec
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hMv, hs'⟩

/-- **The like for a member whose one round is the sealing round**, at whose place no part of a
prover stands. -/
theorem acceptedS_sealed {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = [VerifiableInference.Desc.ChainEnd.sealRound]) (ho : blk.oracles = [[]])
    (hn : (T.hs.find? fun g => g.place == blk.place) = none)
    (h : ∀ k s m E rs gs, ThrS T Said b k s m E → ∃ s', blk.decide s rs gs = .ok s') :
    AcceptedS T Said fall b :=
  acceptedS_of_runs T Said hblk fun k s m E ds l hT hd hl => by
    have el := steps_one_none hn hl
    subst el
    rw [hr] at hd
    obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd
    have eb : bareSteps (W := W) (Y := X) blk =
        [⟨blk.name, ⟨blk.place, 0⟩, VerifiableInference.Desc.ChainEnd.sealRound, [],
          fun _ _ => none, fun _ _ => none, 0, false, none⟩] := by
      simp [bareSteps, hr, ho]
    rw [eb]
    obtain ⟨s', hs⟩ := h k s m E _ _ hT
    refine ⟨_, [], s', rfl, ?_, ?_⟩
    · rw [hr]
      rfl
    · refine VerifiableInference.Desc.Block.step_ok.2 ⟨?_, ?_, hs, ?_⟩
      · rw [hr]
        exact (ProofFile.Honest.Toy.roundsFit_cons (by with_unfolding_all rfl) h₀).trans
          (by with_unfolding_all rfl)
      · rw [hr]
        rfl
      · rw [hr]
        rfl

/-- The step of a member without a round, from its decision. -/
theorem step_quiet {blk : Block S Cl} {ft : Nat} {s s' : S} (hr : blk.rounds = [])
    (h : blk.decide s [] [] = .ok s') : blk.step ft s [] [] = .ok (s', 0) := by
  refine VerifiableInference.Desc.Block.step_ok.2 ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]
    rfl
  · rw [hr]
    rfl
  · rw [hr]
    exact h
  · rw [hr]
    rfl

/-- **`ExchangeS` at a member that owes no item.** -/
theorem exchangeS_nil {b : Nat} (h : (T.row b).owes = []) : ExchangeS T Said b := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  rw [h] at hi
  cases hi

end General

/-- A chain's flat list begins with its first block: with its rounds, oracle messages, place and
decision. -/
theorem flat_first {S Cl : Type} (c : Chain S Cl) :
    ∃ blk, c.blocksInOrder[0]? = some blk ∧ blk.rounds = c.first.rounds ∧ blk.oracles = c.first.oracles ∧
      blk.place = c.first.place ∧ blk.decide = c.first.decide :=
  ⟨{ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter }, rfl, rfl, rfl, rfl, rfl⟩

section AtTerm
open P5J (F0T)
open AtPublicFiles.AtFiles (flat_last)

variable {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {Bk : ProverCoinCounts} {V W X Pb : Type}

local notation "𝔽" => F0T OnBytes.secondHashFunction Zp Np cF

/-- K12's own block as the last chain names it. -/
abbrev ownZ (Np : H2U.Places4) : Block VerifiableInference.Desc.Third.S₃ Unit :=
  VerifiableInference.Desc.K12.Seat.onOwn
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W))

/-- **The shared chain's first member says yes at every state.** -/
theorem acceptedS_front {fall : Nat → (𝔽).S₂ → List Fmt.Drawn → Option String}
    (T₂ : Thread Bk (𝔽).S₂ (𝔽).Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (hbs : T₂.bs = (𝔽).shared.blocksInOrder) : AcceptedS T₂ Said fall 0 := by
  obtain ⟨blk, e, hr, -, -, hd⟩ := flat_first (𝔽).shared
  exact acceptedS_quiet T₂ Said (by rw [hbs]; exact e) (hr.trans rfl)
    fun _ s _ _ _ _ => ⟨s, step_quiet (hr.trans rfl) (by rw [hd]; rfl)⟩

/-- **The shared chain's end** says yes where the thread's sentence in front of it gives the library's
book-keeping at border 11 and `Listed`, and no part of a prover stands at its place. -/
theorem acceptedS_end₂ {fall : Nat → (𝔽).S₂ → List Fmt.Drawn → Option String}
    (T₂ : Thread Bk (𝔽).S₂ (𝔽).Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (hbs : T₂.bs = (𝔽).shared.blocksInOrder) (S : OnBytes.Params.LinShape) (a : Nat)
    (hn : (T₂.hs.find? fun g => g.place == (𝔽).shared.last.place) = none)
    (h : ∀ k s m E, ThrS T₂ Said ((𝔽).shared.blocksInOrder.length - 1) k s m E →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 11 s) = true ∧
        AtPublicFiles.AtFiles.Listed (show _root_.Desc.K14.St from s).st) :
    AcceptedS T₂ Said fall ((𝔽).shared.blocksInOrder.length - 1) := by
  obtain ⟨blk, e, hr, ho, hp, hd⟩ := flat_last (𝔽).shared
  exact acceptedS_sealed T₂ Said (by rw [hbs]; exact e) (hr.trans rfl) (ho.trans rfl)
    (by rw [hp]; exact hn) fun k s m E rs gs hT => by
      obtain ⟨h1, h2⟩ := h k s m E hT
      exact ⟨s, by
        rw [hd]
        exact AtPublicFiles.AtFiles.end₂_passes S a s h1 (AtPublicFiles.AtFiles.joined_of_listed _ h2) [] rs gs⟩

/-- **The taken trees' sources**, the last chain's member 1, say yes where the thread's sentence in
front of it gives the library's `Third.Law.Tied`. -/
theorem acceptedS_takenSources {fall : Nat → (𝔽).S₃ → List Fmt.Drawn → Option String}
    (T₃ : Thread Bk (𝔽).S₃ (𝔽).Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (hbs : T₃.bs = (𝔽).second.blocksInOrder)
    (h : ∀ k s m E, ThrS T₃ Said 1 k s m E → VerifiableInference.Desc.Third.Law.Tied (ownZ Np) s) :
    AcceptedS T₃ Said fall 1 := by
  have hb : ∃ blk, (𝔽).second.blocksInOrder[1]? = some blk ∧ blk.rounds = [] ∧
      ∀ s, blk.decide s [] [] = (VerifiableInference.Desc.Third.takenSources (ownZ Np)).decide s [] [] :=
    ⟨_, rfl, rfl, fun _ => rfl⟩
  obtain ⟨blk, e, hr, hd⟩ := hb
  exact acceptedS_quiet T₃ Said (by rw [hbs]; exact e) hr fun k s m E hT _ =>
    ⟨s, step_quiet hr (by rw [hd]; exact AtPublicFiles.AtFiles.takenSources_passes _ s [] [] (h k s m E hT))⟩

/-- **The last chain's end**, member 3, says yes where the thread's sentence in front of it gives the
library's book-keeping at border 3, `Older` and `Listed`. -/
theorem acceptedS_end₃ {fall : Nat → (𝔽).S₃ → List Fmt.Drawn → Option String}
    (T₃ : Thread Bk (𝔽).S₃ (𝔽).Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (hbs : T₃.bs = (𝔽).second.blocksInOrder) (S : OnBytes.Params.LinShape) (a n g t : Nat)
    (idx : List Nat)
    (h : ∀ k s m E, ThrS T₃ Said 3 k s m E →
      LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true ∧
        AtPublicFiles.AtFiles.Older n g s.st ∧ AtPublicFiles.AtFiles.Listed s.st) :
    AcceptedS T₃ Said fall 3 := by
  have hb : ∃ blk, (𝔽).second.blocksInOrder[3]? = some blk ∧ blk.rounds = [] ∧
      ∀ s, blk.decide s [] [] = (VerifiableInference.Desc.Third.end₃ (Cl := Unit) []).decide s [] [] :=
    ⟨_, rfl, rfl, fun _ => rfl⟩
  obtain ⟨blk, e, hr, hd⟩ := hb
  exact acceptedS_quiet T₃ Said (by rw [hbs]; exact e) hr fun k s m E hT _ => by
    obtain ⟨h1, h2, h3⟩ := h k s m E hT
    exact ⟨s, step_quiet hr (by
      rw [hd]
      exact AtPublicFiles.AtFiles.end₃_passes (Cl := Unit) S a n g t idx s h1 h2
        (AtPublicFiles.AtFiles.joined_of_listed _ h3) [] [] [])⟩

end AtTerm

end ProofFile.Honest

#print axioms ProofFile.Honest.acceptedS_front
#print axioms ProofFile.Honest.acceptedS_end₂
#print axioms ProofFile.Honest.acceptedS_takenSources
#print axioms ProofFile.Honest.acceptedS_end₃
#print axioms ProofFile.Honest.acceptedS_of_runs
#print axioms ProofFile.Honest.acceptedS_sealed
#print axioms ProofFile.Honest.step_quiet
#print axioms ProofFile.Honest.exchangeS_nil
#print axioms ProofFile.Honest.flat_first
