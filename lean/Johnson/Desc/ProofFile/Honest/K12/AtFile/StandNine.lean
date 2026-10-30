-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/StandNine.lean: three facts on member 9 of the proof file's shared
chain that `acceptedS_head_U` and `playsS_nine` take as premises or that a reader asks beside them.

  `seat_of_like`  a block like the seat at a job's place seats the job: with `tailLike_shared`
                 (Honest/K14/OmegaAtShared.lean) that is hblk and hseat at lettersShared's list
  `find_half`    a prover's list finds the half that stands behind sides with other places: hf
  `no_fall_nine` at a stand at border 9 the door's own fold and way in return: the door takes no fall-back
  `told_of_tell`, `say_of_none`   a round with a move, played at a state, is told, and so its part is
                 called (`RunC.called`); behind a rejection a round's message is the fixed substitute: no
                 part's move is run, so no door is read. With `atHandAtU_at_run'`
                 (K12/AtProof/HalfAtPure.lean), at a called part: the fall-back of the door at the test
                 on G_u is taken at no round whose move is run

Limits.
- `no_fall_nine` has `Thr` as a premise: NOT IN FRONT OF A LAW OVER COINS.
- That the six other sides stand at other places is hno: a premise here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysNine
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks first frontBlock withU P14)
open Desc.K14.Honest (Like)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (doorUF colsLoc)

variable {W X : Type}

/-- **A block like the seat at a job's place seats the job.** -/
theorem seat_of_like {Cl : Type} {x : Block St Cl} {J : TestJob W X}
    (hl : Like x (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit))) :
    SeatOf x J (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave := by
  have h := seatOf_inside (Cl := Unit) J
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave
  exact ⟨hl.place.trans h.place, hl.rounds.trans h.rounds, hl.oracles.trans h.oracles,
    fun s rs gs => by rw [hl.decide]; exact h.decide s rs gs⟩

/-- **A prover's list finds the half that stands behind sides with other places.** -/
theorem find_half {V : Type} (six : List (Placed V W X)) (g : Placed V W X)
    (rest : List (Placed V W X)) (p : Place) (hp : g.place = p) (hno : ∀ x ∈ six, x.place ≠ p) :
    ((six ++ g :: rest).find? fun x => x.place == p) = some g := by
  subst hp
  rw [List.find?_append, List.find?_eq_none.2 (fun x hx => by
    simpa using hno x hx)]
  simp [List.find?]

/-- **At a stand at border 9 the door's own fold and way in return.** -/
theorem no_fall_nine {Cl V Pb W₀ Rc X₀ : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb) (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hpre : List.Forall₂ Like (T.bs.take 9) [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8])
    (hah : T.ahead = []) (hch : T.chain = 1) (hft : T.ft = 0)
    (hbeg : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes w.key)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (hst : ∀ w, T.stored w = st w.w₀ w.rc)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E) :
    foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes m.st.input.key)
        (frontOf m).seen.rounds
        (colsLoc Q (st m.st.input.w₀ m.st.input.rc) (frontOf m).seen.rounds) = .ok (s, [], []) ∧
      ∃ t, VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) s = .ok t := by
  obtain ⟨-, h2, h3⟩ := stand_at_nine T c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU hpre hah hch hft hbeg
    st hst u
  exact ⟨h3, _, h2⟩

/-- **A round with a move, played at a state, is told**: where the message returns it is the part's own, and
so the run counts that part as called. So a part that the run does not call, where the run returns, has
its rounds with a move played behind a rejection. -/
theorem told_of_tell {W X : Type} (s : Step W X) (mv : Move Unit W X) (hm : s.move = some mv)
    (back : Option Fmt.RoundView) (m : Mid W X) (x : Told) (h : s.tell back m = .ok x) : x.told = true := by
  unfold Step.tell at h
  cases hs : s.stop m.loc s.nth with
  | some e =>
    simp only [hs] at h
    cases h
  | none =>
    simp only [hs, hm] at h
    cases hy : mv.say () m.shown m.st with
    | error e =>
      simp only [hy] at h
      cases h
    | ok y =>
      simp only [hy] at h
      split at h
      · cases h
      · cases h
        rfl

/-- **Behind a rejection a round's message is the fixed substitute.** -/
theorem say_of_none {S Cl Y : Type} (z : ChainProgress S Cl W Y) (s : Step W Y) (h : z.mid = none) :
    z.say s = .ok (subTold s.decl s.oracles) := by
  unfold ChainProgress.say
  rw [h]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.seat_of_like
#print axioms ProofFile.Honest.K12.AtFile.find_half
#print axioms ProofFile.Honest.K12.AtFile.no_fall_nine
#print axioms ProofFile.Honest.K12.AtFile.told_of_tell
#print axioms ProofFile.Honest.K12.AtFile.say_of_none
