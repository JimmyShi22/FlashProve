-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/JoinDebts.lean: THE 25 LINKS' FIRST HEARING MEMBERS: THE
JOINING RULE ON THE DEBTS. Such a member blk of the first chain's flat list is a lot's sub-protocol
b' with the frame's «opened» joined behind it (the library's `IM.Joined`). A half of the prover
stands at its place, so the record `NoHouse` does not fit. WHAT IS PROVED OF b' (THE FIRST HALF)
REACHES UP TO THE STATE BETWEEN; WHAT IS PROVED OF «opened» (THE SECOND HALF), FROM THERE ON; THE
DEBTS (Honest/Thread/PaysS.lean) ARE ASKED AT blk, THE MEMBER AS IT LIES. Here the rule that joins
the two, for the three debts that read the member's step: `BehindS`, `ExchangeS`, `AcceptedS`. IT
ENDS AT blk.

WHAT THIS IS. Conditional lemmas on definitions of ours and the library's `IM.Joined`: thin, over
`joined_step_iff` (Honest/Law/NoHouse/JoinBack.lean). General in the thread (at the first chain's
type of states). NO NEW DEFINITION: M, WHAT THE FIRST HALF SAYS AT THE STATE BETWEEN, IS A LETTER.
In the statements the first half's premise is the binder `house`, the second half's `frame`. None of
the library's goals.

  `stepped_joined`   the member's step (`Thread.Stepped`), both ways
  `sameReply_trans`   the reply as it was, twice in a row
  `behindS_joined`, `exchangeS_joined`   first half: from the thread in front, the prover's side of
  the step AT blk, b''s step's yes to mid, no mark there: M · second half: from M, «opened»'s yes
  from mid to s', no mark, the reply as it was: the debt's own conclusion at s'
  `acceptedS_joined`   first half: from the thread in front, no stop, no fall, the prover's side of
                       the step: b''s step says yes to some mid, no mark there, M, and (at an
                       address that is not K7's) the reply as it was · second half: from M: «opened»
                       says yes at mid, no mark behind it, the reply as it was

WHICH DEBT NEEDS NO JOINING. `PlaysS` reads of the member its name, place, rounds and oracle
messages, and not its decision: it belongs to the first half outright, AT blk. `RidesPastS` names no
member.

MET FOR NOTHING. M := False at the first two; at the third the first half's premise then cannot be
met.
Limits. NEITHER HALF's PREMISE IS SHOWN AT ANY MEMBER. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.JoinBack
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place KindName)
open VerifiableInference.Desc.First (S hearsReply)
open ProofFile (Cl)

/-- The reply as it was, twice in a row. -/
theorem sameReply_trans {s m t : S} (h₁ : ProofFile.sameReply s m = true)
    (h₂ : ProofFile.sameReply m t = true) : ProofFile.sameReply s t = true := by
  show (s.out.reply == t.out.reply) = true
  rw [IM.sameReply_eq h₁]
  exact h₂

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {Z : ProofFile.Pub} {l : Nat}
  {blk b' : Block S Cl} {a : Place} (hj : IM.Joined Z l blk b' a)
  {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame} {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
  (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
  (hf : fs[l]? = some f)
include hj hfs hf

/-- **THE MEMBER's STEP, BOTH WAYS.** -/
theorem stepped_joined (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) (ds : List Fmt.Drawn)
    (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S) :
    T.Stepped blk k s m E ds y cols s' ↔
      T.Moved blk k m E ds y cols ∧
        (∃ mid, b'.step T.ft s (roundsOf y.1) cols = .ok (mid, cols.length) ∧ mid.failed = none ∧
          (f.opened mid = .ok s' ∧ s'.failed = none) ∧ ProofFile.sameReply mid s' = true) ∧
        (hearsReply a = false → ProofFile.sameReply s s' = true) := by
  unfold Thread.Stepped
  rw [joined_step_iff hj hfs hf T.ft s s' cols.length (roundsOf y.1) cols]

variable {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat} (hblk : T.bs[b]? = some blk)
  (M : Coins Bk → S → Mid W X → Env → List Played × Mid W X → S → Prop)
include hblk

/-- **`BehindS` AT A JOINED MEMBER.** -/
theorem behindS_joined
    (house : ∀ k s m E ds y cols mid, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols →
      b'.step T.ft s (roundsOf y.1) cols = .ok (mid, cols.length) → mid.failed = none →
      M k s m E y mid)
    (frame : ∀ k s m E y mid s', ThrS T Said b k s m E → M k s m E y mid →
      f.opened mid = .ok s' → s'.failed = none → ProofFile.sameReply mid s' = true →
      (hearsReply a = false → ProofFile.sameReply s s' = true) →
      T.Form (b + 1) k s' y.2 ∧ T.rides (b + 1) y.2.st.input s' ∧ T.keeps b s s') :
    BehindS T Said b := by
  intro blk₀ h₀ k s m E ds y cols s' hA hd hS
  obtain rfl := Option.some.inj (hblk.symm.trans h₀)
  obtain ⟨hM, ⟨mid, h1, h2, ⟨h3, h4⟩, h5⟩, h6⟩ :=
    (stepped_joined T hj hfs hf k s m E ds y cols s').1 hS
  exact frame k s m E y mid s' hA (house k s m E ds y cols mid hA hd hM h1 h2) h3 h4 h5 h6

/-- **`ExchangeS` AT A JOINED MEMBER.** -/
theorem exchangeS_joined
    (house : ∀ k s m E ds y cols mid, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols →
      b'.step T.ft s (roundsOf y.1) cols = .ok (mid, cols.length) → mid.failed = none →
      M k s m E y mid)
    (frame : ∀ k s m E y mid s', ThrS T Said b k s m E → M k s m E y mid →
      f.opened mid = .ok s' → s'.failed = none → ProofFile.sameReply mid s' = true →
      (hearsReply a = false → ProofFile.sameReply s s' = true) →
      T.Items (T.row b).owes k s' y.2 (E.add y.1)) :
    ExchangeS T Said b := by
  intro blk₀ h₀ k s m E ds y cols s' hA hd hS
  obtain rfl := Option.some.inj (hblk.symm.trans h₀)
  obtain ⟨hM, ⟨mid, h1, h2, ⟨h3, h4⟩, h5⟩, h6⟩ :=
    (stepped_joined T hj hfs hf k s m E ds y cols s').1 hS
  exact frame k s m E y mid s' hA (house k s m E ds y cols mid hA hd hM h1 h2) h3 h4 h5 h6

/-- **`AcceptedS` AT A JOINED MEMBER**: the way back is spent. -/
theorem acceptedS_joined {fall : Nat → S → List Fmt.Drawn → Option String}
    (house : ∀ k s m E ds y cols, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
      T.Moved blk k m E ds y cols →
      ∃ mid, b'.step T.ft s (roundsOf y.1) cols = .ok (mid, cols.length) ∧ mid.failed = none ∧
        (hearsReply a = false → ProofFile.sameReply s mid = true) ∧ M k s m E y mid)
    (frame : ∀ k s m E y mid, ThrS T Said b k s m E → M k s m E y mid →
      ∃ s', f.opened mid = .ok s' ∧ s'.failed = none ∧ ProofFile.sameReply mid s' = true) :
    AcceptedS T Said fall b := by
  intro blk₀ h₀ k s m E ds y cols hA hd hst hfl hM
  obtain rfl := Option.some.inj (hblk.symm.trans h₀)
  obtain ⟨mid, h1, h2, h6, hMid⟩ := house k s m E ds y cols hA hd hst hfl hM
  obtain ⟨s', h3, h4, h5⟩ := frame k s m E y mid hA hMid
  exact ⟨s', (stepped_joined T hj hfs hf k s m E ds y cols s').2
    ⟨hM, ⟨mid, h1, h2, ⟨h3, h4⟩, h5⟩, fun hh => sameReply_trans (h6 hh) h5⟩⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.sameReply_trans
#print axioms ProofFile.Honest.stepped_joined
#print axioms ProofFile.Honest.behindS_joined
#print axioms ProofFile.Honest.exchangeS_joined
#print axioms ProofFile.Honest.acceptedS_joined
