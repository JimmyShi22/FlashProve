-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RidersAnd.lean: `behind_of_keeps` (Honest/Thread/Riders.lean)
at a `Thread` whose `rides` is one more condition beside the list of clauses. The lemmas of
Honest/Thread/Riders.lean take as a hypothesis that the `Thread`'s `rides` is `ridersOf cs`. The
first chain's parameters under the library's hypothesis `AtMgA` (`lettersHead`,
Honest/Thread/FirstHead.lean) define `rides` as "the reply's clause ∧ Rd": so there that hypothesis
does not hold by unfolding: this was found by the author of the lookups' prover's sides. Here are
the lemmas at a `rides` of the form R₀ ∧ ridersOf cs, with one more hypothesis: that R₀ itself is
carried on; and, at `lettersHead` with Rd := ridersOf cs, that form by unfolding, with the carrying
on of the reply's clause cut in two: the sub-protocol before b₀ establishes it; every other
sub-protocol's clause of `keeps` leaves the reply unchanged. Conditional lemmas on this folder's own
definitions.

  `behind_of_keeps_and`, `behindS_of_keeps_and`   general in the `Thread`
  `head_rides_and`   the form at `lettersHead`: by unfolding
  `head_reply_next`   the reply's clause, one border further

Limits.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **`Behind` from the form, `keeps`, the clauses established, and that the other condition is
carried on.** -/
theorem behind_of_keeps_and {R₀ : Nat → W → S → Prop} {cs : List (RiderCl W S)} {b : Nat}
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (hFK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (h₀ : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', Thr T b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  obtain ⟨hF, hK⟩ := hFK blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ?_, hK⟩
  rw [ei]
  exact (hr _ _ _).2 ⟨h₀ blk hblk k s m E ds y cols s' hA hd hS,
    riders_next ((hr _ _ _).1 hR0).2
      (fun c hc h1 h2 h0 => hst c hc h1 h2 _ _ _ hK h0)
      fun c hc e => hl c hc e blk hblk k s m E ds y cols s' hA hd hS⟩

/-- The same from `ThrS`. -/
theorem behindS_of_keeps_and (Said : Nat → Coins Bk → Mid W X → Prop)
    {R₀ : Nat → W → S → Prop} {cs : List (RiderCl W S)} {b : Nat}
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (hFK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (h₀ : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS T Said b c) : BehindS T Said b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  obtain ⟨hF, hK⟩ := hFK blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ?_, hK⟩
  rw [ei]
  exact (hr _ _ _).2 ⟨h₀ blk hblk k s m E ds y cols s' hA hd hS,
    riders_next ((hr _ _ _).1 hR0).2
      (fun c hc h1 h2 h0 => hst c hc h1 h2 _ _ _ hK h0)
      fun c hc e => hl c hc e blk hblk k s m E ds y cols s' hA hd hS⟩

end

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At `lettersHead` with Rd := ridersOf cs `rides` has that form**: by unfolding. -/
theorem head_rides_and (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (c : Nat)
    (v : Local W₀ Rc ProofFile.Inst Tr) (s : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread.rides c v s ↔
      (b₀ ≤ c → s.out.reply = some v.x.asked) ∧ ridersOf cs c v s := Iff.rfl

/-- **The reply's clause, one border further**: the sub-protocol before b₀ establishes it; past
every other the reply is as it was. -/
theorem head_reply_next {W : Type} {asked : W → OnBytes.E} {b₀ b : Nat} {v : W} {s s' : TS}
    (h0 : b₀ ≤ b → s.out.reply = some (asked v))
    (hlay : b₀ = b + 1 → s'.out.reply = some (asked v))
    (hkeep : b₀ ≤ b → s'.out.reply = s.out.reply) :
    b₀ ≤ b + 1 → s'.out.reply = some (asked v) := by
  intro hb
  by_cases e : b₀ = b + 1
  · exact hlay e
  · have hb' : b₀ ≤ b := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hb e)
    rw [hkeep hb']
    exact h0 hb'

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.behind_of_keeps_and
#print axioms ProofFile.Honest.behindS_of_keeps_and
#print axioms ProofFile.Honest.FirstThread.head_rides_and
#print axioms ProofFile.Honest.FirstThread.head_reply_next
