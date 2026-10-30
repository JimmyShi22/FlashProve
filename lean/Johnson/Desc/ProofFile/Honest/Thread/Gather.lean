-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Gather.lean: the hypothesis `OwesS` (PaysS.lean) of the rules
for a whole description (FileD.lean), from the smaller hypotheses into which the lemmas of this
folder divide it. `OwesS T Said` asks four conditions at every sub-protocol of a chain: `PlaysS`,
`BehindS`, `ExchangeS`, `RidesPastS`. Here they are asked in seven columns, each at every
sub-protocol number `b`. No definition.

  `hP`    `PlaysS` at `b`
  `hFK`   after the step: the form at the next border, and the condition `keeps` at `b`
  `h₀`    after the step: the part `R₀` of the field `rides` that is not a list of rider clauses
  `hst`   `StaysBy` (Riders.lean): each rider clause whose span contains `b` and `b + 1` survives
  `hl`    `LaysAtS` (SharesS.lean): each rider clause whose span begins at `b + 1` is established
  `hX`    `ExchangeAtS` (SharesS.lean) at each item of the forward row's list `owes`
  `hR`    `RidesPastAtS` (SharesS.lean) at each open item that the row neither closes nor has in
          `owes`

  1  `owesS_of_shares`   for any `Thread`
  2  `owesS_first`       at the first chain's parameters (`Letters`, First.lean): the form at the
     next border is asked as the four conditions of `form_behind_of_xk` (FormXK.lean), `keeps` apart

Limits.
  * Conditional lemmas on this folder's own definitions. Nothing shows that a hypothesis holds at
    any sub-protocol.
  * All hypotheses but `hr` and `hst` are asked from the invariant: at a `Thread` whose invariant
    never holds they hold vacuously, and so does the conclusion.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Thread.FormXK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **`OwesS` from the seven columns.** -/
theorem owesS_of_shares {R₀ : Nat → W → S → Prop} {cs : List (RiderCl W S)}
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (hP : ∀ b, b < T.bs.length → PlaysS T Said b)
    (hFK : ∀ b, b < T.bs.length → ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (h₀ : ∀ b, b < T.bs.length → ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' →
      R₀ (b + 1) m.st.input s')
    (hst : ∀ b, b < T.bs.length → ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ b, b < T.bs.length → ∀ c ∈ cs, c.lo = b + 1 → LaysAtS T Said b c)
    (hX : ∀ b, b < T.bs.length → ∀ i ∈ (T.row b).owes, ExchangeAtS T Said b i)
    (hR : ∀ b, b < T.bs.length → ∀ i ∈ T.opened b, i ∉ (T.row b).shuts → i ∉ (T.row b).owes →
      RidesPastAtS T Said b i) : OwesS T Said := fun b hb =>
  ⟨hP b hb, behindS_of_keeps_and T Said hr (hFK b hb) (h₀ b hb) (hst b hb) (hl b hb),
    (exchangeS_iff T Said).2 (hX b hb), ridesPastS_shares T Said (hR b hb)⟩

end

namespace FirstThread
open VerifiableInference.Desc.First (S samplesHeld)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **`OwesS` at the first chain's parameters.** `hF`: the four conditions on the state after the
step that give the form at the next border. `hK`: `keeps`. -/
theorem owesS_first (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    {R₀ : Nat → Local W₀ Rc Xi Tr → S → Prop} {cs : List (RiderCl (Local W₀ Rc Xi Tr) S)}
    (hr : ∀ c w s, L.thread.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      s'.failed = none ∧
      IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) (b + 1) s' =
        true ∧
      samplesHeld L.N L.mgP (IM.openAt L.links L.ps (b + 1)) (L.pubOf m.st.input.x, s') = true ∧
      ∀ q ∈ P1K2.pubAt L.mgP L.links L.ps (b + 1), L.mgP.pubP q (L.pubOf m.st.input.x, s'))
    (hK : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.keeps b s s')
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      R₀ (b + 1) m.st.input s')
    (hst : ∀ b, b < L.thread.bs.length → ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi →
      StaysBy L.thread b c)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ cs, c.lo = b + 1 → LaysAtS L.thread Said b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread Said b i)
    (hR : ∀ b, b < L.thread.bs.length → ∀ i ∈ L.thread.opened b, i ∉ (L.thread.row b).shuts →
      i ∉ (L.thread.row b).owes → RidesPastAtS L.thread Said b i) : OwesS L.thread Said :=
  owesS_of_shares L.thread Said hr hP
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS => by
      obtain ⟨a1, a2, a3, a4⟩ := hF b hb blk hblk k s m E ds y cols s' hA hd hS
      exact ⟨form_behind_of_xk L hS a1 a2 a3 a4,
        hK b hb blk hblk k s m E ds y cols s' hA hd hS⟩)
    h₀ hst hl hX hR

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.owesS_of_shares
#print axioms ProofFile.Honest.FirstThread.owesS_first
