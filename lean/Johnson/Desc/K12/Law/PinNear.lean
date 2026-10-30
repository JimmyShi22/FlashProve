-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/PinNear.lean: what is near a word and has the sample's answers is what the
library's decoder with the sample returns, at a seed without collision. Statements and proofs.

It serves the reading of the oracles' strings as committed messages. No frame, no view and no
program stands in it. There is no new mathematics: three calls of the library's lemmas on its
decoder.
The notions are the library's (Cb/Ld/LdSig.lean): `OMsg` (an oracle message: code, sample map,
radius o.e); `OMsg.dist`; `OMsg.dec` (nearest, first in the fixed order, among the pairs whose
message has the sample's answers; none beyond the radius); `OMsg.Clash` (two different messages of
the word's list share the answers at the seed); `Sig.decs`; `Sig.CF`; `Sig.Ans`; `Sig.over`.
Main names:
  `pin_of_near`: from o.dist f w ≤ o.e, o.Z.val σ.1 w.1 = σ.2 and ¬ o.Clash f σ.1: o.dec f σ = some
    w.1. It holds at every radius: beyond unique decoding the word has a list of near messages; the
    sample picks one, and "no collision" makes the pick unique.
  `near_of_pin`: back, always: what the decoder returns has an encoding within the radius and has
    the answers.
  `decs_of_near`: over a signature: from `Sig.CF σ y`, every member near, and `Sig.Ans`: ∀ a,
    Sig.decs σ y a = some (w a).1. This is the first half of the relaxed relation of `Sig.over`
    (which `PinSig`, Johnson/Desc/Sound/MsgSig.lean, reads at its three readings) from the first
    half of its condition (`CfSig`, same file).
  `pin_unique`: under `Sig.CF` two witnesses that are near and have the answers have one message at
    every member.
Limits: who pays the three premises at a proximity test's group is told here by reading alone;
nothing of it is shown. Near: the test's conclusion (a witness within the radius of the group's
word), member by member; it wants the member's radius to be at least the test's. The answers: the
member's sample row is among the rows that the batching takes; the library's `sig_rows` turns "the
sample's rows hold" into Z.val σ.1 m = σ.2. No collision: the sending's price: the library's
`sig_cnt_clash` (at most (L choose 2) · Z.err seeds; the word fixed before the seed) and, in the
game's form, `Johnson.Pack.sigOf_send` under `MeetsAt` (Johnson/Pack/PortF.lean). A member without a
sample (a mask sent ahead) is no member of such a signature: nothing pins it here. No soundness is
claimed, and nothing is said on hiding.
Lemmas of the library that are called (none runs in a context of `verify-on-bytes`): `sig_dec_good`,
`sig_dec_cand`, `sig_inList_iff` (Cb/Ld/LdSigProofs.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Cb.Ld.LdSigProofs
import Johnson.Pack.PortF

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob

variable {E : Type} [Field E]

/-- The pin, at one oracle message: a pair (message, tail) whose encoding is within the message's
radius of the word as sent, whose message has the sample's answers, is what the library's decoder
with the sample returns, at a seed without collision. -/
theorem pin_of_near (o : OMsg E) (f : o.Str) (σ : o.Smp) (w : o.Wit) (hn : o.dist f w ≤ o.e)
    (ha : o.Z.val σ.1 w.1 = σ.2) (hc : ¬ o.Clash f σ.1) : o.dec f σ = some w.1 :=
  (sig_dec_good E o f σ.1 hc σ.2 w.1).2 ⟨(sig_inList_iff E o f w.1).1 ⟨w, hn, rfl⟩, ha⟩

/-- And back: what the decoder returns is in the list and has the answers: always. -/
theorem near_of_pin (o : OMsg E) (f : o.Str) (σ : o.Smp) (m : o.Msg) (h : o.dec f σ = some m) :
    (∃ w : o.Wit, o.dist f w ≤ o.e ∧ w.1 = m) ∧ o.Z.val σ.1 m = σ.2 := by
  obtain ⟨h1, h2⟩ := sig_dec_cand E o f σ m h
  exact ⟨(sig_inList_iff E o f m).2 h1, h2⟩

/-- The pin over a signature: the first half of Sig.over's relaxed relation, from its condition's
first half (Sig.CF), nearness and the answers, member by member. -/
theorem decs_of_near (S : Sig E) (σ : S.Smp) (y : S.ext.Str) (w : S.Wit) (hc : S.CF σ y)
    (hn : ∀ a, (S.om a).dist (y a) (w a) ≤ (S.om a).e) (ha : S.Ans σ (S.msgs w)) :
    ∀ a, S.decs σ y a = some (w a).1 :=
  fun a => pin_of_near (S.om a) (y a) (σ a) (w a) (hn a) (ha a) (hc a)

/-- At most one message is pinned: two witnesses that are near and have the answers have one
message, member by member, under Sig.CF. -/
theorem pin_unique (S : Sig E) (σ : S.Smp) (y : S.ext.Str) (w w' : S.Wit) (hc : S.CF σ y)
    (hn : ∀ a, (S.om a).dist (y a) (w a) ≤ (S.om a).e) (ha : S.Ans σ (S.msgs w))
    (hn' : ∀ a, (S.om a).dist (y a) (w' a) ≤ (S.om a).e) (ha' : S.Ans σ (S.msgs w')) :
    S.msgs w = S.msgs w' :=
  funext fun a => Option.some.inj ((decs_of_near S σ y w hc hn ha a).symm.trans
    (decs_of_near S σ y w' hc hn' ha' a))

end H2K.Pin

#print axioms H2K.Pin.pin_of_near
#print axioms H2K.Pin.decs_of_near
#print axioms H2K.Pin.pin_unique
