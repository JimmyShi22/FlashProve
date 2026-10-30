-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindRecut.lean: numbers of proof-of-work bits under a plan of splits and merges (`XPlan`,
Iop/Recut.lean; `GBits`, Iop/GBits.lean; Iop/Grind.lean). Definitions, auxiliary lemmas, and what
the plan's own conditions say about rounds with such bits. (Words of this library:
lean/GLOSSARY.md.)

Why. Proof-of-work bits are added last among the protocol transformers (header of Iop/Grind.lean),
but which round gets how many bits is known on the original list of rounds. So a list g on the old
rounds is carried along the plan.
  `GBits.recut P g`
      keep          the number stays
      split         the bits stay with the part that keeps the challenge (the remainder); the first
                    part, whose challenge is empty, gets 0
      merge of prover messages (J1)    the number of the second round. The first round's challenge
                                       has one value; its number must be 0: `GBits.RecutOK`
      merge of challenges (J2)         one number for the merged challenge (c1, c2): the larger of
                                       the two numbers
  `GBits.RecutOK P g`    the side condition at (J1). It guards that no round's bits are dropped, not
                         soundness: where it fails, `recut` drops the first round's bits, which only
                         makes the hypothesis on the new lists harder to meet.
  `GBits.recutOK_app` and the other auxiliary lemmas
                         There is no lemma (GBits.app g g').recut (XPlan.app P Q) = GBits.app
                         (g.recut P) (g'.recut Q): the two sides have different types, because
                         (XPlan.app P Q).shape and P.shape ++ Q.shape are equal only by a proof.
The errors. At a merge of challenges the errors add (`Err.recut`: e1 * card C2 + card C1 * e2) while
the bits take the maximum. So no bound is carried along for free. For explicit lists
`BatchProtocol.SoundAt.recut` gives soundness for `Err.recut P ε`, under its hypotheses.
One proof of work must not pay for several samples. The proof-of-work bits guard the challenge that
is derived from the query that contains the nonce. If the prover could choose something after the
nonce that enters a later part of the same challenge, it could find one nonce and then vary that
choice at no cost. In this library such a round does not exist:
  * all hash blocks of a challenge are blocks of one answer of the oracle, to the one query that
    contains the nonce (in the compiler; proof-of-work bits are added last among the transformers);
  * a round has one prover message and then one challenge. The round made by a merge of challenges
    has the prover message of r1 only (`Round.joinChal`); the old verifier is given the default
    message in the place of r2's. So between c1 and c2 the prover chooses nothing, whatever the
    plan. A plan that would thereby drop a real message does not satisfy `XPlan.OK`
    (`chal_second_one_value` below);
  * the part of the request that is fixed late is no prover message: the compiler puts the whole
    request into the query of the round `BatchProtocol.late`. Under `AXPlan.Late` that round is never the
    second or a later round of a run of merged rounds: `AXPlan.Late` is False there
    (`late_not_second` below: at the first step of a plan; deeper in a plan by the recursion of this
    condition).
    So the following pattern stays two rounds, and the second, if its error needs it, has
    proof-of-work bits of its own: the prover sends root and nonce, and the verifier answers with
    positions and proof-of-work bits; then comes the rest of the request; then the prover sends
    nothing, and the verifier answers with alpha.
Limits: on bounds the file has `GBits.AllLe.recut` and `GBits.AllLe.pull` (on the numbers of
proof-of-work bits); beyond these nothing is said on any bound; nothing on implementations.
-/
import Iop.GBitsLe
import Iop.GrindPull
import Iop.BatchRecut
import Iop.RecutKit

namespace Iop

/-- The numbers of proof-of-work bits on the new rounds. -/
def GBits.recut : {s : Shape} → (P : XPlan s) → GBits s → GBits P.shape
  | _, .nil => fun _ => ()
  | _, .keep _ P => fun (z : ℕ × GBits _) => (z.1, GBits.recut P z.2)
  | _, .cut (s := s) c P =>
    fun (z : ℕ × GBits s) => (0, GBits.recut P (show GBits (c.snd :: s) from z))
  | _, .msg r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) => GBits.recut P (show GBits (r1.joinMsg r2 :: s) from z.2)
  | _, .chal r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) =>
      GBits.recut P (show GBits (r1.joinChal r2 :: s) from (max z.1 z.2.1, z.2.2))

/-- The side condition: a round whose prover message is merged with the next round's has no
proof-of-work bits. -/
def GBits.RecutOK : {s : Shape} → (P : XPlan s) → GBits s → Prop
  | _, .nil => fun _ => True
  | _, .keep _ P => fun (z : ℕ × GBits _) => GBits.RecutOK P z.2
  | _, .cut (s := s) c P =>
    fun (z : ℕ × GBits s) => GBits.RecutOK P (show GBits (c.snd :: s) from z)
  | _, .msg r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) =>
      z.1 = 0 ∧ GBits.RecutOK P (show GBits (r1.joinMsg r2 :: s) from z.2)
  | _, .chal r1 r2 (s := s) _ P =>
    fun (z : ℕ × ℕ × GBits s) =>
      GBits.RecutOK P (show GBits (r1.joinChal r2 :: s) from (max z.1 z.2.1, z.2.2))

theorem GBits.recutOK_keepAll : ∀ {s : Shape} (g : GBits s), GBits.RecutOK (XPlan.keepAll s) g
  | [], _ => trivial
  | _ :: _, (_, g) => GBits.recutOK_keepAll g

theorem GBits.recutOK_app {s t : Shape} (P : XPlan s) (Q : XPlan t)
    (g' : GBits t) (hQ : GBits.RecutOK Q g') :
    ∀ g : GBits s, GBits.RecutOK P g → GBits.RecutOK (XPlan.app P Q) (GBits.app g g') := by
  induction P with
  | nil => intro _ _; exact hQ
  | keep r P ih => exact fun g h => ih g.2 h
  | cut c P ih => exact fun g h => ih g h
  | msg r1 r2 u P ih => exact fun g h => ⟨h.1, ih g.2 h.2⟩
  | chal r1 r2 np P ih => exact fun g h => ih (max g.1 g.2.1, g.2.2) h

/-- A chain of splits asks nothing: `RecutOK` for `p.thenX X` follows from `RecutOK` for X. -/
theorem GBits.recutOK_thenX {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s))
    (g : ℕ × GBits s) (h : GBits.RecutOK X (show GBits (p.last :: s) from g)) :
    GBits.RecutOK (p.thenX X) (show GBits (r :: s) from g) := by
  induction p with
  | keep r => exact h
  | cut c rest ih => exact ih X h

/-- The list of zeros satisfies the side condition, and stays the list of zeros (`recut_zero`). -/
theorem GBits.recutOK_zero {s : Shape} (P : XPlan s) : GBits.RecutOK P (GBits.zero s) := by
  induction P with
  | nil => trivial
  | keep r P ih => exact ih
  | cut c P ih => exact ih
  | msg r1 r2 u P ih => exact ⟨rfl, ih⟩
  | chal r1 r2 np P ih => exact ih

theorem GBits.recut_zero {s : Shape} (P : XPlan s) :
    GBits.recut P (GBits.zero s) = GBits.zero P.shape := by
  induction P with
  | nil => rfl
  | keep r P ih => exact congrArg (Prod.mk 0) ih
  | cut c P ih => exact congrArg (Prod.mk 0) ih
  | msg r1 r2 u P ih => exact ih
  | chal r1 r2 np P ih => exact ih

/-- A bound on all numbers of proof-of-work bits is preserved. -/
theorem GBits.AllLe.recut {n : ℕ} {s : Shape} (P : XPlan s) :
    ∀ g : GBits s, g.AllLe n → (g.recut P).AllLe n := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih => exact fun g h => ⟨h.1, ih g.2 h.2⟩
  | cut c P ih => exact fun g h => ⟨Nat.zero_le n, ih g h⟩
  | msg r1 r2 u P ih => exact fun g h => ih g.2 h.2
  | chal r1 r2 np P ih => exact fun g h => ih (max g.1 g.2.1, g.2.2) ⟨max_le h.1 h.2.1, h.2.2⟩

theorem GBits.AllLe.pull {n : ℕ} :
    ∀ {s : Shape} (σ : Samplers s) {g : GBits s}, g.AllLe n → (g.pull σ).AllLe n
  | [], _, _, _ => trivial
  | _ :: _, (_, σs), (_, _), h => ⟨h.1, GBits.AllLe.pull σs h.2⟩

/-! ## One proof of work must not pay for several samples: two lemmas -/

/-- In a merge of challenges that satisfies `XPlan.OK` the second prover message has one value:
between the two parts of the merged challenge the prover chooses nothing. -/
theorem XPlan.chal_second_one_value {r1 r2 : Round} {s : Shape} {np : r2.Pos → Empty}
    {P : XPlan (r1.joinChal r2 :: s)} (h : (XPlan.chal r1 r2 np P).OK) :
    ∀ m : r2.Msg, m = r2.dMsg := h.1

/-- In a plan that satisfies `AXPlan.Late` at the round in whose query the whole request is put,
that round is not the second round of a merge at the plan's first step, of challenges or of prover
messages: `AXPlan.Late` is false at 1. -/
theorem AXPlan.late_not_second {r1 r2 : Round} {s : Shape} (A : RoundSplits (r1 :: r2 :: s)) :
    (∀ (np : r2.Pos → Empty) (P : XPlan (r1.joinChal r2 :: s))
          (Z : AXPlan (XPlan.chal r1 r2 np P) A),
        ¬ AXPlan.Late (XPlan.chal r1 r2 np P) A Z 1) ∧
    (∀ (u : r1.Chal) (P : XPlan (r1.joinMsg r2 :: s)) (Z : AXPlan (XPlan.msg r1 r2 u P) A),
      ¬ AXPlan.Late (XPlan.msg r1 r2 u P) A Z 1) :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h⟩

end Iop
