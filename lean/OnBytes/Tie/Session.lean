-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Session.lean: a chain read in a session, and the compiled verifier of the library's
theory.

The program reads the chains of one verdict in a session (`readIn`, OnBytes/Chain/Session.lean),
with fast forms of the hash, of the reader and of the record of tree vertices. It decides on the
views afterwards. This file joins two things. The fast forms are equal to those of the directory
Fmt/ (theorems of OnBytes/Chain/ and OnBytes/Hash/). And what the strict reader has read, if a
decision says yes on its view, the compiled verifier accepts (OnBytes/Tie/OneChain.lean).

Main theorems: `readIn_read`, `readIn_compiled`.
It holds for chains that break no limit of OnBytes/Tie/Limits.lean. It claims nothing on soundness.
-/
import OnBytes.Chain.SessionLaws
import OnBytes.Tie.OneChain

set_option autoImplicit false

namespace OnBytes.Tie

/-- What a reading step of a session returns is what the strict reader of Fmt/ reads at the
format's own hash, and its view. -/
theorem readIn_read (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s s' : Session) (r : ChainRead)
    (e : readIn S b i s = some (r, s')) :
    Fmt.readChainX (m := Id) Fmt.formatHash S s.seen b i = some (r.out, r.next) ∧
      r.view = Fmt.viewX S r.out := by
  refine ⟨?_, readIn_view S b i s s' r e⟩
  have t1 := readIn_eq S b i s.seen
  have t2 : readIn S b i ⟨s.seen⟩ = some (r, s') := e
  rw [t2] at t1
  cases hx : Fmt.readChainX (m := Id) Fmt.formatHash S s.seen b i with
  | none => rw [hx] at t1; cases t1
  | some x =>
    rw [hx] at t1
    have t3 := Option.some.inj t1
    have e1 : r.out = x.1 := congrArg (·.1) t3
    have e2 : r.next = x.2 := congrArg (·.2.1) t3
    rw [e1, e2]

/-- If a chain that breaks no limit was read in any state of a session, anywhere in a file below
about 2^32 bytes, and a decision says yes on its view, the compiled verifier of the protocol made
from its description and that decision accepts what was read. -/
theorem readIn_compiled (S : Fmt.SpecX) (dec : Fmt.View → Bool) (hl : limitsOfX S = [])
    (s : Session) (b : ByteArray) (i : Nat) (hb : b.size + 16 ≤ 2 ^ 32 - 144) (r : ChainRead)
    (s' : Session) (e : readIn S b i s = some (r, s')) (hd : dec r.view = true) :
    CompiledAccepts S.base dec r.out := by
  obtain ⟨h1, h2⟩ := readIn_read S b i s s' r e
  rw [h2] at hd
  exact plain_compiled S dec hl s.seen b i hb r.out r.next h1 hd

end OnBytes.Tie

#print axioms OnBytes.Tie.readIn_compiled
