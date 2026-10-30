-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ForkKept.lean: the kind «the code switch»: a yes of the switch's decision
leaves the
sub-proof's ledger as it was: the reading S.fork? says behind the block what it said in front, at
each
of the three sorts of place. NO BLOCK IMPORTS THIS FILE.
  fork_kept    decideWith snd p s rs gs = .ok s' → s'.fork? = s.fork?
  next_kept    … → (s'.fork?).map (·.next) = (s.fork?).map (·.next)      (the form that K4's law
      asks)
Why it holds: at a link the switch runs while the record stands between the links and leaves «here»
(S.fork? answers nothing on both sides: the ledger is laid behind the switch, by the frame's own
step);
at the head's link it writes «kept» and «ids» of the head's own part alone; at the finish «sw»
alone.
A frame fact: it says what the text does not write. No Mathlib. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

theorem fork_kept {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (h : decideWith snd p s rs gs = .ok s') :
    s'.fork? = s.fork? := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, _, k⟩ := link_inv hp h
    rw [k.hOut]
    rfl
  · obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h
    rw [k.hOut]
    simp [S.fork?, k.hHere]
  · obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := finish_inv hp h
    rw [k.hOut]
    simp [S.fork?, k.hHere]

theorem next_kept {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (h : decideWith snd p s rs gs = .ok s') :
    (s'.fork?).map (·.next) = (s.fork?).map (·.next) := by
  rw [fork_kept h]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.fork_kept
#print axioms VerifiableInference.Desc.First.K2.next_kept
