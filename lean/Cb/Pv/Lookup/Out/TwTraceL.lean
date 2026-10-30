-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwTraceL.lean.
The flat trace, cut at its steps. Lists alone.

Main name:
  `traceOfFlat_of`: on rounds that begin with the draw of lam: if the tie's loop, the two trees'
    loops, the closing's sumcheck and the bit test's sumcheck give the named values, each on what
    the step before it left of the rounds (five premises), then `TwV.traceOfFlat N` is the record
    of these values.
Limits: a frame: it says nothing until its five premises are filled (`state_eq7`,
Cb/Pv/Lookup/Out/TwState.lean). What is left of the rounds at the end (r6) is ignored.

-/
import Cb.Pv.Lookup.Out.TwV

set_option autoImplicit false

namespace Tw
open TwV

theorem traceOfFlat_of {P K : Type} [CommRing K] (N : Nums P K) (lam : K) (r1 r2 r3 r4 r5 r6 :
    Rounds K)
    (tieL : List (Sc K)) (join : List K) (keysL : List (Sc K × K)) (kT : K) (kp : List K)
    (tabL : List (Sc K × K)) (tg : K) (pt : List K) (cls : Sc K) (zero : List K) (bits : Sc K)
    (h1 : tieGo (N.n + 1) 0 0 r1 = (tieL, ([], join) :: r2))
    (h2 : lvGo N.oK (N.v' + 1) 0 (tK (⟨lam, tieL, join, [], 0, [], Sc.zero, [], Sc.zero⟩ : Trace K))
        []
      r2 = (keysL, kT, kp, r3))
    (h3 : lvGo N.oT N.d 0 (tgT0 N (⟨lam, tieL, join, [], 0, [], Sc.zero, [], Sc.zero⟩ : Trace K))
        join
      r3 = (tabL, tg, pt, r4))
    (h4 : takeSc r4 tg (inRounds N.oE pt) false = (cls, ([], zero) :: r5))
    (h5 : takeSc r5 0 (inRounds N.oB zero ++ [0]) true = (bits, r6)) :
    traceOfFlat N (([], [lam]) :: r1) = ⟨lam, tieL, join, keysL, kT, tabL, cls, zero, bits⟩ := by
  unfold traceOfFlat
  simp only [List.headD_cons, List.tail_cons, h1, h2, h3, h4, h5]

end Tw
#print axioms Tw.traceOfFlat_of
