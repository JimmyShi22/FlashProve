-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GoodInErr.lean: WHAT A PIECE OWES AT ITS ERRORS IT OWES AT ALL GREATER ERRORS.
One small lemma and its call at the cap.

Why. The pieces of a file's real rows carry the cap as their errors (`Err.cap 128`, Iop/ErrCap.lean:
at each round the number of the round's challenges / 2 ^ 128). A kind proves its law at its own
counts, shows these to lie below the cap round by round (`Err.le`), and goes up by this lemma.

Main names:
  `goodIn_err`: `p.GoodIn on on' R R'` and `Err.le p.err ε` give `{ p with err := ε }.GoodIn …`, at
    the same promises, relations and extractor. By `Doomed.mono_err` (Iop/Rbr.lean).
  `goodIn_atCap`: that at ε := the cap.

Limits: that a kind's counts lie below the cap is a premise: a fact on the plan's numbers, shown
here of no round. THE CAP IS A WHOLE NUMBER: at a round that writes fewer than 2 ^ 128 challenges it
is 0, and a kind with one bad challenge there cannot go up by this lemma. Nothing on acceptance;
nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **What a piece owes at its errors it owes at all greater errors.** -/
theorem goodIn_err (p : Piece C F S Cl W) (ε : Err (uLT C p.ds)) (h : Err.le p.err ε)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    ({ p with err := ε } : Piece C F S Cl W).GoodIn on on' R R' :=
  fun a ha => Doomed.mono_err _ h (g a ha)

/-- At the cap. -/
theorem goodIn_atCap (p : Piece C F S Cl W) (h : Err.le p.err (Err.cap 128 (uLT C p.ds)))
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    ({ p with err := Err.cap 128 (uLT C p.ds) } : Piece C F S Cl W).GoodIn on on' R R' :=
  goodIn_err p _ h on on' R R' g


end VerifiableInference.Desc.Sound
