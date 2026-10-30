-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/PadLS.lean: THE LOOKUP: ITS HEARING TURNS NEITHER THE LEDGER's COEFFICIENTS OF
THE ONE EQUATION (the field LS) NOR ITS NUMBER OF SLOTS (ns): behind a return of the flat lkPad
from a ledger that has its sizes. A statement with its proof.

OBJECT: the flat lkPad (OnBytes/K/Kc/FlatHear.lean): the ledger F' that it returns.
Used by Johnson/Top/H/Keep/RunsPutFork.lean (same_LS, same_ns).
LETTERS: calls, pub, lid, F, t, u free.
Compiled with the whole library.

Main names:
  same_LS, same_ns: of two ledgers that differ at most in what lies under the slots.
  lkPad_LS.

Limits. From a return alone. Two fields alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PadExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem same_LS {F G : Fork} (h : Same F G) : G.LS = F.LS := by
  have e : G = { F with vp := G.vp, mf := G.mf, gotF := G.gotF } := h
  exact (congrArg Fork.LS e).trans rfl

theorem same_ns {F G : Fork} (h : Same F G) : G.ns = F.ns := by
  have e : G = { F with vp := G.vp, mf := G.mf, gotF := G.gotF } := h
  exact (congrArg Fork.ns e).trans rfl

theorem lkPad_LS (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F) :
    F'.LS = F.LS ∧ F'.ns = F.ns := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  have sA := (R.f4 ▸ R.tieSt).trans ((⟨R.keys.same, R.keys.filled, R.keys.out⟩ :
      Stretch M.F5 M.F6 _).trans ⟨R.table.same, R.table.filled, R.table.out⟩)
  have sB := R.r5.stretch
  rw [P.fork]
  have a0 := same_LS sA.same
  have a1 : M.F7.LS = F.LS := a0
  have a3 := same_LS sB.same
  have a2 : M.G8.LS = M.F7.LS := a3
  have b0 := same_ns sA.same
  have b1 : M.F7.ns = F.ns := b0
  have b3 := same_ns sB.same
  have b2 : M.G8.ns = M.F7.ns := b3
  exact ⟨a2.trans a1, b2.trans b1⟩

end Fo.Tp

#print axioms Fo.Tp.lkPad_LS
