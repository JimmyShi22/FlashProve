-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Bound/Base.lean: the integer model at a variable prime: the one size condition on the
prime, and the tools of the proofs that nothing wraps around.

The model's constraints are checked modulo a prime p. This file serves the proofs that they imply,
under the hypotheses of their statements, the computation over the integers, without overflow
modulo p.
Definitions, small lemmas and their proofs.
Why: the theorems that are stated at `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean) stand over the prime
2^64 - 2^32 + 1. The third key of a margin in the head is written with no inverse of a power of two
(Cm/TargetPHead.lean, Policy/Rel/LedgerHead.lean). The proofs of Inst/Model and Cm/ use of the prime
one thing: a multiple of p that is smaller than p in absolute value is 0, at quantities that are all
below 2^61 - 1. So they hold for every p from 2^61 - 1 on (as stated: for every such
number p in the files Cm/TargetInst*.lean, Inst/Model/Bound/*.lean but Cm/TargetInstFFK.lean; for
such a prime p there, in Cm/TargetPLayers.lean and in `Cm.TP.Spec`, Cm/TargetPRel.lean). The other
files Cm/TargetInst*.lean, Inst/Model/Bound/*.lean hold the parts of files of Inst/Model that read
the modulus; each head names its file.

Main names:
  `Big p`: the size condition: 2^61 - 1 ≤ p. A class, so that those files need no further
    argument; every statement for quoting has it as a plain hypothesis (Cm/TargetP*.lean) (those of
    Cm/TargetPRel.lean, Cm/TargetPLangs.lean that need it: not `Cm.TP.Spec.sub`, for every p; not
    `Cm.Spec.target_p_guards`, at `Cb.Gl.p`).
  `big_int`, `big_pow`: the same among integers.
  `eq_of_dvd`: under `Big p`, if p divides a - b and |a - b| < 2^61 - 1, then a = b. The bound is
    the numeral 2^61 - 1, not p: so a step that ends in "|a - b| < 2^61 - 1" holds at every such p.
  `mul_big`: see its docstring.
  `Unit.Adm.mono`, `Router.Adm.mono`, `Ledger.Adm.mono`, `AdmN.mono`, `AdmP.mono`, `AdmS.mono`: the
    records of size conditions of Inst/Model read ".. ≤ p" or ".. < p": they go up with p.

Limits: this file says nothing on a prime below 2^61 - 1 (but for the six `.mono` theorems, which
are for all integers p ≤ p'). It does not say that 2^61 - 1 is the least bound that serves: it is
the bound at which the proofs of Inst/Model stand.
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.FF.NoWrapStream
import Inst.Model.Att.NoWrap0
import Inst.Model.Common.Router
import Inst.Model.Common.Unit

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TI

open Inst.Model

/-- The size condition on the prime. -/
class Big (p : ℕ) : Prop where
  le : 2 ^ 61 - 1 ≤ p

section
variable (p : ℕ) [hB : Big p]

theorem big_int : (2305843009213693951 : ℤ) ≤ (p : ℤ) := by
  have h : 2 ^ 61 - 1 ≤ p := hB.le
  norm_num at h
  exact_mod_cast h

theorem big_pow : (2 ^ 61 - 1 : ℤ) ≤ (p : ℤ) := by
  have e : (2 ^ 61 - 1 : ℤ) = 2305843009213693951 := by norm_num
  rw [e]
  exact big_int p

variable {p}

/-- Under `Big p`, a multiple of p that is below 2^61 - 1 in absolute value is 0. -/
theorem eq_of_dvd {a b : ℤ} (h : (p : ℤ) ∣ a - b) (hlt : |a - b| < 2 ^ 61 - 1) : a = b :=
  AttSeg.NW.eq_of_dvd h (lt_of_lt_of_le hlt (big_pow p))

variable (p)

/-- Under `Big p`, a multiple of p is 0 or at least 2^61 - 1 in absolute value. -/
theorem mul_big (k : ℤ) :
    k = 0 ∨ 2305843009213693951 ≤ (p : ℤ) * k ∨ (p : ℤ) * k ≤ -2305843009213693951 := by
  have h := big_int p
  rcases lt_trichotomy k 0 with hk | hk | hk
  · right; right
    nlinarith
  · exact Or.inl hk
  · right; left
    nlinarith

end

theorem Unit.Adm.mono {p p' B1 B2 Ab : ℤ} {kg ku : ℕ}
    (a : Inst.Model.Unit.Adm p B1 B2 Ab kg ku) (h : p ≤ p') :
    Inst.Model.Unit.Adm p' B1 B2 Ab kg ku :=
  { kg24 := a.kg24, ku24 := a.ku24, g0 := le_trans a.g0 h, ut := le_trans a.ut h,
    hi := le_trans a.hi h, fl := le_trans a.fl h, flG := a.flG, cg := le_trans a.cg h, cgG := a.cgG,
    g := le_trans a.g h, u := le_trans a.u h }

theorem Router.Adm.mono {p p' B1 B2 B3 Ab Lb Mb : ℤ} {kr nx : ℕ}
    (a : Inst.Model.Router.Adm p B1 B2 B3 Ab Lb Mb kr nx) (h : p ≤ p') :
    Inst.Model.Router.Adm p' B1 B2 B3 Ab Lb Mb kr nx :=
  { kr24 := a.kr24, b1pos := a.b1pos, l3 := le_trans a.l3 h, sel := le_trans a.sel h,
    lt := le_trans a.lt h, hi := le_trans a.hi h, lr := le_trans a.lr h, quot := a.quot,
    clr := le_trans a.clr h, clrG := a.clrG, j10 := lt_of_lt_of_le a.j10 h, dd := le_trans a.dd h,
    mr := le_trans a.mr h, xr := le_trans a.xr h }

theorem Ledger.Adm.mono {p p' : ℤ} {np : NormPar} {d : ℕ} {c : ℤ}
    (a : Inst.Model.Ledger.Adm p np d c) (h : p ≤ p') :
    Inst.Model.Ledger.Adm p' np d c :=
  { eps_pos := a.eps_pos, eps_lt := a.eps_lt, M_le := a.M_le, c_pos := a.c_pos,
    row := lt_of_lt_of_le a.row h, j1 := le_trans a.j1 h, big := le_trans a.big h }

section
variable [scl : Scl]
open Inst.Model.FFSeg

theorem AdmN.mono {p p' : ℤ} {D : Dim} (a : AdmN p D) (h : p ≤ p') : AdmN p' D :=
  { big := le_trans a.big h, led1 := fun l => Ledger.Adm.mono (a.led1 l) h,
    led2 := fun l => Ledger.Adm.mono (a.led2 l) h, ok1 := a.ok1, ok2 := a.ok2 }

theorem AdmP.mono {p p' : ℤ} {D : Dim} {tb : Tables} {L0 : ℕ} {w : ℕ → LayerW}
    (a : AdmP p D tb L0 w) (h : p ≤ p') : AdmP p' D tb L0 w :=
  { big := le_trans a.big h, kq := a.kq, kk := a.kk, kv := a.kv, wq := fun l => le_trans (a.wq l) h,
    wk := fun l => le_trans (a.wk l) h, wv := fun l => le_trans (a.wv l) h, even := a.even,
    T := a.T, layers := a.layers, tab := a.tab, wf := a.wf }

theorem AdmS.mono {p p' : ℤ} {D : Dim} {L0 : ℕ} {w : ℕ → LayerW} (a : AdmS p D L0 w) (h : p ≤ p') :
    AdmS p' D L0 w :=
  { ko := a.ko, kd := a.kd, hi := le_trans a.hi h, o := fun l => le_trans (a.o l) h,
    d := fun l => le_trans (a.d l) h, even := a.even, f := a.f, nexp := a.nexp, wf := a.wf }

end

end Cm.TI
