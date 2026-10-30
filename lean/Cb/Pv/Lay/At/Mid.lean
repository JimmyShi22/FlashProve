-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Mid.lean: the stages of a layers' sub-proof's own rounds up to the batched sumcheck of
the inner products (Mid, Cb/Pv/Lay/OwnAll.lean) at a value, with its law link proved.

Main names:
  `MidPar`: over the letters of Cb/Pv/Lay/At/Fore.lean: that the cells are read linearly off the
    entries (hrd); that an expert has no more hidden units than a layer (hfe); the places of the
    batched sumcheck's masks.
  `ip`: the letters of Cb/Pv/Lay/At/Inner.lean from these; the affine side of the join as a form in
    the entries is that of Cb/Pv/Lay/At/Line.lean.
  `st4`: the state of the batched sumcheck, read off the chain's statement: the lookup's point and
    leavings of the first statement, the sent sum of the terms, the output of the terms' sumcheck,
    the element drawn.
  `mid_link`: the field link: the sum claim of the batched sumcheck gives that the batch of the two
    gaps is 0: by link_of (Start.lean), lineS_form (Line.lean) and inn_hc (InnerSum.lean).
  `mid`: the record; which coefficient of a round is left out is pick's choice
    (Cb/Pv/Lay/Merge.lean): the linear one in a plain variable, the constant one in the further
    variable. That this choice is lawful for these parameters is not shown here.

Limits: that the programs' records are these is not said here. Nothing is said on an honest prover
or on hiding.


-/
import Cb.Pv.Lay.At.Fore
import Cb.Pv.Lay.At.InnerSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW)

noncomputable section

/-- The letters of the stages up to the batched sumcheck that stay free, beside At/Fore.lean's. -/
structure MidPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends ForePar E M X where
  /-- the cells are read linearly off the entries -/
  hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
    rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c
  /-- an expert has no more hidden units than a layer -/
  hfe : D.fe ≤ D.f
  /-- the masks of the batched sumcheck -/
  wI : PIdx (ldPartFmt E (kS D) (fun _ => 2) ++ [pDummy E 2]) → J
  cI : IA D ⊕ IB D → J

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace MidPar
variable (P : MidPar E M X)

/-- The letters of the batched sumcheck. -/
@[reducible] def ip : InnPar0 E where
  T := P.tp
  lnTg := lnTg P.D P.tb P.L0 P.rd
  lnInc := lnInc P.D P.tb P.L0 P.rd
  wI := P.wI
  cI := P.cI

variable {X' : Type} (x0 : X' → X) (pv : X' → Fin P.D.lT → E) (Rd0 : X' → M → Prop)

/-- The state of the batched sumcheck, read off the chain's statement. -/
def st4 (y : (P.fore x0 pv Rd0).s3.Nx × E) : P.ip.St where
  z := P.zOf (x0 ((P.fore x0 pv Rd0).x3 y.1))
  kTg := P.kTg (x0 ((P.fore x0 pv Rd0).x3 y.1))
  kInc := P.kInc (x0 ((P.fore x0 pv Rd0).x3 y.1))
  s := (y.1.1.2 : Fin 1 → E) 0
  o3 := y.1.2
  β := y.2

open Classical in
/-- **The law link.** -/
theorem mid_link (b : (P.fore x0 pv Rd0).s3.Nx) (β : E) (m : M)
    (h : P.ip.inn.toSum.T.par.SumHolds
      (P.ip.inn.tg (P.st4 x0 pv Rd0 (b, β)), P.st4 x0 pv Rd0 (b, β)) (P.msg m)) :
    (P.fore x0 pv Rd0).g0 b m + β * (P.fore x0 pv Rd0).g1 b m = 0 := by
  have hs := (P.ip.inn.sum_iff (P.st4 x0 pv Rd0 (b, β)) (P.msg m)).1
    ((psc_our_sum E P.ip.inn.toSum.T _ _).1 h)
  exact link_of P.ip.Y3 P.ip.lnTg P.ip.lnInc P.rT (P.st4 x0 pv Rd0 (b, β)) (P.msg m) _
    (accS P.D (P.rd (P.msg m)) (P.rw (P.msg m)) (P.st4 x0 pv Rd0 (b, β)).z)
    (lineS P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.st4 x0 pv Rd0 (b, β)).z)
    (lineS_form P.D P.tb P.L0 P.rd P.hrd _ _ _)
    (P.ip.inn_hc P.hfe (P.st4 x0 pv Rd0 (b, β)) (P.msg m)) hs

/-- The stages up to the batched sumcheck, at statements X'. -/
def mid : Mid E M X' where
  toFore := P.fore x0 pv Rd0
  In := P.ip.inn
  st4 := P.st4 x0 pv Rd0
  rd4 := P.msg
  F4 := fun st => pick (P.ip.inn.toSum.T.par.vars st)
  link := P.mid_link x0 pv Rd0

end MidPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.MidPar.mid_link
