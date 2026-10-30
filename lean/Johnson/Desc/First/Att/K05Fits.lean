-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Fits.lean: the library's premise Fits (Cb/Pv/Att/End/Cl.lean: twenty
fields) at the closed parameters
with the meant linear claims (Att/K05Meant.lean), at the library's own record of the late entries'
names
(End/Names.lean: lateN: the late entries are just the names that the ten records call good).

Main names:
  `endLay`: the letters of the end: the cells' places are the base parameters', beside the ledger's
    slots; the tables' two
    block sizes; the names lateN.
  `closed_fits`: Fits, from seven premises on the base parameters and public numbers: the cells are
    read at given
    places; the two block sizes are small enough; the first two calls have one size; a plane family
      fits its call; a
    position has at most 2 ^ kap bits; two plane messages.

Limits: that the programs' late message has just these entries at these names is said nowhere
(End/Names.lean's own limit).
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.Names
import Cb.Pv.Att.End.Cl
import Johnson.Desc.First.Att.K05Meant

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb.Pv.Att Inst.Model
open Cb.Pv.Att.End

variable {K : Type} [Field K] [Fintype K] {M0 X Mg : Type}

/-- The letters of the end at the closed parameters. -/
noncomputable def endLay (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (cellJ0 : AttSeg.Raw → P0.J)
    (ls lmS : ℕ) (j0 : NameJ P0.D ls lmS) : EndLay (closedOf P0 Λ ns N) (NameJ P0.D ls lmS) where
  cellJ := fun c => Sum.inr (cellJ0 c)
  ls := ls
  lmS := lmS
  Y := lateN P0.D ls lmS j0

open Classical in
/-- **Fits at the closed parameters with the meant claims.** -/
theorem closed_fits (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N))
    (cellJ0 : AttSeg.Raw → P0.J) (ls lmS : ℕ) (j0 : NameJ P0.D ls lmS) (hrd : ∀ e, P0.rd e = rdOf cellJ0 e)
    (hls : ls ≤ P0.D.ln) (hlm : ∀ u : AttSeg.Fam, IsPlane u → lmS ≤ u.l P0.D) (ha : P0.C.a 0 = P0.C.a 1)
    (hla : ∀ u : AttSeg.Fam, IsPlane u → u.l P0.D ≤ P0.C.a u.call) (hk : P0.D.lT ≤ 2 ^ P0.kap) (hn : P0.npl = 2) :
    Fits (endLay P0 (meantLin P0 Λ0 ns N Q) ns N cellJ0 ls lmS j0) (meantQ P0 Λ0 ns N Q) where
  rd := fun e => hrd fun j => e (Sum.inr j)
  ls := hls
  lmS := hlm
  a01 := ha
  la := hla
  kap := hk
  npl := hn
  gLin := names_lin P0.D ls lmS j0
  g6b := names6b P0.D ls lmS j0
  g6d := names6d P0.D ls lmS j0
  g8 := names8 P0.D ls lmS j0
  g11 := names11 P0.D ls lmS j0
  g12 := names12 P0.D ls lmS j0
  gM := namesM P0.D ls lmS j0
  g16 := names16 P0.D ls lmS j0
  g18 := names18 P0.D ls lmS j0
  gH := namesH P0.D ls lmS j0
  LM := meant_LM P0 Λ0 ns N Q
  LD := meant_LD P0 Λ0 ns N Q
  LE := meant_LE P0 Λ0 ns N Q

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_fits
