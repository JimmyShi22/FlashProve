-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecKit.lean: this file is book-keeping: an interactive oracle proof, or reduction, with its
explicit input or output re-indexed along a function.
In this library's words: the same protocol on other instances.

Terms only, for Hiop/RecInterface.lean and the other files that import this one. No protocol of this
library occurs here.

Why: an encoded index may have a record (Hiop/RecInterface.lean), which joins the explicit instance
of every later protocol on that encoded index. So the same verifier is looked at in two ways: on
instances (x, record), and, for a fixed record, on instances x. The passage is "read x' as f x'".

Main names:
  `Q.comap f`: an IOP (Iop/InteractiveOracleProof.lean), a batch IOP (Iop/Batch.lean): same shape by definition, so
    that lists of errors, transcripts and sets of verifier messages carry over unchanged.
  `H.comap f g`: their honest sides: the instance x' is read as f x', the private input w' as g w'.
  `R.comapX f`, `Q.comapX f`: an IOR (Ior/Ior.lean), a batch IOP given as an IOR (Ior/Batch.lean):
    the explicit part of the input is read through f.
  `R.mapOut g`: the explicit part of the output is mapped by g.

Limits: no property is stated here; rules of transport are in Hiop/RecKitSound.lean (soundness and
knowledge soundness) and Hiop/RecKitHonest.lean (the honest side and the formats of IOPs and batch
IOPs).

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch

set_option autoImplicit false

namespace Iop
open Prob

variable {X X' : Type} {E : ExtSpec}

/-- The same IOP on other instances: x' is read as f x'. -/
def InteractiveOracleProof.comap (Q : InteractiveOracleProof X E) (f : X' → X) : InteractiveOracleProof X' E where
  shape := Q.shape
  blinded := Q.blinded
  extReads := fun x => Q.extReads (f x)
  reads := fun x => Q.reads (f x)
  accept := fun x => Q.accept (f x)

/-- The same for a batch IOP: every slot's instance is read through f. -/
def BatchInteractiveOracleProof.comap (Q : BatchInteractiveOracleProof X E) (f : X' → X) : BatchInteractiveOracleProof X' E where
  loc := Q.loc.comap f
  ann := Q.ann

/-- The honest side: the instance is read through f, the private input through g. -/
def Honest.comap {Q : InteractiveOracleProof X E} {Wt Wt' : Type} (H : Honest Q Wt) (f : X' → X) (g : Wt' → Wt) :
    Honest (Q.comap f) Wt' where
  Coin := H.Coin
  ext := fun w => H.ext (g w)
  strat := fun w x c => H.strat (g w) (f x) c
  Bad := H.Bad
  Hid := fun w x => H.Hid (g w) (f x)

def BatchHonestProver.comap {Q : BatchInteractiveOracleProof X E} {Wt Wt' : Type} (H : BatchHonestProver Q Wt)
    (f : X' → X) (g : Wt' → Wt) : BatchHonestProver (Q.comap f) Wt' where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := fun w => H.ext (g w)
  strat0 := fun w c0 => H.strat0 (g w) c0
  strat := fun w c0 x c => H.strat (g w) c0 (f x) c
  Bad := H.Bad
  Hid := fun w x => H.Hid (g w) (f x)
  stop0 := H.stop0

namespace IOR
variable {Xi Xi' Xo Xo' : Type} {Ei Eo : ExtSpec}

/-- The same IOR, the explicit part of its input read through f. -/
def comapX (R : IOR Xi Ei Xo Eo) (f : Xi' → Xi) : IOR Xi' Ei Xo Eo where
  shape := R.shape
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out := fun x => R.out (f x)
  imp := R.imp
  srcE := R.srcE
  srcO := R.srcO
  tie := R.tie

/-- The explicit part of its output mapped by g. -/
def mapOut (R : IOR Xi Ei Xo Eo) (g : Xo → Xo') : IOR Xi Ei Xo' Eo where
  shape := R.shape
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out := fun x y τ => (R.out x y τ).map g
  imp := R.imp
  srcE := R.srcE
  srcO := R.srcO
  tie := R.tie

end IOR

/-- The same for a batch IOP given as an IOR. -/
def BIOP.comapX (Q : BIOP X E) (f : X' → X) : BIOP X' E where
  ior := Q.ior.comapX f
  ann := Q.ann

end Iop
