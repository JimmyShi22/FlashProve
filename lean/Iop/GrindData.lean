-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindData.lean: the serializers of a record of protocols (`BatchProtocol`, Iop/Batch.lean) with
proof-of-work bits ("grinding": Iop/Grind.lean, Iop/BatchGrind.lean), from those of the record
without them and a serializer sW of nonces. Data. (Words of this library: lean/GLOSSARY.md.)
Positions, alphabets and oracles of a round do not change, so the serializer of (position, symbol)
is the old one; the plain part of a round with such bits is (old plain part, nonce).
    `Ser.gPlain sP sW b`    the serializer of `GPlain W b P`: at b = 0 the old serializer itself;
                            else the old plain part, then the nonce
    `SerA.grind`            for each round of a protocol with slots, the serializers of its two
                            plain parts, that of the shared component and that of the slot's
                            component: the nonce is in the shared component's in a shared round, in
                            the slot's in a local round (`Kind.b0`, `Kind.bJ`, Iop/BatchGrind.lean).
                            In the words of Iop/SerB.lean's head: a round is shared or local (its
                            kind), and its annotation (`RAnn`, Iop/Batch.lean) divides the prover
                            message into a shared component and the slot's component.
That every round's oracle part is a string (`Shape.IsPoint`, Iop/Shape.lean) is carried over by
`Shape.IsPoint.grind` (Iop/GrindProofs.lean); wire records and the compiler's other data by
Iop/GrindWire.lean.
-/
import Iop.BatchGrind
import Iop.SerB

set_option autoImplicit false

namespace Iop

variable {W : Type}

/-- The serializer of a plain part with a nonce. -/
def Ser.gPlain {P : Type} (sP : Ser P) (sW : Ser W) : (b : ℕ) → Ser (GPlain W b P)
  | 0 => sP
  | _ + 1 => Ser.prod sP sW

variable [Inhabited W]

def SerR.grind {r : Round} (a : SerR r) (sW : Ser W) (b : ℕ) : SerR (r.grind W b) :=
  (a.1, Ser.gPlain a.2 sW b)

def SerS.grind (sW : Ser W) : {s : Shape} → SerS s → (g : GBits s) → SerS (s.grind W g)
  | [], _, _ => ()
  | _ :: _, (a, e), (b, g) => (SerR.grind a sW b, SerS.grind sW e g)

def SerA.grind (sW : Ser W) :
    {s : Shape} → (A : RoundSplits s) → SerA s A → (g : GBits s) → SerA (s.grind W g) (A.grind W g)
  | [], _, _, _ => ()
  | _ :: _, (a, A), (e, es), (b, g) =>
    ((Ser.gPlain e.1 sW (a.kind.b0 b), Ser.gPlain e.2 sW (a.kind.bJ b)), SerA.grind sW A es g)

variable {I X : Type} {L : BatchProtocol I X}

/-- The serializers of the record with proof-of-work bits. -/
def SerLHB.grind (D : SerLHB L) (sW : Ser W) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    SerLHB (L.grind W gT gL gB) where
  tag := D.tag
  x := D.x
  sg := D.sg
  T := SerS.grind sW D.T gT
  Lk := SerS.grind sW D.Lk gL
  O := SerS.grind sW D.O gB
  A := SerA.grind sW L.onlineBatch.ann D.A gB

end Iop
