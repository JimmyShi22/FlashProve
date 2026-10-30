-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/SerThin.lean: a total code of all real and ghost points of the compiled scheme's oracles, in a
form made for the evaluator: the interface behind a function of `Unit`; no recursion on a shape.

Definitions that compute (the laws are those of the library's serialisers: Iop/Ser.lean).
A total code (`StrCode`, Rom/Hotel.lean) writes every point as a bit string, injectively, with a
parser. The real and the ghost points: `AllPts`, Run/CodingImpl.lean.

Why: the encoding of Run/CodingPage.lean writes every typed point that the programs' format does not
write behind an escape, by any total code ("back"). The first exit to a single oracle
(`OComp.overOne`, Rom/Family.lean) asks all blocks of an answer, so also the message blocks of round
0, which the format does not have: so "back" is called in a run. The library's own total code
(`serReal`, `serGhost`, Compile/Batch/Ser.lean) has the interface (`BatchProtocol`, Iop/Batch.lean) as a
parameter and goes through the shapes round by round: tried, with a trace in a round's instance: it
builds the list of all verifier messages.
Here the same definitions, at lam = 256 and without the tag in front, with the interface behind a
function of `Unit` (Lf, explicit and first), and the serialisers of symbols and of plain parts given
as data, one for each of the three protocols.

Main names:
  `SerP Lf`: x (the instance), sg (a symbol of an encoded index), sym t (a symbol with its
    position), pb t (a plain part of some round).
  `backP`: the total code.

Limits: this file does not say that its strings are the library's (they need not be: any total code
serves). What the evaluator builds is a fact about a compiler.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingImpl
import Compile.Ser

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

variable {I X : Type} (Lf : Unit → BatchProtocol I X)

/-- The serialisers that are data. -/
structure SerP where
  x   : Ser X
  sg  : Ser (Lf ()).Symbol
  sym : ∀ t : Tag, Ser (SymAny (shapeOf (Lf ()) t))
  pb  : ∀ t : Tag, Ser (PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))

variable (D : SerP Lf)

def serLeafP : Ser (LeafIn (Lf ())) :=
  Ser.ofEquiv (β := Option ((Lf ()).Symbol ⊕ (Σ t : Tag, SymAny (shapeOf (Lf ()) t))) × Bits)
    ⟨fun q => (q.body, q.salt), fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
    (Ser.prod (Ser.option (Ser.sum D.sg (Ser.sigma serTag fun t => D.sym t))) serBits)

def serHeadP (sx : Ser X) : Ser (Head 256 X) :=
  Ser.ofEquiv (β := (List (Dig 256) × Option X × Bits)
      ⊕ (Option X × Bits) ⊕ (Bits × Bits) ⊕ (List (Dig 256) × Bits) ⊕ Bits)
    ⟨fun q => match q with
      | .f1 cms x salt => .inl (cms, x, salt)
      | .f2 xl ρ => .inr (.inl (xl, ρ))
      | .f3 ρ0 c => .inr (.inr (.inl (ρ0, c)))
      | .f4 cms rt => .inr (.inr (.inr (.inl (cms, rt))))
      | .f5 ρ0 => .inr (.inr (.inr (.inr ρ0))),
     fun y => match y with
      | .inl (cms, x, salt) => .f1 cms x salt
      | .inr (.inl (xl, ρ)) => .f2 xl ρ
      | .inr (.inr (.inl (ρ0, c))) => .f3 ρ0 c
      | .inr (.inr (.inr (.inl (cms, rt)))) => .f4 cms rt
      | .inr (.inr (.inr (.inr ρ0))) => .f5 ρ0,
     fun q => by cases q <;> rfl,
     fun y => by rcases y with ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | _ <;> rfl⟩
    (Ser.sum (Ser.prod (Ser.list (serDig 256)) (Ser.prod (Ser.option sx) serBits))
      (Ser.sum (Ser.prod (Ser.option sx) serBits) (Ser.sum (Ser.prod serBits serBits)
        (Ser.sum (Ser.prod (Ser.list (serDig 256)) serBits) serBits))))

def serFbP (t : Tag) : Ser (FbIn 256 (Lf ()) t) :=
  Ser.ofEquiv (β := ℕ × Head 256 X × Option (Dig 256) × PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    ⟨fun q => (q.round, q.head, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat (Ser.prod (serHeadP D.x) (Ser.prod (Ser.option (serDig 256)) (D.pb t))))

def serGP (t : Tag) : Ser (JoiningRoundQuery 256 (Lf ()) t) :=
  Ser.ofEquiv (β := ℕ × Bits × Option (Dig 256) × PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    ⟨fun q => (q.round, q.ρ, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat (Ser.prod serBits (Ser.prod (Ser.option (serDig 256)) (D.pb t))))

def serRealP (K : ℕ) : Ser (RealPts 256 K (Lf ())) :=
  Ser.sum (serLeafP Lf D)
    (Ser.sum (Ser.prod serBits serBits)
      (Ser.sum serBits
        (Ser.sum (Ser.prod serBits serBits)
          (Ser.sum (Ser.sigma serTag fun t => Ser.prod (serFbP Lf D t) (Ser.fin (K + 1)))
            (Ser.sigma serTag fun t => serGP Lf D t)))))

def serGhostP (K : ℕ) : Ser (GhostPts 256 K (Lf ())) :=
  Ser.sigma serTag fun t => Ser.prod Ser.nat (Ser.prod (serFbP Lf D t) (Ser.fin (K + 1)))

/-- A total code of all real and ghost points. -/
def backP (K : ℕ) : StrCode (AllPts 256 K (Lf ())) :=
  (Ser.sum (serRealP Lf D K) (serGhostP Lf D K)).toStrCode

end Run
