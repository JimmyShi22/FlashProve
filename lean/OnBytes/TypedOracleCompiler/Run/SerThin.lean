-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SerThin.lean.
Run/SerThin.lean: A TOTAL CODE OF ALL REAL AND GHOST POINTS OF THE COMPILED SCHEME'S ORACLES, IN A
FORM MADE FOR THE EVALUATOR: THE INTERFACE BEHIND A FUNCTION OF Unit; NO RECURSION ON A SHAPE.
Definitions that compute (the laws are those of the library's serialisers: Iop/Ser.lean).
WHY. The encoding of Run/CodingPage.lean writes every typed point that the programs' format does not
write behind an escape, by ANY total code ("back"). The first exit to a single oracle asks ALL
blocks of an answer, so also the message blocks of round 0, which the format does not have: SO
"back" IS CALLED IN A RUN. The library's own total code (Compile/Batch/Ser.lean: serReal, serGhost)
has the interface as a parameter and goes through the shapes round by round: TRIED, with a trace in
a round's instance: it builds the list of all verifier messages.
HERE THE SAME TEXTS with the interface behind a function of Unit (Lf, explicit and first), and THE
SERIALISERS OF SYMBOLS AND OF PLAIN PARTS GIVEN AS DATA, one for each of the three protocols:
   SerP Lf              x (the instance), sg (a symbol of an encoded index), sym t (a symbol with
                        its position), pb t (a plain part of some round)
   serLeafP, serHeadP, serFbP, serGP, serRealP, serGhostP leaf queries; the five formats of a chain
   query's head; chain queries; the queries of the joining round; all real points; all ghost points
   backP Lf D K : StrCode (AllPts 256 K (Lf ()))
WHAT IS NOT SAID. That its strings are the library's (they need not be: any total code serves). What
the evaluator builds is a fact about a compiler.

Terms: lean/GLOSSARY.md.

-/
import Run.SerThin
import OnBytes.TypedOracleCompiler.Run.CodingImpl
import Compile.Ser

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X)

/-- The serialisers that are data. -/
structure SerP where
  x   : Ser X
  /-- TWO: of a leaf's body (in the library: sg, of a stored symbol, and sym t, of an own one) -/
  bd  : Ser (Lf ()).Bd
  pb  : ∀ t : Tag, Ser (PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))

variable (D : SerP Lf)

def serLeafP : Ser (LeafIn (Lf ())) :=
  Ser.ofEquiv (β := (Lf ()).Bd × Bits)
    ⟨fun q => (q.body, q.salt), fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
    (Ser.prod D.bd serBits)

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
  Ser.ofEquiv (β := ℕ × Head 256 X × List (Dig 256) × PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    ⟨fun q => (q.round, q.head, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat (Ser.prod (serHeadP D.x) (Ser.prod (Ser.list (serDig 256)) (D.pb t))))

def serGP (t : Tag) : Ser (JoiningRoundQuery 256 (Lf ()) t) :=
  Ser.ofEquiv (β := ℕ × Bits × List (Dig 256) × PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    ⟨fun q => (q.round, q.ρ, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat (Ser.prod serBits (Ser.prod (Ser.list (serDig 256)) (D.pb t))))

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

end TypedOracleCompiler.Run
