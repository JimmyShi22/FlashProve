-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Ser.lean: the points of the compiled scheme's typed oracles, encoded as strings by an
explicit, self-delimiting serialization.
(Words of this library: lean/GLOSSARY.md.)

Over one hash function on strings (Rom/Family.lean) hash block j of a typed oracle's answer to a
query is the hash of a string. This file encodes the point (oracle, query, number of the block) as
that string, from serializers of the parts that depend on the protocol (Iop/SerB.lean: `SerLHB`),
which are data. Nothing is chosen by `Classical.choice`.

  `serReal`   the serializer of the points `RealPts` (Compile/Batch/ImplOf.lean)
  `codeReal`   the same as a code of whole strings with a parser (Rom/Hotel.lean)
  `serGhost`, `codeGhost`   the same for the points of the ghost names `fbw t k`, which no algorithm
                            of the scheme queries (`GhostPts`): protocol, k in unary, the
                            Fiat-Shamir query, the number of the block; no tag in front. They do not
                            change the format below (`code_real`: the string that is hashed is the
                            bit 1 followed by the string of `serReal`)

Format of `serReal`: `D.tag`; then 0 for a leaf query, 10 node, 110 leaf of a request tree, 1110
node of a request tree, 11110 Fiat-Shamir, 11111 the oracle g, in the last two cases then the
protocol; then the fields in the order of the structures. The five formats of a Fiat-Shamir query
are told apart by 0, 10, 110, 1110, 1111. Options and sums have one leading bit; lists of digests
have the bit 1 before each element and the bit 0 at the end; bit strings have a length prefix;
digests are lam raw bits; the number of a round is in unary; the number of a block has ⌈log₂ (K +
1)⌉ bits.

Notation: `lam`: a natural number: "Digests have `lam` bits"; `K`: a natural number: an answer of
`fb t` "is K hash blocks, from which the challenge is made, and a chaining value" (both: the head of
Compile/Batch/Oracles.lean); `D`: a `SerLHB L` (Iop/SerB.lean): "What the serialization of the
queries needs of the record of protocols"; `D.tag`: a `List Bool`: "a constant prefix of every
string of `serReal` (Compile/Batch/Ser.lean): a tag for the parameter set" (`tag_prefix`); `RoundSplits s`:
"The annotation of a shape" (Iop/Batch.lean); `PlainPart s A`: "the plain part of one component of the
prover message of some round: α_0 (left) or α_j (right)" (Compile/Batch/Oracles.lean).
-/
import Iop.SerB
import Compile.Ser
import Compile.Batch.ImplOf

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom

variable {I X : Type}

/-- the serializers for the rounds of a protocol -/
def _root_.Iop.SerLHB.shape {L : BatchProtocol I X} (D : SerLHB L) : (t : Tag) → SerS (shapeOf L t)
  | .test => D.T
  | .link => D.Lk
  | .onl => D.O

/-- the serializers for the annotation of a protocol -/
def _root_.Iop.SerLHB.ann {L : BatchProtocol I X} (D : SerLHB L) : (t : Tag) → SerA (shapeOf L t) (annOf L t)
  | .test => SerA.allLocal _ D.T
  | .link => SerA.allLocal _ D.Lk
  | .onl => D.A

/-! ## The parts -/

def serPB : (s : Shape) → (A : RoundSplits s) → SerA s A → Ser (PlainPart s A)
  | [], _, _ => Ser.empty
  | _ :: s, (_, A), ((a, b), e) => Ser.sum (Ser.sum a b) (serPB s A e)

variable {L : BatchProtocol I X} (D : SerLHB L) (lam K : ℕ)

def serLeafIn : Ser (LeafIn L) :=
  Ser.ofEquiv (β := Option (L.Symbol ⊕ (Σ t : Tag, SymAny (shapeOf L t))) × Bits)
    ⟨fun q => (q.body, q.salt), fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
    (Ser.prod
      (Ser.option (Ser.sum D.sg (Ser.sigma serTag fun t => serSymAny (shapeOf L t) (D.shape t))))
      serBits)

def serHead : Ser (Head lam X) :=
  Ser.ofEquiv (β := (List (Dig lam) × Option X × Bits)
      ⊕ (Option X × Bits) ⊕ (Bits × Bits) ⊕ (List (Dig lam) × Bits) ⊕ Bits)
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
    (Ser.sum (Ser.prod (Ser.list (serDig lam)) (Ser.prod (Ser.option D.x) serBits))
      (Ser.sum (Ser.prod (Ser.option D.x) serBits) (Ser.sum (Ser.prod serBits serBits)
        (Ser.sum (Ser.prod (Ser.list (serDig lam)) serBits) serBits))))

def serFbIn (t : Tag) : Ser (FbIn lam L t) :=
  Ser.ofEquiv (β := ℕ × Head lam X × Option (Dig lam) × PlainPart (shapeOf L t) (annOf L t))
    ⟨fun q => (q.round, q.head, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat
      (Ser.prod (serHead D lam)
        (Ser.prod (Ser.option (serDig lam)) (serPB (shapeOf L t) (annOf L t) (D.ann t)))))

def serGIn (t : Tag) : Ser (JoiningRoundQuery lam L t) :=
  Ser.ofEquiv (β := ℕ × Bits × Option (Dig lam) × PlainPart (shapeOf L t) (annOf L t))
    ⟨fun q => (q.round, q.ρ, q.rt, q.plain), fun y => ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod Ser.nat
      (Ser.prod serBits
        (Ser.prod (Ser.option (serDig lam)) (serPB (shapeOf L t) (annOf L t) (D.ann t)))))

/-! ## The points -/

/-- The serializer of the points (`RealPts`). -/
def serReal : Ser (RealPts lam K L) :=
  Ser.tagged D.tag
    (Ser.sum (serLeafIn D)
      (Ser.sum (Ser.prod serBits serBits)
        (Ser.sum serBits
          (Ser.sum (Ser.prod serBits serBits)
            (Ser.sum (Ser.sigma serTag fun t => Ser.prod (serFbIn D lam t) (Ser.fin (K + 1)))
              (Ser.sigma serTag fun t => serGIn D lam t))))))

/-- the same as an injective encoding as bit strings, with its parser -/
def codeReal : StrCode (RealPts lam K L) := (serReal D lam K).toStrCode

/-- Every string of the encoding begins with `D.tag`, the tag for the parameter set. -/
theorem tag_prefix (x : RealPts lam K L) : D.tag <+: (codeReal D lam K).put x := by
  show D.tag <+: (serReal D lam K).put x
  rw [serReal, Ser.put_tagged]
  exact List.prefix_append _ _

/-- The serializer of the points of the ghost names. -/
def serGhost : Ser (GhostPts lam K L) :=
  Ser.sigma serTag fun t => Ser.prod Ser.nat (Ser.prod (serFbIn D lam t) (Ser.fin (K + 1)))

/-- the same as an injective encoding as bit strings, with its parser -/
def codeGhost : StrCode (GhostPts lam K L) := (serGhost D lam K).toStrCode

/-- The typed oracles of the compiled scheme over one hash function (`OracleCoding`), as a term in the data
D. -/
def implReal : OracleCoding (spec lam K L) lam := implOf lam K L (codeReal D lam K) (codeGhost D lam K)

end Compile.Batch
