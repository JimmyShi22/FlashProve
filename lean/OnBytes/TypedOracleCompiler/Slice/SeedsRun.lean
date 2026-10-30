-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsRun.lean: what the seeds' protocol's chain at its one fixed string computes
under a family of oracle functions: two queries, and the verifier's messages that the wiring makes
of their answers.

The judge of OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean begins with the chain of the sibling's seeds'
protocol (`seedsT`, OnBytes/TypedOracleCompiler/Slice/SeedsT.lean; the sibling is a second form of the
library's soundness road, under OnBytes/TypedOracleCompiler/) at one fixed string: no instance, no salt, the default
request root, no roots, the rounds' fixed plain parts. To tie that run to a program's hash calls one
has to know which typed queries it asks and what it makes of the answers. This file says it, for any
interface, wire, tag and way of writing plain parts.
 - `p0S embP`, `p1S embP`: the two rounds' fixed plain parts, as they stand in the queries;
 - `q0S embP cms`: the first query: round 0, head `.f1 cms none []`, no root, `p0S`; `q1S embP ρ`:
   the drawing round's query: round 1, head `.f2 none ρ`, no root, `p1S`;
 - `chainAt_seeds_det`: under a family F the chain's value is: the first round's verifier's message
   from F's answer a₀ at `q0S`; the drawing round's from F's answer a₁ at `q1S` at the link of a₀;
   no roots; the last phase holds the link of a₁. No hypothesis;
 - `drawnT_snd`: what the chain draws, as the format's record, hangs on the drawing round's message
   alone.

Main definitions: `p0S`, `p1S`, `q0S`, `q1S`.
Main theorems: `chainAt_seeds_det`, `drawnT_snd`.

Not claimed. Nothing on any page: how the two queries are spelled as strings is in
OnBytes/TypedOracleCompiler/Run/FirstName.lean and SeedRound.lean, at plain parts that are parameters there. Nothing
on what the kit's draw makes of hash blocks. That a run in a trace has this value follows only where
each entry of the trace holds F's own answer. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/
is the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedsTData

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (t : Tag) (C : PQ.CK) (e : _root_.Fmt.Entry) (E : ExtSpec)
  (embP : PlainPart (seedsT C (dSeed e) E).shape (RoundSplits.allLocal (seedsT C (dSeed e) E).shape) →
    PlainPart (shapeOf L t) (annOf L t))

/-- The silent first round's fixed plain part, as it stands in the first query. -/
def p0S : PlainPart (shapeOf L t) (annOf L t) :=
  embP (.inl (.inr ((RAnn.allLocal (PQ.s0 C).up).plain (PQ.s0 C).up.dPlain).2))

/-- The drawing round's fixed plain part, as it stands in that round's query. -/
def p1S : PlainPart (shapeOf L t) (annOf L t) :=
  embP (.inr (.inl (.inr ((RAnn.allLocal (PQ.roundS C (dSeed e)).up).plain
    (PQ.roundS C (dSeed e)).up.dPlain).2)))

/-- The chain's first query, under the outer roots cms. -/
def q0S (cms : List (Dig 256)) : FbIn 256 L t := ⟨0, .f1 cms none [], [], p0S t C e E embP⟩

/-- The drawing round's query, at the chain value ρ. -/
def q1S (ρ : Bits) : FbIn 256 L t := ⟨1, .f2 none ρ, [], p1S t C e E embP⟩

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (we : WireE E)

/-- The equation before the field for a late instance is read: by unfolding. -/
theorem chainAt_seeds_aux (F : Fam (typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256)) :
    (recomputeChain (L := L) (K := K + 1) t cms none [] default (seedsT C (dSeed e) E).shape
        (RoundSplits.allLocal _) (wqT C K chal (dSeed e) we).sh embP 0 .first []
        (plainsT C (dSeed e) E)).det F =
      some (((PQ.wire0S C K chal).chal (F (.fb t) (q0S t C e E embP cms)).1,
          (PQ.wireS C K chal (dSeed e)).chal
            (F (.fb t) (⟨1, .f2 (lateInstancePart L 1 none)
              (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (q0S t C e E embP cms))), [],
              p1S t C e E embP⟩ : FbIn 256 L t)).1, ()),
        ((none, some []), (none, some []), ()),
        .loc (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (⟨1, .f2 (lateInstancePart L 1 none)
                      (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (q0S t C e E embP cms))), [],
                      p1S t C e E embP⟩ : FbIn 256 L t)))) := rfl

/-- What the chain at the fixed string computes under a family F of oracle functions: two
queries; the verifier's messages that the wiring makes of their answers; no roots. -/
theorem chainAt_seeds_det (F : Fam (typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256)) :
    (recomputeChain (L := L) (K := K + 1) t cms none [] default (seedsT C (dSeed e) E).shape
        (RoundSplits.allLocal _) (wqT C K chal (dSeed e) we).sh embP 0 .first []
        (plainsT C (dSeed e) E)).det F =
      some (((PQ.wire0S C K chal).chal (F (.fb t) (q0S t C e E embP cms)).1,
          (PQ.wireS C K chal (dSeed e)).chal
            (F (.fb t) (q1S t C e E embP
              (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (q0S t C e E embP cms))))).1, ()),
        ((none, some []), (none, some []), ()),
        .loc (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (q1S t C e E embP
                  (TypedOracleCompiler.Compile.Batch.link (F (.fb t) (q0S t C e E embP cms))))))) := by
  have hl1 : lateInstancePart L 1 (none : Option X) = none := by
    unfold lateInstancePart
    split <;> rfl
  rw [chainAt_seeds_aux, hl1]
  rfl

omit t embP in
/-- What the chain draws, as the format's record of draws, hangs on the drawing round's verifier's
message alone. -/
theorem drawnT_snd (c0 c0' : (PQ.s0 C).up.Chal) (c1 : (PQ.roundS C (dSeed e)).up.Chal) :
    drawnT C (dSeed e) E (c0, c1, ()) = drawnT C (dSeed e) E (c0', c1, ()) := rfl

end TypedOracleCompiler.Slice
