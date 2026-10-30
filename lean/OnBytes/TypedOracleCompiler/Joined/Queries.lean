-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Queries.lean: the typed queries by which the compiled verifier of a file passes
from one hash chain to the next: the two seals, the slot and the binding root.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


The compiled verifier (`recomputeChain`, `reqCheck`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) at a written
file (`FileW`, OnBytes/TypedOracleCompiler/Joined/Wire.lean) asks one Fiat-Shamir query in each round, and at the
joining round two queries. Five of its queries stand between the chains. Here each is written out as
a function of the proof string π and of the values that the chain has reached, so that a map from
typed queries to strings can be held against them one by one.

  `qFirst`    (F1), round 0: chain 1's first call. It holds the outer roots, the early part of the
              instance and `π.salt`.
  `qSeal₁`    (G), round `G.nJ`: it holds ρ, the chaining value behind chain 1's last round. Its
              answer c is SEAL 1, the slot's value.
  `slotLeaf`  the input of the leaf of the binding tree: c, and behind it `π.rsalt`. From its digest
              the verifier climbs along `π.path`, from leaf number `π.slot`, and compares the result
              with `π.rtreq`, the binding root.
  `qShared`   (F4), round `G.nJ`: chain 2's first call. It holds the outer roots and the binding
              root.
  `qThird`    (F3), round `G.n3`: chain 3's first call. It holds ρ0, the chaining value behind chain
              2's last round, which is SEAL 2, and c.
  `pbF`, `pbJ0`, `pbJj`, `pb3`: the plain parts of these rounds as plain parts of the whole.

Limits: definitions only. That these stand in every trace in which the compiled verifier of a file
says yes, with ρ, c and ρ0 handed on from chain to chain, is `FileW.asked` [with its file
OnBytes/TypedOracleCompiler/Joined/Asked.lean not in this library; so here read: not proved in this library];
`asks_of_yes` (OnBytes/TypedOracleCompiler/Joined/JoinsRoots.lean) has it of the like four queries of
OnBytes/TypedOracleCompiler/Joined/Joins.lean, under `G.Laws`. The roots in a query (rt) are arguments: they are the
next entries of `π.roots`, as many as the component has trees.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.Wire
import OnBytes.TypedOracleCompiler.Joined.Cut

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The plain parts of the four rounds, as plain parts of the whole -/

section
variable (G : Chains)

/-- the slot's plain part of the front -/
def pbF (z : (RAnn.allLocal G.rF).Pj) : PlainPart G.sh G.ann := .inl (.inr z)

/-- a plain part from the joining round on -/
def pbJ' (z : PlainPart G.shJ G.annJ) : PlainPart G.sh G.ann :=
  .inr (PB.right (A := RoundSplits.allLocal G.s₁) (B := G.annJ) z)

/-- the shared plain part of the joining round -/
def pbJ0 (z : G.aJ.P0) : PlainPart G.sh G.ann := pbJ' G (.inl (.inl z))

/-- the slot's plain part of the joining round -/
def pbJj (z : G.aJ.Pj) : PlainPart G.sh G.ann := pbJ' G (.inl (.inr z))

/-- the slot's plain part of the seam -/
def pb3 (z : (RAnn.allLocal G.r3).Pj) : PlainPart G.sh G.ann :=
  pbJ' G (.inr (PB.right (A := RoundSplits.const (RAnn.ofShared .sh) G.s₂) (B := G.ann₃) (.inl (.inr z))))

end

/-! ## The queries between the chains -/

namespace FileW
variable {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec} (F : FileW W G Y E)

/-- (F1): chain 1's first call. rt: the roots of the front's trees. -/
def qFirst (cms : List (Dig lam)) (x : Y) (rt : List (Dig lam)) (π : F.Prf) : FbIn lam L F.t :=
  ⟨0, .f1 cms ((F.xin x).map L.early) π.salt, rt,
    F.embP (pbF G ((RAnn.allLocal G.rF).plain (G.plF π.plains)).2)⟩

/-- (G): the query whose answer is SEAL 1, the slot's value. ρ: the chaining value behind chain 1's
last round; rt: the roots of the trees of the slot's component of the joining round. -/
def qSeal₁ (ρ : Bits) (rt : List (Dig lam)) (π : F.Prf) : JoiningRoundQuery lam L F.t :=
  ⟨G.nJ, ρ, rt, F.embP (pbJj G (G.aJ.plain (G.plJ π.plains)).2)⟩

/-- The input of the leaf of the binding tree: the slot's value, and behind it the slot's salt. -/
def slotLeaf (c : Dig lam) (π : F.Prf) : Bits := List.ofFn c ++ π.rsalt

/-- (F4): chain 2's first call. It holds the binding root. rt: the roots of the trees of the shared
component of the joining round. -/
def qShared (cms : List (Dig lam)) (rt : List (Dig lam)) (π : F.Prf) : FbIn lam L F.t :=
  ⟨G.nJ, .f4 cms (List.ofFn π.rtreq), rt, F.embP (pbJ0 G (G.aJ.plain (G.plJ π.plains)).1)⟩

/-- (F3): chain 3's first call. ρ0: SEAL 2, the chaining value behind chain 2's last round; c: SEAL
1; rt: the roots of the seam's trees. -/
def qThird (ρ0 : Bits) (c : Dig lam) (rt : List (Dig lam)) (π : F.Prf) : FbIn lam L F.t :=
  ⟨G.n3, .f3 ρ0 (List.ofFn c), rt,
    F.embP (pb3 G ((RAnn.allLocal G.r3).plain (G.pl3 π.plains)).2)⟩

end FileW

end TypedOracleCompiler.Joined
