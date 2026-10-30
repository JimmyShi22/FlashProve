-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Verifier.lean: the compiled verifier of a file whose argument string is hashed in
three Fiat-Shamir chains, as one function.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

A key file and a proof file are each hashed in three chains, one after the other. Such a file is ONE
batch protocol whose rounds are the rounds of the three chains in a row (`Chains`, `Desc.batch`,
Compile/Joined/Types.lean). So the compiled verifier of one slot (`verifyOneProtocol`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) applies to the whole file, and what is proved of it holds
of the file (`verifyFile_eq`).

`verifyFile` says the same verifier chain by chain: it recomputes the first chain, then the second,
then the third, each by one call of `recomputeChain`, and then does once what `verifyOneProtocol` does behind the
chain. What passes from a chain to the next is written out: the phase in which the chain ended, and
the roots that it has not taken from the list. After local rounds the phase holds the last chaining
value; after the joining round and the shared rounds it holds the last shared chaining value and
the slot value (`Phase`). Mind where the cut lies: the query to g that closes the first chain, whose
answer is the slot value, is made in the joining round, so by `run₂`, not by `run₁`.

Main names:
  `wire₁`, `wire₂`, `wire₃`: the wire records of a chain's rounds, cut out of the file's.
  `emb₁` ..., `pls₁` ...: a chain's share of the map for plain parts, and of the plain parts.
  `run₁`, `run₂`, `run₃`: one chain, recomputed from where the chain before it ended.
  `glue`: what the three chains yield, as what one chain over all rounds yields.
  `chainF`: the three chains, one after the other; `chainF_eq`: it is `recomputeChainOfProof` at `Desc.batch`.
  `verifyFile`: the verifier of a file; it takes what `verifyOneProtocol` takes.
  `verifyFile_eq`: it is `verifyOneProtocol` at `Desc.batch`, for all arguments, under no hypothesis.
  `runsIn_chainF_iff`, `runsIn_verifyFile_iff`: in a trace, the verifier says yes exactly if each
    chain runs to a value from where the chain before it ended, the format is strict, and the part
    behind the chains says yes.
  `FileW.verify`, `FileW.verify_eq`: the same at a written file (OnBytes/TypedOracleCompiler/Joined/Wire.lean): it
    is `Written.verify` at `FileW.written`.

Limits: a term of the theory, in a section without code: that it can be evaluated at the size of a
real file is not claimed. Nothing is said of soundness here. That a chain ends in the phase that
the next one needs is no hypothesis: where kind and phase have no format, `recomputeChain` yields none and
the verifier says no.

Terms: lean/GLOSSARY.md.

-/
import Compile.Joined.Types
import Compile.MerkleRom
import OnBytes.TypedOracleCompiler.Joined.Cut
import OnBytes.TypedOracleCompiler.Joined.Wire

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}

/-! ## One chain -/

section Parts
variable {G : Chains} {D : Desc G Y E} (wq : ProtocolQueryLayout lam K D.batch)

/-- the wire records of the first chain's rounds -/
def wire₁ : RoundsQueryLayout lam K G.c₁ G.A₁ :=
  WireSB.fst (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃) wq.sh

/-- the wire records of the second chain's rounds -/
def wire₂ : RoundsQueryLayout lam K G.c₂ G.A₂ :=
  WireSB.fst (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃)
    (WireSB.snd (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃) wq.sh)

/-- the wire records of the third chain's rounds -/
def wire₃ : RoundsQueryLayout lam K G.c₃ G.A₃ :=
  WireSB.snd (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃)
    (WireSB.snd (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃) wq.sh)

end Parts

/-- what a chain over the rounds s yields: the verifier messages, the roots that it has taken, round
by round, and the phase in which it ended -/
abbrev Out (lam : ℕ) (s : Shape) : Type := Rho s × RootsOfChain lam s × Phase lam

section Runs
variable (t : Tag) {G : Chains} (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- how a plain part of the first chain's rounds is written into a query -/
def emb₁ : PlainPart G.c₁ G.A₁ → PlainPart (shapeOf L t) (annOf L t) := fun z =>
  embP (PB.left (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃) z)

/-- the same for the second chain's rounds -/
def emb₂ : PlainPart G.c₂ G.A₂ → PlainPart (shapeOf L t) (annOf L t) := fun z =>
  embP (PB.right (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃)
    (PB.left (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) z))

/-- the same for the third chain's rounds -/
def emb₃ : PlainPart G.c₃ G.A₃ → PlainPart (shapeOf L t) (annOf L t) := fun z =>
  embP (PB.right (s := G.c₁) (u := G.c₂ ++ G.c₃) (A := G.A₁) (B := RoundSplits.app G.A₂ G.A₃)
    (PB.right (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃) z))

/-- the plain parts of the first chain's rounds -/
def pls₁ : Plains G.c₁ := Plains.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains

/-- the plain parts of the second chain's rounds -/
def pls₂ : Plains G.c₂ :=
  Plains.fst (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains)

/-- the plain parts of the third chain's rounds -/
def pls₃ : Plains G.c₃ :=
  Plains.snd (s := G.c₂) (t := G.c₃) (Plains.snd (s := G.c₁) (t := G.c₂ ++ G.c₃) π.plains)

/-- The first chain: from the start, with all roots of the argument string. -/
def run₁ : TypedOracleComputation lam K L (Option (Out lam G.c₁)) :=
  recomputeChain t cms (xin x) π.salt π.rtreq G.c₁ G.A₁ (wire₁ wq) (emb₁ t embP) 0 .first π.roots
    (pls₁ D π)

/-- The second chain: from the phase in which the first ended, with the roots that it has left. -/
def run₂ (a : Out lam G.c₁) : TypedOracleComputation lam K L (Option (Out lam G.c₂)) :=
  recomputeChain t cms (xin x) π.salt π.rtreq G.c₂ G.A₂ (wire₂ wq) (emb₂ t embP) (0 + G.c₁.length) a.2.2
    (π.roots.drop (RootsOfChain.count G.c₁ a.2.1)) (pls₂ D π)

/-- The third chain: from the phase in which the second ended, with the roots that the first two
have left. -/
def run₃ (a : Out lam G.c₁) (b : Out lam G.c₂) : TypedOracleComputation lam K L (Option (Out lam G.c₃)) :=
  recomputeChain t cms (xin x) π.salt π.rtreq G.c₃ G.A₃ (wire₃ wq) (emb₃ t embP)
    (0 + G.c₁.length + G.c₂.length) b.2.2
    ((π.roots.drop (RootsOfChain.count G.c₁ a.2.1)).drop (RootsOfChain.count G.c₂ b.2.1)) (pls₃ D π)

/-- what the three chains yield, laid in a row; the phase is the last chain's -/
def glue {G : Chains} (a : Out lam G.c₁) (b : Out lam G.c₂) (c : Out lam G.c₃) : Out lam G.sh :=
  (Rho.app (s := G.c₁) (t := G.c₂ ++ G.c₃) a.1 (Rho.app (s := G.c₂) (t := G.c₃) b.1 c.1),
    RT.app (s := G.c₁) (u := G.c₂ ++ G.c₃) a.2.1 (RT.app (s := G.c₂) (u := G.c₃) b.2.1 c.2.1),
    c.2.2)

/-! ## The three chains -/

/-- the three chains of a file, recomputed one after the other -/
def chainF : TypedOracleComputation lam K L (Option (Out lam G.sh)) :=
  thenO (run₁ t D wq embP xin cms x π) fun a =>
  thenO (run₂ t D wq embP xin cms x π a) fun b =>
  thenO (run₃ t D wq embP xin cms x π a b) fun c =>
  OComp.pure (some (glue a b c))

/-- the three chains in a row are the one chain of the file as a batch protocol -/
theorem chainF_eq :
    chainF t D wq embP xin cms x π = recomputeChainOfProof t D.batch wq embP xin cms x π := by
  show _ = recomputeChain t cms (xin x) π.salt π.rtreq (G.c₁ ++ (G.c₂ ++ G.c₃))
    (RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃)) wq.sh embP 0 .first π.roots π.plains
  rw [chainB_app]
  refine congrArg (thenO _) (funext fun a => ?_)
  rw [chainB_app, thenO_assoc]
  refine congrArg (thenO _) (funext fun b => ?_)
  rw [thenO_assoc]
  exact congrArg (thenO _) (funext fun c => (thenO_pure_some _ _).symm)

/-- a chain after a chain runs to a value exactly if the first runs to a value and the second runs
on from it -/
theorem runsIn_thenO_iff {α β : Type} {tr : Trace (typedOracleFamily lam K L)} (c : TypedOracleComputation lam K L (Option α))
    (g : α → TypedOracleComputation lam K L (Option β)) (b : β) :
    RunsIn tr (thenO c g) (some b) ↔ ∃ a, RunsIn tr c (some a) ∧ RunsIn tr (g a) (some b) := by
  unfold thenO
  rw [runsIn_bind_iff]
  constructor
  · rintro ⟨r, h1, h2⟩
    cases r with
    | none => cases runsIn_pure_iff.1 h2
    | some a => exact ⟨a, h1, h2⟩
  · rintro ⟨a, h1, h2⟩
    exact ⟨some a, h1, h2⟩

/-- In a trace the three chains run to z exactly if each runs to a value from where the chain before
it ended, and z is these values in a row. -/
theorem runsIn_chainF_iff {tr : Trace (typedOracleFamily lam K L)} (z : Out lam G.sh) :
    RunsIn tr (chainF t D wq embP xin cms x π) (some z) ↔
      ∃ a b c, RunsIn tr (run₁ t D wq embP xin cms x π) (some a) ∧
        RunsIn tr (run₂ t D wq embP xin cms x π a) (some b) ∧
        RunsIn tr (run₃ t D wq embP xin cms x π a b) (some c) ∧ z = glue a b c := by
  unfold chainF
  simp only [runsIn_thenO_iff, runsIn_pure_iff, Option.some.injEq]
  constructor
  · rintro ⟨a, h1, b, h2, c, h3, rfl⟩
    exact ⟨a, b, c, h1, h2, h3, rfl⟩
  · rintro ⟨a, b, c, h1, h2, h3, rfl⟩
    exact ⟨a, h1, b, h2, c, h3, rfl⟩

end Runs

/-! ## The verifier -/

section Verify
variable (sMT sFS : ℕ) (t : Tag) {G : Chains} (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch)
  (embS : (p : OPos G.sh) → OSym G.sh p → Body L)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- The compiled verifier of a file in three chains, with the strict format and pruned sets of
paths: the three chains; the format; then `checkPrunedOpenings`. -/
def verifyFile : TypedOracleComputation lam K L Bool :=
  (chainF t D wq embP xin cms x π).bind fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      if proofHasStrictFormat sMT sFS D.batch wq depthReq x π ρ rts ph then
        checkPrunedOpenings D.batch wq embS embE depthReq cms x π ρ rts ph
      else pure false

/-- the verifier of a file is the compiled verifier of one slot, at the file as a batch protocol -/
theorem verifyFile_eq :
    verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π =
      verifyOneProtocol sMT sFS t D.batch wq embS embP xin embE depthReq cms x π := by
  unfold verifyFile verifyOneProtocol
  rw [chainF_eq]
  refine congrArg (OComp.bind _) (funext fun r => ?_)
  cases r <;> rfl

/-- In a trace the verifier of a file says yes exactly if the three chains run to values, each from
where the chain before it ended, the argument string has the strict format, and the part behind the
chains says yes. -/
theorem runsIn_verifyFile_iff {tr : Trace (typedOracleFamily lam K L)} :
    RunsIn tr (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π) true ↔
      ∃ a b c, RunsIn tr (run₁ t D wq embP xin cms x π) (some a) ∧
        RunsIn tr (run₂ t D wq embP xin cms x π a) (some b) ∧
        RunsIn tr (run₃ t D wq embP xin cms x π a b) (some c) ∧
        proofHasStrictFormat sMT sFS D.batch wq depthReq x π (glue a b c).1 (glue a b c).2.1
          (glue a b c).2.2 = true ∧
        RunsIn tr (checkPrunedOpenings D.batch wq embS embE depthReq cms x π (glue a b c).1 (glue a b c).2.1
          (glue a b c).2.2) true := by
  unfold verifyFile
  rw [runsIn_bind_iff]
  constructor
  · rintro ⟨r, h1, h2⟩
    cases r with
    | none => cases runsIn_pure_iff.1 h2
    | some z =>
      obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := (runsIn_chainF_iff t D wq embP xin cms x π z).1 h1
      refine ⟨a, b, c, ha, hb, hc, ?_⟩
      by_cases hs : proofHasStrictFormat sMT sFS D.batch wq depthReq x π (glue a b c).1 (glue a b c).2.1
          (glue a b c).2.2 = true
      · exact ⟨hs, by simpa only [hs, if_true] using h2⟩
      · exact absurd h2 (by
          simp only [hs, Bool.false_eq_true, if_false]
          exact fun h => by cases runsIn_pure_iff.1 h)
  · rintro ⟨a, b, c, ha, hb, hc, hs, hA⟩
    refine ⟨some (glue a b c),
      (runsIn_chainF_iff t D wq embP xin cms x π _).2 ⟨a, b, c, ha, hb, hc, rfl⟩, ?_⟩
    simpa only [hs, if_true] using hA

end Verify

/-! ## At a written file -/

section Written
variable {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} (F : FileW W G Y E)

/-- the compiled verifier of a written file, chain by chain -/
def FileW.verify (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y) (π : F.Prf) : TypedOracleComputation lam W.K L Bool :=
  verifyFile sMT sFS F.t F.D F.wq F.embS F.embP F.xin F.embE (W.dReq F.t) cms x π

/-- it is the compiled verifier of one slot at the file as a written protocol -/
theorem FileW.verify_eq (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y) (π : F.Prf) :
    F.verify sMT sFS cms x π = F.written.verify sMT sFS cms x π :=
  verifyFile_eq sMT sFS F.t F.D F.wq F.embS F.embP F.xin F.embE (W.dReq F.t) cms x π

end Written

end TypedOracleCompiler.Joined
