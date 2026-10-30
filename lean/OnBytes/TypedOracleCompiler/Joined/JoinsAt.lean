-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/JoinsAt.lean: how the three chains of a file hand on their values, under fixed
oracle functions.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Joins.lean says, of runs in a trace, in which phase each chain ends and which
queries stand between the chains. This file carries that to values under fixed oracle functions g
(`OComp.det`), by the bridge of OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean.

Main names:
  `joins_at`: if the three chains have the values a, b, e under g, then a ends in `.loc ρ₁`, b in
    `.shr ρ₀ c` and e in `.aft ρ₃ c`, where the slot value c is g's answer to the query to g that
    holds ρ₁ (`qSeal₁`).
  `slot_at`: so the slot value with which the third chain ends is that answer.

  `rtJ`: the roots in that query: of the roots that the first chain has left, as many as the slot's
    component of the joining round has trees.

Limits: nothing says what ρ₁ is, nor how g comes from a hash on strings.
No other file of the library uses `joins_at` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.JoinsRoots
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}
  {t : Tag} {G : Chains} {D : Desc G Y E} {wq : ProtocolQueryLayout lam K D.batch}
  {embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam D.batch}
  {a : Out lam G.c₁} {b : Out lam G.c₂} {e : Out lam G.c₃}

/-- The roots in the query to g of the joining round: of the roots that the first chain has left, as
many as the slot's component of that round has trees. -/
def rtJ (D : Desc G Y E) (wq : ProtocolQueryLayout lam K D.batch) (π : OneProtocolProof lam D.batch) (a : Out lam G.c₁) :
    List (Dig lam) :=
  (rts₂ D π a).take (wire₂ wq).1.depthJ.length

/-- **The values that the chains hand on, under g.** The first chain ends in a chaining value ρ₁;
the slot value c is g's answer to the query to g that holds ρ₁; the second chain ends in a chaining
value ρ₀ with c; the third ends with the same c. -/
theorem joins_at (hG : G.Laws) {g : Fam (typedOracleFamily lam K L)}
    (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) :
    ∃ (ρ₁ ρ₀ ρ₃ : Bits) (c : Dig lam),
      a.2.2 = .loc ρ₁ ∧ b.2.2 = .shr ρ₀ c ∧ e.2.2 = .aft ρ₃ c ∧
      g (OracleName.g t) (qSeal₁ t D embP π ρ₁ (rtJ D wq π a)) = c := by
  obtain ⟨t1, -, r1⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₁
  obtain ⟨t2, a2, r2⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₂
  obtain ⟨t3, -, r3⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) h₃
  obtain ⟨-, -, ρ₁, -, e1⟩ := run₁_ends t D wq embP xin cms x π r1
  obtain ⟨c, -, ρ₀, qg, -, e2⟩ := run₂_asks t D wq embP xin cms x π hG e1 r2
  obtain ⟨-, -, ρ₃, -, e3⟩ := run₃_joins t D wq embP xin cms x π e2 r3
  exact ⟨ρ₁, ρ₀, ρ₃, c, e1, e2, e3, a2 _ qg⟩

/-- The slot value with which the third chain ends is g's answer to the query to g that holds the
chaining value in which the first chain ends. -/
theorem slot_at (hG : G.Laws) {g : Fam (typedOracleFamily lam K L)}
    (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) {c : Dig lam}
    (hc : e.2.2.slotVal = some c) :
    ∃ ρ₁ : Bits, a.2.2 = .loc ρ₁ ∧ g (OracleName.g t) (qSeal₁ t D embP π ρ₁ (rtJ D wq π a)) = c := by
  obtain ⟨ρ₁, ρ₀, ρ₃, c', e1, -, e3, hg⟩ := joins_at hG h₁ h₂ h₃
  rw [e3] at hc
  obtain rfl : c' = c := Option.some.inj hc
  exact ⟨ρ₁, e1, hg⟩

end TypedOracleCompiler.Joined
