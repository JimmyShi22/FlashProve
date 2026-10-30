-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/RootsTrees.lean: the list of roots of a proof string against the list of trees
that is read off the wire record.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Wire.lean reads the trees of a file off its wire record (`treesSB`,
`FileW.trees`), by the rule by which the chain takes roots from the list. Here that rule is tied to
the chain itself.

Main names:
  `joinedPh`          has the chain passed the joining round, by its phase
  `count_eq_trees`    a run of the chain has taken as many roots as `treesSB` lists trees
  `FileW.roots_trees` where the compiled verifier of a written file, with the strict-format check,
                      says yes: the chain has yielded roots R round by round, the proof string's
                      list of roots is these in a row
                      (`RootsOfChain.flat`), and it has as many entries as the file has trees

Limits: here the lengths agree. That entry number n of the list of roots is the root of tree number
n is in OnBytes/TypedOracleCompiler/Joined/RootsAt.lean.
`FileW.roots_trees` speaks of the strict verifier alone (`F.written.verify`: with the strict-format
check, OnBytes/TypedOracleCompiler/Joined/Wire.lean): its proof uses that check's clause that the list holds at most
as many roots as the chain has taken. Nothing on `verifyLax`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Roots
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Compile.Batch.Runs

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc TreeRef)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- has the chain passed the joining round -/
def joinedPh : Phase lam → Bool
  | .first => false
  | .loc _ => false
  | .shr _ _ => true
  | .aft _ _ => true

theorem length_refs (i : ℕ) (own : Bool) (n : ℕ) : (refs i own n).length = n := by
  simp [refs]

/-- A run of the chain has taken as many roots as `treesSB` lists trees. -/
theorem count_eq_trees {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      RootsOfChain.count s R = (treesSB s A W i (joinedPh ph)).length
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (rt, R), h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr, hf⟩ := runsIn_chainB_cons_flags h
      have ih := count_eq_trees s A W _ (i + 1) ph₁ ph' rts' pls ρ R hr
      cases hv with
      | f1 root ans hk =>
        have h1 := (hf.2 root rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_none, Option.getD_some, List.length_nil] at ih ⊢
        omega
      | f2 _ root ans hk =>
        have h1 := (hf.2 root rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_none, Option.getD_some, List.length_nil] at ih ⊢
        omega
      | join _ rtj rt0 c ans hk hg =>
        have h1 := (hf.2 rtj rfl).1
        have h0 := (hf.1 rt0 rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_some, Bool.false_eq_true, if_false] at ih ⊢
        omega
      | f5 _ _ root ans hk =>
        have h0 := (hf.1 root rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_none, Option.getD_some, List.length_nil, if_true] at ih ⊢
        omega
      | f3 _ _ root ans hk =>
        have h1 := (hf.2 root rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_none, Option.getD_some, List.length_nil] at ih ⊢
        omega
      | f2' _ _ root ans hk =>
        have h1 := (hf.2 root rfl).1
        simp only [RootsOfChain.count, treesSB, hk, joinedPh, List.length_append, length_refs,
          Option.getD_none, Option.getD_some, List.length_nil] at ih ⊢
        omega

/-- Where the compiled verifier of a written file, with the strict-format check, says yes, the proof
string's list of roots is what the chain has taken, round by round, and it has as many entries as
the file has trees. -/
theorem FileW.roots_trees {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
    {E : ExtSpec} (F : FileW W G Y E) {sMT sFS : ℕ} {cms : List (Dig lam)} {x : Y} {π : F.Prf}
    {tr : Trace (typedOracleFamily lam W.K L)} (h : RunsIn tr (F.written.verify sMT sFS cms x π) true) :
    ∃ (ρ : Rho G.sh) (R : RootsOfChain lam G.sh) (ph : Phase lam),
      RunsIn tr (recomputeChainOfProof F.t F.D.batch F.wq F.embP F.xin cms x π) (some (ρ, R, ph)) ∧
      π.roots = RT.flat G.sh R ∧ π.roots.length = F.trees.length := by
  unfold Written.verify verifyOneProtocol at h
  obtain ⟨r, hr, h2⟩ := (runsIn_bind_iff _ _ _).1 h
  rcases r with _ | ⟨ρ, R, ph⟩
  · exact absurd (runsIn_pure_iff.1 h2) (by simp)
  · dsimp only at h2
    split_ifs at h2 with hs
    · have hc : π.roots.length ≤ RootsOfChain.count G.sh R := by
        unfold proofHasStrictFormat at hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        exact hs.1.1.1.1.1.2
      obtain ⟨h3, h4⟩ := flat_of_runsIn hr
      have h5 : RootsOfChain.count G.sh R = F.trees.length := count_eq_trees _ _ _ _ _ _ _ _ _ _ _ hr
      have h6 : π.roots.length = RootsOfChain.count G.sh R := Nat.le_antisymm hc h4
      refine ⟨ρ, R, ph, hr, ?_, h6.trans h5⟩
      rw [h3, ← h6, List.take_length]
    · exact absurd (runsIn_pure_iff.1 h2) (by simp)

end TypedOracleCompiler.Joined
