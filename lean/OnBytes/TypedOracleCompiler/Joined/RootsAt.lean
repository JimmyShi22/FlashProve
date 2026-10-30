-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/RootsAt.lean: the list of roots of a proof string against the list of trees that
is read off the wire record, entry by entry.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/RootsTrees.lean shows that a run of the chain takes as many roots as `treesSB`
(OnBytes/TypedOracleCompiler/Joined/Wire.lean) lists trees. Here: entry number n of the roots is the root of tree
number n.

Main names:
  `RootsOfChain.rootOf s R j ref`: the root that R, the roots round by round, holds for the tree ref.
  `map_rootOf_treesSB`: if the chain runs from the phase ph and yields the roots R: the roots that R
    holds for the listed trees, in the list's order, are the entries of `RootsOfChain.flat s R`
    (OnBytes/TypedOracleCompiler/Joined/Roots.lean), all of them.
  `rootOf_of_getElem?`: the same for entry number n.
  `FileW.roots_at`: where the compiled verifier of a written file says yes: the roots that the chain
    has yielded for the file's trees, in their order, are the proof string's list of roots.
  `le_round_of_mem_treesSB`, `map_rootOf_refs`, `map_rootOf_tail`: what these need.

Limits: nothing on a chain that does not run to its end. Nothing on soundness.
`FileW.roots_at` speaks of the strict verifier alone (`F.written.verify`: with the strict-format
check, OnBytes/TypedOracleCompiler/Joined/Wire.lean): through `FileW.roots_trees` its proof uses that check's clause
that the list holds at most as many roots as the chain has taken. Nothing on `verifyLax`.
No other file of the library uses `rootOf_of_getElem?` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.RootsTrees

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- every listed tree belongs to a round from number i on -/
theorem le_round_of_mem_treesSB : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ)
    (b : Bool) (ref : TreeRef), ref ∈ treesSB s A W i b → i ≤ ref.round
  | [], _, _, _, _, _, h => by cases h
  | _ :: s, (a, A), (w, W), i, b, ref, h => by
    have ih := fun b' (h' : ref ∈ treesSB s A W (i + 1) b') =>
      Nat.le_of_succ_le (le_round_of_mem_treesSB s A W (i + 1) b' ref h')
    have hr : ∀ own n, ref ∈ refs i own n → i ≤ ref.round := by
      intro own n h'
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 h'
      exact Nat.le_refl i
    rw [treesSB] at h
    generalize a.kind = kd at h
    cases kd with
    | lo =>
      rcases List.mem_append.1 h with h | h
      · exact hr _ _ h
      · exact ih _ h
    | sh =>
      rcases List.mem_append.1 h with h | h
      · cases b
        · exact hr _ _ h
        · cases h
      · rcases List.mem_append.1 h with h | h
        · exact hr _ _ h
        · exact ih _ h

/-- The root that R holds for a tree; j: the number of the first round of s. none: R has no root for
it (its round is not one of s, its component was not sent, or has fewer trees). -/
def RT.rootOf : (s : Shape) → RootsOfChain lam s → ℕ → TreeRef → Option (Dig lam)
  | [], _, _, _ => none
  | _ :: s, (c, R), j, ref =>
    if ref.round = j then ((if ref.own then c.2 else c.1).getD [])[ref.tree]?
    else RT.rootOf s R (j + 1) ref

theorem map_getElem?_range {α : Type} (l : List α) :
    (List.range l.length).map (fun k => l[k]?) = l.map some := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

/-- the trees of one component of the first round -/
theorem map_rootOf_refs {r : Round} {s : Shape} (c : RtC lam × RtC lam) (R : RootsOfChain lam s) (j : ℕ)
    (own : Bool) (n : ℕ) (hn : ((if own then c.2 else c.1).getD []).length = n) :
    (refs j own n).map (RT.rootOf (r :: s) (c, R) j) =
      ((if own then c.2 else c.1).getD []).map some := by
  subst hn
  unfold refs
  rw [List.map_map, ← map_getElem?_range]
  refine List.map_congr_left fun k _ => ?_
  simp [RT.rootOf]

/-- the trees of the later rounds -/
theorem map_rootOf_tail {r : Round} {s : Shape} {A : RoundSplits s} (W : RoundsQueryLayout lam K s A)
    (c : RtC lam × RtC lam) (R : RootsOfChain lam s) (j : ℕ) (b : Bool) :
    (treesSB s A W (j + 1) b).map (RT.rootOf (r :: s) (c, R) j) =
      (treesSB s A W (j + 1) b).map (RT.rootOf s R (j + 1)) := by
  refine List.map_congr_left fun ref h => ?_
  have h1 := le_round_of_mem_treesSB s A W (j + 1) b ref h
  rw [RT.rootOf, if_neg (by omega)]

/-- **The list of roots against the table of trees.** If the chain runs from the phase ph and yields
the roots R, then entry by entry the root that R holds for a listed tree is the entry of `RootsOfChain.flat`
at the same place; and the two lists have one length. j: the number of the first round of s. -/
theorem map_rootOf_treesSB {tr : Trace (typedOracleFamily lam K L)} (t : Tag) (cms : List (Dig lam))
    (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s) (ph' : Phase lam) (j : ℕ),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      (treesSB s A W j (joinedPh ph)).map (RT.rootOf s R j) = (RT.flat s R).map some
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls), (c0, ρ), (c, R), ph', j, h => by
    obtain ⟨cur, ans, ph₁, rts', hv, -, -, hrun, hfl⟩ := runsIn_chainB_cons_flags h
    have ih := map_rootOf_treesSB t cms x salt rtreq s A W _ _ ph₁ rts' pls ρ R ph' (j + 1) hrun
    have lo : ∀ (root : List (Dig lam)) (b : Bool), a.kind = .lo → c = (none, some root) →
        (treesSB s A W (j + 1) b).map (RT.rootOf s R (j + 1)) = (RT.flat s R).map some →
        (treesSB (r :: s) (a, A) (w, W) j b).map (RT.rootOf (r :: s) (c, R) j) =
          (RT.flat (r :: s) (c, R)).map some := by
      intro root b hk hc hi
      subst hc
      rw [treesSB, hk]
      show (refs j true w.depthJ.length ++ treesSB s A W (j + 1) b).map _ = _
      rw [List.map_append, map_rootOf_refs (none, some root) R j true _ (hfl.2 root rfl).1,
        map_rootOf_tail, hi]
      simp [RT.flat]
    cases hv with
    | f1 root ans hk => exact lo root _ hk rfl ih
    | f2 ρ1 root ans hk => exact lo root _ hk rfl ih
    | f3 ρ0 cv root ans hk => exact lo root _ hk rfl ih
    | f2' ρ1 cv root ans hk => exact lo root _ hk rfl ih
    | f5 ρ0 cv root ans hk =>
      rw [treesSB, hk]
      show ([] ++ (refs j false w.depth0.length ++ treesSB s A W (j + 1) true)).map _ = _
      rw [List.nil_append, List.map_append,
        map_rootOf_refs (some root, none) R j false _ (hfl.1 root rfl).1, map_rootOf_tail]
      rw [show (treesSB s A W (j + 1) true).map (RT.rootOf s R (j + 1)) = _ from ih]
      simp [RT.flat]
    | join ρ1 rtj rt0 cv ans hk hg =>
      rw [treesSB, hk]
      show (refs j true w.depthJ.length ++
        (refs j false w.depth0.length ++ treesSB s A W (j + 1) true)).map _ = _
      rw [List.map_append, List.map_append,
        map_rootOf_refs (some rt0, some rtj) R j true _ (hfl.2 rtj rfl).1,
        map_rootOf_refs (some rt0, some rtj) R j false _ (hfl.1 rt0 rfl).1, map_rootOf_tail]
      rw [show (treesSB s A W (j + 1) true).map (RT.rootOf s R (j + 1)) = _ from ih]
      simp [RT.flat]

/-- entry number n of the table of trees, and entry number n of the roots that the run has taken -/
theorem rootOf_of_getElem? {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {s : Shape} {A : RoundSplits s}
    {W : RoundsQueryLayout lam K s A} {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {ph : Phase lam} {rts : List (Dig lam)} {pls : Plains s} {ρ : Rho s} {R : RootsOfChain lam s}
    {ph' : Phase lam} (j : ℕ)
    (h : RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls)
      (some (ρ, R, ph'))) (n : ℕ) (ref : TreeRef)
    (hn : (treesSB s A W j (joinedPh ph))[n]? = some ref) :
    RT.rootOf s R j ref = (RT.flat s R)[n]? ∧ (RT.rootOf s R j ref).isSome := by
  have e := congrArg (fun l => l[n]?)
    (map_rootOf_treesSB t cms x salt rtreq s A W embP i ph rts pls ρ R ph' j h)
  simp only [List.getElem?_map, hn, Option.map_some] at e
  cases hf : (RT.flat s R)[n]? with
  | none => rw [hf] at e; cases e
  | some d =>
    rw [hf] at e
    have e' : RT.rootOf s R j ref = some d := Option.some.inj e
    exact ⟨e', by rw [e']; rfl⟩

/-- **A yes of a written file's verifier**: the roots that the chain has yielded for the file's
trees, in the order of the table of trees, are the proof string's list of roots. -/
theorem FileW.roots_at {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
    {E : ExtSpec} (F : FileW W G Y E) {sMT sFS : ℕ} {cms : List (Dig lam)} {x : Y} {π : F.Prf}
    {tr : Trace (typedOracleFamily lam W.K L)} (h : RunsIn tr (F.written.verify sMT sFS cms x π) true) :
    ∃ (ρ : Rho G.sh) (R : RootsOfChain lam G.sh) (ph : Phase lam),
      RunsIn tr (recomputeChainOfProof F.t F.D.batch F.wq F.embP F.xin cms x π) (some (ρ, R, ph)) ∧
      F.trees.map (RT.rootOf G.sh R 0) = π.roots.map some := by
  obtain ⟨ρ, R, ph, hr, h1, -⟩ := F.roots_trees h
  refine ⟨ρ, R, ph, hr, ?_⟩
  rw [h1]
  exact map_rootOf_treesSB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 hr

end TypedOracleCompiler.Joined
