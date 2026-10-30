-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Roots.lean: the roots that a run of a compiled verifier's chain has taken are the
first entries of the list of roots that it was given, in the list's own order.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

`recomputeChain` (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) is given one list of roots and takes from its
front what each round needs. It returns the roots round by round and component by component (`RootsOfChain`),
not the list that it has left.

Main names:
  `RT.flat s R`: the roots of R in the order in which the chain takes them: round by round; in a
    round the roots of the slot's component, then those of the shared one (in the joining round both
    are sent; in every other round at most one of the two).
  `RT.length_flat`: they are as many as `RootsOfChain.count` counts. `RT.flat_app`: over `s ++ u`.
  `flat_prefix_of_runsIn`: if the chain runs in a list of queries with answers and yields R, the
    list of roots that it was given begins with `RT.flat s R`.
  `flat_of_runsIn`: the same said with `List.take`, and that the list is long enough.
  `eq_flat_of_runsIn`: a list with no more roots than the run has taken is `RT.flat s R`.

Limits: nothing on what stands behind these entries in the list: the chain does not look at it.
Nothing on soundness.
No other file of the library uses `eq_flat_of_runsIn`, `RT.flat_app` or `takeRt_append` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Cut
import Compile.MerkleRom

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the roots of R in the order in which the chain takes them -/
def RT.flat : (s : Shape) → RootsOfChain lam s → List (Dig lam)
  | [], _ => []
  | _ :: s, (c, R) => c.2.getD [] ++ c.1.getD [] ++ RT.flat s R

theorem RT.length_flat : ∀ (s : Shape) (R : RootsOfChain lam s), (RT.flat s R).length = RootsOfChain.count s R
  | [], _ => rfl
  | _ :: s, (c, R) => by
    have h := RT.length_flat s R
    show (c.2.getD [] ++ c.1.getD [] ++ RT.flat s R).length =
      (c.1.getD []).length + (c.2.getD []).length + RootsOfChain.count s R
    rw [List.length_append, List.length_append, h]
    omega

theorem RT.flat_app : ∀ {s u : Shape} (R : RootsOfChain lam s) (R' : RootsOfChain lam u),
    RT.flat (s ++ u) (RT.app R R') = RT.flat s R ++ RT.flat u R'
  | [], _, _, _ => rfl
  | _ :: s, _, (c, R), R' => by
    show c.2.getD [] ++ c.1.getD [] ++ RT.flat _ (RT.app R R') =
      c.2.getD [] ++ c.1.getD [] ++ RT.flat s R ++ _
    rw [RT.flat_app R R', List.append_assoc _ (RT.flat s R)]

/-- what `takeRt` takes and what it leaves make up the list -/
theorem takeRt_append {n : ℕ} {rts a b : List (Dig lam)} (h : takeRt n rts = some (a, b)) :
    rts = a ++ b := by
  unfold takeRt at h
  split at h
  · cases h
    exact (List.take_append_drop n rts).symm
  · cases h

/-- **The roots of a run are the first entries of the list.** -/
theorem flat_prefix_of_runsIn {tr : Trace (typedOracleFamily lam K L)} (t : Tag) (cms : List (Dig lam))
    (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s) (ph' : Phase lam),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls) (some (ρ, R, ph')) →
      RT.flat s R <+: rts
  | [], _, _, _, _, _, rts, _, _, _, _, _ => List.nil_prefix
  | r :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls), (c0, ρ), (c, R), ph', h => by
    have tail : ∀ (c' : RtC lam × RtC lam) (ch : r.Chal) (ph1 : Phase lam)
        (rts' : List (Dig lam)),
        RunsIn tr ((recomputeChain (K := K) t cms x salt rtreq s A W (fun z => embP (Sum.inr z)) (i + 1)
            ph1 rts' pls).bind fun r1 =>
          OComp.pure (r1.map fun z =>
            (((ch, z.1), (c', z.2.1), z.2.2) : Rho (r :: s) × RootsOfChain lam (r :: s) × Phase lam)))
          (some ((c0, ρ), (c, R), ph')) →
        c = c' ∧ RT.flat s R <+: rts' := by
      intro c' ch ph1 rts' h'
      obtain ⟨r1, h1, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      have h3 := runsIn_pure_iff.1 h2
      rcases r1 with _ | ⟨ρ1, R1, ph2⟩
      · cases h3
      · have h4 : (((ch, ρ1), (c', R1), ph2) :
              (r.Chal × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
            ((c0, ρ), (c, R), ph') := Option.some.inj h3
        simp only [Prod.mk.injEq] at h4
        obtain ⟨⟨-, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := h4
        exact ⟨rfl, flat_prefix_of_runsIn t cms x salt rtreq s A W _ _ _ _ _ _ _ _ h1⟩
    have ask : ∀ {β : Type} (o : OracleName) (q : domOf lam L o) (k : rngOf lam K o → TypedOracleComputation lam K L β)
        (z : β), RunsIn tr ((askTypedOracle (L := L) (K := K) o q).bind k) z → ∃ ans, RunsIn tr (k ans) z :=
      fun o q k z h' => by
        obtain ⟨ans, -, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
        exact ⟨ans, h2⟩
    simp only [recomputeChain] at h
    generalize actOf cms (Option.map L.early x) salt a.kind ph = act at h
    rcases act with _ | ⟨hd, _ | _, next⟩ | ρ1
    · cases runsIn_pure_iff.1 h
    · dsimp only at h
      generalize h0 : takeRt w.depth0.length rts = tk at h
      rcases tk with _ | ⟨rt, rts'⟩
      · cases runsIn_pure_iff.1 h
      · obtain ⟨ans, h2⟩ := ask _ _ _ _ h
        obtain ⟨rfl, rest, h3⟩ := tail _ _ _ _ h2
        exact ⟨rest, by
          rw [takeRt_append h0, ← h3]
          simp [RT.flat]⟩
    · dsimp only at h
      generalize hJ : takeRt w.depthJ.length rts = tk at h
      rcases tk with _ | ⟨rt, rts'⟩
      · cases runsIn_pure_iff.1 h
      · obtain ⟨ans, h2⟩ := ask _ _ _ _ h
        obtain ⟨rfl, rest, h3⟩ := tail _ _ _ _ h2
        exact ⟨rest, by
          rw [takeRt_append hJ, ← h3]
          simp [RT.flat]⟩
    · dsimp only at h
      generalize hJ : takeRt w.depthJ.length rts = tk at h
      rcases tk with _ | ⟨rtj, rts1⟩
      · cases runsIn_pure_iff.1 h
      · dsimp only at h
        generalize h0 : takeRt w.depth0.length rts1 = tk0 at h
        rcases tk0 with _ | ⟨rt0, rts'⟩
        · cases runsIn_pure_iff.1 h
        · obtain ⟨cv, h1⟩ := ask _ _ _ _ h
          obtain ⟨ans, h2⟩ := ask _ _ _ _ h1
          obtain ⟨rfl, rest, h3⟩ := tail _ _ _ _ h2
          exact ⟨rest, by
            rw [takeRt_append hJ, takeRt_append h0, ← h3]
            simp [RT.flat]⟩

/-- the same with `List.take`; and the list is long enough -/
theorem flat_of_runsIn {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {s : Shape} {A : RoundSplits s}
    {W : RoundsQueryLayout lam K s A} {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {ph : Phase lam} {rts : List (Dig lam)} {pls : Plains s} {ρ : Rho s} {R : RootsOfChain lam s}
    {ph' : Phase lam}
    (h : RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls)
      (some (ρ, R, ph'))) :
    RT.flat s R = rts.take (RootsOfChain.count s R) ∧ RootsOfChain.count s R ≤ rts.length := by
  have hp := flat_prefix_of_runsIn t cms x salt rtreq s A W embP i ph rts pls ρ R ph' h
  rw [← RT.length_flat]
  exact ⟨(List.prefix_iff_eq_take.1 hp), hp.length_le⟩

/-- If the list holds no more roots than the run has taken (the strict format asks that), the list
is the roots of the run. -/
theorem eq_flat_of_runsIn {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {s : Shape} {A : RoundSplits s}
    {W : RoundsQueryLayout lam K s A} {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {ph : Phase lam} {rts : List (Dig lam)} {pls : Plains s} {ρ : Rho s} {R : RootsOfChain lam s}
    {ph' : Phase lam}
    (h : RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls)
      (some (ρ, R, ph'))) (hl : rts.length ≤ RootsOfChain.count s R) : rts = RT.flat s R :=
  ((flat_prefix_of_runsIn t cms x salt rtreq s A W embP i ph rts pls ρ R ph' h).eq_of_length_le
    (by rw [RT.length_flat]; exact hl)).symm

end TypedOracleCompiler.Joined
