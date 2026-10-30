-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Count.lean: HOW MANY TYPED QUERIES THE COMPILED PROVER ASKS AT MOST, ON EVERY
PATH: OComp.QueryBound (Rom/OComp.lean) of proveX (OnBytes/Prover/Defs.lean) at a number that is
read off the wire record, the caps and the length of the slot's path.

Why. The goals' budget on the honest side (HonestWithin, Ladder.lean) asks QueryBound of "prove": it
counts every path: a capped search counts cap i + 1 queries, though it asks about 2^b on average.

Main names.
  treesN, fsN, chainN   the numbers: 2 · 2^d a tree of depth d; 1 or cap i + 1 a Fiat-Shamir query;
    the sum over the rounds.
  queryBound_pairUpO, allOut_pairUpO, queryBound_levelsO, queryBound_leavesO, allOut_leavesO,
    queryBound_treeO, queryBound_treesO, queryBound_climbO   the trees and the request tree's path.
  queryBound_searchO, queryBound_fsO   the search.
  queryBound_chainO, queryBound_proveX   THE STATEMENT.

The trees' walk is that of OnBytes/K/Arm/TreeCommitCount.lean (the written committer's count, over
another family of oracles), whose general step Rom.OComp.QueryBound.bindOut is called.

Limits. AN UPPER BOUND, loose in four ways: a tree of depth d counts 2 · 2^d (the true count is
2^(d + 1) - 1); every round counts both components' trees, the two queries and the path of the
joining round, and both components' Fiat-Shamir numbers, though an arm of the chain asks one of
them (at the written wires the other component has no tree and no test: it then adds 1 a round).
TYPED queries: by Ladder.lean's own word at honestBudget a typed query costs one query to the hash
function for each digest of its answer: that factor is not in this number. One slot, one chain. That
the prover has no coins: noCoin_proveX (OnBytes/Prover/Main.lean).
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Main
import OnBytes.K.Arm.TreeCommitCount

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile.GenPub (AllOut)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The second form's type of a Fiat-Shamir answer. (The first form's is in sight too.) -/
local notation "FsAns₂" => TypedOracleCompiler.Compile.Batch.FsAns
/-- The second form's type of programs. -/
local notation "OC₂" => TypedOracleCompiler.Compile.Batch.TypedOracleComputation

/-! ## The numbers -/

/-- 2 · 2^d for each tree of depth d. -/
def treesN : List ℕ → ℕ
  | [] => 0
  | d :: ds => 2 * 2 ^ d + treesN ds

/-- A Fiat-Shamir query: 1 without a test, n + 1 with one. -/
def fsN {C P : Type} : Option (GrW C P) → ℕ → ℕ
  | none, _ => 1
  | some _, n => n + 1

/-- The sum over the rounds. i: the number of the first of the rounds s; p: the length of the slot's
path in the request tree. -/
def chainN : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _, _, _ => 0
  | _ :: s, (_, A), (w, W), cap, i, p =>
      treesN w.depthJ + treesN w.depth0 + (2 + p) + (fsN w.grJ (cap i) + fsN w.gr0 (cap i)) +
        chainN s A W cap (i + 1) p

/-! ## The trees -/

theorem queryBound_askV (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf lam L o) :
    (askTypedOracle (L := L) (K := K) o q).QueryBound 1 := fun _ => trivial

theorem queryBound_pairUpO : ∀ l : List (Dig lam),
    (pairUp (hashTreeNode (K := K) (L := L)) l).QueryBound (l.length / 2)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => by
      show ((hashTreeNode (K := K) (L := L) a b).bind fun c =>
        (pairUp (hashTreeNode (K := K) (L := L)) t).bind fun r => OComp.pure (c :: r)).QueryBound
          ((t.length + 1 + 1) / 2)
      have e : (t.length + 1 + 1) / 2 = 1 + (t.length / 2 + 0) := by omega
      rw [e]
      exact OComp.QueryBound.bind (queryBound_askV _ _) fun _ =>
        OComp.QueryBound.bind (queryBound_pairUpO t) fun _ => trivial

theorem allOut_pairUpO : ∀ l : List (Dig lam),
    AllOut (fun u => u.length + l.length / 2 = l.length) (pairUp (hashTreeNode (K := K) (L := L)) l)
  | [] => by
      show ([] : List (Dig lam)).length + ([] : List (Dig lam)).length / 2 = _
      simp
  | [x] => by
      show [x].length + [x].length / 2 = [x].length
      simp
  | a :: b :: t => by
      show AllOut _ ((hashTreeNode (K := K) (L := L) a b).bind fun c =>
        (pairUp (hashTreeNode (K := K) (L := L)) t).bind fun r => OComp.pure (c :: r))
      refine AllOut.bind (Q' := fun _ => True) (fun _ => trivial) fun c _ =>
        AllOut.bind (allOut_pairUpO t) fun r hr => ?_
      have hr' : r.length + t.length / 2 = t.length := hr
      show (c :: r).length + (a :: b :: t).length / 2 = (a :: b :: t).length
      simp only [List.length_cons]
      omega

/-- The building of the levels asks at most as many queries as the first level has entries. -/
theorem queryBound_levelsO : ∀ (d : ℕ) (l : List (Dig lam)),
    (levelsM (hashTreeNode (K := K) (L := L)) d l).QueryBound l.length
  | 0, _ => trivial
  | d + 1, l => by
      show ((pairUp (hashTreeNode (K := K) (L := L)) l).bind fun u =>
        (levelsM (hashTreeNode (K := K) (L := L)) d u).bind fun r => OComp.pure (l :: r)).QueryBound
          l.length
      have h := OComp.QueryBound.bindOut (t := l.length - l.length / 2)
        (g := fun u => (levelsM (hashTreeNode (K := K) (L := L)) d u).bind fun r => OComp.pure (l :: r))
        (queryBound_pairUpO l) (allOut_pairUpO l) fun u hu => by
          have hu' : u.length + l.length / 2 = l.length := hu
          have e : l.length - l.length / 2 = u.length + 0 := by omega
          rw [e]
          exact OComp.QueryBound.bind (queryBound_levelsO d u) fun _ => trivial
      exact h.mono (by omega)

theorem queryBound_leavesO : ∀ l : List (LeafIn L),
    (leavesO (lam := lam) (K := K) l).QueryBound l.length
  | [] => trivial
  | x :: xs => by
      show ((askTypedOracle (L := L) (K := K) OracleName.leaf x).bind fun u =>
        (leavesO xs).bind fun us => OComp.pure (u :: us)).QueryBound (xs.length + 1)
      have e : xs.length + 1 = 1 + (xs.length + 0) := by omega
      rw [e]
      exact OComp.QueryBound.bind (queryBound_askV _ _) fun _ =>
        OComp.QueryBound.bind (queryBound_leavesO xs) fun _ => trivial

theorem allOut_leavesO : ∀ l : List (LeafIn L),
    AllOut (fun us => us.length = l.length) (leavesO (lam := lam) (K := K) l)
  | [] => rfl
  | x :: xs => by
      show AllOut _ ((askTypedOracle (L := L) (K := K) OracleName.leaf x).bind fun u =>
        (leavesO xs).bind fun us => OComp.pure (u :: us))
      refine AllOut.bind (Q' := fun _ => True) (fun _ => trivial) fun u _ =>
        AllOut.bind (allOut_leavesO xs) fun us hus => ?_
      have hus' : us.length = xs.length := hus
      show (u :: us).length = (x :: xs).length
      simp only [List.length_cons]
      exact congrArg (· + 1) hus'

/-- A tree of depth d: at most 2 · 2^d queries. -/
theorem queryBound_treeO (d : ℕ) (inp : ℕ → LeafIn L) :
    (treeO (lam := lam) (K := K) d inp).QueryBound (2 * 2 ^ d) := by
  have hl : ((List.range (2 ^ d)).map inp).length = 2 ^ d := by simp
  have h := OComp.QueryBound.bindOut (t := 2 ^ d)
    (g := fun l => (levelsM (hashTreeNode (K := K) (L := L)) d l).bind fun lv =>
      (OComp.pure ⟨inp, lv⟩ : OC₂ lam K L (TreeK lam L)))
    (queryBound_leavesO ((List.range (2 ^ d)).map inp)) (allOut_leavesO _) fun l hl' => by
      have hl'' : l.length = ((List.range (2 ^ d)).map inp).length := hl'
      have e : 2 ^ d = l.length + 0 := by omega
      rw [e]
      exact OComp.QueryBound.bind (queryBound_levelsO d l) fun _ => trivial
  rw [hl] at h
  exact h.mono (by omega)

theorem queryBound_treesO {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ),
      (treesO (lam := lam) (K := K) pad sl posAt emb o k ds).QueryBound (treesN ds)
  | _, [] => trivial
  | k, d :: ds => by
      have h := OComp.QueryBound.bind (queryBound_treeO (lam := lam) (K := K) d fun j =>
          (⟨match posAt k j with
            | some p => emb p (r.rd o p)
            | none => pad, sl k j⟩ : LeafIn L))
        (g := fun T => (treesO pad sl posAt emb o (k + 1) ds).bind fun Ts =>
          (OComp.pure (T :: Ts) : OC₂ lam K L (List (TreeK lam L))))
        (t := treesN ds + 0) fun _ =>
          OComp.QueryBound.bind (queryBound_treesO pad sl posAt emb o (k + 1) ds) fun _ => trivial
      exact h.mono (by show 2 * 2 ^ d + (treesN ds + 0) ≤ 2 * 2 ^ d + treesN ds; omega)

theorem queryBound_climbO : ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam),
    (climbM (rnodeV (K := K) (L := L)) path j c).QueryBound path.length
  | [], _, _ => trivial
  | s :: ss, j, c => by
    have e : (s :: ss).length = 1 + ss.length := by simp [Nat.add_comm]
    rw [e]
    by_cases hb : j % 2 = 0
    · simp only [climbM, if_pos hb]
      exact OComp.QueryBound.bind (queryBound_askV _ _) fun u => queryBound_climbO ss _ u
    · simp only [climbM, if_neg hb]
      exact OComp.QueryBound.bind (queryBound_askV _ _) fun u => queryBound_climbO ss _ u

/-! ## The search -/

theorem queryBound_searchO {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : P → OC₂ lam K L (FsAns₂ lam K)) (hask : ∀ β, (ask β).QueryBound 1) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal ask α fuel n).QueryBound fuel
  | 0, _ => trivial
  | fuel + 1, n => by
    have h := OComp.QueryBound.bind (s := 1) (t := fuel) (hask (gr.put n α))
      (g := fun a => if gr.ok (chal a.1) then
          (OComp.pure (some (gr.put n α, a)) : OC₂ lam K L (Option (P × FsAns₂ lam K)))
        else searchO gr chal ask α fuel (n + 1)) fun a => by
        by_cases hk : gr.ok (chal a.1) = true
        · simp only [if_pos hk]
          trivial
        · simp only [if_neg hk]
          exact queryBound_searchO gr chal ask hask α fuel (n + 1)
    exact h.mono (by omega)

theorem queryBound_fsO {C P : Type} (gr : Option (GrW C P)) (cap : ℕ)
    (chal : (Fin K → Dig lam) → C) (ask : P → OC₂ lam K L (FsAns₂ lam K))
    (hask : ∀ β, (ask β).QueryBound 1) (α : P) :
    (fsO gr cap chal ask α).QueryBound (fsN gr cap) := by
  cases gr with
  | none =>
    show ((ask α).bind fun a => (OComp.pure (some (α, a)) :
      OC₂ lam K L (Option (P × FsAns₂ lam K)))).QueryBound (1 + 0)
    exact OComp.QueryBound.bind (hask _) fun _ => trivial
  | some q => exact queryBound_searchO q chal ask hask α _ _

theorem queryBound_onFs {P β : Type} (i n : ℕ) (k : P × FsAns₂ lam K → OC₂ lam K L (Res β))
    (hk : ∀ p, (k p).QueryBound n) : ∀ o, (onFs i k o).QueryBound n
  | none => trivial
  | some p => hk p

/-! ## The chain -/

/-- **The chain asks at most chainN typed queries, on every path.** -/
theorem queryBound_chainO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t cms x co cap s A W embS embP i ph σ).QueryBound
        (chainN s A W cap i co.path.length)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    have tail : ∀ {β : Type} (ph' σ') (f : Res (OutP lam L s) → OC₂ lam K L β),
        (∀ r, (f r).QueryBound 0) →
        ((chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          ph' σ').bind f).QueryBound (chainN s A W cap (i + 1) co.path.length + 0) :=
      fun ph' σ' f hf =>
        OComp.QueryBound.bind (queryBound_chainO t cms x co cap s A W _ _ _ ph' σ') hf
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact (OComp.QueryBound.bind (queryBound_treesO _ _ _ _ _ _ _) fun _ =>
            OComp.QueryBound.bind (queryBound_fsO _ _ _ _ (fun _ => queryBound_askV _ _) _)
              (queryBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsN w.grJ (cap i) + fsN w.gr0 (cap i)) + chainN s A W cap (i + 1) co.path.length
                omega)
        | false =>
          exact (OComp.QueryBound.bind (queryBound_treesO _ _ _ _ _ _ _) fun _ =>
            OComp.QueryBound.bind (queryBound_fsO _ _ _ _ (fun _ => queryBound_askV _ _) _)
              (queryBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsN w.grJ (cap i) + fsN w.gr0 (cap i)) + chainN s A W cap (i + 1) co.path.length
                omega)
      | join ρ =>
        exact (OComp.QueryBound.bind (queryBound_treesO _ _ _ _ _ _ _) fun _ =>
          OComp.QueryBound.bind (queryBound_treesO _ _ _ _ _ _ _) fun _ =>
          OComp.QueryBound.bind (queryBound_askV _ _) fun _ =>
          OComp.QueryBound.bind (queryBound_askV _ _) fun _ =>
          OComp.QueryBound.bind (queryBound_climbO _ _ _) fun _ =>
            OComp.QueryBound.bind (queryBound_fsO _ _ _ _ (fun _ => queryBound_askV _ _) _)
              (queryBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsN w.grJ (cap i) + fsN w.gr0 (cap i)) + chainN s A W cap (i + 1) co.path.length
                omega)

/-- **The compiled prover of one slot asks at most chainN typed queries, on every path.** -/
theorem queryBound_proveX (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).QueryBound
      (chainN Q.loc.shape Q.ann wq.sh cap 0 co.path.length) :=
  (OComp.QueryBound.bind (t := 0)
    (queryBound_chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ)
    (by intro _; trivial)).mono (by omega)

end OnBytes.Prover

#print axioms OnBytes.Prover.queryBound_treeO
#print axioms OnBytes.Prover.queryBound_treesO
#print axioms OnBytes.Prover.queryBound_climbO
#print axioms OnBytes.Prover.queryBound_searchO
#print axioms OnBytes.Prover.queryBound_fsO
#print axioms OnBytes.Prover.queryBound_chainO
#print axioms OnBytes.Prover.queryBound_proveX
