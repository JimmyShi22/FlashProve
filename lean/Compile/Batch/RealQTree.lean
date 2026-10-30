-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/RealQTree.lean: for a program that never queries a ghost name `fbw`, `realQ` changes
nothing. In particular it changes nothing for the program of a node (`nodeP'`: a fresh encoding of
the index and its tree). `realQ` (Compile/Batch/Oracles.lean) writes the ghost names back: a query
to fbw t k becomes the query to fb t at the same input (words of this library: lean/GLOSSARY.md).

  `NoGT c`  The program c with tokens (`Step`, Rom/Defer.lean; `erase`, Compile/Star.lean) makes no
            query, ordinary or marked, to a ghost name fbw t k: a recursion on the term.
            `NoGT.bind`: sequential composition.
  `realQ_erase`  For such a program: realQ (erase c vs) = erase c vs, that is eraseR c vs = erase c
                 vs.
  `nog_nodeP'`  With `nog_drawT` .. `nog_commitE`: each is `NoGT` (`nog_pairUp`, `nog_levelsM`: if
                their argument `node` is, hn): a sample, the tree over an encoded index, and the
                node (a sample and such a tree: no Fiat-Shamir query at all).
  `eraseR_nodeP'`  eraseR (nodeP' ..) vs = erase (nodeP' ..) vs.

What it is for: the forms of the scheme with a seed derive the node of the sampled copy again; they
are about erase (nodeP' ..) (`PS`, Compile/Batch/SeedStar.lean), while the committer is `realQ` of
the whole erased program.

The induction follows that of Compile/Batch/GhostRouted.lean.

Notation: `fb t`, `fbw t k` (`OracleName`, Compile/Batch/Oracles.lean): `fb t`: Fiat-Shamir for the protocol
t; `fbw t k`: an oracle of the analysis: proof-of-work attempt k + 1 is written as a query to
`fbw t k`, and `realQ` maps it back to `fb t`; `St lam K L α` (Compile/Batch/TokTree.lean):
`Step (spec lam K L) (split lam K L) α`; `vs`: a `List Bits`, the store: in `erase`
(Compile/Star.lean) tokens are strings, kept in a list; `eraseR c vs` (Compile/Batch/RealQ.lean):
what a scheme runs of a program with tokens: its erasure with the ghost names written back
(`realQ`); `W`: a `QueryLayout lam L` (Iop/BatchWire.lean); `WP`: a `WireBP L` (Iop/BatchWireP.lean); `p`:
a `Params` (Compile/Star.lean).
-/
import Compile.Batch.RealQ
import Compile.Batch.Star

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {α β : Type}

/-- no query to a ghost name -/
def NoGT : St lam K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, NoGT (k r)
  | .plain o _ k => (∀ t j, o ≠ OracleName.fbw t j) ∧ ∀ r, NoGT (k r)
  | .fresh _ k => ∀ u, NoGT (k u)
  | .marked o _ _ _ _ k => (∀ t j, o ≠ OracleName.fbw t j) ∧ ∀ v u, NoGT (k v u)
  | .reveal _ k => ∀ vs, NoGT (k vs)

theorem NoGT.bind {c : St lam K L α} {g : α → St lam K L β} (hc : NoGT c) (hg : ∀ a, NoGT (g a)) :
    NoGT (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (hc r)
  | plain o q k ih => exact ⟨hc.1, fun r => ih r (hc.2 r)⟩
  | fresh ℓ k ih => exact fun u => ih u (hc u)
  | marked o t us pt inj k ih => exact ⟨hc.1, fun v u => ih v u (hc.2 v u)⟩
  | reveal ts k ih => exact fun vs => ih vs (hc vs)

/-- For a program without a query to a ghost name, `realQ` changes nothing. -/
theorem realQ_erase {c : St lam K L α} (hc : NoGT c) : ∀ vs, realQ (erase c vs) = erase c vs := by
  induction c with
  | pure a => intro vs; rfl
  | sample n k ih => intro vs; exact congrArg _ (funext fun r => ih r (hc r) vs)
  | plain o q k ih =>
    intro vs
    show realQ (OComp.query o q fun r => erase (k r) vs) = OComp.query o q fun r => erase (k r) vs
    rw [realQ_query o hc.1]
    exact congrArg _ (funext fun r => ih r (hc.2 r) vs)
  | fresh ℓ k ih => intro vs; exact congrArg _ (funext fun r => ih _ (hc _) _)
  | marked o t us pt inj k ih =>
    intro vs
    show realQ (OComp.query o _ fun r => erase (k _ _) _) = OComp.query o _ fun r => erase (k _ _) _
    rw [realQ_query o hc.1]
    exact congrArg _ (funext fun r => ih _ _ (hc.2 _ _) _)
  | reveal ts k ih => intro vs; exact ih _ (hc _) vs

theorem eraseR_of_noGT {c : St lam K L α} (hc : NoGT c) (vs : List Bits) :
    eraseR c vs = erase c vs :=
  realQ_erase hc vs

/-! ## The induction, program by program -/

theorem nog_drawT {β : Type} (e : Enum β) : NoGT (drawT (lam := lam) (K := K) (L := L) e) :=
  fun _ => trivial

theorem nog_leafT (sMT : ℕ) (b : Body L) : NoGT (leafT (lam := lam) (K := K) sMT b) := fun _ =>
  ⟨fun _ _ h => (by cases h), fun _ _ => trivial⟩

theorem nog_showT (t : Tok) : NoGT (showT (lam := lam) (K := K) (L := L) t) := fun _ => trivial

theorem nog_leafE (sMT : ℕ) (b : Body L) (blind : Bool) :
    NoGT (leafE (lam := lam) (K := K) sMT b blind) := by
  unfold leafE
  cases blind
  · exact ⟨fun _ _ h => (by cases h), fun _ => trivial⟩
  · exact (nog_leafT sMT b).bind fun x => (nog_showT x.2).bind fun _ => trivial

theorem nog_nodeE (a b : Dig lam) : NoGT (nodeE (K := K) (L := L) a b) :=
  ⟨fun _ _ h => (by cases h), fun _ => trivial⟩

theorem nog_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool), NoGT (leavesE (lam := lam) (K := K) (L := L) sMT l)
  | [] => trivial
  | (b, bl) :: t => (nog_leafE sMT b bl).bind fun _ => (nog_leavesE sMT t).bind fun _ => trivial

theorem nog_pairUp {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, NoGT (node a b)) :
    ∀ l : List D, NoGT (pairUp node l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (hn a b).bind fun _ => (nog_pairUp hn t).bind fun _ => trivial

theorem nog_levelsM {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, NoGT (node a b)) :
    ∀ (d : ℕ) (l : List D), NoGT (levelsM node d l)
  | 0, _ => trivial
  | d + 1, l => (nog_pairUp hn l).bind fun _ => (nog_levelsM hn d _).bind fun _ => trivial

theorem nog_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    NoGT (commitE (lam := lam) (K := K) (L := L) sMT d leaf) :=
  (nog_leavesE sMT _).bind fun x => (nog_levelsM nog_nodeE d x.1).bind fun _ => trivial

variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- The node: a sample and a tree over an encoded index -/
theorem nog_nodeP' (i : I) : NoGT (nodeP' W WP p i) :=
  (nog_drawT WP.ri).bind fun _ => (nog_commitE p.sMT W.depth _).bind fun _ => trivial

theorem eraseR_nodeP' (i : I) (vs : List Bits) :
    eraseR (nodeP' W WP p i) vs = erase (nodeP' W WP p i) vs :=
  eraseR_of_noGT (nog_nodeP' W WP p i) vs

end Compile.Batch
