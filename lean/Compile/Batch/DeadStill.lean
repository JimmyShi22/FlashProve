-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadStill.lean: the tree over an encoded index is made without a Fiat-Shamir query
(words of this library: lean/GLOSSARY.md).

For every relation ag on answers that relates nothing but at the Fiat-Shamir oracles `fb t` and
their ghost names `fbw t j` (`OnlyFb`, Compile/Batch/DeadFrame.lean), these programs with tokens are
`Still ag` (Compile/StillWalk.lean): they query oracles only where ag relates no two answers. So
what `erase` (Compile/Star.lean) makes of such a program depends on its answers only up to ag
(`OComp.FactorsBy`, Rom/OverOneN.lean: at every query, answers that ag relates have the same
continuation program), whatever the program returns, and although the erasure also returns its
store, the list of the tokens' strings (`Still.erase`, `OComp.StillBy.fac`).

  `still_drawT`, `still_leafT`, `still_showT`, `still_leafE`, `still_nodeE`, `still_leavesE`,
  `still_pairUp`, `still_levelsM` (both for a `node` with `Still ag (node a b)` for all a, b),
  `still_commitE`; `still_nodeP'`: a fresh encoding of the index and its salted tree (`nodeP'`,
  Compile/Batch/Star.lean).
  `no_seed`  At the auxiliary oracle `other`, `agF W` (Compile/Batch/SpecOneCall.lean) relates
             nothing: what `OComp.StillBy.derive` needs of the seed's oracle.

A separate file, because both the prover of the scheme whose proving key is (i, seed)
(Compile/Batch/DeadUP.lean) and the lazy prover (Compile/Batch/DeadL.lean) make the node, or parts
of it, again and go on with the store that this leaves.

Notation:
  `Stl`: this file's notation for `Still … ag` (Compile/StillWalk.lean);
  `i`: the index, of type I (lean/GLOSSARY.md: index);
  `sMT`: a natural number; the length of the salt of a leaf (Compile/Batch/Verifier.lean);
  `b` in `leafT`, `leafE` (Compile/Batch/TokTree.lean): a `Body L`, the body of a leaf; `blind`: a
    Bool (see `leafE`).

Limits: nothing on a program with a Fiat-Shamir query.
-/
import Compile.StillWalk
import Compile.Batch.DeadFrame
import Compile.Batch.Star

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}

local notation "Stl" => Still (S := spec lam K L) (sp := split lam K L) ag

theorem still_drawT {β : Type} (e : Enum β) : Stl (drawT (lam := lam) (K := K) (L := L) e) :=
  fun _ => trivial

theorem still_leafT (hag : OnlyFb ag) (sMT : ℕ) (b : Body L) :
    Stl (leafT (lam := lam) (K := K) sMT b) :=
  fun _ => ⟨fun q r r' => no_leaf hag q r r', fun _ _ => trivial⟩

theorem still_showT (t : Tok) : Stl (showT (lam := lam) (K := K) (L := L) t) := fun _ => trivial

theorem still_leafE (hag : OnlyFb ag) (sMT : ℕ) (b : Body L) (blind : Bool) :
    Stl (leafE (lam := lam) (K := K) sMT b blind) := by
  unfold leafE
  cases blind
  · exact ⟨fun r r' => no_leaf hag _ r r', fun _ => trivial⟩
  · exact (still_leafT hag sMT b).bind fun x => (still_showT x.2).bind fun _ => trivial

theorem still_nodeE (hag : OnlyFb ag) (a b : Dig lam) : Stl (nodeE (K := K) (L := L) a b) :=
  ⟨fun r r' => no_node hag _ r r', fun _ => trivial⟩

theorem still_leavesE (hag : OnlyFb ag) (sMT : ℕ) :
    ∀ l : List (Body L × Bool), Stl (leavesE (lam := lam) (K := K) (L := L) sMT l)
  | [] => trivial
  | (b, bl) :: t =>
    (still_leafE hag sMT b bl).bind fun _ => (still_leavesE hag sMT t).bind fun _ => trivial

theorem still_pairUp {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, Stl (node a b)) :
    ∀ l : List D, Stl (pairUp node l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (hn a b).bind fun _ => (still_pairUp hn t).bind fun _ => trivial

theorem still_levelsM {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, Stl (node a b)) :
    ∀ (d : ℕ) (l : List D), Stl (levelsM node d l)
  | 0, _ => trivial
  | d + 1, l => (still_pairUp hn l).bind fun _ => (still_levelsM hn d _).bind fun _ => trivial

theorem still_commitE (hag : OnlyFb ag) (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Stl (commitE (lam := lam) (K := K) (L := L) sMT d leaf) :=
  (still_leavesE hag sMT _).bind fun x =>
    (still_levelsM (still_nodeE hag) d x.1).bind fun _ => trivial

end Compile.Batch.Dead

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- Under `OnlyFb`: a fresh encoding of the index and its salted tree (`nodeP'`) is `Still ag`. -/
theorem still_nodeP' (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag) (i : I) :
    Still (S := spec lam W.K L) (sp := split lam W.K L) ag (nodeP' W WP p i) :=
  (still_drawT WP.ri).bind fun _ => (still_commitE hag p.sMT W.depth _).bind fun _ => trivial

/-- at the seed's oracle `other` the relation relates nothing -/
theorem no_seed (W : QueryLayout lam L) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) :
    ∀ q r r', ¬ agF W σ.o q r r' := by
  rw [hσ]
  exact fun _ _ _ h => h

end Compile.Batch.Dead
