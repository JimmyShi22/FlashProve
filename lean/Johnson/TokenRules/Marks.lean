-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Marks.lean: THE HASHING OF A COMPILED RUN, AND THE MAKING OF A TABLE, AS TOKEN
PROGRAMS, REVEAL NOTHING AND FIT A TEST ON THE ORACLE'S NAME: the proofs of Spec.marksHash and
Spec.marksTab (Johnson/TokenRules/Spec.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

Marks mk c vs (Compile/DeferRun/Spec.lean) says that from the store vs, on every path, the program c
reveals nothing, each of its marked evaluations is at a point with mk and each ordinary one at a
point without. The tests here look at the oracle's name alone, so each proof walks the program's
text: marks_bind (two programs one after the other) and one lemma for each program of
Johnson/TokenSide/.

-/
import Johnson.TokenRules.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc (SafeO TidyO GrowsO ClosedO Deps callCostB)
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

section Calculus
variable {S : OSpec} {sp : Split S} {α β : Type}

/-- Two programs one after the other fit a test, if the first does and the second does from every
store. -/
theorem marks_bind {mk : Mark S} (c : Step S sp α) (g : α → Step S sp β)
    (hg : ∀ a vs, Marks mk (g a) vs) : ∀ vs, Marks mk c vs → Marks mk (c.bind g) vs := by
  induction c with
  | pure a => exact fun vs _ => hg a vs
  | sample n k ih => exact fun vs h r => ih r vs (h r)
  | plain o q k ih => exact fun vs h => ⟨h.1, fun r => ih r vs (h.2 r)⟩
  | fresh ℓ k ih => exact fun vs h u => ih _ _ (h u)
  | marked o t us pt inj k ih => exact fun vs h => ⟨h.1, fun r => ih _ _ _ (h.2 r)⟩
  | reveal ts k ih => exact fun vs h => h.elim

end Calculus

section Trees
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {mk : Mark (typedOracleFamily lam K L)}

theorem marks_leafT (hl : ∀ q, mk OracleName.leaf q = true) (ℓ : ℕ) (us : List Tok)
    (pre : List Bits → Bits) (b : Body L) (vs : List Bits) :
    Marks mk (leafT (K := K) ℓ us pre b) vs :=
  fun _ => ⟨hl _, fun _ => trivial⟩

theorem marks_leavesT (hl : ∀ q, mk OracleName.leaf q = true) (ℓ : ℕ) (us : List Tok)
    (pre : List Bits → Bits) : ∀ (bs : List (Body L)) (vs : List Bits),
    Marks mk (TokenSide.leavesT (K := K) ℓ us pre bs) vs
  | [], _ => trivial
  | b :: bs, vs => by
      rw [TokenSide.leavesT]
      exact marks_bind _ _
        (fun _ vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_leavesT hl ℓ us pre bs vs'))
        vs (marks_leafT hl ℓ us pre b vs)

theorem marks_nodeT (hn : ∀ q, mk OracleName.node q = false) (a b : Dig lam) (vs : List Bits) :
    Marks mk (nodeT (K := K) (L := L) a b) vs :=
  ⟨hn _, fun _ => trivial⟩

theorem marks_pairUp (hn : ∀ q, mk OracleName.node q = false) : ∀ (l : List (Dig lam)) (vs : List Bits),
    Marks mk (pairUp (nodeT (K := K) (L := L)) l) vs
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: t, vs => by
      show Marks mk ((nodeT a b).bind fun c => (pairUp nodeT t).bind fun r => Step.pure (c :: r)) vs
      exact marks_bind _ _
        (fun _ vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_pairUp hn t vs'))
        vs (marks_nodeT hn a b vs)

theorem marks_levelsM (hn : ∀ q, mk OracleName.node q = false) : ∀ (n : ℕ) (l : List (Dig lam))
    (vs : List Bits), Marks mk (levelsM (nodeT (K := K) (L := L)) n l) vs
  | 0, _, _ => trivial
  | n + 1, l, vs => by
      show Marks mk
        ((pairUp nodeT l).bind fun u => (levelsM nodeT n u).bind fun r => Step.pure (l :: r)) vs
      exact marks_bind _ _
        (fun u vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_levelsM hn n u vs'))
        vs (marks_pairUp hn l vs)

theorem marks_treeT (hl : ∀ q, mk OracleName.leaf q = true) (hn : ∀ q, mk OracleName.node q = false) (ℓ : ℕ)
    (us : List Tok) (pre : List Bits → Bits) (d : ℕ) (body : ℕ → Body L) (vs : List Bits) :
    Marks mk (treeT (K := K) ℓ us pre d body) vs := by
  unfold treeT
  exact marks_bind _ _
    (fun l vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_levelsM hn d l.1 vs'))
    vs (marks_leavesT hl ℓ us pre _ vs)

theorem marks_treesT (hl : ∀ q, mk OracleName.leaf q = true) (hn : ∀ q, mk OracleName.node q = false) {r : Round}
    (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (pad : Body L)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (ds : List ℕ) (k : ℕ) (vs : List Bits),
      Marks mk (treesT (K := K) ℓ us pre pad posAt emb o k ds) vs
  | [], _, _ => trivial
  | d :: ds, k, vs => by
      rw [treesT]
      exact marks_bind _ _
        (fun _ vs' => marks_bind _ _ (fun _ _ => by trivial) vs'
          (marks_treesT hl hn ℓ us pre pad posAt emb o ds (k + 1) vs'))
        vs (marks_treeT hl hn ℓ us pre d _ vs)

end Trees

section Chain
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem marks_fbT (t : Tag) (n i : ℕ) (tk : Tok) (us : List Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (rt : List (Dig lam)) (pl : PlainPart (shapeOf L t) (annOf L t)) (vs : List Bits) :
    Marks mkHash (fbT (K := K) t n i tk us hd hinj rt pl) vs := by
  cases n <;> exact ⟨rfl, fun _ => trivial⟩

theorem marks_climbT : ∀ (ss : List (Dig lam)) (j : ℕ) (c : Tok) (vs : List Bits),
    Marks mkHash (climbT (K := K) (L := L) ss j c) vs
  | [], _, _, _ => trivial
  | s :: ss, j, c, vs => by
      rw [climbT]
      refine marks_bind _ _
        (fun u vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_climbT ss (j / 2) u vs'))
        vs ?_
      split <;> exact ⟨rfl, fun _ => trivial⟩

theorem marks_searchT {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : ℕ → P → StT lam K L ((Fin K → Dig lam) × Tok))
    (hask : ∀ n α vs, Marks mkHash (ask n α) vs) (α : P) :
    ∀ (fuel n : ℕ) (dd : List Tok) (vs : List Bits),
      Marks mkHash (searchT gr chal ask α fuel n dd) vs
  | 0, _, _, _ => trivial
  | fuel + 1, n, dd, vs => by
      rw [searchT]
      refine marks_bind _ _ (fun a vs' => ?_) vs (hask _ _ vs)
      split
      · exact trivial
      · exact marks_searchT gr chal ask hask α fuel (n + 1) _ vs'

theorem marks_fsT {C P : Type} (gr : Option (GrW C P)) (cap : ℕ) (chal : (Fin K → Dig lam) → C)
    (ask : ℕ → P → StT lam K L ((Fin K → Dig lam) × Tok))
    (hask : ∀ n α vs, Marks mkHash (ask n α) vs) (α : P) (vs : List Bits) :
    Marks mkHash (fsT gr cap chal ask α) vs := by
  cases gr with
  | none => exact marks_bind _ _ (fun _ _ => by trivial) vs (hask 0 α vs)
  | some g => exact marks_searchT g chal ask hask α (cap + 1) 0 [] vs

theorem marks_onFsT {P β : Type} (i : ℕ) (k : Hit lam K P → StT lam K L (Res β))
    (hk : ∀ p vs, Marks mkHash (k p) vs) : ∀ (o : Option (Hit lam K P)) (vs : List Bits),
    Marks mkHash (onFsT i k o) vs
  | none, _ => trivial
  | some p, vs => hk p vs

theorem mkHash_leaf (q : (typedOracleFamily lam K L).Dom OracleName.leaf) : mkHash (K := K) (L := L) OracleName.leaf q = true :=
  rfl
theorem mkHash_node (q : (typedOracleFamily lam K L).Dom OracleName.node) : mkHash (K := K) (L := L) OracleName.node q = false :=
  rfl
theorem mkTable_leaf (q : (typedOracleFamily lam K L).Dom OracleName.leaf) :
    mkTable (K := K) (L := L) OracleName.leaf q = true := rfl
theorem mkTable_node (q : (typedOracleFamily lam K L).Dom OracleName.node) :
    mkTable (K := K) (L := L) OracleName.node q = false := rfl

theorem marks_chainT (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ : Strat s Unit)
      (vs : List Bits),
      Marks mkHash (chainT t cms x ℓ pre salt cd cap s A W embS embP i ph σ) vs
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), vs => by
      rw [chainT]
      split
      · refine marks_bind _ _ (fun TJ vs₁ => ?_) vs
          (marks_treesT mkHash_leaf mkHash_node _ _ _ _ _ _ _ _ _ vs)
        refine marks_bind _ _ (marks_onFsT i _ fun q vs₂ => ?_) vs₁
          (marks_fsT _ _ _ _ (fun n α vs' => marks_fbT t n i _ _ _ _ _ _ vs') _ vs₁)
        exact marks_bind _ _ (fun _ _ => by trivial) vs₂
          (marks_chainT t cms x ℓ pre salt cd cap s A W _ _ _ _ _ vs₂)
      · refine marks_bind _ _ (fun T0 vs₁ => ?_) vs
          (marks_treesT mkHash_leaf mkHash_node _ _ _ _ _ _ _ _ _ vs)
        refine marks_bind _ _ (marks_onFsT i _ fun q vs₂ => ?_) vs₁
          (marks_fsT _ _ _ _ (fun n α vs' => marks_fbT t n i _ _ _ _ _ _ vs') _ vs₁)
        exact marks_bind _ _ (fun _ _ => by trivial) vs₂
          (marks_chainT t cms x ℓ pre salt cd cap s A W _ _ _ _ _ vs₂)
      · refine marks_bind _ _ (fun TJ vs₁ => ?_) vs
          (marks_treesT mkHash_leaf mkHash_node _ _ _ _ _ _ _ _ _ vs)
        refine marks_bind _ _ (fun T0 vs₂ => ?_) vs₁
          (marks_treesT mkHash_leaf mkHash_node _ _ _ _ _ _ _ _ _ vs₁)
        refine marks_bind _ _ (fun c vs₃ => ?_) vs₂ ⟨rfl, fun _ => trivial⟩
        refine marks_bind _ _ (fun d vs₄ => ?_) vs₃ ⟨rfl, fun _ => trivial⟩
        refine marks_bind _ _ (fun rq vs₅ => ?_) vs₄ (marks_climbT _ _ _ vs₄)
        refine marks_bind _ _ (marks_onFsT i _ fun q vs₆ => ?_) vs₅
          (marks_fsT _ _ _ _ (fun n α vs' => marks_fbT t n i _ _ _ _ _ _ vs') _ vs₅)
        exact marks_bind _ _ (fun _ _ => by trivial) vs₆
          (marks_chainT t cms x ℓ pre salt cd cap s A W _ _ _ _ _ vs₆)
      · exact trivial

theorem marks_digsT : ∀ (n : ℕ) (vs : List Bits),
    Marks mkHash (digsT (lam := lam) (K := K) (L := L) n) vs
  | 0, _ => trivial
  | n + 1, vs => by
      rw [digsT]
      exact marks_bind _ _
        (fun _ vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_digsT n vs'))
        vs (fun _ => trivial)

theorem marks_drawD (ln : RunLen lam L) (vs : List Bits) :
    Marks mkHash (drawD (K := K) ln) vs := by
  unfold drawD
  exact marks_bind _ _
    (fun _ vs' => marks_bind _ _ (fun _ _ => by trivial) vs' (marks_digsT ln.dq vs'))
    vs (fun _ => trivial)

end Chain

/-- **The hashing of a compiled run fits mkHash.** -/
theorem marksHash : Spec.marksHash := by
  intro I X lam K L t Y E Q wq embS embP xin cms x σ ln pre cap vs
  unfold hashT
  intro u
  exact marks_bind _ _
    (fun cd vs₁ => marks_bind _ _ (fun _ _ => by trivial) vs₁
      (marks_chainT t cms (xin x) ln.fr pre _ cd cap _ _ _ _ _ _ _ _ vs₁))
    _ (marks_drawD ln _)

/-- **The making of a table fits mkTable.** -/
theorem marksTab : Spec.marksTab := by
  intro I X lam L Bd aT aL W S h tl b₀ i r vs
  unfold tabT
  exact marks_bind _ _
    (fun T vs₁ => marks_bind _ _ (fun _ _ => by trivial) vs₁
      (show Marks mkTable (seedsT W S T.root) vs₁ from ⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩))
    vs (marks_treeT mkTable_leaf mkTable_node _ _ _ _ _ vs)

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.marksHash
#print axioms OnBytes.TokenRules.marksTab
