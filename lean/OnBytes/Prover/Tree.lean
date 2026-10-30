-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Tree.lean: under fixed oracle functions the compiled prover's tree builders
(OnBytes/Prover/Defs.lean) yield trees that are kept rightly (OnBytes/Prover/Inv.lean).

Main names:
  `det_leavesO`, `det_treeO`   the values of `leavesO` and `treeO` under g
  `treeO_at`      the tree that is built is kept rightly, over the inputs that were given
  `treesO_at`, `treesO_at0`   the trees of a component meet `CompAt`, if every salt has sMT bits
  `treesO_salt`   every leaf of these trees has the salt that was handed in
  `TreeK.At.length_path`, `TreeK.At.climb`   in a tree that is kept rightly the path of leaf j has
                  one digest for each level and climbs from that leaf's digest to the root
  `noCoin_leavesO`   the leaves' builder has no coins (the trees': OnBytes/Prover/Returns.lean)

Limits: nothing on probability; salts by their lengths alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Inv

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem det_leavesO (g : Fam (typedOracleFamily lam K L)) : ∀ xs : List (LeafIn L),
    (leavesO (K := K) xs).det g = xs.map fun x => (g OracleName.leaf x : Dig lam)
  | [] => rfl
  | x :: xs => by
    show ((askTypedOracle (L := L) (K := K) OracleName.leaf x).bind fun u =>
      (leavesO xs).bind fun us => OComp.pure (u :: us)).det g = _
    rw [OComp.det_bind, OComp.det_bind, det_leavesO g xs]
    rfl

theorem det_levelsO (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (l : List (Dig lam)) :
    (levelsM (hashTreeNode (K := K) (L := L)) d l).det g = levelsF (nodeAt g) d l :=
  Evaluates.levelsM (evaluates_det g) (qN := hashTreeNode (K := K) (L := L)) (hN := nodeAt g)
    (fun _ _ => rfl) d l

theorem det_treeO (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (inp : ℕ → LeafIn L) :
    (treeO (K := K) d inp).det g =
      ⟨inp, levelsF (nodeAt g) d
        ((List.range (2 ^ d)).map fun j => (g OracleName.leaf (inp j) : Dig lam))⟩ := by
  unfold treeO
  rw [OComp.det_bind, OComp.det_bind, det_leavesO, det_levelsO]
  show (⟨inp, levelsF (nodeAt g) d
    (List.map (β := Dig lam) (fun x => g OracleName.leaf x) ((List.range (2 ^ d)).map inp))⟩ :
      TreeK lam L) = _
  rw [List.map_map]
  rfl

/-- The tree that is built is kept rightly, over the inputs that were given. -/
theorem treeO_at (g : Fam (typedOracleFamily lam K L)) (d : ℕ) (inp : ℕ → LeafIn L) :
    ((treeO (K := K) d inp).det g).At g d ∧ ((treeO (K := K) d inp).det g).inp = inp := by
  rw [det_treeO]
  exact ⟨rfl, rfl⟩

theorem det_treesO_cons (g : Fam (typedOracleFamily lam K L)) {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) (k d : ℕ)
    (ds : List ℕ) :
    (treesO (K := K) pad sl posAt emb o k (d :: ds)).det g =
      (treeO (K := K) d fun j => ⟨match posAt k j with
          | some p => emb p (r.rd o p)
          | none => pad, sl k j⟩).det g ::
        (treesO (K := K) pad sl posAt emb o (k + 1) ds).det g := by
  show ((treeO (K := K) d _).bind fun T =>
    (treesO pad sl posAt emb o (k + 1) ds).bind fun Ts => OComp.pure (T :: Ts)).det g = _
  rw [OComp.det_bind, OComp.det_bind]
  rfl

/-- The trees of a component, from tree number k on. -/
theorem treesO_at (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) {r : Round} (pad : Body L)
    (sl : ℕ → ℕ → Bits) (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (hs : ∀ n j, (sl n j).length = sMT) : ∀ (k : ℕ) (ds : List ℕ),
    CompAt g sMT (fun n j => posAt (k + n) j) emb o ds
      ((treesO (K := K) pad sl posAt emb o k ds).det g)
  | _, [] => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | k, d :: ds => by
    obtain ⟨ihl, ih⟩ := treesO_at g sMT pad sl posAt emb o hs (k + 1) ds
    rw [det_treesO_cons]
    refine ⟨by rw [List.length_cons, List.length_cons, ihl], fun n d' T hd hT => ?_⟩
    cases n with
    | zero =>
      obtain rfl : d = d' := by simpa using hd
      obtain rfl : _ = T := by simpa using hT
      refine ⟨(treeO_at g d _).1, fun j p hp => ?_⟩
      rw [(treeO_at g d _).2]
      have hp' : posAt k j = some p := hp
      exact ⟨by simp only [hp'], hs k j⟩
    | succ n =>
      obtain ⟨hA, hl⟩ := ih n d' T (by simpa using hd) (by simpa using hT)
      refine ⟨hA, fun j p hp => hl j p ?_⟩
      have e : k + (n + 1) = k + 1 + n := by omega
      show posAt (k + 1 + n) j = some p
      rw [← e]
      exact hp

/-- The trees of a component. -/
theorem treesO_at0 (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) {r : Round} (pad : Body L)
    (sl : ℕ → ℕ → Bits) (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (hs : ∀ n j, (sl n j).length = sMT) (ds : List ℕ) :
    CompAt g sMT posAt emb o ds ((treesO (K := K) pad sl posAt emb o 0 ds).det g) := by
  have h := treesO_at (K := K) g sMT pad sl posAt emb o hs 0 ds
  simpa only [Nat.zero_add] using h

/-- every leaf of the trees of a component has the salt that was handed in -/
theorem treesO_salt (g : Fam (typedOracleFamily lam K L)) {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ) (n : ℕ) (T : TreeK lam L),
      ((treesO (K := K) pad sl posAt emb o k ds).det g)[n]? = some T →
      ∀ j, (T.inp j).salt = sl (k + n) j
  | _, [], _, _, h, _ => by simp [treesO, OComp.det] at h
  | k, d :: ds, n, T, h, j => by
    rw [det_treesO_cons] at h
    cases n with
    | zero =>
      obtain rfl : _ = T := by simpa using h
      rw [(treeO_at g d _).2]
      rfl
    | succ n =>
      have := treesO_salt g pad sl posAt emb o (k + 1) ds n T (by simpa using h) j
      rwa [show k + 1 + n = k + (n + 1) by omega] at this

/-! ## Paths -/

theorem TreeK.At.length_path {g : Fam (typedOracleFamily lam K L)} {d : ℕ} {T : TreeK lam L} (h : T.At g d)
    (j : ℕ) : (pathOf T.lv j).length = d := by
  rw [h]
  exact length_pathOf_levelsF _ d _ j

theorem TreeK.At.climb {g : Fam (typedOracleFamily lam K L)} {d : ℕ} {T : TreeK lam L} (h : T.At g d) {j : ℕ}
    (hj : j < 2 ^ d) :
    climbF (nodeAt g) (pathOf T.lv j) j (g OracleName.leaf (T.inp j) : Dig lam) = T.root := by
  have hl : (List.map (β := Dig lam) (fun j => g OracleName.leaf (T.inp j)) (List.range (2 ^ d))).length =
      2 ^ d := by
    rw [List.length_map, List.length_range]
  have hg : (List.map (β := Dig lam) (fun j => g OracleName.leaf (T.inp j)) (List.range (2 ^ d))).getD j
      default = g OracleName.leaf (T.inp j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have := climbF_pathOf (nodeAt g) d _ j hl hj
  rw [hg] at this
  unfold TreeK.root
  rw [h]
  exact this

/-! ## No coins -/

theorem noCoin_leavesO : ∀ xs : List (LeafIn L), (leavesO (lam := lam) (K := K) xs).NoCoin
  | [] => trivial
  | _ :: xs => fun _ => (noCoin_leavesO xs).bind fun _ => trivial

end OnBytes.Prover
