-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedParTree.lean: the token trees of the compiled prover do not look at the numbers of
their tokens. (Words of this library: lean/GLOSSARY.md.)

A token is the number of a secret string in the store on which a token program runs.
`Compile.Seed.Par N₀ δ r c c'` (Compile/SeedKit.lean) says: c on a store, and c' on the store
without the δ strings after the first N₀, make the same queries and take the same samples, and their
results are related by r. A token t of c' is the token `Life2.up N₀ δ t` of c.

The one difficulty. The programs of Compile/Batch/TokTree.lean read lists of tokens with a default
value: the number 0 where the list has no entry (`rootOf`, `pathOf`, `ancOf`, `getD j 0`).
`up N₀ δ 0` is δ, not 0, if N₀ = 0. So "read, then renumber" is "renumber, then read" only where the
default value is not read, and that is so in a full tree.

  Part 1  `FullLv d lv`: d + 1 levels of the lengths 2^d, .., 2, 1. In full levels `rootOf`,
          `pathOf · j` and `ancOf · j` (j < 2^d) commute with every function of the entries
  Part 2  `upTT`: a token tree with its tokens renumbered. `FullT d t`: full levels and 2^d salts
  Part 3  the programs on two stores. The result of `commitT` is full; that of `reqT` (on 2^depthReq
          slot values) has full levels

Limits: nothing about a request tree over a number of slot values other than 2^depthReq: there the
root can be the default value, and the statement would be false (`root_upTT` asks `FullLv`).
-/
import Compile.Batch.SeedParNode
import Mathlib.Data.List.Forall2

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

open Life2 (up)
open Compile.Seed (Par)

/-! ## Part 1. Full levels -/

section Full
variable {D D' : Type}

/-- d + 1 levels of the lengths 2^d, .., 2, 1 -/
def FullLv : ℕ → List (List D) → Prop
  | 0, lv => ∃ a, lv = [[a]]
  | d + 1, lv => ∃ l ls, lv = l :: ls ∧ l.length = 2 ^ (d + 1) ∧ FullLv d ls

theorem FullLv.ne : ∀ {d : ℕ} {lv : List (List D)}, FullLv d lv → ∃ l ls, lv = l :: ls
  | 0, _, ⟨a, h⟩ => ⟨[a], [], h⟩
  | _ + 1, _, ⟨l, ls, h, _⟩ => ⟨l, ls, h⟩

theorem getD_map_of_lt [Inhabited D] [Inhabited D'] (φ : D → D') {l : List D}
    {i : ℕ} (h : i < l.length) :
    (l.map φ).getD i default = φ (l.getD i default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some]

variable [Inhabited D] [Inhabited D'] (φ : D → D')

theorem rootOf_cons (l l' : List D) (ls : List (List D)) :
    rootOf (l :: l' :: ls) = rootOf (l' :: ls) := rfl

theorem rootOf_map :
    ∀ {d : ℕ} {lv : List (List D)}, FullLv d lv → rootOf (lv.map (List.map φ)) = φ (rootOf lv)
  | 0, _, ⟨a, h⟩ => by subst h; rfl
  | d + 1, _, ⟨l, ls, h, _, hf⟩ => by
    subst h
    obtain ⟨l', ls', rfl⟩ := hf.ne
    exact (rootOf_map hf : rootOf ((l' :: ls').map (List.map φ)) = φ (rootOf (l' :: ls')))

theorem sib_lt {j n : ℕ} (h : j < 2 * n) : (if j % 2 = 0 then j + 1 else j - 1) < 2 * n := by
  split_ifs <;> omega

theorem pathOf_map :
    ∀ {d : ℕ} {lv : List (List D)} {j : ℕ},
      FullLv d lv → j < 2 ^ d → pathOf (lv.map (List.map φ)) j = (pathOf lv j).map φ
  | 0, _, _, ⟨a, h⟩, _ => by subst h; rfl
  | d + 1, _, j, ⟨l, ls, h, hl, hf⟩, hj => by
    subst h
    obtain ⟨l', ls', rfl⟩ := hf.ne
    have hj' : j < 2 * 2 ^ d := by rw [pow_succ] at hj; omega
    show (l.map φ).getD (if j % 2 = 0 then j + 1 else j - 1) default ::
        pathOf ((l' :: ls').map (List.map φ)) (j / 2) =
      φ (l.getD (if j % 2 = 0 then j + 1 else j - 1) default) :: (pathOf (l' :: ls') (j / 2)).map φ
    rw [getD_map_of_lt φ (by rw [hl, pow_succ, mul_comm]; exact sib_lt hj'),
      pathOf_map hf (by omega)]

theorem ancOf_map :
    ∀ {d : ℕ} {lv : List (List D)} {j : ℕ},
      FullLv d lv → j < 2 ^ d → ancOf (lv.map (List.map φ)) j = (ancOf lv j).map φ
  | 0, _, j, ⟨a, h⟩, hj => by
    subst h
    have : j = 0 := by simpa using hj
    subst this
    rfl
  | d + 1, _, j, ⟨l, ls, h, hl, hf⟩, hj => by
    subst h
    have hj' : j < 2 * 2 ^ d := by rw [pow_succ] at hj; omega
    show (l.map φ).getD j default :: ancOf (ls.map (List.map φ)) (j / 2) =
      φ (l.getD j default) :: (ancOf ls (j / 2)).map φ
    rw [getD_map_of_lt φ (by rw [hl]; exact hj), ancOf_map hf (by omega)]

end Full

/-! ## Part 2. Token trees, renumbered -/

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (N₀ δ : ℕ)

/-- the tokens of a token tree, shown through Life2.up (renumbered) -/
def upTT (t : TTree) : TTree := ⟨t.levels.map (List.map (up N₀ δ)), t.salts.map (up N₀ δ)⟩

/-- a full tree of the depth d over salted leaves -/
def FullT (d : ℕ) (t : TTree) : Prop := FullLv d t.levels ∧ t.salts.length = 2 ^ d

variable {N₀ δ}

theorem root_upTT {d : ℕ} {t : TTree} (h : FullLv d t.levels) :
    (upTT N₀ δ t).root = up N₀ δ t.root := rootOf_map _ h

/-! ## Part 3. The programs on two stores -/

/-- "Par.reveal" for a list of tokens that is only equal to the renumbered list -/
theorem Par.reveal' {S : OSpec} {sp : Split S} {α β : Type} {r : α → β → Prop}
    {ts ts' : List Tok} (e : ts = ts'.map (up N₀ δ)) {k : List Bits → Step S sp α}
    {k' : List Bits → Step S sp β} (h : ∀ w, Par N₀ δ r (k w) (k' w)) :
    Par N₀ δ r (Step.reveal ts k) (Step.reveal ts' k') := by
  subst e
  exact Par.reveal h

theorem par_leavesT (sMT : ℕ) :
    ∀ l : List (Body L), Par N₀ δ
      (fun a a' =>
        a = (a'.1.map (up N₀ δ), a'.2.map (up N₀ δ)) ∧
        a'.1.length = l.length ∧
        a'.2.length = l.length)
      (leavesT (lam := lam) (K := K) sMT l) (leavesT sMT l)
  | [] => Par.pure ⟨rfl, rfl, rfl⟩
  | b :: t => by
    show Par N₀ δ _
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
    refine (par_leafT sMT b).bind fun a a' h => (par_leavesT sMT t).bind fun c c' h' => ?_
    obtain ⟨rfl, -, -⟩ := h
    obtain ⟨rfl, h1, h2⟩ := h'
    exact Par.pure ⟨rfl, congrArg (· + 1) h1, congrArg (· + 1) h2⟩

/-- a node function on tokens that does not look at their numbers -/
def ParNode (N₀ δ : ℕ) (hN : Tok → Tok → St lam K L Tok) : Prop :=
  ∀ a b, Par N₀ δ (fun c c' => c = up N₀ δ c') (hN (up N₀ δ a) (up N₀ δ b)) (hN a b)

theorem parNode_nodeT : ParNode N₀ δ (nodeT (lam := lam) (K := K) (L := L)) := fun a b =>
  Par.marked (S := spec lam K L) (sp := split lam K L) (t := a) (us := [b])
    (k := fun _ d => Step.pure d) (k' := fun _ d => Step.pure d) OracleName.node
    (fun v vs => ((v, vs.headD []) : Bits × Bits)) _ fun _ _ _ => Par.pure rfl

theorem parNode_rnodeT : ParNode N₀ δ (rnodeT (lam := lam) (K := K) (L := L)) := fun a b =>
  Par.marked (S := spec lam K L) (sp := split lam K L) (t := a) (us := [b])
    (k := fun _ d => Step.pure d) (k' := fun _ d => Step.pure d) OracleName.rnode
    (fun v vs => ((v, vs.headD []) : Bits × Bits)) _ fun _ _ _ => Par.pure rfl

theorem par_pairUpT {hN : Tok → Tok → St lam K L Tok} (hp : ParNode N₀ δ hN) :
    ∀ (l : List Tok) (n : ℕ), l.length = 2 * n →
      Par N₀ δ (fun a a' => a = a'.map (up N₀ δ) ∧ a'.length = n)
        (pairUp hN (l.map (up N₀ δ))) (pairUp hN l)
  | a :: b :: t, n, hl => by
    show Par N₀ δ _
      ((hN (up N₀ δ a) (up N₀ δ b)).bind fun c =>
        (pairUp hN (t.map (up N₀ δ))).bind fun r => Step.pure (c :: r))
      ((hN a b).bind fun c => (pairUp hN t).bind fun r => Step.pure (c :: r))
    have hl' : t.length = 2 * (n - 1) := by simp only [List.length_cons] at hl; omega
    refine (hp a b).bind fun c c' h => (par_pairUpT hp t (n - 1) hl').bind fun r r' h' => ?_
    subst h
    obtain ⟨rfl, h2⟩ := h'
    refine Par.pure ⟨rfl, ?_⟩
    simp only [List.length_cons] at hl ⊢
    omega
  | [], n, hl => Par.pure ⟨rfl, by simp only [List.length_nil] at hl ⊢; omega⟩
  | [_], n, hl => by simp only [List.length_cons, List.length_nil] at hl; omega

theorem par_levelsT {hN : Tok → Tok → St lam K L Tok} (hp : ParNode N₀ δ hN) :
    ∀ (d : ℕ) (l : List Tok), l.length = 2 ^ d →
      Par N₀ δ (fun a a' => a = a'.map (List.map (up N₀ δ)) ∧ FullLv d a')
        (levelsM hN d (l.map (up N₀ δ))) (levelsM hN d l)
  | 0, l, hl => by
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (by simpa using hl)
    exact Par.pure ⟨rfl, a, rfl⟩
  | d + 1, l, hl => by
    show Par N₀ δ _
      ((pairUp hN (l.map (up N₀ δ))).bind fun u =>
        (levelsM hN d u).bind fun r => Step.pure (l.map (up N₀ δ) :: r))
      ((pairUp hN l).bind fun u => (levelsM hN d u).bind fun r => Step.pure (l :: r))
    refine (par_pairUpT hp l (2 ^ d) (by rw [hl, pow_succ, mul_comm])).bind fun u u' h => ?_
    obtain ⟨rfl, hu⟩ := h
    refine (par_levelsT hp d u' hu).bind fun r r' h' => ?_
    obtain ⟨rfl, hf⟩ := h'
    exact Par.pure ⟨rfl, l, r', rfl, hl, hf⟩

/-- A token tree over salted leaves: its tokens are related by up, and it is full. -/
theorem par_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    Par N₀ δ (fun a a' => a = upTT N₀ δ a' ∧ FullT d a')
      (commitT (lam := lam) (K := K) sMT d leaf) (commitT sMT d leaf) := by
  show Par N₀ δ _
    ((leavesT sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
      (levelsM nodeT d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree))
    ((leavesT sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
      (levelsM nodeT d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree))
  refine (par_leavesT sMT _).bind fun x x' h => ?_
  obtain ⟨rfl, h1, h2⟩ := h
  simp only [List.length_map, List.length_range] at h1 h2
  refine (par_levelsT parNode_nodeT d x'.1 h1).bind fun lv lv' h' => ?_
  obtain ⟨rfl, hf⟩ := h'
  exact Par.pure ⟨rfl, hf, h2⟩

/-- The opening of a leaf j < 2^d of a full tree. -/
theorem par_openT {σ : Type} {d : ℕ} {t : TTree} (ht : FullT d t) {j : ℕ} (hj : j < 2 ^ d) (a : σ) :
    Par N₀ δ Eq (openT (lam := lam) (K := K) (L := L) (upTT N₀ δ t) j a) (openT t j a) := by
  unfold openT
  have e1 : (upTT N₀ δ t).salts.getD j 0 = up N₀ δ (t.salts.getD j 0) :=
    getD_map_of_lt (up N₀ δ) (by rw [ht.2]; exact hj)
  have e2 : pathOf (upTT N₀ δ t).levels j = (pathOf t.levels j).map (up N₀ δ) :=
    pathOf_map _ ht.1 hj
  have e3 : ancOf (upTT N₀ δ t).levels j = (ancOf t.levels j).map (up N₀ δ) := ancOf_map _ ht.1 hj
  rw [e1, e2, e3, List.length_map]
  exact Par.reveal' (by simp only [List.map_cons, List.map_append]) fun _ => Par.pure rfl

theorem par_rleafT (c : Tok) :
    Par N₀ δ (fun d d' => d = up N₀ δ d')
      (rleafT (lam := lam) (K := K) (L := L) (up N₀ δ c)) (rleafT c) :=
  Par.marked (S := spec lam K L) (sp := split lam K L) (t := c) (us := [])
    (k := fun _ d => Step.pure d) (k' := fun _ d => Step.pure d) OracleName.rleaf (fun v _ => (v : Bits))
    _ fun _ _ _ => Par.pure rfl

theorem par_rleavesT :
    ∀ cs : List Tok, Par N₀ δ (fun a a' => a = a'.map (up N₀ δ) ∧ a'.length = cs.length)
      (rleavesT (lam := lam) (K := K) (L := L) (cs.map (up N₀ δ))) (rleavesT cs)
  | [] => Par.pure ⟨rfl, rfl⟩
  | c :: t => by
    show Par N₀ δ _
      ((rleafT (up N₀ δ c)).bind fun d =>
        (rleavesT (t.map (up N₀ δ))).bind fun r => Step.pure (d :: r))
      ((rleafT c).bind fun d => (rleavesT t).bind fun r => Step.pure (d :: r))
    refine (par_rleafT c).bind fun d d' h => (par_rleavesT t).bind fun r r' h' => ?_
    subst h
    obtain ⟨rfl, h2⟩ := h'
    exact Par.pure ⟨rfl, congrArg (· + 1) h2⟩

/-- The request tree over 2^depthReq slot values: its tokens are related by up, and its levels are
full. -/
theorem par_reqT (depthReq : ℕ) (cs : List Tok) (hc : cs.length = 2 ^ depthReq) :
    Par N₀ δ (fun a a' => a = upTT N₀ δ a' ∧ FullLv depthReq a'.levels)
      (reqT (lam := lam) (K := K) (L := L) depthReq (cs.map (up N₀ δ))) (reqT depthReq cs) := by
  show Par N₀ δ _
    ((rleavesT (cs.map (up N₀ δ))).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
    ((rleavesT cs).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
  refine (par_rleavesT cs).bind fun ls ls' h => ?_
  obtain ⟨rfl, h1⟩ := h
  refine (par_levelsT parNode_rnodeT depthReq ls' (h1.trans hc)).bind fun lv lv' h' => ?_
  obtain ⟨rfl, hf⟩ := h'
  exact Par.pure ⟨rfl, hf⟩

end Seed
end Compile.Batch
