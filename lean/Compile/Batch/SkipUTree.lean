-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SkipUTree.lean: the Merkle trees of the two provers, in the relation `Rom.Skip`. First
part of the proof of `Spec.skipPp` (Compile/Batch/SpecSkipU.lean). (Words of this library:
lean/GLOSSARY.md.)

`Skip Q w c₁ c₂` (Rom/Skip.lean) says that c₂ is c₁ without work that is never shown. The
correspondence w says which tokens of c₁ and c₂ denote the same string (`w.ρ`), and which tokens of
c₁ are dead (`w.dd`: c₂ has no such token and c₁ never shows it).

  Part 1  when two lists of tokens, two lists of lists of tokens, two token trees, two optional
          token trees, two lists of token trees correspond under w (`RL`, `RLL`, `RT`, `ROT`,
          `RLT`); a list of dead tokens (`DL`);
          all of these stay true under a larger correspondence; the pure functions that pick tokens
          from lists give corresponding tokens if `w.ρ 0 0`
  Part 2  both programs build the same tree on corresponding tokens: the trees correspond
  Part 3  the first program alone builds a tree over a message of an empty slot, and the second does
          nothing meanwhile; its leaves' digests, and each level over dead tokens, are dead
  Part 4  both programs open a leaf of corresponding trees, if `w.ρ 0 0`: the openings are equal
  Part 5  the request tree: the leaf of a full slot is hashed by both programs; the leaf of an empty
          slot is hashed by the first program from a dead slot value and sampled by the second. If
          the slot values correspond (`RC`), the two request trees correspond. This is the one place
          where the rule `markedF` of Rom/Skip.lean is used

Limits: nothing about probability and nothing about runs: these are statements about programs as
terms.
-/
import Compile.Batch.SpecSkipU
import Mathlib.Data.List.Forall2

noncomputable section

namespace Compile.Batch.SkipU
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. Corresponding lists and trees -/

section Lists
variable {α β : Type} {R : α → β → Prop}

theorem f2_getD {d₁ : α} {d₂ : β} (hd : R d₁ d₂) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ j, R (l₁.getD j d₁) (l₂.getD j d₂)
  | _, _, .nil, _ => hd
  | _, _, .cons h _, 0 => h
  | _, _, .cons _ t, j + 1 => by simpa using f2_getD hd t j

theorem f2_headD {d₁ : α} {d₂ : β} (hd : R d₁ d₂) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → R (l₁.headD d₁) (l₂.headD d₂)
  | _, _, .nil => hd
  | _, _, .cons h _ => h

theorem f2_getLastD :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ R l₁ l₂ → ∀ {d₁ : α} {d₂ : β}, R d₁ d₂ → R (l₁.getLastD d₁) (l₂.getLastD d₂)
  | _, _, .nil, _, _, hd => hd
  | _, _, .cons h t, _, _, _ => by
    rw [List.getLastD_cons, List.getLastD_cons]
    exact f2_getLastD t h

theorem f2_tail :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁.tail l₂.tail
  | _, _, .nil => .nil
  | _, _, .cons _ t => t

theorem f2_app {l₂ : List α} {l₂' : List β} :
    ∀ {l₁ : List α} {l₁' : List β},
      List.Forall₂ R l₁ l₁' → List.Forall₂ R l₂ l₂' → List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, .nil, h₂ => h₂
  | _, _, .cons h t, h₂ => .cons h (f2_app t h₂)

theorem f2_snoc {l₁ : List α} {l₁' : List β} {a : α} {b : β}
    (h : List.Forall₂ R l₁ l₁') (hab : R a b) :
    List.Forall₂ R (l₁ ++ [a]) (l₁' ++ [b]) :=
  f2_app h (.cons hab .nil)

end Lists

/-- two lists of tokens correspond, entry by entry -/
abbrev RL (w : Wd) : List Tok → List Tok → Prop := List.Forall₂ w.ρ
/-- two lists of lists of tokens correspond -/
abbrev RLL (w : Wd) : List (List Tok) → List (List Tok) → Prop := List.Forall₂ (RL w)
/-- all tokens of a list are dead -/
def DL (w : Wd) (l : List Tok) : Prop := ∀ t ∈ l, w.dd t

/-- two token trees correspond -/
structure RT (w : Wd) (t₁ t₂ : TTree) : Prop where
  levels : RLL w t₁.levels t₂.levels
  salts : RL w t₁.salts t₂.salts

/-- two optional token trees correspond -/
def ROT (w : Wd) : Option TTree → Option TTree → Prop
  | some a, some b => RT w a b
  | none, none => True
  | _, _ => False

theorem RL.mono {w v : Wd} (h : w ≤ v) {l₁ l₂ : List Tok} (hl : RL w l₁ l₂) : RL v l₁ l₂ :=
  Skip.forall₂_mono h hl
theorem RLL.mono {w v : Wd} (h : w ≤ v) {l₁ l₂ : List (List Tok)} (hl : RLL w l₁ l₂) :
    RLL v l₁ l₂ :=
  hl.imp fun _ _ x => RL.mono h x
theorem DL.mono {w v : Wd} (h : w ≤ v) {l : List Tok} (hl : DL w l) : DL v l := fun t ht =>
  h.dd t (hl t ht)
theorem RT.mono {w v : Wd} (h : w ≤ v) {t₁ t₂ : TTree} (ht : RT w t₁ t₂) : RT v t₁ t₂ :=
  ⟨RLL.mono h ht.levels, RL.mono h ht.salts⟩
theorem ROT.mono {w v : Wd} (h : w ≤ v) : ∀ {t₁ t₂ : Option TTree}, ROT w t₁ t₂ → ROT v t₁ t₂
  | some _, some _, ht => RT.mono h ht
  | none, none, _ => trivial
theorem ROTs.mono {w v : Wd} (h : w ≤ v)
    {l₁ l₂ : List (Option TTree)} (hl : List.Forall₂ (ROT w) l₁ l₂) : List.Forall₂ (ROT v) l₁ l₂ :=
  hl.imp fun _ _ x => ROT.mono h x

theorem rl_rootOf {w : Wd} (h0 : w.ρ 0 0) {l₁ l₂ : List (List Tok)} (h : RLL w l₁ l₂) :
    w.ρ (rootOf l₁) (rootOf l₂) :=
  f2_headD h0 (f2_getLastD h .nil)

theorem RT.root {w : Wd} (h0 : w.ρ 0 0) {t₁ t₂ : TTree} (h : RT w t₁ t₂) : w.ρ t₁.root t₂.root :=
  rl_rootOf h0 h.levels

/-- two lists of token trees correspond, tree by tree: the trees over one component of a round -/
abbrev RLT (w : Wd) : List TTree → List TTree → Prop := List.Forall₂ (RT w)

theorem RLT.mono {w v : Wd} (h : w ≤ v) {l₁ l₂ : List TTree} (hl : RLT w l₁ l₂) : RLT v l₁ l₂ :=
  hl.imp fun _ _ x => RT.mono h x

theorem RLTs.mono {w v : Wd} (h : w ≤ v)
    {l₁ l₂ : List (List TTree)} (hl : List.Forall₂ (RLT w) l₁ l₂) : List.Forall₂ (RLT v) l₁ l₂ :=
  hl.imp fun _ _ x => RLT.mono h x

/-- the roots correspond, in the order of the trees -/
theorem RLT.roots {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {l₁ l₂ : List TTree}, RLT w l₁ l₂ → RL w (l₁.map TTree.root) (l₂.map TTree.root)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (RT.root h0 h) (RLT.roots h0 t)

/-- at one tree, or none, `RLT` is `ROT` -/
theorem rlt_toList {w : Wd} : ∀ {a b : Option TTree}, RLT w a.toList b.toList ↔ ROT w a b
  | some _, some _ => ⟨fun h => (List.forall₂_cons.mp h).1, fun h => .cons h .nil⟩
  | none, none => ⟨fun _ => trivial, fun _ => .nil⟩
  | some _, none => ⟨nofun, False.elim⟩
  | none, some _ => ⟨nofun, False.elim⟩

theorem rl_pathOf {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {l₁ l₂ : List (List Tok)}, RLL w l₁ l₂ → ∀ j, RL w (pathOf l₁ j) (pathOf l₂ j)
  | _, _, .nil, _ => .nil
  | _, _, .cons _ .nil, _ => .nil
  | _, _, .cons h (.cons h' t), j => .cons (f2_getD h0 h _) (rl_pathOf h0 (.cons h' t) (j / 2))

theorem rl_ancOf {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {l₁ l₂ : List (List Tok)}, RLL w l₁ l₂ → ∀ j, RL w (ancOf l₁ j) (ancOf l₂ j)
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, j => .cons (f2_getD h0 h _) (rl_ancOf h0 t (j / 2))

/-! ## Part 2. Both programs build the same tree -/

theorem sk_nodeT {w : Wd} {a₁ a₂ b₁ b₂ : Tok} (ha : w.ρ a₁ a₂) (hb : w.ρ b₁ b₂) :
    Skip (fun v c₁ c₂ => v.ρ c₁ c₂) w (nodeT (lam := lam) (K := K) (L := L) a₁ b₁) (nodeT a₂ b₂) :=
  Skip.marked' _ _ _ ha (.cons hb .nil) fun _ _ _ _ _ h => .pure h

theorem sk_rnodeT {w : Wd} {a₁ a₂ b₁ b₂ : Tok} (ha : w.ρ a₁ a₂) (hb : w.ρ b₁ b₂) :
    Skip (fun v c₁ c₂ => v.ρ c₁ c₂) w
      (rnodeT (lam := lam) (K := K) (L := L) a₁ b₁) (rnodeT a₂ b₂) :=
  Skip.marked' _ _ _ ha (.cons hb .nil) fun _ _ _ _ _ h => .pure h

section Levels
variable {hN : Tok → Tok → St lam K L Tok}
  (H : ∀ (w : Wd) (a₁ a₂ b₁ b₂ : Tok),
    w.ρ a₁ a₂ → w.ρ b₁ b₂ → Skip (fun v c₁ c₂ => v.ρ c₁ c₂) w (hN a₁ b₁) (hN a₂ b₂))
include H

theorem sk_pairUp :
    ∀ (l₁ l₂ : List Tok) {w : Wd},
      RL w l₁ l₂ → Skip (fun v r₁ r₂ => RL v r₁ r₂) w (pairUp hN l₁) (pairUp hN l₂)
  | [], _, _, .nil => .pure .nil
  | [_], _, _, .cons h .nil => .pure (.cons h .nil)
  | a₁ :: b₁ :: t₁, a₂ :: b₂ :: t₂, w, .cons ha (.cons hb ht) => by
    show Skip _ w ((hN a₁ b₁).bind fun c => (pairUp hN t₁).bind fun r => Step.pure (c :: r))
      ((hN a₂ b₂).bind fun c => (pairUp hN t₂).bind fun r => Step.pure (c :: r))
    refine (H w _ _ _ _ ha hb).bind' fun v c₁ c₂ hv hc => ?_
    refine (sk_pairUp t₁ t₂ (RL.mono hv ht)).bind' fun v' r₁ r₂ hv' hr => ?_
    exact .pure (.cons (hv'.ρ _ _ hc) hr)

theorem sk_levelsM :
    ∀ (d : ℕ) {l₁ l₂ : List Tok} {w : Wd},
      RL w l₁ l₂ → Skip (fun v r₁ r₂ => RLL v r₁ r₂) w (levelsM hN d l₁) (levelsM hN d l₂)
  | 0, _, _, _, h => .pure (.cons h .nil)
  | d + 1, l₁, l₂, w, h => by
    show Skip _ w ((pairUp hN l₁).bind fun u => (levelsM hN d u).bind fun r => Step.pure (l₁ :: r))
      ((pairUp hN l₂).bind fun u => (levelsM hN d u).bind fun r => Step.pure (l₂ :: r))
    refine (sk_pairUp H l₁ l₂ h).bind' fun v u₁ u₂ hv hu => ?_
    refine (sk_levelsM d hu).bind' fun v' r₁ r₂ hv' hr => ?_
    exact .pure (.cons (RL.mono (Wd.le_trans hv hv') h) hr)

end Levels

theorem sk_leafT (sMT : ℕ) (b : Body L) (w : Wd) :
    Skip (fun v x₁ x₂ => v.ρ x₁.1 x₂.1 ∧ v.ρ x₁.2 x₂.2) w
      (leafT (lam := lam) (K := K) sMT b) (leafT sMT b) :=
  Skip.fresh' _ fun _ _ _ _ hs =>
    Skip.marked' _ _ _ hs .nil fun _ _ _ _ hv hd => .pure ⟨hv.ρ _ _ hs, hd⟩

theorem sk_leavesT (sMT : ℕ) :
    ∀ (bs : List (Body L)) (w : Wd), Skip (fun v x₁ x₂ => RL v x₁.1 x₂.1 ∧ RL v x₁.2 x₂.2) w
      (leavesT (lam := lam) (K := K) sMT bs) (leavesT sMT bs)
  | [], _ => .pure ⟨.nil, .nil⟩
  | b :: t, w => by
    show Skip _ w
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
    refine (sk_leafT sMT b w).bind' fun v x₁ x₂ _ hx => ?_
    refine (sk_leavesT sMT t v).bind' fun v' r₁ r₂ hv' hr => ?_
    exact .pure ⟨.cons (hv'.ρ _ _ hx.2) hr.1, .cons (hv'.ρ _ _ hx.1) hr.2⟩

/-- both programs commit to the same leaves: the trees correspond -/
theorem sk_commitT (sMT depth : ℕ) (leaf : ℕ → Body L) (w : Wd) :
    Skip (fun v t₁ t₂ => RT v t₁ t₂) w
      (commitT (lam := lam) (K := K) sMT depth leaf) (commitT sMT depth leaf) := by
  show Skip _ w
    ((leavesT sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
      (levelsM nodeT depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree))
    ((leavesT sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
      (levelsM nodeT depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree))
  refine (sk_leavesT sMT _ w).bind' fun v x₁ x₂ _ hx => ?_
  refine (sk_levelsM (fun _ _ _ _ _ => sk_nodeT) depth hx.1).bind' fun v' r₁ r₂ hv' hr => ?_
  exact .pure ⟨hr, RL.mono hv' hx.2⟩

/-! ## Part 3. The first program alone builds a tree: the second does nothing meanwhile -/

theorem skL_nodeT {w : Wd} {a : Tok} (b : Tok) (ha : w.dd a) :
    Skip (fun v c (_ : Unit) => v.dd c) w
      (nodeT (lam := lam) (K := K) (L := L) a b) (Step.pure ()) :=
  Skip.markedL' _ _ _ _ ha fun _ _ _ _ h => .pure h

theorem skL_pairUp :
    ∀ (l : List Tok) {w : Wd}, DL w l →
      Skip (fun v r (_ : Unit) => DL v r) w
        (pairUp (nodeT (lam := lam) (K := K) (L := L)) l) (Step.pure ())
  | [], _, h => .pure h
  | [_], _, h => .pure h
  | a :: b :: t, w, h => by
    show Skip _ w ((nodeT a b).bind fun c => (pairUp nodeT t).bind fun r => Step.pure (c :: r)) _
    refine (skL_nodeT b (h a (by simp))).bindL fun v c hv hc => ?_
    refine (skL_pairUp t (DL.mono hv fun x hx => h x (by simp [hx]))).bindL fun v' r hv' hr => ?_
    refine .pure fun x hx => ?_
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv'.dd _ hc
    · exact hr x hx

theorem skL_levelsM :
    ∀ (d : ℕ) {l : List Tok} {w : Wd}, DL w l →
      Skip (fun _ _ (_ : Unit) => True) w
        (levelsM (nodeT (lam := lam) (K := K) (L := L)) d l) (Step.pure ())
  | 0, _, _, _ => .pure trivial
  | d + 1, l, w, h => by
    show Skip _ w
      ((pairUp nodeT l).bind fun u => (levelsM nodeT d u).bind fun r => Step.pure (l :: r)) _
    refine (skL_pairUp l h).bindL fun v u _ hu => ?_
    refine (skL_levelsM d hu).bindL fun v' r _ _ => ?_
    exact .pure trivial

theorem skL_leafT (sMT : ℕ) (b : Body L) (w : Wd) :
    Skip (fun v x (_ : Unit) => v.dd x.2) w (leafT (lam := lam) (K := K) sMT b) (Step.pure ()) :=
  Skip.freshL' _ fun _ _ _ hs => Skip.markedL' _ _ _ _ hs fun _ _ _ _ hd => .pure hd

theorem skL_leavesT (sMT : ℕ) :
    ∀ (bs : List (Body L)) (w : Wd),
      Skip (fun v x (_ : Unit) => DL v x.1) w (leavesT (lam := lam) (K := K) sMT bs) (Step.pure ())
  | [], _ => .pure fun _ h => nomatch h
  | b :: t, w => by
    show Skip _ w
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
      _
    refine (skL_leafT sMT b w).bindL fun v x _ hx => ?_
    refine (skL_leavesT sMT t v).bindL fun v' r hv' hr => ?_
    refine .pure fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hv'.dd _ hx
    · exact hr y hy

/-- the first program alone commits to a message: the second program has nothing to do -/
theorem skL_commitT (sMT depth : ℕ) (leaf : ℕ → Body L) (w : Wd) :
    Skip (fun _ _ (_ : Unit) => True) w
      (commitT (lam := lam) (K := K) sMT depth leaf) (Step.pure ()) := by
  show Skip _ w
    ((leavesT sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
      (levelsM nodeT depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree)) _
  refine (skL_leavesT sMT _ w).bindL fun v x _ hx => ?_
  refine (skL_levelsM depth hx).bindL fun v' r _ _ => ?_
  exact .pure trivial

/-! ## Part 4. Openings -/

theorem sk_openT {σ : Type} {w : Wd} (h0 : w.ρ 0 0) {t₁ t₂ : TTree}
    (h : RT w t₁ t₂) (j : ℕ) (a : σ) :
    Skip (fun _ o₁ o₂ => o₁ = o₂) w
      (openT (lam := lam) (K := K) (L := L) t₁ j a) (openT t₂ j a) := by
  have hp := rl_pathOf h0 h.levels j
  refine Skip.reveal (.cons (f2_getD h0 h.salts j) (f2_app hp (rl_ancOf h0 h.levels j)))
    fun vs => .pure ?_
  rw [hp.length_eq]

/-- the tokens of a tree over an encoded index denote the same strings in both programs -/
def SelfE (w : Wd) (t : TreeH lam) : Prop := ∀ s s', some (s, s') ∈ t.salts → w.ρ s s ∧ w.ρ s' s'

theorem SelfE.mono {w v : Wd} (h : w ≤ v) {t : TreeH lam} (ht : SelfE w t) : SelfE v t :=
  fun s s' hs => ⟨h.ρ _ _ (ht s s' hs).1, h.ρ _ _ (ht s s' hs).2⟩

theorem sk_openE {σ : Type} {w : Wd} {t : TreeH lam} (h : SelfE w t) (j : ℕ) (a : σ) :
    Skip (fun _ o₁ o₂ => o₁ = o₂) w (openE (K := K) (L := L) t j a) (openE t j a) := by
  unfold openE
  cases hs : t.salts.getD j none with
  | none => exact .pure rfl
  | some ss =>
    obtain ⟨s, d⟩ := ss
    have hm : some (s, d) ∈ t.salts := by
      rw [List.getD_eq_getElem?_getD] at hs
      cases hj : t.salts[j]? with
      | none => rw [hj] at hs; cases hs
      | some y =>
        rw [hj] at hs
        obtain rfl : y = some (s, d) := hs
        exact List.mem_of_getElem? hj
    exact Skip.reveal (.cons (h s d hm).1 (.cons (h s d hm).2 .nil)) fun vs => .pure rfl

/-! ## Part 5. The request tree -/

/-- a slot value of the first program against what the second program has for the slot: the same
string, or (empty slot) nothing, and then the slot value is dead -/
def RC (w : Wd) (c₁ : Tok) : Option Tok → Prop
  | some c₂ => w.ρ c₁ c₂
  | none => w.dd c₁

theorem RC.mono {w v : Wd} (h : w ≤ v) {c₁ : Tok} : ∀ {c₂ : Option Tok}, RC w c₁ c₂ → RC v c₁ c₂
  | some _, x => h.ρ _ _ x
  | none, x => h.dd _ x

theorem RCs.mono {w v : Wd} (h : w ≤ v) {l₁ : List Tok}
    {l₂ : List (Option Tok)} (hl : List.Forall₂ (RC w) l₁ l₂) : List.Forall₂ (RC v) l₁ l₂ :=
  hl.imp fun _ _ x => RC.mono h x

/-- Under `RC` the leaves of the two request trees correspond: where the slot is empty, the first
program hashes a dead slot value and the second samples the leaf. -/
theorem sk_rleaves :
    ∀ (cs₁ : List Tok) (cs₂ : List (Option Tok)) {w : Wd}, List.Forall₂ (RC w) cs₁ cs₂ →
      Skip (fun v r₁ r₂ => RL v r₁ r₂) w
        (rleavesT (lam := lam) (K := K) (L := L) cs₁) (rleavesTU cs₂)
  | [], _, _, .nil => .pure .nil
  | c₁ :: t₁, some c₂ :: t₂, w, .cons hc ht => by
    show Skip _ w ((rleafT c₁).bind fun d => (rleavesT t₁).bind fun r => Step.pure (d :: r))
      ((rleafT c₂).bind fun d => (rleavesTU t₂).bind fun r => Step.pure (d :: r))
    refine Skip.marked' _ _ _ hc .nil fun _ v d₁ d₂ hv hd => ?_
    refine (sk_rleaves t₁ t₂ (RCs.mono hv ht)).bind' fun v' r₁ r₂ hv' hr => ?_
    exact .pure (.cons (hv'.ρ _ _ hd) hr)
  | c₁ :: t₁, none :: t₂, w, .cons hc ht => by
    show Skip _ w ((rleafT c₁).bind fun d => (rleavesT t₁).bind fun r => Step.pure (d :: r))
      (Step.fresh ((split lam K L).tl OracleName.rleaf) fun d =>
        (rleavesTU t₂).bind fun r => Step.pure (d :: r))
    refine Skip.markedF' _ _ _ _ hc fun _ v d₁ d₂ hv hd => ?_
    refine (sk_rleaves t₁ t₂ (RCs.mono hv ht)).bind' fun v' r₁ r₂ hv' hr => ?_
    exact .pure (.cons (hv'.ρ _ _ hd) hr)

/-- under `RC` the two request trees correspond -/
theorem sk_req (depthReq : ℕ) {cs₁ : List Tok} {cs₂ : List (Option Tok)}
    {w : Wd} (h : List.Forall₂ (RC w) cs₁ cs₂) :
    Skip (fun v t₁ t₂ => RT v t₁ t₂) w
      (reqT (lam := lam) (K := K) (L := L) depthReq cs₁) (reqTU depthReq cs₂) := by
  show Skip _ w
    ((rleavesT cs₁).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
    ((rleavesTU cs₂).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
  refine (sk_rleaves cs₁ cs₂ h).bind' fun v l₁ l₂ _ hl => ?_
  refine (sk_levelsM (fun _ _ _ _ _ => sk_rnodeT) depthReq hl).bind' fun v' r₁ r₂ _ hr => ?_
  exact .pure ⟨hr, .nil⟩

end Compile.Batch.SkipU
