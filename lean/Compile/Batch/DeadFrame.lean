-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadFrame.lean: the frame of the proof that the tail (the part of an answer that the
program gets as a new token: Rom/Defer.lean) of a proof-of-work attempt that is not kept is never
used: the live tokens of the prover's data; the trees; the Fiat-Shamir queries and the search over
nonces; one round in one slot (words of this library: lean/GLOSSARY.md).

To be shown of every piece c of the programs with tokens of C and P: `Compile.LiveW (agF W) T TP c`
(Compile/LiveWalk.lean; `agF`: Compile/Batch/SpecOneCall.lean): T: the live tokens in c's arguments;
TP a: those in its value. It says: c never uses the string of a dead token; and, started on a store
that holds all tokens taken as live, after two failed attempts that are not the last c goes on in
the same way and never uses the new tail's string. The tails of attempts that are not kept (the
fields `dead` of `SlotAcc` and `Acc0`; the lists dd of the search) are not live.

  `liveTT`, `liveOT`, `liveTs`, `liveAcc`, `liveA0`, `livePh`, `liveTH`  The live tokens of a token
                                                                         tree, of an optional one,
                                                                         of a list of such, of a
                                                                         slot's and of the shared
                                                                         data, of a phase, of a tree
                                                                         over an encoded index.
  Part 1  Trees: a lemma (`lw_leafT` .. `lw_drawT`) for each program on trees of
          Compile/Batch/TokTree.lean.
  Part 2  `lw_fbT`, `lw_fbTw`: a query whose new tail may be dead. `lw_fbW`, `lw_fbTG`, `lw_fbG`:
          the search: what follows gets the tails dd of the attempts that are not kept and must be a
          `LiveW` in which they are not live.
  Part 3  `lw_slotLo`: a local round in one slot.

The hypothesis on the relation, at a search (`FitsLoop`): if it relates two answers at the query of
attempt number j, then both fail the search's own check and j is not the last number. For `agF W` it
is proved, under hypotheses, in Compile/Batch/DeadFits.lean.

Limits: those on `LiveW` in the header of Compile/LiveWalk.lean (the larger T, the less is said).
-/
import Compile.LiveWalk
import Compile.Batch.SpecOneCall

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## The live tokens -/

def liveTT (t : TTree) (u : Tok) : Prop := (∃ l ∈ t.levels, u ∈ l) ∨ u ∈ t.salts
def liveOT (t : Option TTree) (u : Tok) : Prop := ∃ x, t = some x ∧ liveTT x u

/-- the live tokens of a list of token trees: those of each tree -/
def liveOTs (l : List TTree) (u : Tok) : Prop := ∃ x ∈ l, liveTT x u

def liveTs (l : List (Option TTree)) (u : Tok) : Prop := ∃ t ∈ l, liveOT t u
def liveAcc {Y : Type} (a : SlotAcc lam K Y) (u : Tok) : Prop :=
  u = a.tk ∨ u = a.c ∨ u ∈ a.toks ∨ liveTs a.trees u
def liveA0 (a : Acc0) (u : Tok) : Prop := u ∈ a.toks ∨ liveTs a.trees u ∨ liveOT a.req u
def livePh : PhT → Tok → Prop
  | .shr tk0, u => u = tk0
  | _, _ => False

theorem liveOTs_nil (u : Tok) : ¬ liveOTs [] u := fun ⟨_, e, _⟩ => nomatch e

theorem liveOTs_cons (x : TTree) (l : List TTree) (u : Tok) :
    liveOTs (x :: l) u ↔ liveTT x u ∨ liveOTs l u :=
  ⟨fun ⟨y, hy, hu⟩ => (List.mem_cons.1 hy).elim (fun e => .inl (e ▸ hu)) fun e => .inr ⟨y, e, hu⟩,
    fun h => h.elim (fun hu => ⟨x, List.mem_cons_self, hu⟩)
      fun ⟨y, hy, hu⟩ => ⟨y, List.mem_cons_of_mem _ hy, hu⟩⟩

/-- a relation that relates no two answers but at the Fiat-Shamir oracles `fb t` and their ghost
names `fbw t j` -/
def OnlyFb (ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop) : Prop :=
  ∀ o q r r', ag o q r r' → (∃ t, o = .fb t) ∨ ∃ t j, o = .fbw t j

variable {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop} (hag : OnlyFb ag)

local notation "Lw" => LiveW (S := spec lam K L) (sp := split lam K L) ag

/-! ## Part 1. Trees
Under `OnlyFb`: ag relates nothing at `leaf`, `node`, `rleaf`, `rnode`, `g t` (`no_leaf` .. `no_g`);
for each program x on trees of Compile/Batch/TokTree.lean, and for `drawT`, a lemma lw_x (`lw_leafT`
.. `lw_drawT`) says that x is a `LiveW`, if the tokens in its arguments are in T or (but for
`openT`, `openE`) are the default token 0 (not all hypotheses are named here: see the statements).
Token trees: `leafT`, `nodeT`, `leavesT`, `commitT`, `openT`, `showT`; the request tree: `rleafT`,
`rnodeT`, `rleavesT`, `reqT`; trees over encoded indices: `leafE`, `nodeE`, `leavesE`, `commitE`,
`openE`. The live tokens of the value are the second argument of `Lw` in each statement: for
`commitT`, `reqT`: `liveTT`; for `commitE`: `liveTH`; for `openT`, `openE`, `showT`, `nodeE`,
`drawT`: none. -/

section Trees
include hag

theorem no_leaf (q r r') : ¬ ag .leaf q r r' :=
  fun h => by rcases hag _ _ _ _ h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e
theorem no_node (q r r') : ¬ ag .node q r r' :=
  fun h => by rcases hag _ _ _ _ h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e
theorem no_rleaf (q r r') : ¬ ag .rleaf q r r' :=
  fun h => by rcases hag _ _ _ _ h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e
theorem no_rnode (q r r') : ¬ ag .rnode q r r' :=
  fun h => by rcases hag _ _ _ _ h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e
theorem no_g (t q r r') : ¬ ag (.g t) q r r' :=
  fun h => by rcases hag _ _ _ _ h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e

theorem lw_leafT {T : Tok → Prop} (sMT : ℕ) (b : Body L) :
    Lw T (fun x u => u = x.1 ∨ u = x.2) (leafT (lam := lam) (K := K) sMT b) :=
  .fresh _ fun _ =>
    .marked _ _ _ (.inl (.inr rfl)) (fun _ h => nomatch h)
      (fun _ _ => .pure fun _ hu => hu.elim (fun e => .inl (.inr e)) .inr) (no_leaf hag)

theorem lw_nodeT {T : Tok → Prop} {a b : Tok} (ha : T a ∨ a = 0) (hb : T b ∨ b = 0) :
    Lw T (fun x u => u = x) (nodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ _ _ ha (fun u h => by rw [List.mem_singleton.1 h]; exact hb)
    (fun _ d => .pure fun u hu => .inr hu) (no_node hag)

theorem lw_leavesT {T : Tok → Prop} (sMT : ℕ) :
    ∀ l : List (Body L), Lw T (fun x u => u ∈ x.1 ∨ u ∈ x.2) (leavesT (lam := lam) (K := K) sMT l)
  | [] => .pure fun u hu => by rcases hu with h | h <;> cases h
  | b :: t =>
      (lw_leafT hag sMT b).bind fun x =>
          ((lw_leavesT sMT t).imp (fun _ h => h) fun _ _ h => h).bind fun r => .pure fun u hu => by
      rcases hu with h | h <;> rcases List.mem_cons.1 h with e | e
      · exact .inl (.inr (.inr e))
      · exact .inr (.inl e)
      · exact .inl (.inr (.inl e))
      · exact .inr (.inr e)

omit hag in
/-- a level of nodes over a level all of whose tokens are live -/
theorem lw_pairUp {T : Tok → Prop} {node : Tok → Tok → St lam K L Tok}
    (hn : ∀ (T' : Tok → Prop) a b,
      (T' a ∨ a = 0) → (T' b ∨ b = 0) → Lw T' (fun x u => u = x) (node a b)) :
    ∀ l : List Tok, (∀ u ∈ l, T u) → Lw T (fun x u => u ∈ x) (pairUp node l)
  | [], _ => .pure fun u hu => nomatch hu
  | [a], h => .pure fun u hu => h u hu
  | a :: b :: t, h => (hn T a b (.inl (h a (by simp))) (.inl (h b (by simp)))).bind fun c =>
      ((lw_pairUp hn t fun u hu => h u (by simp [hu])).imp (fun _ h => .inl h) fun _ _ h => h).bind
          fun r => .pure fun u hu => by
        rcases List.mem_cons.1 hu with e | e
        · exact .inl (.inr e)
        · exact .inr e

omit hag in
theorem lw_levelsM {node : Tok → Tok → St lam K L Tok}
    (hn : ∀ (T' : Tok → Prop) a b,
      (T' a ∨ a = 0) → (T' b ∨ b = 0) → Lw T' (fun x u => u = x) (node a b)) :
    ∀ (d : ℕ) (T : Tok → Prop) (l : List Tok),
      (∀ u ∈ l, T u) → Lw T (fun x u => ∃ y ∈ x, u ∈ y) (levelsM node d l)
  | 0, _, l, h => .pure fun u hu => by
      obtain ⟨y, hy, hu⟩ := hu
      rw [List.mem_singleton.1 hy] at hu
      exact h u hu
  | d + 1, T, l, h =>
      (lw_pairUp hn l h).bind fun v =>
          (lw_levelsM hn d _ v fun u hu => .inr hu).bind fun r => .pure fun u hu => by
      obtain ⟨y, hy, hu⟩ := hu
      rcases List.mem_cons.1 hy with e | e
      · exact .inl (.inl (h u (e ▸ hu)))
      · exact .inr ⟨y, e, hu⟩

theorem lw_commitT {T : Tok → Prop} (sMT d : ℕ) (leaf : ℕ → Body L) :
    Lw T liveTT (commitT (lam := lam) (K := K) sMT d leaf) :=
  (lw_leavesT hag sMT _).bind fun x =>
      (lw_levelsM (fun _ _ _ => lw_nodeT hag) d _ x.1 fun _ hu => Or.inr (Or.inl hu)).bind
          fun _ => .pure fun u hu => by
    rcases hu with h | h
    · exact .inr h
    · exact .inl (.inr (.inr h))

omit hag in
theorem getD_or (l : List Tok) (j : ℕ) : l.getD j 0 ∈ l ∨ l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[j]? with
  | none => exact .inr rfl
  | some x => exact .inl (List.mem_of_getElem? h)

omit hag in
theorem headD_or (l : List Tok) : l.headD 0 ∈ l ∨ l.headD 0 = 0 := by
  cases l with
  | nil => exact .inr rfl
  | cons a t => exact .inl (by simp)

omit hag in
theorem mem_pathOf :
    ∀ (lv : List (List Tok)) (j : ℕ) (u : Tok), u ∈ pathOf lv j → (∃ l ∈ lv, u ∈ l) ∨ u = 0
  | [], _, _, h => nomatch h
  | [_], _, _, h => nomatch h
  | l :: l' :: ls, j, u, h => by
    rcases List.mem_cons.1 h with e | e
    · rcases getD_or l (if j % 2 = 0 then j + 1 else j - 1) with h' | h'
      · exact .inl ⟨l, by simp, e ▸ h'⟩
      · exact .inr (e.trans h')
    · rcases mem_pathOf (l' :: ls) (j / 2) u e with ⟨y, hy, hu⟩ | h'
      · exact .inl ⟨y, List.mem_cons_of_mem _ hy, hu⟩
      · exact .inr h'

omit hag in
theorem mem_ancOf :
    ∀ (lv : List (List Tok)) (j : ℕ) (u : Tok), u ∈ ancOf lv j → (∃ l ∈ lv, u ∈ l) ∨ u = 0
  | [], _, _, h => nomatch h
  | l :: ls, j, u, h => by
    rcases List.mem_cons.1 h with e | e
    · rcases getD_or l j with h' | h'
      · exact .inl ⟨l, by simp, e ▸ h'⟩
      · exact .inr (e.trans h')
    · rcases mem_ancOf ls (j / 2) u e with ⟨y, hy, hu⟩ | h'
      · exact .inl ⟨y, List.mem_cons_of_mem _ hy, hu⟩
      · exact .inr h'

omit hag in
theorem getLastD_mem : ∀ (ls : List (List Tok)) (a : List Tok), ls.getLastD a ∈ a :: ls
  | [], a => List.mem_cons_self
  | b :: t, a => by
    rw [List.getLastD_cons]
    exact List.mem_cons_of_mem _ (getLastD_mem t b)

omit hag in
/-- the root of a token tree is one of its tokens, or the default 0 -/
theorem root_or (t : TTree) : liveTT t t.root ∨ t.root = 0 := by
  unfold TTree.root rootOf
  rcases headD_or (t.levels.getLastD []) with h | h
  · rcases List.mem_cons.1 (getLastD_mem t.levels []) with e | e
    · rw [e] at h; exact nomatch h
    · exact .inl (.inl ⟨_, e, h⟩)
  · exact .inr h

omit hag in
theorem lw_openT {T : Tok → Prop} {σ : Type} (t : TTree) (j : ℕ)
    (a : σ) (h : ∀ u, liveTT t u → T u) :
    Lw T (fun _ _ => False) (openT (lam := lam) (K := K) (L := L) t j a) :=
  .reveal (fun u hu => by
    rcases List.mem_cons.1 hu with e | e
    · rcases getD_or t.salts j with h' | h'
      · exact .inl (h u (.inr (e ▸ h')))
      · exact .inr (e.trans h')
    · rcases List.mem_append.1 e with e | e
      · exact (mem_pathOf _ _ _ e).imp (fun x => h u (.inl x)) id
      · exact (mem_ancOf _ _ _ e).imp (fun x => h u (.inl x)) id) fun _ => .pure fun _ hu => hu.elim

omit hag in
theorem lw_showT {T : Tok → Prop} {t : Tok} (h : T t ∨ t = 0) :
    Lw T (fun _ _ => False) (showT (lam := lam) (K := K) (L := L) t) :=
  .reveal (fun u hu => by rw [List.mem_singleton.1 hu]; exact h) fun _ => .pure fun _ hu => hu.elim

theorem lw_rleafT {T : Tok → Prop} {c : Tok} (h : T c ∨ c = 0) :
    Lw T (fun x u => u = x) (rleafT (lam := lam) (K := K) (L := L) c) :=
  .marked _ _ _ h (fun _ h => nomatch h) (fun _ _ => .pure fun _ hu => .inr hu) (no_rleaf hag)

theorem lw_rnodeT {T : Tok → Prop} {a b : Tok} (ha : T a ∨ a = 0) (hb : T b ∨ b = 0) :
    Lw T (fun x u => u = x) (rnodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ _ _ ha (fun u h => by rw [List.mem_singleton.1 h]; exact hb)
    (fun _ _ => .pure fun _ hu => .inr hu) (no_rnode hag)

theorem lw_rleavesT :
    ∀ (T : Tok → Prop) (l : List Tok),
      (∀ u ∈ l, T u ∨ u = 0) → Lw T (fun x u => u ∈ x) (rleavesT (lam := lam) (K := K) (L := L) l)
  | _, [], _ => .pure fun _ hu => nomatch hu
  | T, c :: t, h =>
      (lw_rleafT hag (h c (by simp))).bind fun d =>
          (lw_rleavesT _ t fun u hu => (h u (by simp [hu])).imp .inl id).bind fun r =>
              .pure fun u hu => by
      rcases List.mem_cons.1 hu with e | e
      · exact .inl (.inr e)
      · exact .inr e

theorem lw_reqT {T : Tok → Prop} (depthReq : ℕ) (cs : List Tok) (h : ∀ u ∈ cs, T u ∨ u = 0) :
    Lw T liveTT (reqT (lam := lam) (K := K) (L := L) depthReq cs) :=
  (lw_rleavesT hag T cs h).bind fun ls =>
      (lw_levelsM (fun _ _ _ => lw_rnodeT hag) depthReq _ ls fun _ hu => Or.inr hu).bind
          fun _ => .pure fun u hu => by
    rcases hu with h | h
    · exact .inr h
    · exact nomatch h

/-- the live tokens of a tree over an encoded index: the salt and the digest token of each salted
leaf -/
def liveTH (t : TreeH lam) (u : Tok) : Prop := ∃ x, some x ∈ t.salts ∧ (u = x.1 ∨ u = x.2)

theorem lw_leafE {T : Tok → Prop} (sMT : ℕ) (b : Body L) (bl : Bool) :
    Lw T (fun x u => ∃ y, x.2 = some y ∧ (u = y.1 ∨ u = y.2))
      (leafE (lam := lam) (K := K) sMT b bl) := by
  unfold leafE
  cases bl
  · exact .plain _ _ (fun r r' h => (no_leaf hag _ _ _ h).elim) fun _ =>
      .pure fun _ hu => by obtain ⟨_, e, _⟩ := hu; exact nomatch e
  · exact (lw_leafT hag sMT b).bind fun x =>
        (lw_showT (.inl (.inr (.inr rfl)))).bind fun _ => .pure fun u hu => by
      obtain ⟨y, e, h⟩ := hu
      obtain rfl : x = y := Option.some.inj e
      exact .inl (.inr h)

theorem lw_nodeE {T : Tok → Prop} (a b : Dig lam) :
    Lw T (fun _ _ => False) (nodeE (K := K) (L := L) a b) :=
  .plain _ _ (fun _ _ h => (no_node hag _ _ _ h).elim) fun _ => .pure fun _ hu => hu.elim

theorem lw_leavesE {T : Tok → Prop} (sMT : ℕ) :
    ∀ l : List (Body L × Bool), Lw
      T (fun x u => ∃ y, some y ∈ x.2 ∧ (u = y.1 ∨ u = y.2)) (leavesE (lam := lam) (K := K) sMT l)
  | [] => .pure fun _ hu => by obtain ⟨_, e, _⟩ := hu; exact nomatch e
  | (b, bl) :: t =>
      (lw_leafE hag sMT b bl).bind fun x =>
          ((lw_leavesE sMT t).imp (fun _ h => h) fun _ _ h => h).bind fun r => .pure fun u hu => by
      obtain ⟨y, e, h⟩ := hu
      rcases List.mem_cons.1 e with e | e
      · exact .inl (.inr ⟨y, e.symm, h⟩)
      · exact .inr ⟨y, e, h⟩

omit hag in
/-- levels of digests: no token -/
theorem lw_pairUpD {T : Tok → Prop} {node : Dig lam → Dig lam → St lam K L (Dig lam)}
    (hn : ∀ (T' : Tok → Prop) a b, Lw T' (fun _ _ => False) (node a b)) :
    ∀ l : List (Dig lam), Lw T (fun _ _ => False) (pairUp node l)
  | [] => .pure fun _ hu => hu.elim
  | [_] => .pure fun _ hu => hu.elim
  | a :: b :: t =>
    (hn T a b).bind fun _ =>
      ((lw_pairUpD hn t).imp (fun _ h => h) fun _ _ h => h).bind fun _ => .pure fun _ hu => hu.elim

omit hag in
theorem lw_levelsMD {node : Dig lam → Dig lam → St lam K L (Dig lam)}
    (hn : ∀ (T' : Tok → Prop) a b, Lw T' (fun _ _ => False) (node a b)) :
    ∀ (d : ℕ) (T : Tok → Prop) (l : List (Dig lam)), Lw T (fun _ _ => False) (levelsM node d l)
  | 0, _, _ => .pure fun _ hu => hu.elim
  | d + 1, _, l =>
    (lw_pairUpD hn l).bind fun v => (lw_levelsMD hn d _ v).bind fun _ => .pure fun _ hu => hu.elim

theorem lw_commitE {T : Tok → Prop} (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Lw T liveTH (commitE (lam := lam) (K := K) sMT d leaf) :=
  (lw_leavesE hag sMT _).bind fun x =>
    (lw_levelsMD (fun _ => lw_nodeE hag) d _ x.1).bind fun _ => .pure fun _ hu => .inl (.inr hu)

omit hag in
theorem lw_openE {T : Tok → Prop} {σ : Type} (t : TreeH lam) (j : ℕ)
    (a : σ) (h : ∀ u, liveTH t u → T u) :
    Lw T (fun _ _ => False) (openE (K := K) (L := L) t j a) := by
  unfold openE
  cases hs : t.salts.getD j none with
  | none => exact .pure fun _ hu => hu.elim
  | some s =>
    have hm : some s ∈ t.salts := by
      rw [List.getD_eq_getElem?_getD] at hs
      cases hj : t.salts[j]? with
      | none => rw [hj] at hs; exact nomatch hs
      | some y => rw [hj] at hs; exact (show y = some s from hs) ▸ List.mem_of_getElem? hj
    exact .reveal (fun u hu => by
      rcases List.mem_cons.1 hu with e | e
      · exact .inl (h u ⟨s, hm, .inl e⟩)
      · exact .inl (h u ⟨s, hm, .inr (List.mem_singleton.1 e)⟩)) fun _ => .pure fun _ hu => hu.elim

omit hag in
theorem lw_drawT {T : Tok → Prop} {β : Type} (e : Enum β) :
    Lw T (fun _ _ => False) (drawT (lam := lam) (K := K) (L := L) e) :=
  .sample _ fun _ => .pure fun _ hu => hu.elim

end Trees

/-! ## Part 2. Queries to g and to the Fiat-Shamir oracle; the search over nonces -/

section Evals
variable {β : Type} {T : Tok → Prop} {TP : β → Tok → Prop}

include hag in
theorem lw_gT (t : Tag) (i : ℕ) {tk : Tok} {root : Option Tok} (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Tok → St lam K L β} (htk : T tk ∨ tk = 0) (hr : ∀ u ∈ root.toList, T u ∨ u = 0)
    (hk : ∀ c, Lw (fun u => T u ∨ u = c) TP (k c)) : Lw T TP (gT t i tk root pl k) :=
  .marked _ _ _ htk hr (fun _ c => hk c) (no_g hag t)

include hag in
theorem lw_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} (hk : ∀ tr, Lw (fun u => T u ∨ liveOT tr u) TP (k tr)) :
    Lw T TP (withTree sMT has depth leaf k) := by
  cases has with
  | true =>
    exact (lw_commitT hag sMT depth leaf).bind fun tr =>
      (hk (some tr)).imp
        (fun u hu => hu.imp id fun ⟨x, e, h⟩ => (Option.some.inj e) ▸ h) fun _ _ h => h
  | false => exact (hk none).imp (fun u hu => hu.elim id fun ⟨_, e, _⟩ => nomatch e) fun _ _ h => h

include hag in
/-- `withTrees sMT ds leaf k` is a `LiveW` if, on every list of trees, k is one in which the tokens
of all these trees count as live too. Nothing is said to k on how many trees there are. (T stands
behind the quantifier: it grows with each tree.) -/
theorem lw_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {T : Tok → Prop} {k : List TTree → St lam K L β},
      (∀ trs, Lw (fun u => T u ∨ liveOTs trs u) TP (k trs)) → Lw T TP (withTrees sMT ds leaf k)
  | [], _, _, _, hk =>
    (hk []).imp (fun u hu => hu.elim id fun h => (liveOTs_nil u h).elim) fun _ _ h => h
  | d :: ds, leaf, _, _, hk =>
    (lw_commitT hag sMT d (leaf 0)).bind fun tr =>
      lw_withTrees sMT ds (fun n => leaf (n + 1)) fun trs =>
        (hk (tr :: trs)).imp
          (fun u hu => hu.elim (fun h => .inl (.inl h)) fun h =>
            ((liveOTs_cons tr trs u).1 h).elim (fun h' => .inl (.inr h')) .inr)
          fun _ _ h => h

/-- A Fiat-Shamir query whose new tail may be dead. hd: after two answers that ag relates: the same
continuation, in which the new tail is not live. -/
theorem lw_fbT (t : Tag) (i : ℕ) {tk : Tok} {us : List Tok} {root : Option Tok}
    (hd' : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd' vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} (h1 : ∃ u, T u)
    (htk : T tk ∨ tk = 0) (hus : ∀ u ∈ us ++ root.toList, T u ∨ u = 0)
    (hk : ∀ bl tl, Lw (fun u => T u ∨ u = tl) TP (k bl tl))
    (hd : ∀ (q : FbIn lam L t) r r',
      q.plain = pl → ag (.fb t) q r r' → ∀ tl, k r.1 tl = k r'.1 tl ∧ Lw T TP (k r.1 tl)) :
    Lw T TP (fbT t i tk us root hd' hinj pl k) :=
  .markedDead _ _ _ h1 htk hus hk fun _ _ r r' e tl => hd _ r r' rfl e tl

theorem lw_fbTw (t : Tag) (j i : ℕ) {tk : Tok} {us : List Tok} {root : Option Tok}
    (hd' : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd' vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} (h1 : ∃ u, T u)
    (htk : T tk ∨ tk = 0) (hus : ∀ u ∈ us ++ root.toList, T u ∨ u = 0)
    (hk : ∀ bl tl, Lw (fun u => T u ∨ u = tl) TP (k bl tl))
    (hd : ∀ (q : FbIn lam L t) r r',
      q.plain = pl → ag (.fbw t j) q r r' → ∀ tl, k r.1 tl = k r'.1 tl ∧ Lw T TP (k r.1 tl)) :
    Lw T TP (fbTw t j i tk us root hd' hinj pl k) :=
  .markedDead _ _ _ h1 htk hus hk fun _ _ r r' e tl => hd _ r r' rfl e tl

section Loop
variable {C P : Type}

/-- What the relation must say at the queries of a search: two answers that it relates at the query
of attempt number m both fail the search's check, and m is not the last number. -/
def FitsLoop (ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop) (chal : Blk lam K → C)
    (t : Tag) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (g : GrW C P) : Prop :=
  ∀ (m : ℕ) (q : FbIn lam L t) (r r' : rngOf lam K (.fb t)), m ≤ g.more →
    q.plain = emb (g.put m α) → (ag (.fb t) q r r' ∨ ∃ j, ag (.fbw t j) q r r') →
    g.ok (chal r.1) = false ∧ g.ok (chal r'.1) = false ∧ m < g.more

/-- The attempts after the first. n more attempts after attempt number j + 1; j + 1 + n is the last
number. -/
theorem lw_fbW {chal : Blk lam K → C} {t : Tag} (i : ℕ) {tk : Tok} {us : List Tok}
    {root : Option Tok} (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}
    {g : GrW C P} (hF : FitsLoop ag chal t emb α g) (h1 : ∃ u, T u) (htk : T tk ∨ tk = 0)
    (hus : ∀ u ∈ us ++ root.toList, T u ∨ u = 0) {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ (m : ℕ) (dd : List Tok) (bl : Blk lam K) (tl : Tok),
      Lw (fun u => T u ∨ u = tl) TP (k m dd bl tl)) (n : ℕ) :
    ∀ (j : ℕ) (dd : List Tok),
      j + 1 + n = g.more → Lw T TP (fbW g chal t i tk us root hd' hinj emb α k n j dd) := by
  induction n with
  | zero =>
    intro j dd e
    refine lw_fbTw t j i hd' hinj _ h1 htk hus (fun bl tl => hk _ _ bl tl) fun q r r' hq ha _ => ?_
    have h3 := (hF (j + 1) q r r' (by omega) hq (.inr ⟨j, ha⟩)).2.2
    omega
  | succ n ih =>
    intro j dd e
    refine lw_fbTw t j i hd' hinj _ h1 htk hus (fun bl tl => ?_) fun q r r' hq ha tl => ?_
    · show Lw _ TP (if g.ok (chal bl) then _ else _)
      by_cases hok : g.ok (chal bl) = true
      · rw [if_pos hok]; exact hk _ _ bl tl
      · rw [if_neg hok]; exact (ih (j + 1) (tl :: dd) (by omega)).imp (fun _ h => .inl h) fun _ _ h => h
    · obtain ⟨f1, f2, -⟩ := hF (j + 1) q r r' (by omega) hq (.inr ⟨j, ha⟩)
      show (if g.ok (chal r.1) then _ else _) = (if g.ok (chal r'.1) then _ else _) ∧
        Lw T TP (if g.ok (chal r.1) then _ else _)
      rw [f1, f2]
      exact ⟨rfl, ih (j + 1) (tl :: dd) (by omega)⟩

/-- The search over nonces is a `LiveW`, under `FitsLoop` and the hypotheses below. -/
theorem lw_fbTG {chal : Blk lam K → C} {t : Tag} (i : ℕ) {tk : Tok} {us : List Tok}
    {root : Option Tok} (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}
    {g : GrW C P} (hF : FitsLoop ag chal t emb α g) (h1 : ∃ u, T u) (htk : T tk ∨ tk = 0)
    (hus : ∀ u ∈ us ++ root.toList, T u ∨ u = 0) {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ (m : ℕ) (dd : List Tok) (bl : Blk lam K) (tl : Tok),
      Lw (fun u => T u ∨ u = tl) TP (k m dd bl tl)) :
    Lw T TP (fbTG g chal t i tk us root hd' hinj emb α k) := by
  unfold fbTG
  cases hm : g.more with
  | zero =>
    refine lw_fbT t i hd' hinj _ h1 htk hus (fun bl tl => hk _ _ bl tl) fun q r r' hq ha _ => ?_
    have h3 := (hF 0 q r r' (Nat.zero_le _) hq (.inl ha)).2.2
    omega
  | succ n =>
    refine lw_fbT t i hd' hinj _ h1 htk hus (fun bl tl => ?_) fun q r r' hq ha tl => ?_
    · show Lw _ TP (if g.ok (chal bl) then _ else _)
      by_cases hok : g.ok (chal bl) = true
      · rw [if_pos hok]; exact hk _ _ bl tl
      · rw [if_neg hok]; exact (lw_fbW i hd' hinj hF h1 htk hus hk n 0 [tl] (by omega)).imp (fun _ h => .inl h) fun _ _ h => h
    · obtain ⟨f1, f2, -⟩ := hF 0 q r r' (Nat.zero_le _) hq (.inl ha)
      show (if g.ok (chal r.1) then _ else _) = (if g.ok (chal r'.1) then _ else _) ∧
        Lw T TP (if g.ok (chal r.1) then _ else _)
      rw [f1, f2]
      exact ⟨rfl, lw_fbW i hd' hinj hF h1 htk hus hk n 0 [tl] (by omega)⟩

/-- A Fiat-Shamir query, with proof-of-work bits or without. hN: without proof-of-work bits the
relation relates no two answers at its query. -/
theorem lw_fbG {chal : Blk lam K → C} {t : Tag} (i : ℕ) {tk : Tok} {us : List Tok}
    {root : Option Tok} (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}
    (gr : Option (GrW C P)) (hF : ∀ g, gr = some g → FitsLoop ag chal t emb α g)
    (hN : gr = none → ∀ (q : FbIn lam L t) r r', q.plain = emb α → ¬ ag (.fb t) q r r')
    (h1 : ∃ u, T u) (htk : T tk ∨ tk = 0) (hus : ∀ u ∈ us ++ root.toList, T u ∨ u = 0)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ (m : Option ℕ) (dd : List Tok) (bl : Blk lam K) (tl : Tok),
      Lw (fun u => T u ∨ u = tl) TP (k m dd bl tl)) :
    Lw T TP (fbG gr chal t i tk us root hd' hinj emb α k) := by
  cases gr with
  | none =>
    exact lw_fbT t i hd' hinj _ h1 htk hus (fun bl tl => hk _ _ bl tl)
      fun q r r' hq ha _ => (hN rfl q r r' hq ha).elim
  | some g => exact lw_fbTG i hd' hinj (hF g rfl) h1 htk hus fun m dd bl tl => hk (some m) dd bl tl

/-- the same as `lw_fbG` in a slot, whatever its phase -/
theorem lw_fbSlotG {chal : Blk lam K → C} {t : Tag} (i : ℕ) (cms : List (Dig lam)) (x : Option X)
    (ph : PhT) {tk c : Tok} {root : Option Tok} {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}
    (gr : Option (GrW C P)) (hF : ∀ g, gr = some g → FitsLoop ag chal t emb α g)
    (hN : gr = none → ∀ (q : FbIn lam L t) r r', q.plain = emb α → ¬ ag (.fb t) q r r')
    (h1 : ∃ u, T u) (htk : T tk ∨ tk = 0) (hc : T c ∨ c = 0) (hph : ∀ u, livePh ph u → T u)
    (hr : ∀ u ∈ root.toList, T u ∨ u = 0) {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ (m : Option ℕ) (dd : List Tok) (bl : Blk lam K) (tl : Tok),
      Lw (fun u => T u ∨ u = tl) TP (k m dd bl tl)) :
    Lw T TP (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph with
  | shr tk0 =>
    exact lw_fbG i _ _ gr hF hN h1 hc (fun u hu => by
      rcases List.mem_append.1 hu with e | e
      · exact .inl (hph u (List.mem_singleton.1 e))
      · exact hr u e) hk
  | first => exact lw_fbG i _ _ gr hF hN h1 htk (fun u hu => hr u (by simpa using hu)) hk
  | loc => exact lw_fbG i _ _ gr hF hN h1 htk (fun u hu => hr u (by simpa using hu)) hk
  | aft => exact lw_fbG i _ _ gr hF hN h1 htk (fun u hu => hr u (by simpa using hu)) hk

end Loop

end Evals

/-! ## Part 3. A local round in one slot -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- the root of an optional tree is live, or the default 0 -/
theorem rootOT_or (tr : Option TTree) : ∀ u ∈ (tr.map TTree.root).toList, liveOT tr u ∨ u = 0 := by
  cases tr with
  | none => exact fun _ h => nomatch h
  | some x =>
    intro u h
    rw [show u = x.root from List.mem_singleton.1 h]
    exact (root_or x).imp (fun h' => ⟨x, rfl, h'⟩) id

/-- the root of each tree of a list is live, or the default 0 -/
theorem rootOTs_or (trs : List TTree) : ∀ u ∈ trs.map TTree.root, liveOTs trs u ∨ u = 0 := by
  intro u h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact (root_or x).imp (fun h' => ⟨x, hx, h'⟩) id

include hag in
/-- A local round in one slot is a `LiveW`, under `OnlyFb` and the hypotheses below. The live tokens
of the slot's data stay live; the tails of the attempts that are not kept go into the field `dead`,
which is not live. -/
theorem lw_slotLo {T : Tok → Prop} {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (hF : ∀ α g, w.grJ = some g → FitsLoop ag w.chal t plJ α g)
    (hN : w.grJ = none → ∀ α (q : FbIn lam L t) r r', q.plain = plJ α → ¬ ag (.fb t) q r r')
    (z : SlotSt lam K Y (r :: s)) (hz : ∀ u, liveAcc z.2 u → T u) (hph : ∀ u, livePh ph u → T u) :
    Lw T (fun z' u => liveAcc z'.2 u) (slotLo sMT t cms xin a w emb plJ i ph z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotLo]
  refine lw_withTree hag sMT _ _ _ fun tr => ?_
  refine lw_fbSlotG i cms _ ph w.grJ (hF _) (fun h => hN h _)
    ⟨acc.tk, .inl (hz _ (.inl rfl))⟩ (.inl (.inl (hz _ (.inl rfl))))
    (.inl (.inl (hz _ (.inr (.inl rfl))))) (fun u hu => .inl (hph u hu))
    (fun u hu => (rootOT_or tr u hu).imp .inr id) fun nc dd bl tl => .pure fun u hu => ?_
  rcases hu with e | e | e | e
  · exact .inr e
  · exact .inl (.inl (hz u (.inr (.inl e))))
  · rcases List.mem_append.1 e with e | e
    · exact .inl (.inl (hz u (.inr (.inr (.inl e)))))
    · exact .inr (List.mem_singleton.1 e)
  · obtain ⟨x, hx, hu⟩ := e
    rcases List.mem_append.1 hx with e | e
    · exact .inl (.inl (hz u (.inr (.inr (.inr ⟨x, e, hu⟩)))))
    · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))

end Rounds

end Compile.Batch.Dead
