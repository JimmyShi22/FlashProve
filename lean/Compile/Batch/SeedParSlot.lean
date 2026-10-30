-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedParSlot.lean: the programs of one slot and the proof strings of the compiled
prover do not look at the numbers of their tokens. What it is for: `Face.TokFree`,
Compile/Batch/SeedStar.lean. (Words of this library: lean/GLOSSARY.md.)

For the sub-programs of Compile/Batch/Prover.lean other than the recursion over the rounds: run on a
store with their tokens shown through `Life2.up` (renumbered: a number below N₀ stays, any other
grows by δ; Compile/Step1_life2_Virt.lean; token, store: the head of
Compile/Batch/SeedParTree.lean), and run on the store without the δ strings after the first N₀, they
make the same queries and take the same samples; tokens in their results are related by `up`;
strings in their results are the same (`Compile.Seed.Par`, Compile/SeedKit.lean).

Default values. These programs write the number 0 where no token is meant, and `up N₀ δ 0` is δ, not
0, if N₀ = 0. So the relations include conditions under which no such 0 is read:
* the slot value c of a slot is 0 until the chains have joined, and is read only afterwards: `upAcc`
  renumbers it only if its flag says "joined" (`chainsHaveJoined`: a function of the phase);
* the list of tokens of a slot is not empty (`GoodAcc`);
* the trees of a slot and of the shared part are full, each with the depth of its round (`TOK ds l`:
  the list l of trees, round by round, against the list ds of depths; `depthsJ`, `depths0`: the
  depths of all rounds);
* the request tree has full levels of the depth depthReq (`Good0`), and the number of a slot is
  below 2^depthReq.

Limits: nothing is said about distributions. Of a slot that holds no request `par_finishAll` asks
only that it is empty in both runs: no proof string is made for it.
-/
import Compile.Batch.SeedParTree

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

open Life2 (up)
open Compile.Seed (Par upS upTree)
open List (Forall₂)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {Y : Type} (N₀ δ : ℕ)

/-! ## Part 1. The states of a slot and of the shared part, with the tokens renumbered -/

/-- the tokens of a slot, shown through up (renumbered); its slot value only if the chains have
joined (before that it is the default value 0) -/
def upAcc (b : Bool) (a : SlotAcc lam K Y) : SlotAcc lam K Y :=
  { a with
    tk := up N₀ δ a.tk, c := if b then up N₀ δ a.c else a.c,
    trees := a.trees.map (Option.map (upTT N₀ δ)),
    toks := a.toks.map (up N₀ δ), dead := a.dead.map (up N₀ δ) }

def upAcc0 (a : Acc0) : Acc0 :=
  ⟨a.trees.map (Option.map (upTT N₀ δ)), a.toks.map (up N₀ δ), a.req.map (upTT N₀ δ),
    a.nons, a.dead.map (up N₀ δ)⟩

def upPh : PhT → PhT
  | .shr tk => .shr (up N₀ δ tk)
  | .first => .first
  | .loc => .loc
  | .aft => .aft

/-- have the chains joined? -/
def chainsHaveJoined : PhT → Bool
  | .shr _ => true
  | .aft => true
  | .first => false
  | .loc => false

/-- the trees l, round by round, are full with the depths ds -/
def TOK (ds : List ℕ) (l : List (Option TTree)) : Prop :=
  Forall₂ (fun d ot => ∀ tr, ot = some tr → FullT d tr) ds l

def GoodAcc (dJ : List ℕ) (a : SlotAcc lam K Y) : Prop := TOK dJ a.trees ∧ a.toks ≠ []

def Good0 (depthReq : ℕ) (d0 : List ℕ) (a : Acc0) : Prop :=
  TOK d0 a.trees ∧ ∀ rq, a.req = some rq → FullLv depthReq rq.levels

/-- the relation of the two runs, for the state of a slot -/
def RelAcc (b : Bool) (dJ : List ℕ) (a a' : SlotAcc lam K Y) : Prop :=
  a = upAcc N₀ δ b a' ∧ GoodAcc dJ a'

/-- the same for a slot with the rest of its strategy -/
def RelZ {s : Shape} (b : Bool) (dJ : List ℕ) (z z' : SlotSt lam K Y s) : Prop :=
  z.1 = z'.1 ∧ RelAcc N₀ δ b dJ z.2 z'.2

/-- the relation that the proof strings need: of a slot without a request it asks only that it is
empty in both runs -/
def RelFin (dJ : List ℕ) (a a' : SlotAcc lam K Y) : Prop :=
  a.x = a'.x ∧ (a'.x ≠ none → ∃ b, RelAcc N₀ δ b dJ a a')

/-- the depths of the trees over the slots' components, round by round -/
def depthsJ : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List ℕ
  | [], _, _ => []
  | _ :: s, (_, A), (w, W) => w.depthJ :: depthsJ s A W

/-- the depths of the trees over the shared components, round by round -/
def depths0 : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List ℕ
  | [], _, _ => []
  | _ :: s, (_, A), (w, W) => w.depth0 :: depths0 s A W

variable {N₀ δ}

theorem TOK.snoc {ds : List ℕ} {l : List (Option TTree)} (h : TOK ds l) {d : ℕ} {ot : Option TTree}
    (h' : ∀ tr, ot = some tr → FullT d tr) : TOK (ds ++ [d]) (l ++ [ot]) :=
  List.rel_append h (.cons h' .nil)

theorem TOK.snoc_none {ds : List ℕ} {l : List (Option TTree)} (h : TOK ds l) (d : ℕ) :
    TOK (ds ++ [d]) (l ++ [none]) :=
  h.snoc fun _ e => by cases e

theorem TOK.snoc_some {ds : List ℕ} {l : List (Option TTree)} (h : TOK ds l) {d : ℕ}
    {tr : TTree} (h' : FullT d tr) :
    TOK (ds ++ [d]) (l ++ [some tr]) :=
  h.snoc fun _ e => by cases e; exact h'

theorem upPh_afterLo (ph : PhT) : (upPh N₀ δ ph).afterLo = upPh N₀ δ ph.afterLo := by
  cases ph <;> rfl

theorem joined_afterLo (ph : PhT) : chainsHaveJoined ph.afterLo = chainsHaveJoined ph := by cases ph <;> rfl

theorem kind_cases (k : Kind) : k = .lo ∨ k = .sh := by cases k <;> simp

theorem forall₂_map {α α' β β' : Type} {r : α → α' → Prop} {r' : β → β' → Prop} {f : α → β}
    {f' : α' → β'} (h : ∀ a a', r a a' → r' (f a) (f' a')) :
    ∀ {l : List α} {l' : List α'}, Forall₂ r l l' → Forall₂ r' (l.map f) (l'.map f')
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (forall₂_map h h2)

/-! ## Part 2. The rounds, in one slot -/

theorem par_eachM {σ σ' τ τ' : Type} {r : σ → σ' → Prop} {r' : τ → τ' → Prop} {f : σ → St lam K L τ}
    {f' : σ' → St lam K L τ'} (h : ∀ a a', r a a' → Par N₀ δ r' (f a) (f' a')) :
    ∀ {l : List σ} {l' : List σ'}, Forall₂ r l l' →
      Par N₀ δ (fun o o' => Forall₂ r' o o' ∧ o'.length = l'.length) (eachM f l) (eachM f' l')
  | _, _, .nil => Par.pure ⟨.nil, rfl⟩
  | _, _, @Forall₂.cons _ _ _ a a' l l' h1 h2 => by
    show Par N₀ δ _ ((f a).bind fun b => (eachM f l).bind fun r => Step.pure (b :: r))
      ((f' a').bind fun b => (eachM f' l').bind fun r => Step.pure (b :: r))
    exact (h _ _ h1).bind fun b b' hb =>
      (par_eachM h h2).bind fun c c' hc => Par.pure ⟨.cons hb hc.1, congrArg (· + 1) hc.2⟩

theorem par_fbT {β β' : Type} {r : β → β' → Prop} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} {k' : Blk lam K → Tok → St lam K L β'}
    (h : ∀ bl tl, N₀ ≤ tl → Par N₀ δ r (k bl (up N₀ δ tl)) (k' bl tl)) :
    Par N₀ δ r (fbT t i (up N₀ δ tk) (us.map (up N₀ δ)) (root.map (up N₀ δ)) hd hinj pl k)
      (fbT t i tk us root hd hinj pl k') := by
  unfold fbT
  have e : us.map (up N₀ δ) ++ (root.map (up N₀ δ)).toList = (us ++ root.toList).map (up N₀ δ) := by
    cases root <;> simp
  simp only [e, List.length_map, Option.map_map]
  exact Par.marked (S := spec lam K L) (sp := split lam K L) (t := tk)
    (us := us ++ root.toList) (OracleName.fb t) _ _ h

theorem par_fbSlot {β β' : Type} {r : β → β' → Prop} (t : Tag) (i : ℕ) (cms : List (Dig lam))
    (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} {k' : Blk lam K → Tok → St lam K L β'}
    (h : ∀ bl tl, N₀ ≤ tl → Par N₀ δ r (k bl (up N₀ δ tl)) (k' bl tl)) :
    Par N₀ δ r
      (fbSlot t i cms x (upPh N₀ δ ph) (up N₀ δ tk) (if chainsHaveJoined ph then up N₀ δ c else c)
        (root.map (up N₀ δ)) pl k)
      (fbSlot t i cms x ph tk c root pl k') := by
  cases ph with
  | first => exact par_fbT t i tk [] root (fun _ => Head.f1 cms (x.map L.early)) (fun _ => f1_inj cms _) pl h
  | loc => exact par_fbT t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl h
  | aft => exact par_fbT t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl h
  | shr tk0 => exact par_fbT t i c [tk0] root (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _) pl h

theorem par_fbTw {β β' : Type} {r : β → β' → Prop} (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} {k' : Blk lam K → Tok → St lam K L β'}
    (h : ∀ bl tl, N₀ ≤ tl → Par N₀ δ r (k bl (up N₀ δ tl)) (k' bl tl)) :
    Par N₀ δ r (fbTw t j i (up N₀ δ tk) (us.map (up N₀ δ)) (root.map (up N₀ δ)) hd hinj pl k)
      (fbTw t j i tk us root hd hinj pl k') := by
  unfold fbTw
  have e : us.map (up N₀ δ) ++ (root.map (up N₀ δ)).toList = (us ++ root.toList).map (up N₀ δ) := by
    cases root <;> simp
  simp only [e, List.length_map, Option.map_map]
  exact Par.marked (S := spec lam K L) (sp := split lam K L) (t := tk)
    (us := us ++ root.toList) (OracleName.fbw t j) _ _ h

/-- the attempts after the first of a search (`fbW`, Compile/Batch/Prover.lean; hypotheses below):
the two runs make the same attempts; the chaining values of the failed ones correspond (by
`up N₀ δ`) -/
theorem par_fbW {β β' C P : Type} {r : β → β' → Prop} (g : GrW C P) (chal : Blk lam K → C) (t : Tag)
    (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {k' : ℕ → List Tok → Blk lam K → Tok → St lam K L β'}
    (h : ∀ m dd bl tl,
      N₀ ≤ tl → Par N₀ δ r (k m (dd.map (up N₀ δ)) bl (up N₀ δ tl)) (k' m dd bl tl)) :
    ∀ n j dd, Par N₀ δ r
      (fbW g chal t i (up N₀ δ tk) (us.map (up N₀ δ)) (root.map (up N₀ δ))
        hd hinj emb α k n j (dd.map (up N₀ δ)))
      (fbW g chal t i tk us root hd hinj emb α k' n j dd)
  | 0, j, dd => par_fbTw t j i tk us root hd hinj _ fun bl tl htl => h _ dd bl tl htl
  | n + 1, j, dd => par_fbTw t j i tk us root hd hinj _ fun bl tl htl => by
      by_cases hok : g.ok (chal bl) = true
      · simp only [hok, if_true]; exact h _ dd bl tl htl
      · simp only [hok]; exact par_fbW g chal t i tk us root hd hinj emb α h n (j + 1) (tl :: dd)

/-- A Fiat-Shamir query, with or without proof-of-work bits (`fbG`, Compile/Batch/Prover.lean):
under the hypotheses below, the query with its tokens under `up N₀ δ` and the query itself run alike
(`Par`, Compile/SeedKit.lean). -/
theorem par_fbG {β β' C P : Type} {r : β → β' → Prop} (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {k' : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β'}
    (h : ∀ nc dd bl tl,
      N₀ ≤ tl → Par N₀ δ r (k nc (dd.map (up N₀ δ)) bl (up N₀ δ tl)) (k' nc dd bl tl)) :
    Par N₀ δ r
      (fbG gr chal t i (up N₀ δ tk) (us.map (up N₀ δ)) (root.map (up N₀ δ)) hd hinj emb α k)
      (fbG gr chal t i tk us root hd hinj emb α k') := by
  cases gr with
  | none => exact par_fbT t i tk us root hd hinj _ fun bl tl htl => h none [] bl tl htl
  | some g =>
    show Par N₀ δ r
      (fbTG g chal t i (up N₀ δ tk) (us.map (up N₀ δ)) (root.map (up N₀ δ))
        hd hinj emb α fun m => k (some m))
      (fbTG g chal t i tk us root hd hinj emb α fun m => k' (some m))
    unfold fbTG
    cases g.more with
    | zero => exact par_fbT t i tk us root hd hinj _ fun bl tl htl => h (some 0) [] bl tl htl
    | succ n =>
      refine par_fbT t i tk us root hd hinj _ fun bl tl htl => ?_
      by_cases hok : g.ok (chal bl) = true
      · simp only [hok, if_true]; exact h (some 0) [] bl tl htl
      · simp only [hok]; exact par_fbW g chal t i tk us root hd hinj emb α (fun m dd bl tl htl => h (some m) dd bl tl htl) n 0 [tl]

theorem par_fbSlotG {β β' C P : Type} {r : β → β' → Prop} (gr : Option (GrW C P))
    (chal : Blk lam K → C) (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT)
    (tk c : Tok) (root : Option Tok) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {k' : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β'}
    (h : ∀ nc dd bl tl,
      N₀ ≤ tl → Par N₀ δ r (k nc (dd.map (up N₀ δ)) bl (up N₀ δ tl)) (k' nc dd bl tl)) :
    Par N₀ δ r
      (fbSlotG gr chal t i cms x (upPh N₀ δ ph) (up N₀ δ tk) (if chainsHaveJoined ph then up N₀ δ c else c)
        (root.map (up N₀ δ)) emb α k)
      (fbSlotG gr chal t i cms x ph tk c root emb α k') := by
  cases ph with
  | first => exact par_fbG gr chal t i tk [] root (fun _ => Head.f1 cms (x.map L.early)) (fun _ => f1_inj cms _) emb α h
  | loc => exact par_fbG gr chal t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) emb α h
  | aft => exact par_fbG gr chal t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) emb α h
  | shr tk0 => exact par_fbG gr chal t i c [tk0] root (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _) emb α h

theorem par_gT {β β' : Type} {r : β → β' → Prop} (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam K L β} {k' : Tok → St lam K L β'}
    (h : ∀ c, N₀ ≤ c → Par N₀ δ r (k (up N₀ δ c)) (k' c)) :
    Par N₀ δ r (gT (lam := lam) t i (up N₀ δ tk) (root.map (up N₀ δ)) pl k)
      (gT t i tk root pl k') := by
  unfold gT
  have e : (root.map (up N₀ δ)).toList = root.toList.map (up N₀ δ) := by cases root <;> rfl
  simp only [e, Option.map_map]
  exact Par.marked (S := spec lam K L) (sp := split lam K L) (t := tk) (us := root.toList) (OracleName.g t)
    _ _ fun _ c hc => h c hc

/-- the root of the tree over a component, if it has one -/
theorem map_root_up {d : ℕ} {ot : Option TTree} (h : ∀ tr, ot = some tr → FullT d tr) :
    (ot.map (upTT N₀ δ)).map TTree.root = (ot.map TTree.root).map (up N₀ δ) := by
  cases ot with
  | none => rfl
  | some tr =>
    show some (upTT N₀ δ tr).root = some (up N₀ δ tr.root)
    rw [root_upTT (h tr rfl).1]

/-- To renumber the tokens of the trees over a component and then take the roots gives the
renumbered roots, if every tree has full levels of some depth. Nothing is asked of an empty list. -/
theorem map_roots_up :
    ∀ {trs : List TTree}, (∀ tr ∈ trs, ∃ d, FullLv d tr.levels) →
      (trs.map (upTT N₀ δ)).map TTree.root = (trs.map TTree.root).map (up N₀ δ)
  | [], _ => rfl
  | tr :: trs, h => by
    obtain ⟨d, hd⟩ := h tr List.mem_cons_self
    simp only [List.map_cons]
    rw [root_upTT hd, map_roots_up fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- the same for a list of trees as `par_withTrees` hands it on -/
theorem map_roots_up_of_forall₂ {ds : List ℕ} {trs : List TTree} (h : Forall₂ FullT ds trs) :
    (trs.map (upTT N₀ δ)).map TTree.root = (trs.map TTree.root).map (up N₀ δ) :=
  map_roots_up (by
    induction h with
    | nil => exact fun _ hx => by cases hx
    | cons h1 _ ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, h1.1⟩
      · exact ih x hx)

/-- The tree over a component, if it has one, and then k. -/
theorem par_withTree {β β' : Type} {r : β → β' → Prop} (sMT : ℕ) (has : Bool) (d : ℕ)
    (leaf : ℕ → Body L) {k : Option TTree → St lam K L β} {k' : Option TTree → St lam K L β'}
    (h : ∀ ot, (∀ tr, ot = some tr → FullT d tr) → Par N₀ δ r (k (ot.map (upTT N₀ δ))) (k' ot)) :
    Par N₀ δ r (withTree sMT has d leaf k) (withTree sMT has d leaf k') := by
  cases has with
  | false => exact h none fun _ e => by cases e
  | true =>
    refine Par.bind (par_commitT sMT d leaf) fun tr tr' ht => ?_
    obtain ⟨rfl, hf⟩ := ht
    exact h (some tr') fun _ e => by cases e; exact hf

/-- The trees over a component, one after the other, and then k. What follows is given as many trees
as depths, every tree full with the depth at its own place in ds. -/
theorem par_withTrees {β β' : Type} {r : β → β' → Prop} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β}
      {k' : List TTree → St lam K L β'},
      (∀ trs, Forall₂ FullT ds trs → Par N₀ δ r (k (trs.map (upTT N₀ δ))) (k' trs)) →
      Par N₀ δ r (withTrees sMT ds leaf k) (withTrees sMT ds leaf k')
  | [], _, _, _, h => h [] .nil
  | d :: ds, leaf, _, _, h =>
    Par.bind (par_commitT sMT d (leaf 0)) fun tr tr' ht => by
      obtain ⟨rfl, hf⟩ := ht
      exact par_withTrees sMT ds (fun j => leaf (j + 1)) fun trs hs => h (tr' :: trs) (.cons hf hs)

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- A local round, in one slot. -/
theorem par_slotLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZ N₀ δ (chainsHaveJoined ph) dJ z z') :
    Par N₀ δ (fun o o' => RelZ N₀ δ (chainsHaveJoined ph) (dJ ++ [w.depthJ]) o o' ∧ o'.2.x = z'.2.x)
      (slotLo sMT t cms xin a w emb plJ i (upPh N₀ δ ph) z)
      (slotLo sMT t cms xin a w emb plJ i ph z') := by
  obtain ⟨⟨m, k⟩, acc'⟩ := z'
  obtain ⟨st, acc⟩ := z
  obtain ⟨h1, h2, hg⟩ := h
  dsimp only at h1 h2 hg
  subst h1 h2
  unfold slotLo
  dsimp only
  refine par_withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun ot hf => ?_
  rw [map_root_up hf]
  refine par_fbSlotG w.grJ w.chal t i cms (acc'.x.bind xin) ph acc'.tk acc'.c (ot.map TTree.root)
    plJ _ fun nc dd bl tl _ => Par.pure ⟨⟨rfl, ?_, hg.1.snoc hf, ?_⟩, rfl⟩
  · simp only [upAcc, List.map_append, List.map_cons, List.map_nil]
  · simp

/-- The joining round, in one slot. -/
theorem par_slotJoin {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {b : Bool} {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZ N₀ δ b dJ z z') :
    Par N₀ δ (fun o o' => RelZ N₀ δ true (dJ ++ [w.depthJ]) o o' ∧ o'.2.x = z'.2.x)
      (slotJoin sMT t a w emb plJ i z) (slotJoin sMT t a w emb plJ i z') := by
  obtain ⟨⟨m, k⟩, acc'⟩ := z'
  obtain ⟨st, acc⟩ := z
  obtain ⟨h1, h2, hg⟩ := h
  dsimp only at h1 h2 hg
  subst h1 h2
  unfold slotJoin
  dsimp only
  refine par_withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun ot hf => ?_
  rw [map_root_up hf]
  refine par_gT t i acc'.tk (ot.map TTree.root) _ fun c _ =>
    Par.pure ⟨⟨rfl, ?_, hg.1.snoc hf, ?_⟩, rfl⟩
  · simp only [upAcc, List.map_append, List.map_cons, List.map_nil, if_true]
  · simp

theorem RelZ.c_eq {s : Shape} {dJ : List ℕ} {z z' : SlotSt lam K Y s} (h : RelZ N₀ δ true dJ z z') :
    z.2.c = up N₀ δ z'.2.c := by
  rw [h.2.1]
  rfl

/-- The joining round in all slots. -/
theorem par_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {b : Bool} {dJ : List ℕ} :
    ∀ {zs zs' : List (SlotSt lam K Y (r :: s))}, Forall₂ (RelZ N₀ δ b dJ) zs zs' →
      Par N₀ δ (fun o o' =>
          Forall₂ (RelZ N₀ δ true (dJ ++ [w.depthJ])) o.1 o'.1 ∧
          o.2 = o'.2.map (up N₀ δ) ∧
          o'.2.length = zs'.length ∧
          o'.1.length = zs'.length)
        (joinM sMT t a w emb plJ i zs) (joinM sMT t a w emb plJ i zs')
  | _, _, .nil => Par.pure ⟨.nil, rfl, rfl, rfl⟩
  | _, _, @Forall₂.cons _ _ _ z z' zs zs' h1 h2 => by
    show Par N₀ δ _
      ((slotJoin sMT t a w emb plJ i z).bind fun y =>
        (joinM sMT t a w emb plJ i zs).bind fun o => Step.pure (y :: o.1, y.2.c :: o.2))
      ((slotJoin sMT t a w emb plJ i z').bind fun y =>
        (joinM sMT t a w emb plJ i zs').bind fun o => Step.pure (y :: o.1, y.2.c :: o.2))
    refine (par_slotJoin sMT t a w emb plJ i z z' h1).bind fun y y' hy =>
      (par_joinM a w emb plJ i h2).bind fun o o' ho =>
        Par.pure ⟨.cons hy.1 ho.1, ?_, congrArg (· + 1) ho.2.2.1, congrArg (· + 1) ho.2.2.2⟩
    show y.2.c :: o.2 = up N₀ δ y'.2.c :: o'.2.map (up N₀ δ)
    rw [hy.1.c_eq, ho.2.1]

end Rounds

/-- a slot receives a shared verifier message (`hear`) after its component of the round has been
recorded -/
theorem relZ_hear_noted {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    {b : Bool} {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZ N₀ δ b dJ z z') :
    RelZ N₀ δ b dJ (hear w bl true z) (hear w bl true z') := by
  obtain ⟨⟨m, k⟩, acc'⟩ := z'
  obtain ⟨st, acc⟩ := z
  obtain ⟨h1, h2, hg⟩ := h
  dsimp only at h1 h2 hg
  subst h1 h2
  exact ⟨rfl, rfl, hg⟩

/-- a slot receives a shared verifier message (`hear`) in a round in which it sends nothing -/
theorem relZ_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    {b : Bool} {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZ N₀ δ b dJ z z') :
    RelZ N₀ δ b (dJ ++ [w.depthJ]) (hear w bl false z) (hear w bl false z') := by
  obtain ⟨⟨m, k⟩, acc'⟩ := z'
  obtain ⟨st, acc⟩ := z
  obtain ⟨h1, h2, hg⟩ := h
  dsimp only at h1 h2 hg
  subst h1 h2
  refine ⟨rfl, ?_, hg.1.snoc_none _, hg.2⟩
  simp [hear, upAcc]

theorem par_tree0 {β β' : Type} {rr : β → β' → Prop} (sMT : ℕ) {r : Round} (a : RAnn r)
    (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0)
    {k : Option TTree → St lam K L β} {k' : Option TTree → St lam K L β'}
    (h : ∀ ot,
      (∀ tr, ot = some tr → FullT w.depth0 tr) → Par N₀ δ rr (k (ot.map (upTT N₀ δ))) (k' ot)) :
    Par N₀ δ rr (tree0 sMT a w emb m0 k) (tree0 sMT a w emb m0 k') :=
  par_withTree sMT w.has0 w.depth0 _ h

/-! ## Part 3. The openings -/

theorem par_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    {d : ℕ} {tr : TTree} (ht : FullT d tr) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, (∀ j ∈ js, j < 2 ^ d) →
      Par N₀ δ Eq (opensComp (K := K) (L := L) dec posAt o (upTT N₀ δ tr) isRead f js)
        (opensComp dec posAt o tr isRead f js)
  | [], _ => Par.pure rfl
  | j :: js, hj => by
    unfold opensComp
    refine Par.bind
      (par_opensComp dec posAt o ht isRead f js fun x hx => hj x (List.mem_cons_of_mem _ hx))
      fun f f' h => ?_
    subst h
    cases posAt j with
    | none => exact Par.pure rfl
    | some p =>
      by_cases hr : isRead p = true
      · simp only [hr, if_true]
        refine Par.bind (par_openT ht (hj j List.mem_cons_self) _) fun op op' h => ?_
        subst h
        exact Par.pure rfl
      · simp only [hr, Bool.false_eq_true, if_false]
        exact Par.pure rfl

theorem par_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (d : ℕ)
    (o : r.Orc) {tr : Option TTree} (ht : ∀ x, tr = some x → FullT d x) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Par N₀ δ Eq (opensOpt (K := K) (L := L) dec posAt d o (tr.map (upTT N₀ δ)) isRead f)
      (opensOpt dec posAt d o tr isRead f) := by
  cases tr with
  | none => exact Par.pure rfl
  | some x => exact par_opensComp dec posAt o (ht x rfl) isRead f _ fun j hj => List.mem_range.1 hj

/-- The openings in the trees of a component, made from the renumbered trees and made from the trees
themselves, are related by `Par` and return the same openings. A tree is asked to be full only in
the pairs of a depth and a tree that `opensTrees` walks. So nothing is asked where the component was
not sent (no tree). -/
theorem par_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      (∀ x ∈ ds.zip trs, FullT x.1 x.2) →
      Par N₀ δ Eq
        (opensTrees (K := K) (L := L) dec posAt o isRead k ds (trs.map (upTT N₀ δ)) f)
        (opensTrees dec posAt o isRead k ds trs f)
  | _, [], _, _, _ => Par.pure rfl
  | _, _ :: _, [], _, _ => Par.pure rfl
  | k, d :: ds, tr :: trs, f, ht => by
    refine Par.bind
      (par_opensTrees dec posAt o isRead (k + 1) ds trs f fun x h =>
        ht x (List.mem_cons_of_mem _ h))
      fun f1 f2 h => ?_
    subst h
    exact par_opensComp dec (posAt k) o (ht (d, tr) List.mem_cons_self) isRead _ _
      fun j hj => List.mem_range.1 hj

/-- the same for a list of trees as `par_withTrees` hands it on -/
theorem par_opensTrees_of_forall₂ {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) {ds : List ℕ}
    {trs : List TTree} (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (ht : Forall₂ FullT ds trs) :
    Par N₀ δ Eq
      (opensTrees (K := K) (L := L) dec posAt o isRead k ds (trs.map (upTT N₀ δ)) f)
      (opensTrees dec posAt o isRead k ds trs f) :=
  par_opensTrees dec posAt o isRead k ds trs f fun _ h => (List.forall₂_iff_zip.1 ht).2 h

theorem par_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      TOK (depthsJ s A W) tjs → TOK (depths0 s A W) t0s →
      Par N₀ δ Eq
        (opensB (L := L) s A W τ (tjs.map (Option.map (upTT N₀ δ)))
          (t0s.map (Option.map (upTT N₀ δ))) isRead)
        (opensB s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _, _, _ => Par.pure rfl
  | r :: s, (a, A), (w, W), (m, _, τ), _, _, isRead, @Forall₂.cons _ _ _ _ tj _ tjs hj hjs, @Forall₂.cons _ _ _ _ t0 _ t0s h0 h0s => by
    unfold opensB
    refine Par.bind (par_opensOpt w.pt.decPos w.posAt0 w.depth0 m.1 h0 _ _) fun f0 f0' h => ?_
    subst h
    refine Par.bind (par_opensOpt w.pt.decPos w.posAtJ w.depthJ m.1 hj _ _) fun f f' h => ?_
    subst h
    refine Par.bind (par_opensB s A W τ tjs t0s _ hjs h0s) fun g g' h => ?_
    subst h
    exact Par.pure rfl

theorem par_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    Par N₀ δ Eq (openE (K := K) (L := L) (upTree N₀ δ t) j a) (openE t j a) := by
  unfold openE
  show Par N₀ δ _ (match (t.salts.map (upS N₀ δ)).getD j none with
    | some (s, s') =>
      Step.reveal [s, s'] fun vs => Step.pure (⟨a, vs.headD [], pathOf t.levels j⟩ : Opening lam σ)
    | none => Step.pure (⟨a, [], pathOf t.levels j⟩ : Opening lam σ)) _
  rw [Compile.Seed.getD_upS]
  cases t.salts.getD j none with
  | none => exact Par.pure rfl
  | some ss => exact Par.reveal (ts := [ss.1, ss.2]) fun w => Par.pure rfl

theorem par_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos,
      Par N₀ δ Eq (opensExtB (K := K) (L := L) we y (trees.map (upTree N₀ δ)) isRead ps)
        (opensExtB we y trees isRead ps)
  | [] => Par.pure rfl
  | p :: ps => by
    unfold opensExtB
    refine Par.bind (par_opensExtB we y trees isRead ps) fun f f' h => ?_
    subst h
    by_cases hr : isRead p = true
    · simp only [hr, if_true]
      rw [Compile.Seed.getD_upTree]
      refine Par.bind (par_openE _ _ _) fun op op' h => ?_
      subst h
      exact Par.pure rfl
    · simp only [hr, Bool.false_eq_true, if_false]
      exact Par.pure rfl

/-! ## Part 4. The proof strings; a slot at the start -/

theorem toList_root_up {d : ℕ} {ot : Option TTree} (h : ∀ tr, ot = some tr → FullLv d tr.levels) :
    ((ot.map (upTT N₀ δ)).map TTree.root).toList = ((ot.map TTree.root).toList).map (up N₀ δ) := by
  cases ot with
  | none => rfl
  | some tr =>
    show [(upTT N₀ δ tr).root] = [up N₀ δ tr.root]
    rw [root_upTT (h tr rfl)]

theorem rootToks_up :
    ∀ {dJ d0 : List ℕ} {l l' : List (Option TTree)}, TOK dJ l → TOK d0 l' →
      rootToks (l.map (Option.map (upTT N₀ δ))) (l'.map (Option.map (upTT N₀ δ))) =
        (rootToks l l').map (up N₀ δ)
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .cons _ _, .nil => rfl
  | _, _, _, _, @Forall₂.cons _ _ _ _ tj _ tjs hj hjs, @Forall₂.cons _ _ _ _ t0 _ t0s h0 h0s => by
    show ((tj.map (upTT N₀ δ)).map TTree.root).toList ++
        ((t0.map (upTT N₀ δ)).map TTree.root).toList ++
        rootToks (tjs.map (Option.map (upTT N₀ δ))) (t0s.map (Option.map (upTT N₀ δ))) =
      ((tj.map TTree.root).toList ++ (t0.map TTree.root).toList ++ rootToks tjs t0s).map (up N₀ δ)
    rw [toList_root_up fun tr e => (hj tr e).1, toList_root_up fun tr e => (h0 tr e).1,
      rootToks_up hjs h0s, List.map_append, List.map_append]

theorem headD_up {l : List Tok} (h : l ≠ []) : (l.map (up N₀ δ)).headD 0 = up N₀ δ (l.headD 0) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

section Prove
variable (sFS : ℕ) {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (trees : List (TreeH lam)) (w : Wt)

/-- The proof string of a slot. -/
theorem par_finishSlot {depthReq : ℕ} (c0 : H.Coin0) {a0 : Acc0}
    (h0 : Good0 depthReq (depths0 Q.loc.shape Q.ann wq.sh) a0) {j : ℕ} (hj : j < 2 ^ depthReq)
    (x : Y) (cj : H.Coin) (b : Bool) {acc : SlotAcc lam K (Y × H.Coin)}
    (hg : GoodAcc (depthsJ Q.loc.shape Q.ann wq.sh) acc) :
    Par N₀ δ Eq
      (finishSlot (L := L) Q H wq wp (trees.map (upTree N₀ δ)) w c0 (upAcc0 N₀ δ a0)
        j x cj (upAcc N₀ δ b acc))
      (finishSlot Q H wq wp trees w c0 a0 j x cj acc) := by
  have eR : rootToks (acc.trees.map (Option.map (upTT N₀ δ)))
        (a0.trees.map (Option.map (upTT N₀ δ))) =
      (rootToks acc.trees a0.trees).map (up N₀ δ) :=
    rootToks_up hg.1 h0.1
  have eP : ((a0.req.map (upTT N₀ δ)).map fun rq => pathOf rq.levels j).getD [] =
      ((a0.req.map fun rq => pathOf rq.levels j).getD []).map (up N₀ δ) := by
    cases hq : a0.req with
    | none => rfl
    | some rq => exact pathOf_map _ (h0.2 rq hq) hj
  have eA : ((a0.req.map (upTT N₀ δ)).map fun rq => ancOf rq.levels j).getD [] =
      ((a0.req.map fun rq => ancOf rq.levels j).getD []).map (up N₀ δ) := by
    cases hq : a0.req with
    | none => rfl
    | some rq => exact ancOf_map _ (h0.2 rq hq) hj
  have eT : ((a0.req.map (upTT N₀ δ)).map TTree.root).toList =
      ((a0.req.map TTree.root).toList).map (up N₀ δ) :=
    toList_root_up h0.2
  unfold finishSlot
  dsimp only [upAcc, upAcc0]
  rw [eR, eP, eA, eT, headD_up hg.2]
  simp only [List.length_map]
  split_ifs with hw
  · exact Par.pure rfl
  · refine Par.reveal' (by simp only [List.map_cons, List.map_append]) fun vs => ?_
    refine Par.bind (par_opensB Q.loc.shape Q.ann wq.sh _ acc.trees a0.trees _ hg.1 h0.1)
      fun f f' h => ?_
    subst h
    refine Par.bind (par_opensExtB wq.ext (H.ext w) trees _ wq.ext.all) fun g g' h => ?_
    subst h
    exact Par.pure rfl

/-- The proof strings of all slots. -/
theorem par_finishAll {depthReq : ℕ} (fl : ℕ → Bool) (c0 : H.Coin0) {a0 : Acc0}
    (h0 : Good0 depthReq (depths0 Q.loc.shape Q.ann wq.sh) a0) :
    ∀ (j : ℕ) {l l' : List (SlotAcc lam K (Y × H.Coin))},
      Forall₂ (RelFin N₀ δ (depthsJ Q.loc.shape Q.ann wq.sh)) l l' → j + l'.length ≤ 2 ^ depthReq →
      Par N₀ δ Eq
        (finishAll (L := L) Q H wq wp (trees.map (upTree N₀ δ)) w fl c0 (upAcc0 N₀ δ a0) j l)
        (finishAll Q H wq wp trees w fl c0 a0 j l')
  | _, _, _, .nil, _ => Par.pure rfl
  | j, _, _, @Forall₂.cons _ _ _ acc acc' l l' h1 h2, hl => by
    simp only [List.length_cons] at hl
    unfold finishAll
    refine Par.bind (r := Eq) ?_ fun π π' h => ?_
    · rw [h1.1]
      cases hx : acc'.x with
      | none => exact Par.pure rfl
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · obtain ⟨b, rfl, hg⟩ := h1.2 (by rw [hx]; exact fun e => by cases e)
          exact par_finishSlot Q H wq wp trees w c0 h0 (by omega) x cj b hg
        · exact Par.pure rfl
    · subst h
      refine Par.bind (par_finishAll fl c0 h0 (j + 1) h2 (by omega)) fun r r' h => ?_
      subst h
      exact Par.pure rfl

/-- A slot at the start: its salt is its only token. -/
theorem par_initSlot (c0 : H.Coin0) (x : Option Y) :
    Par N₀ δ (fun z z' => RelZ N₀ δ false [] z z' ∧ z'.2.x.isSome = x.isSome)
      (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) (initSlot sFS Q H wp w c0 x) := by
  unfold initSlot
  refine Par.bind (par_drawT wp.coin) fun cj cj' h => ?_
  subst h
  refine Par.fresh sFS fun salt _ => Par.pure ⟨⟨rfl, rfl, .nil, by simp⟩, ?_⟩
  cases x <;> rfl

end Prove

end Seed
end Compile.Batch
