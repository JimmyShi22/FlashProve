-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SizeAccepted.lean: a slot's proof string that the compiled verifier with the
strict-format check (`verifyOneProtocol`) accepts has the format `FitsB` of Compile/Batch/Size.lean. This
file does not prove a size bound for keys and proofs (for pruned Merkle paths:
Compile/Batch/SizeO.lean). (Words of this library: lean/GLOSSARY.md.)

  `count_le_cRoots`   the roots that a run of the chain has taken are at most `cRoots`
  `parts_of_runsIn`, `tests_of_afterB`
      what an accepting run of `verifyOneProtocol` has checked (its end is `checkPrunedOpenings`, which checks the
      lengths of all paths although it uses only some of their digests)
  `OpensOK`   `OpensOK L Z`: the three verifiers read at most Z's numbers of positions
  `runsIn_of_accepts`   if V accepts under the oracle functions f, it returns true within some trace

Hypotheses of `fitsB_of_accepted`, none of which is about the key, the proof, the request or the
oracles: the wire record is well-formed (`wq.OKG`), the verifier reads at most the given numbers of
positions, and the trees over the external strings have at most the given depth. `RunsIn`
(Compile/Spec.lean) asks nothing of the answers but that they are in the trace: so the statements
hold for all oracle functions, and for every key and proof, honest or not.

Notation: the chain: `recomputeChain`, `recomputeChainOfProof` (Compile/Batch/Verifier.lean): "Recompute the chain of the
slot: the verifier messages of the local transcript, the roots round by round, and the last phase":
ρ, rts, ph; `ph`: a `Phase lam`: "how far the chain of a slot has come"; `t`: a `Tag`
(Compile/Oracles.lean); `cms`: a `List (Dig lam)`: "the external roots cms"; `embS`, `embP`, `embE`:
"embS, embP, embE say how symbols and plain parts are written into queries" (`verifyB`,
Compile/Batch/Verifier.lean); `xin`: of type `Y → Option X`.
-/
import Compile.Batch.Size
import Compile.Batch.GlueBinding
import Compile.Batch.CompleteOpen
import Compile.Batch.Runs
import Compile.SizeAccepted

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.SizeA
open Iop Rom Compile.SizeH

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. What the checks imply -/

theorem of_strictComp {sMT : ℕ} {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ} {sent : Bool}
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h : strictComp sMT posAt depth sent isRead g = true) {j : ℕ} (hj : j < 2 ^ depth) {p : r.Pos}
    (hp : posAt j = some p) {op : Opening lam (r.Sym p)} (hop : g p = some op) :
    sent = true ∧ isRead p = true ∧ op.salt.length = sMT := by
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simp only [hp, hop, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- if `checksComp` returns checks, they contain the opening of every read position at a leaf of js
-/
theorem mem_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)), checksComp posAt depth emb rt isRead g js = some cs →
      ∀ j ∈ js, ∀ p, posAt j = some p → isRead p = true →
        ∃ op, g p = some op ∧ (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ : Check lam L) ∈ cs
  | [], _, _, _, hj, _, _, _ => by cases hj
  | j0 :: js, cs, h, j, hj, p, hp, hr => by
      unfold checksComp at h
      split at h
      · rename_i p0 hp0
        split_ifs at h with hr0
        · split at h
          · rename_i op cs' hop hcs
            obtain rfl := Option.some.inj h
            rcases List.mem_cons.1 hj with rfl | hj'
            · obtain rfl : p0 = p := Option.some.inj (hp0.symm.trans hp)
              exact ⟨op, hop, List.mem_cons_self⟩
            · obtain ⟨op', h1, h2⟩ :=
                mem_checksComp posAt depth emb rt isRead g js cs' hcs j hj' p hp hr
              exact ⟨op', h1, List.mem_cons_of_mem _ h2⟩
          · cases h
        · rcases List.mem_cons.1 hj with rfl | hj'
          · obtain rfl : p0 = p := Option.some.inj (hp0.symm.trans hp)
            exact absurd hr hr0
          · exact mem_checksComp posAt depth emb rt isRead g js cs h j hj' p hp hr
      · rename_i hp0
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [hp0] at hp; cases hp
        · exact mem_checksComp posAt depth emb rt isRead g js cs h j hj' p hp hr

/-- one component: every opening at the position of a leaf is at a read position, has a salt of sMT
bits and a path of the depth of the tree -/
def TestedC (sMT : ℕ) {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Prop :=
  ∀ j p op, j < 2 ^ depth → posAt j = some p → g p = some op →
    isRead p = true ∧ op.salt.length = sMT ∧ op.path.length = depth

theorem testedC_of {sMT : ℕ} {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ}
    {emb : (p : r.Pos) → r.Sym p → Body L} {rt : Option (Dig lam)} {isRead : r.Pos → Bool}
    {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h1 : strictComp sMT posAt depth rt.isSome isRead g = true) {cs : List (Check lam L)}
    (h2 : checksOpt posAt depth emb rt isRead g = some cs) (h3 : ∀ c ∈ cs, c.wellFormed = true) :
    TestedC sMT posAt depth isRead g := by
  intro j p op hj hp hop
  obtain ⟨hs, hr, hl⟩ := of_strictComp h1 hj hp hop
  obtain ⟨c, rfl⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨op', hop', hmem⟩ :=
    mem_checksComp posAt depth emb c isRead g _ cs h2 j (List.mem_range.2 hj) p hp hr
  obtain rfl : op' = op := Option.some.inj (hop'.symm.trans hop)
  have := h3 _ hmem
  simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨hr, hl, this.1⟩

/-- One tree with its root: if the strict-format check passes and the checks are there and well
formed, `TestedC` holds of the tree. -/
theorem testedC_of_checksComp {sMT : ℕ} {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ}
    {emb : (p : r.Pos) → r.Sym p → Body L} {rt : Dig lam} {isRead : r.Pos → Bool}
    {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h1 : strictComp sMT posAt depth true isRead g = true) {cs : List (Check lam L)}
    (h2 : checksComp posAt depth emb rt isRead g (List.range (2 ^ depth)) = some cs)
    (h3 : ∀ c ∈ cs, c.wellFormed = true) : TestedC sMT posAt depth isRead g := by
  intro j p op hj hp hop
  obtain ⟨-, hr, hl⟩ := of_strictComp h1 hj hp hop
  obtain ⟨op', hop', hmem⟩ :=
    mem_checksComp posAt depth emb rt isRead g _ cs h2 j (List.mem_range.2 hj) p hp hr
  obtain rfl : op' = op := Option.some.inj (hop'.symm.trans hop)
  have := h3 _ hmem
  simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨hr, hl, this.1⟩

/-- One tree without a root: if the strict-format check passes, there is no opening at the position
of a leaf, so `TestedC` holds of the tree. -/
theorem testedC_of_noRoot {sMT : ℕ} {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ}
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h1 : strictComp sMT posAt depth false isRead g = true) :
    TestedC sMT posAt depth isRead g :=
  fun _ _ _ hj hp hop => absurd (of_strictComp h1 hj hp hop).1 (by simp)

/-- `TestedC` for every tree of one component, from tree number k on (`posAt n j`: the position at
leaf j of tree number n) -/
def TestedTrees (sMT : ℕ) {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (isRead : r.Pos → Bool)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ℕ → List ℕ → Prop
  | _, [] => True
  | k, d :: ds => TestedC sMT (posAt k) d isRead g ∧ TestedTrees sMT posAt isRead g (k + 1) ds

/-- From `TestedTrees` from tree number k on: `TestedC` holds of tree number k + n at the n-th depth
of the list. -/
theorem testedC_of_testedTrees {sMT : ℕ} {r : Round} {posAt : ℕ → ℕ → Option r.Pos}
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))} :
    ∀ (k : ℕ) (ds : List ℕ), TestedTrees sMT posAt isRead g k ds →
      ∀ n d, ds[n]? = some d → TestedC sMT (posAt (k + n)) d isRead g
  | _, [], _, _, _, hd => by simp at hd
  | _, _ :: _, h, 0, _, hd => by
      obtain rfl := Option.some.inj hd
      exact h.1
  | k, _ :: ds, h, n + 1, d, hd => by
      rw [show k + (n + 1) = k + 1 + n by omega]
      rw [List.getElem?_cons_succ] at hd
      exact testedC_of_testedTrees (k + 1) ds h.2 n d hd

/-- The trees of one component from number k on, each with or without a root: if the strict-format
check passes and the checks are there and well formed, `TestedTrees` holds. -/
theorem testedTrees_of_checksTrees {sMT : ℕ} {r : Round} {posAt : ℕ → ℕ → Option r.Pos}
    {emb : (p : r.Pos) → r.Sym p → Body L} {isRead : r.Pos → Bool}
    {g : (p : r.Pos) → Option (Opening lam (r.Sym p))} :
    ∀ (k : ℕ) (ds : List ℕ) (rts : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      strictTrees sMT posAt isRead g k ds rts = true →
      checksTrees posAt emb isRead g k ds rts = some l →
      (∀ z ∈ l, ∀ c ∈ z.2.2, c.wellFormed = true) → TestedTrees sMT posAt isRead g k ds
  | _, [], _, _, _, _, _ => trivial
  | k, _ :: ds, [], _, h1, _, _ => by
      simp only [strictTrees, Bool.and_eq_true] at h1
      exact ⟨testedC_of_noRoot h1.1,
        testedTrees_of_checksTrees (emb := emb) (k + 1) ds [] [] h1.2
          (by cases ds <;> simp only [checksTrees]) fun _ h => by cases h⟩
  | k, _ :: ds, _ :: cs, l, h1, h2, h3 => by
      simp only [strictTrees, Bool.and_eq_true] at h1
      simp only [checksTrees] at h2
      split at h2
      · rename_i a b ha hb
        obtain rfl := Option.some.inj h2
        exact ⟨testedC_of_checksComp h1.1 ha fun x hx => h3 _ List.mem_cons_self x hx,
          testedTrees_of_checksTrees (k + 1) ds cs b h1.2 hb fun z hz =>
            h3 z (List.mem_cons_of_mem _ hz)⟩
      · cases h2

/-- One component with a list of trees: if the strict-format check passes and the checks of all its
trees are there and well formed, `TestedTrees` holds. -/
theorem testedTrees_of {sMT : ℕ} {r : Round} {posAt : ℕ → ℕ → Option r.Pos} {ds : List ℕ}
    {emb : (p : r.Pos) → r.Sym p → Body L} {rts : List (Dig lam)} {isRead : r.Pos → Bool}
    {g : (p : r.Pos) → Option (Opening lam (r.Sym p))}
    (h1 : strictTrees sMT posAt isRead g 0 ds rts = true) {cs : List (Check lam L)}
    (h2 : checksOfTrees posAt ds emb rts isRead g = some cs) (h3 : ∀ c ∈ cs, c.wellFormed = true) :
    TestedTrees sMT posAt isRead g 0 ds := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h2
  exact testedTrees_of_checksTrees 0 ds rts l h1 hl fun z hz c hc =>
    h3 c (List.mem_flatMap.2 ⟨z, hz, hc⟩)

/-- the same for both components of all rounds -/
def Tested (sMT : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (OPos s → Bool) →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Prop
  | [], _, _, _, _ => True
  | _ :: s, (_, A), (w, W), isRead, g =>
      TestedC sMT w.posAt0 w.depth0 (fun p => isRead (.inl p)) (fun p => g (.inl p)) ∧
      TestedC sMT w.posAtJ w.depthJ (fun p => isRead (.inl p)) (fun p => g (.inl p)) ∧
      Tested sMT s A W (fun p => isRead (.inr p)) (fun p => g (.inr p))

theorem tested_of {sMT : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (g : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
      strictSB sMT s A W rts isRead g = true → checksB s A W emb rts isRead g = some cs →
      (∀ c ∈ cs, c.wellFormed = true) → Tested sMT s A W isRead g
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, g, cs, h1, h2, h3 => by
      have h1' : (strictComp sMT w.posAt0 w.depth0 rt.1.join.isSome
              (fun p => isRead (.inl p)) (fun p => g (.inl p)) &&
            strictComp sMT w.posAtJ w.depthJ rt.2.join.isSome
              (fun p => isRead (.inl p)) (fun p => g (.inl p)) &&
            strictSB sMT s A W rts (fun p => isRead (.inr p)) (fun p => g (.inr p))) = true := h1
      simp only [Bool.and_eq_true] at h1'
      unfold checksB at h2
      split at h2
      · rename_i a b c ha hb hc
        obtain rfl := Option.some.inj h2
        exact ⟨testedC_of h1'.1.1 ha fun x hx =>
            h3 x (List.mem_append_left _ (List.mem_append_left _ hx)),
          testedC_of h1'.1.2 hb fun x hx =>
            h3 x (List.mem_append_left _ (List.mem_append_right _ hx)),
          tested_of s A W _ rts _ _ c h1'.2 hc fun x hx => h3 x (List.mem_append_right _ hx)⟩
      · cases h2

theorem length_entriesC_le {r : Round} {posAt : ℕ → Option r.Pos} {depth : ℕ}
    {isRead : r.Pos → Bool} {g : (p : r.Pos) → Option (Opening lam (r.Sym p))} (place : r.Pos → ℕ)
    (hpl : ∀ j p, posAt j = some p → place p = j) (B : Finset r.Pos)
    (hB : ∀ j p, posAt j = some p → isRead p = true → p ∈ B)
    (h : ∀ j p op, posAt j = some p → g p = some op → isRead p = true) :
    (entriesC posAt depth g).length ≤ B.card := by
  refine le_trans (length_filterMap_le_filter _ (Cmpl.readAt posAt isRead) (fun j e he => ?_) _)
    (Cmpl.length_filter_readAt_le posAt place hpl isRead B hB _)
  obtain ⟨p, hp, he'⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨op, hop, -⟩ := Option.map_eq_some_iff.1 he'
  unfold Cmpl.readAt
  rw [hp]
  exact h j p op hp hop

/-- If in the trees from number k on an opening stands only at read positions, the opened positions
of these trees are at most as many as B has elements (B holds every read position of these trees).
hpl also says that a position stands in one tree only: else it would be counted twice. -/
theorem length_entriesTrees_le {r : Round} {posAt : ℕ → ℕ → Option r.Pos} {isRead : r.Pos → Bool}
    {g : (p : r.Pos) → Option (Opening lam (r.Sym p))} (tree place : r.Pos → ℕ)
    (hpl : ∀ n j p, posAt n j = some p → tree p = n ∧ place p = j) :
    ∀ (k : ℕ) (ds : List ℕ) (B : Finset r.Pos),
      (∀ n j p, k ≤ n → posAt n j = some p → isRead p = true → p ∈ B) →
      (∀ n j p op, k ≤ n → posAt n j = some p → g p = some op → isRead p = true) →
      (entriesTrees posAt g k ds).length ≤ B.card
  | _, [], _, _, _ => Nat.zero_le _
  | k, d :: ds, B, hB, h => by
      have a : (entriesC (posAt k) d g).length ≤ (B.filter fun p => tree p = k).card :=
        length_entriesC_le (isRead := isRead) place (fun j p hp => (hpl k j p hp).2) _
          (fun j p hp hr => Finset.mem_filter.2 ⟨hB k j p le_rfl hp hr, (hpl k j p hp).1⟩)
          fun j p op hp hop => h k j p op le_rfl hp hop
      have b := length_entriesTrees_le tree place hpl (k + 1) ds (B.filter fun p => ¬ tree p = k)
        (fun n j p hn hp hr =>
          Finset.mem_filter.2 ⟨hB n j p (by omega) hp hr, by rw [(hpl n j p hp).1]; omega⟩)
        fun n j p op hn hp hop => h n j p op (by omega) hp hop
      rw [entriesTrees, List.length_append]
      exact le_trans (Nat.add_le_add a b)
        (le_of_eq (Finset.card_filter_add_card_filter_not (s := B) fun p => tree p = k))

/-- From `Tested` (hypotheses below): the lists of opened positions satisfy `FitsEnt`, round by
round. -/
theorem fitsEnt_of_tested (sMT : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ (isRead : OPos s → Bool) (g : (p : OPos s) → Option (Opening lam (OSym s p))),
        Tested sMT s A W isRead g →
        ∀ (B : Finset (OPos s)), (∀ p, isRead p = true → p ∈ B) →
          ∀ o : OpenList s,
            OpenList.Bounds s o B → FitsEnt sMT s (flatS s A W) o (entriesSB s A W g)
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, W), hW, isRead, g, h, B, hB, (n, o), ho => by
      refine ⟨?_, ?_,
        fitsEnt_of_tested sMT s A W hW.2 (fun p => isRead (.inr p)) (fun p => g (.inr p)) h.2.2
          (Finset.toRight (show Finset (r.Pos ⊕ OPos s) from B))
          (fun p hp => Finset.mem_toRight.2 (hB (.inr p) hp)) o ho.2⟩
      · classical
        have hl : ∀ p,
            isRead (.inl p) = true → p ∈ Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B) :=
          fun p hp => Finset.mem_toLeft.2 (hB (.inl p) hp)
        have c0 : (entriesC w.posAt0 w.depth0 fun p => g (.inl p)).length ≤
            ((Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B)).filter fun p =>
              ¬ a.own p = true).card :=
          length_entriesC_le (isRead := fun p => isRead (.inl p))
            w.place (fun j p hp => (hW.1.place_posAt0 j p hp).2) _
            (fun j p hp hr =>
              Finset.mem_filter.2 ⟨hl p hr, by rw [(hW.1.place_posAt0 j p hp).1]; simp⟩)
            fun j p op hp hop => (h.1 j p op (by
              obtain ⟨h1, h2⟩ := hW.1.place_posAt0 j p hp
              rw [← h2]; exact hW.1.place_lt0 p h1) hp hop).1
        have cJ : (entriesC w.posAtJ w.depthJ fun p => g (.inl p)).length ≤
            ((Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B)).filter fun p =>
              a.own p = true).card :=
          length_entriesC_le (isRead := fun p => isRead (.inl p))
            w.place (fun j p hp => (hW.1.place_posAtJ j p hp).2) _
            (fun j p hp hr => Finset.mem_filter.2 ⟨hl p hr, (hW.1.place_posAtJ j p hp).1⟩)
            fun j p op hp hop => (h.2.1 j p op (by
              obtain ⟨h1, h2⟩ := hW.1.place_posAtJ j p hp
              rw [← h2]; exact hW.1.place_ltJ p h1) hp hop).1
        have hsum := Finset.card_filter_add_card_filter_not
          (s := Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B)) (fun p => a.own p = true)
        show (entriesC w.posAt0 w.depth0 (fun p => g (.inl p)) ++
            entriesC w.posAtJ w.depthJ fun p => g (.inl p)).length ≤ n
        rw [List.length_append]
        have := ho.1
        omega
      · rintro ⟨p, op⟩ hx
        rcases List.mem_append.1
          (show (⟨p, op⟩ : EntR lam r) ∈
            entriesC w.posAt0 w.depth0 (fun p => g (.inl p)) ++
              entriesC w.posAtJ w.depthJ fun p => g (.inl p) from hx) with hx | hx
        · obtain ⟨⟨j, hj, hp⟩, hop⟩ := (mem_entriesC _ _ _ p op).1 hx
          obtain ⟨-, h2, h3⟩ := h.1 j p op hj hp hop
          exact ⟨le_of_eq h2, le_trans (le_of_eq h3) (le_max_left _ _)⟩
        · obtain ⟨⟨j, hj, hp⟩, hop⟩ := (mem_entriesC _ _ _ p op).1 hx
          obtain ⟨-, h2, h3⟩ := h.2.1 j p op hj hp hop
          exact ⟨le_of_eq h2, le_trans (le_of_eq h3) (le_max_right _ _)⟩

theorem length_toList_eq {α : Type} (x : Option α) : x.toList.length = x.isSome.toNat := by
  cases x <;> rfl

/-- The chain takes a root only where the wire record has a tree: the roots that a run of the chain
has taken are at most cRoots. -/
theorem count_le_cRoots {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)} {x : Option X}
    {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      RootsOfChain.count s RTs ≤ cRoots s A ws
  | [], _, _, _, _, _, _, _, _, _, _, _ => Nat.le_refl _
  | _ :: s, (a, A), (w, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (rt, RTs), h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr, hf⟩ := runsIn_chainB_cons_flags h
      have ih := count_le_cRoots s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hr
      have key : rt.1.join.toList.length + rt.2.join.toList.length ≤
          (match a.kind with | .lo => 0 | .sh => w.has0.toNat) + w.hasJ.toNat := by
        cases hv with
        | f1 root ans hk =>
          rw [hk, ← hf.2 root rfl]; exact le_of_eq (congrArg (0 + ·) (length_toList_eq root))
        | f2 ρ' root ans hk =>
          rw [hk, ← hf.2 root rfl]; exact le_of_eq (congrArg (0 + ·) (length_toList_eq root))
        | f3 ρ0 c root ans hk =>
          rw [hk, ← hf.2 root rfl]; exact le_of_eq (congrArg (0 + ·) (length_toList_eq root))
        | f2' ρ' c root ans hk =>
          rw [hk, ← hf.2 root rfl]; exact le_of_eq (congrArg (0 + ·) (length_toList_eq root))
        | f5 ρ0 c root ans hk => rw [hk]; exact Nat.add_le_add (le_of_eq (by rw [← hf.1 root rfl]; exact length_toList_eq root)) (Nat.zero_le _)
        | join ρ' rtj rt0 c ans hk hg =>
          rw [hk]
          exact Nat.add_le_add (le_of_eq (by rw [← hf.1 rt0 rfl]; exact length_toList_eq rt0))
            (le_of_eq (by rw [← hf.2 rtj rfl]; exact length_toList_eq rtj))
      exact Nat.add_le_add key ih

theorem mem_checksExt {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (Check lam L)), checksExt we emb cms isRead g ps = some cs →
      ∀ p ∈ ps, isRead p = true →
        ∃ op,
          g p = some op ∧
          (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
              cms.getD (we.which p) default, we.depth⟩ : Check lam L) ∈ cs
  | [], _, _, _, hp, _ => by cases hp
  | p0 :: ps, cs, h, p, hp, hr => by
      unfold checksExt at h
      split_ifs at h with hr0
      · split at h
        · rename_i op cs' hop hcs
          obtain rfl := Option.some.inj h
          rcases List.mem_cons.1 hp with rfl | hp'
          · exact ⟨op, hop, List.mem_cons_self⟩
          · obtain ⟨op', h1, h2⟩ := mem_checksExt we emb cms isRead g ps cs' hcs p hp' hr
            exact ⟨op', h1, List.mem_cons_of_mem _ h2⟩
        · cases h
      · rcases List.mem_cons.1 hp with rfl | hp'
        · exact absurd hr hr0
        · exact mem_checksExt we emb cms isRead g ps cs h p hp' hr

/-! ## Part 2. An accepting run of verifyOneProtocol -/

section B

variable {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
  {wq : ProtocolQueryLayout lam K Q} {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y}
  {π : OneProtocolProof lam Q} {tr : Trace (spec lam K L)}

/-- An accepting run has recomputed the chain, passed the strict-format check, and gone on to
accept. -/
theorem parts_of_runsIn
    (h : RunsIn tr (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) true) :
    ∃ ρ rts ph,
      RunsIn tr (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)) ∧
      proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph = true ∧
      RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true := by
  unfold verifyOneProtocol at h
  obtain ⟨r, hr, h⟩ := (runsIn_bind_iff _ _ _).1 h
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · dsimp only at h
    split_ifs at h with hst
    · exact ⟨ρ, rts, ph, hr, hst, h⟩
    · exact absurd (runsIn_pure_iff.1 h) (by simp)

/-- what checkPrunedOpenings has checked when it accepts -/
theorem tests_of_afterB {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (h : RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true) :
    (haveI := wq.decO; haveI := wq.ext.dec
     ∃ a b, checksB Q.loc.shape Q.ann wq.sh embS rts
           (fun p => decide (p ∈ Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann rts π.plains)))
           π.opens = some a ∧
      checksExt wq.ext embE cms (fun p => decide (p ∈ Q.loc.extReads x ρ)) π.ext wq.ext.all =
        some b ∧
      ∀ c ∈ a ++ b, c.wellFormed = true) ∧
      (ph.slotVal.isSome = true → π.path.length = depthReq) := by
  unfold checkPrunedOpenings at h
  split at h
  · rename_i Fs hFs
    obtain ⟨-, a, b, ha, hb, hflat⟩ := forestsOf_spec hFs
    split_ifs at h with hc
    · refine ⟨⟨a, b, ha, hb, fun c hcm => ?_⟩, fun hs => ?_⟩
      · have := List.all_eq_true.1 hc.2 c (hflat ▸ hcm)
        simp only [Bool.and_eq_true] at this
        exact this.1
      · obtain ⟨c, hcv⟩ := Option.isSome_iff_exists.1 hs
        unfold afterF reqPart at h
        simp only [pure_eq, runsIn_bind_iff, runsIn_pure_iff, hcv] at h
        obtain ⟨ok, -, okr, hokr, hall⟩ := h
        simp only [Bool.and_eq_true] at hall
        obtain rfl := hall.1.2
        unfold reqCheck at hokr
        split_ifs at hokr with hq
        · exact hq.1
        · exact absurd (runsIn_pure_iff.1 hokr) (by simp)
    · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · exact absurd (runsIn_pure_iff.1 h) (by simp)

/-- Under the hypotheses below: a slot's proof string that `verifyOneProtocol` accepts within a trace has
`FitsB`. -/
theorem fitsB_of_accepted (hwq : wq.OKG) (o : OpenList Q.loc.shape) (ho : Q.loc.OpensLe o)
    (eN : ExtNums) (hE : ∀ x ρ, (Q.loc.extReads x ρ).card ≤ eN.n) (hd : wq.ext.depth ≤ eN.d)
    (h : RunsIn tr (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) true) :
    FitsB sMT sFS wq depthReq o eN (encB wq π) := by
  obtain ⟨ρ, rts, ph, hch, hst, haft⟩ := parts_of_runsIn h
  obtain ⟨⟨a, b, ha, hb, hwf⟩, hpath⟩ := tests_of_afterB haft
  unfold proofHasStrictFormat at hst
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩ := hst
  refine ⟨le_of_eq s1, le_trans s2 (count_le_cRoots _ _ _ _ _ _ _ _ _ _ _ hch), ?_, ?_, ?_,
    Nat.le_sub_one_of_lt s5, ?_⟩
  · exact fitsEnt_of_tested sMT Q.loc.shape Q.ann wq.sh hwq.sh _ π.opens
      (tested_of Q.loc.shape Q.ann wq.sh embS rts _ _ a s3 ha fun c hc =>
        hwf c (List.mem_append_left _ hc))
      (Q.loc.reads x ρ _) (fun p hp => by simpa only [decide_eq_true_eq] using hp) o (ho x ρ _)
  · refine le_trans
      (length_entriesE_le hwq.ext π.ext _
        (fun p op hop => (Compile.SizeA.of_strictExt hwq.ext s4 p op hop).1)
        (Q.loc.extReads x ρ) ?_) (hE x ρ)
    exact fun p hp => by simpa only [decide_eq_true_eq] using hp
  · rintro ⟨q, op⟩ hx
    have hop := (mem_entriesE hwq.ext _ q op).1 hx
    obtain ⟨hr, hsl⟩ := Compile.SizeA.of_strictExt hwq.ext s4 q op hop
    obtain ⟨op', hop', hmem⟩ := mem_checksExt wq.ext embE cms _ _ _ b hb q (hwq.ext.complete q) hr
    obtain rfl : op' = op := Option.some.inj (hop'.symm.trans hop)
    have := hwf _ (List.mem_append_right _ hmem)
    simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨le_of_eq hsl, le_trans (le_of_eq this.1) hd⟩
  · rcases s6 with h6 | h6
    · exact le_of_eq (hpath h6)
    · show π.path.length ≤ depthReq
      rw [List.isEmpty_iff.1 h6]
      exact Nat.zero_le _

end B

end Compile.Batch.SizeA

namespace Compile.Batch
open Iop Rom Compile.Batch.SizeA

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The three verifiers read at most Z's numbers of positions. -/
structure OpensOK (L : BatchProtocol I X) (Z : SizeNums L) : Prop where
  T : L.offline.OpensLe Z.oT
  Lk : L.link.OpensLe Z.oL
  O : L.onlineBatch.loc.OpensLe Z.oO
  eT : ∀ x ρ, (L.offline.extReads x ρ).card ≤ Z.eT
  eL : ∀ x ρ, (L.link.extReads x ρ).card ≤ Z.eL
  eO : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ Z.eO

/-- If V accepts under the oracle functions f, it accepts when its queries are answered from some
trace. -/
theorem runsIn_of_accepts (W : QueryLayout lam L) (p : Params) (f : Fam (spec lam W.K L)) {v : IVK lam L}
    {x : X} {π : Prf lam L} (h : true ∈ ((V W p v x π).runEager f).support) :
    ∃ tr, RunsIn tr (V W p v x π) true := by
  rw [← runEager_withTrace_fst f, PMF.support_map] at h
  obtain ⟨c, hc, hc1⟩ := h
  have := runsIn_of_mem_support (detBound_V W p v x π) f c hc
  rw [hc1] at this
  exact ⟨c.2, this⟩


end Compile.Batch
