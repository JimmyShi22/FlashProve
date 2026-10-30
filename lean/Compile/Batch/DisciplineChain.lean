-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineChain.lean: a local round of the Fiat-Shamir chains of a batch, from an
orderly state (`TidyO`) with `SlotI` in each slot, and under the further hypotheses of the
statements: (1) obeys the rules of deferred programming; (2) keeps both, `TidyO` and `SlotI`, and
with `SlotI` what each slot's one reveal (in this sense: the `Step.reveal` in the body of
`finishSlot`; `openT`, `openE` are further ones) needs of it, for the rounds made (`SlotI.fin`:
`SlotF`). Also: the invariant between two rounds, `ChainInv` (words of this library:
lean/GLOSSARY.md).

For `Spec.safeProveB` (Compile/Batch/DisciplineStar.lean), on the programs of
Compile/Batch/Prover.lean. The definitions of `SlotI`, `SlotF`, `Cap` are in
Compile/Batch/DisciplineSlot.lean. Part A: what one marked query does to the set of tokens of a
slot. A component may have no tree (`has0`, `hasJ`, Iop/BatchWire.lean). All lemmas on a round are
about x : Option TTree, the tree over the component if it has one; `rtL x` is the list of its root,
with one entry or none; `NewT` says what is known of the tree just after it has been made, and
nothing if there is none; `safe_withTree` is the one place where the two cases are told apart. A
round may have proof-of-work bits (`fbG`, `fbSlotG`, Compile/Batch/Prover.lean): its Fiat-Shamir
query is then a search. The search is taken as one unit (`Tries`, `safe_fbG`,
Compile/Batch/DisciplineLoop.lean): the lemmas of Part A are about the state after all attempts; the
tails of the failed attempts join the set of tokens of the slot as dead tails. One marked query is
the search with one attempt. `NewTree`, `NewTs`, `safe_withTrees`, `usOfRoots`, `lo_preTrees`: what
`NewT`, `safe_withTree`, `usOf`, `lo_pre` say, for a component with a list of trees (`withTrees`,
Compile/Batch/Prover.lean). In Part B (the rounds) `usOfRoots` and `lo_preTrees` alone are about
such lists, and no lemma on a program of a round (`safe_fbSlotG`, `safe_slotLo`, `safe_eachLo`)
uses any of these.

Notation:
  local, shared (of a round; the head of Compile/Batch/Verifier.lean): shared if its challenge is
    one for all slots, local if each slot has its own;
  `SlotF`, `Cap`, `SlotI` (Compile/Batch/DisciplineSlot.lean): what the end needs of a slot; what
    the next round needs of a slot; both, and the next token to be charged is no dead tail;
  `n₀`: a natural number; `SlotF.new`: n₀ ≤ u for every token u of the slot
    (Compile/Batch/DisciplineSlot.lean);
  `lo`: a natural number; `NewT d lo depth x`: the tree is in order with tokens from lo on;
  `done`: a list of pairs of numbers: the depths of the trees of the rounds made (`ChainInv`); in
    a pair the slot's tree first, then the shared one (`depthsOf`,
    Compile/Batch/DisciplineSlot.lean);
  `j`: the number of the slot (`InU`, Compile/Batch/DisciplineSlot.lean);
  `ph`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `acc.tk`, `acc.c` (fields of `SlotAcc`, Compile/Batch/Prover.lean: what a slot has accumulated):
    the token that the next query of its chain holds (not in the phase `shr tk0`: see `live`,
    Compile/Batch/DisciplineSlot.lean); its slot value, once the chains have joined;
  charged, others, tail (fields of `Ev`, Rom/Defer.lean): every marked evaluation is charged to
    one token; it may hold further tokens; the tail of its answer is a new token;
  `OpenOf ph acc` (Compile/Batch/DisciplineSlot.lean): the open ends: the tokens of the slot that
    may still be charged;
  `Sealed d u` (Compile/Batch/DisciplineTree.lean; `SealedW`, Compile/Batch/DisciplineRun.lean):
    some query to an oracle outside `Wk` holds u;
  `Dead d u` (Compile/Batch/DisciplineSlot.lean; `DeadW`, Compile/Batch/DisciplineRun.lean): u is
    the tail of a query, to an oracle outside `Wk`, whose charged token has a later query;
  `Wk` (Compile/Batch/DisciplineSlot.lean): the leaf oracle of request trees;
  `Run Cc Ch R e M d d'` (Compile/Batch/DisciplineRun.lean): what a run does: Cc bounds the old
    tokens that it charges, Ch those that its queries hold; e and M count (R: see its doc comment);
  `zr`, `NoTok` (Compile/Batch/DisciplineE.lean): no query; no token;
  `MLo lam K L t dJ m` (Compile/Batch/DisciplineCnt.lean): the queries of one slot in a local
    round (a bound); m: the attempts after the first;
  `moreOf gr` (Compile/Batch/Counts.lean): at most this many attempts after the first: 0 without
    proof-of-work bits.
-/
import Compile.Batch.DisciplineSlot
import Compile.Batch.DisciplineLoop

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type}

/-! ## Part A. One marked query -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₂ : List α}
    {l₂' : List β} (h₂ : List.Forall₂ R l₂ l₂') :
    ∀ {l₁ : List α} {l₁' : List β}, List.Forall₂ R l₁ l₁' → List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, .nil => h₂
  | _, _, .cons h t => .cons h (forall₂_append h₂ t)

section Generic
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {W : S.ι → Prop} {d : DSt S}

theorem ClS.congr {V V' Op Op' : Tok → Prop} (h : ClS W d V Op)
    (hV : ∀ u, V' u ↔ V u) (hOp : ∀ u, V u → Op u → Op' u) : ClS W d V' Op' where
  closed := fun e he hc =>
    ⟨(hV _).2 (h.closed e he ((hV _).1 hc)).1,
      fun v hv => (hV _).2 ((h.closed e he ((hV _).1 hc)).2 v hv)⟩
  lt := fun u hu => h.lt u ((hV u).1 hu)
  sealed := fun u hu => (h.sealed u ((hV u).1 hu)).imp_right (hOp u ((hV u).1 hu))

/-- Under the hypotheses below: an open end of a closed set is charged: the set grows by the tail
and by the others; the tail is the new open end; the charged token and the others are sealed. -/
theorem ClS.extend_mark {V Op : Tok → Prop} (hd : TidyO Rl d) (h : ClS W d V Op) {o : S.ι}
    (ho : ¬ W o) {t : Tok} {us : List Tok} (hus : ∀ u ∈ us, u < d.vals.length ∧ (V u ∨ Deps d u []))
    (P : S.Dom o) (r : S.Rng o) (T : Table S) :
    ClS W (afterMark sp d o t us P r T) (fun u => V u ∨ u = d.vals.length ∨ u ∈ us)
      (fun u => u = d.vals.length ∨ (Op u ∧ u ≠ t ∧ u ∉ us)) where
  closed := fun e he hc => by
    rcases mem_evs_afterMark he with he | rfl
    · rcases hc with hc | hc | hc
      · exact ⟨Or.inl (h.closed e he hc).1, fun v hv => Or.inl ((h.closed e he hc).2 v hv)⟩
      · exact absurd (hc ▸ hd.charged_lt e he) (lt_irrefl _)
      · rcases (hus _ hc).2 with hv | hv
        · exact ⟨Or.inl (h.closed e he hv).1, fun v hv' => Or.inl ((h.closed e he hv).2 v hv')⟩
        · exact absurd (hv e he rfl).1 List.not_mem_nil
    · exact ⟨Or.inr (Or.inl rfl), fun v hv => Or.inr (Or.inr hv)⟩
  lt := fun u hu => by
    rw [length_afterMark]
    rcases hu with hu | hu | hu
    · exact Nat.lt_succ_of_lt (h.lt u hu)
    · exact hu ▸ Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hus u hu).1
  sealed := fun u hu => by
    by_cases h1 : u = t
    · exact Or.inl (SealedW.of_mark ho d t us P r T (Or.inl h1))
    · by_cases h2 : u ∈ us
      · exact Or.inl (SealedW.of_mark ho d t us P r T (Or.inr h2))
      · rcases hu with hu | hu | hu
        · rcases h.sealed u hu with hs | hs
          · exact Or.inl (hs.mono (Persist.ofMark d o t us P r T))
          · exact Or.inr (Or.inr ⟨hs, h1, h2⟩)
        · exact Or.inr (Or.inl hu)
        · exact absurd hu h2

/-- Under the hypotheses below: an open end of a closed set is charged by all attempts of a search:
the set grows by the tails and by the others; the last tail is the new open end; the other tails are
dead; the charged token and the others are sealed. -/
theorem ClS.extend_tries {V Op : Tok → Prop} {d' : DSt S} (hd : TidyO Rl d) (h : ClS W d V Op)
    {os : List S.ι} (ho : ∀ o ∈ os, ¬ W o) {t : Tok} {us l : List Tok} {tl : Tok}
    (hus : ∀ u ∈ us, u < d.vals.length ∧ (V u ∨ Deps d u []))
    (hT : Tries sp t us d os (l ++ [tl]) d') :
    ClS W d' (fun u => V u ∨ u = tl ∨ u ∈ l ∨ u ∈ us)
      (fun u => u = tl ∨ DeadW W d' u ∨ (Op u ∧ u ≠ t ∧ u ∉ us)) where
  closed := fun e he hc => by
    rcases hT.mem_evs e he with he | ⟨_, b, c, _⟩
    · have hlt := hd.charged_lt e he
      rcases hc with hc | hc | hc | hc
      · exact ⟨Or.inl (h.closed e he hc).1, fun v hv => Or.inl ((h.closed e he hc).2 v hv)⟩
      · exact absurd hlt
          (Nat.not_lt.mpr
            (hT.tail_ge _ (hc ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl))))
      · exact absurd hlt (Nat.not_lt.mpr (hT.tail_ge _ (List.mem_append_left _ hc)))
      · rcases (hus _ hc).2 with hv | hv
        · exact ⟨Or.inl (h.closed e he hv).1, fun v hv' => Or.inl ((h.closed e he hv).2 v hv')⟩
        · exact absurd (hv e he rfl).1 List.not_mem_nil
    · refine ⟨?_, fun v hv => Or.inr (Or.inr (Or.inr (b ▸ hv)))⟩
      rcases List.mem_append.mp c with c | c
      · exact Or.inr (Or.inr (Or.inl c))
      · exact Or.inr (Or.inl (List.mem_singleton.mp c))
  lt := fun u hu => by
    rcases hu with hu | hu | hu | hu
    · exact lt_of_lt_of_le (h.lt u hu) hT.length_le
    · exact hT.tail_lt u (hu ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · exact hT.tail_lt u (List.mem_append_left _ hu)
    · exact lt_of_lt_of_le (hus u hu).1 hT.length_le
  sealed := fun u hu => by
    by_cases h1 : u = t
    · exact Or.inl (hT.sealed ho (Or.inl h1))
    · by_cases h2 : u ∈ us
      · exact Or.inl (hT.sealed ho (Or.inr h2))
      · rcases hu with hu | hu | hu | hu
        · rcases h.sealed u hu with hs | hs
          · exact Or.inl (hs.mono (hT.run (R := fun _ => False) (e := fun _ => 0)).keeps)
          · exact Or.inr (Or.inr (Or.inr ⟨hs, h1, h2⟩))
        · exact Or.inr (Or.inl hu)
        · exact Or.inr (Or.inr (Or.inl (hT.dead ho u hu)))
        · exact absurd hu h2

end Generic

theorem Cap.not_sealed {d : DSt (spec lam K L)} {ph : PhT} {a0 : Acc0}
    {acc : SlotAcc lam K Y} (h : Cap p d ph a0 acc) : ¬ Sealed d (live ph acc) := by
  cases ph with
  | shr tk0 => exact h.2.2.1.not_sealed
  | first => exact h.1.not_sealed
  | loc => exact h.1.not_sealed
  | aft => exact h.1.not_sealed

theorem Cap.lt {d : DSt (spec lam K L)} {ph : PhT} {a0 : Acc0}
    {acc : SlotAcc lam K Y} (h : Cap p d ph a0 acc) :
    live ph acc < d.vals.length := by
  cases ph with
  | shr tk0 => exact h.1
  | first => exact h.1.lt
  | loc => exact h.1.lt
  | aft => exact h.1.lt

theorem Cap.mem {d : DSt (spec lam K L)} {ph : PhT} {a0 : Acc0}
    {acc : SlotAcc lam K Y} (h : Cap p d ph a0 acc) : live ph acc ∈ acc.toks := by
  cases ph with
  | shr tk0 => exact h.2.2.2.2.1
  | first => exact h.2.2
  | loc => exact h.2.2
  | aft => exact h.2.2

/-- What the next round needs survives a run whose queries do not hold the live token and that does
not show it. -/
theorem Cap.grows {d d' : DSt (spec lam K L)} {ph : PhT} {a0 : Acc0} {acc : SlotAcc lam K Y}
    {Ch R : Tok → Prop} {e M : OracleName → ℕ} (h : Cap p d ph a0 acc) (hg : GrowsO Ch R e M d d')
    (hc : ¬ Ch (live ph acc)) (hr : ¬ R (live ph acc)) : Cap p d' ph a0 acc := by
  cases ph with
  | shr tk0 =>
    exact ⟨lt_of_lt_of_le h.1 hg.length_le, not_shown_grows h.1 h.2.1 hg hr,
      h.2.2.1.grows h.1 hg hc, h.2.2.2.1.grows hg, h.2.2.2.2⟩
  | first => exact ⟨h.1.grows hg hc hr, h.2.1.grows hg, h.2.2⟩
  | loc => exact ⟨h.1.grows hg hc hr, h.2.1.grows hg, h.2.2⟩
  | aft => exact ⟨h.1.grows hg hc hr, h.2.1.grows hg, h.2.2⟩

/-- Under `SlotI`: the live token of a slot may be charged -/
theorem SlotI.fit {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0}
    {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI p d n₀ done ph a0 j acc) : Fit d (live ph acc) :=
  ⟨h.cap.not_sealed, h.alive⟩

/-- Under `TidyO`: a slot is not disturbed by a run that charges no sealed token, no dead tail and
none of its open ends, whose queries do not hold its live token, and that shows nothing. -/
theorem SlotI.frame {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {ph : PhT} {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} {Cc Ch : Tok → Prop}
    {e M : OracleName → ℕ} (h : SlotI p d n₀ done ph a0 j acc)
    (hd : TidyO (rulesB K L lam p) d) (hr : Run Cc Ch NoTok e M d d')
    (hc : ∀ u, Cc u → Fit d u ∧ ¬ OpenOf ph acc u) (hh : ¬ Ch (live ph acc)) :
    SlotI p d' n₀ done ph a0 j acc :=
  ⟨h.fin.keeps hr hc,
    h.cap.grows hr.grows hh fun x => x,
    DeadW.keeps_not h.alive hd h.cap.lt hr fun u hu => (hc u hu).1.1⟩

/-- the root of the tree over a component, as the tokens that a query holds for it: none if the
component has no tree -/
abbrev rtL (x : Option TTree) : List Tok := (x.map TTree.root).toList

theorem mem_rtL {x : Option TTree} {u : Tok} : u ∈ rtL x ↔ ∃ tr, x = some tr ∧ u = tr.root := by
  cases x <;> simp [rtL]

/-- The tree over a component, just made, if the component has one (what safe_commitT says of it):
it is in order with tokens from lo on, its root is untouched, its other tokens are sealed. -/
def NewT (d : DSt (spec lam K L)) (lo depth : ℕ) (x : Option TTree) : Prop :=
  ∀ tr, x = some tr →
    TTOK d lo depth tr ∧
    Untouched d tr.root ∧
    lo ≤ tr.root ∧
    ∀ i < 2 ^ depth,
      ∀ u ∈ tr.salts.getD i 0 :: (pathOf tr.levels i ++ ancOf tr.levels i), u = tr.root ∨ Sealed d u

theorem NewT.unt {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree} (h : NewT d lo depth x)
    {u : Tok} (hu : u ∈ rtL x) : Untouched d u := by
  obtain ⟨tr, e, rfl⟩ := mem_rtL.1 hu
  exact (h tr e).2.1

theorem NewT.lt {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree} (h : NewT d lo depth x)
    {u : Tok} (hu : u ∈ rtL x) : u < d.vals.length :=
  (h.unt hu).lt

theorem NewT.le {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree} (h : NewT d lo depth x)
    {u : Tok} (hu : u ∈ rtL x) : lo ≤ u := by
  obtain ⟨tr, e, rfl⟩ := mem_rtL.1 hu
  exact (h tr e).2.2.1

/-- Under the hypotheses below: the new tree after a query that holds its root and is charged to an
older token is in order, and all its tokens are sealed. -/
theorem NewT.tts {d : DSt (spec lam K L)} {n₀ lo depth : ℕ} {x : Option TTree}
    (h : NewT d lo depth x) (hn : n₀ ≤ lo) {o : OracleName} (ho : ¬ Wk o) {t : Tok} (ht : t < lo)
    {us : List Tok} (hrm : ∀ u ∈ rtL x, u ∈ us) (P : (spec lam K L).Dom o)
    (r : (spec lam K L).Rng o) (T : Table (spec lam K L)) (tr : TTree) (e : x = some tr) :
    TTS (afterMark (split lam K L) d o t us P r T) n₀ depth tr := by
  obtain ⟨htr, _, _, hse⟩ := h tr e
  have hrun : Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) NoTok zr (cnt1 o 1) d
      (afterMark (split lam K L) d o t us P r T) :=
    Run.ofMark d o t us P r T
  refine ⟨⟨fun i hi => (htr.open_ i hi).keeps hrun.charges fun u hu hcu => ?_,
      fun i hi u hu => le_trans hn (htr.new i hi u hu)⟩,
    fun i hi u hu => ?_⟩
  · exact absurd (htr.new i hi u hu) (Nat.not_le.mpr (hcu ▸ ht))
  · rcases hse i hi u hu with h1 | h1
    · exact SealedW.of_mark ho d t us P r T (Or.inr (hrm u (mem_rtL.2 ⟨tr, e, h1⟩)))
    · exact h1.mono hrun.keeps

/-- the same as `NewT.tts` after all attempts of a search -/
theorem NewT.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo depth : ℕ} {x : Option TTree}
    (h : NewT d lo depth x) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o) {t : Tok}
    (ht : t < lo) {us tls : List Tok} (hrm : ∀ u ∈ rtL x, u ∈ us)
    (hT : Tries (split lam K L) t us d os tls d') (tr : TTree) (e : x = some tr) :
    TTS d' n₀ depth tr := by
  obtain ⟨htr, _, _, hse⟩ := h tr e
  have hrun : Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) NoTok zr
      (fun o => os.count o) d d' := hT.run
  refine ⟨⟨fun i hi => (htr.open_ i hi).keeps hrun.charges fun u hu hcu => ?_,
      fun i hi u hu => le_trans hn (htr.new i hi u hu)⟩,
    fun i hi u hu => ?_⟩
  · exact absurd (htr.new i hi u hu) (Nat.not_le.mpr (hcu ▸ ht))
  · rcases hse i hi u hu with h1 | h1
    · exact hT.sealed ho (Or.inr (hrm u (mem_rtL.2 ⟨tr, e, h1⟩)))
    · exact h1.mono hrun.keeps

/-- One tree over a component, just made (what safe_commitT says of it): it is in order with tokens
from lo on, its root is untouched, its other tokens are sealed. -/
def NewTree (d : DSt (spec lam K L)) (lo depth : ℕ) (tr : TTree) : Prop :=
  TTOK d lo depth tr ∧
  Untouched d tr.root ∧
  lo ≤ tr.root ∧
  ∀ i < 2 ^ depth,
    ∀ u ∈ tr.salts.getD i 0 :: (pathOf tr.levels i ++ ancOf tr.levels i), u = tr.root ∨ Sealed d u

theorem NewTree.mono {d : DSt (spec lam K L)} {lo lo' depth : ℕ} {tr : TTree}
    (h : NewTree d lo depth tr) (hl : lo' ≤ lo) : NewTree d lo' depth tr :=
  ⟨⟨h.1.open_, fun j hj u hu => le_trans hl (h.1.new j hj u hu)⟩, h.2.1, le_trans hl h.2.2.1,
    h.2.2.2⟩

/-- What is known of a new tree survives a run that charges no old token, whose queries hold no old
token, and that shows no old token. -/
theorem NewTree.keeps {d d' : DSt (spec lam K L)} {lo depth : ℕ} {tr : TTree} {e M : OracleName → ℕ}
    (h : NewTree d lo depth tr) (hr : Run NoTok NoTok NoTok e M d d') : NewTree d' lo depth tr :=
  ⟨h.1.keeps hr.charges fun _ hu => hu.elim, h.2.1.grows hr.grows (fun hu => hu) (fun hu => hu),
    h.2.2.1, fun i hi u hu => (h.2.2.2 i hi u hu).imp_right fun hs => hs.mono hr.keeps⟩

/-- Under the hypotheses below: a new tree after all attempts of a search that hold its root and are
charged to an older token is in order, and all its tokens are sealed. -/
theorem NewTree.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo depth : ℕ} {tr : TTree}
    (h : NewTree d lo depth tr) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o) {t : Tok}
    (ht : t < lo) {us tls : List Tok} (hrm : tr.root ∈ us)
    (hT : Tries (split lam K L) t us d os tls d') : TTS d' n₀ depth tr := by
  obtain ⟨htr, _, _, hse⟩ := h
  have hrun : Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) NoTok zr
      (fun o => os.count o) d d' := hT.run
  refine ⟨⟨fun i hi => (htr.open_ i hi).keeps hrun.charges fun u hu hcu => ?_,
      fun i hi u hu => le_trans hn (htr.new i hi u hu)⟩,
    fun i hi u hu => ?_⟩
  · exact absurd (htr.new i hi u hu) (Nat.not_le.mpr (hcu ▸ ht))
  · rcases hse i hi u hu with h1 | h1
    · exact hT.sealed ho (Or.inr (h1 ▸ hrm))
    · exact h1.mono hrun.keeps

/-- The trees over a component, just made: one for each depth of ds, in this order, each as
safe_commitT leaves it, with tokens from lo on. -/
def NewTs (d : DSt (spec lam K L)) (lo : ℕ) (ds : List ℕ) (trs : List TTree) : Prop :=
  List.Forall₂ (NewTree d lo) ds trs

theorem NewTs.nil (d : DSt (spec lam K L)) (lo : ℕ) : NewTs d lo [] [] :=
  List.Forall₂.nil

theorem NewTs.cons {d : DSt (spec lam K L)} {lo depth : ℕ} {tr : TTree} {ds : List ℕ}
    {trs : List TTree} (h : NewTree d lo depth tr) (ht : NewTs d lo ds trs) :
    NewTs d lo (depth :: ds) (tr :: trs) :=
  List.Forall₂.cons h ht

/-- there are as many trees as depths -/
theorem NewTs.length_eq {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) : trs.length = ds.length :=
  (List.Forall₂.length_eq h).symm

/-- every root in the list is the root of a tree with `NewTree` at some depth of ds -/
theorem NewTs.of_mem_roots {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) :
    ∃ depth ∈ ds, ∃ tr, NewTree d lo depth tr ∧ u = tr.root := by
  induction h with
  | nil => exact absurd hu List.not_mem_nil
  | cons hx _ ih =>
    rw [List.map_cons] at hu
    rcases List.mem_cons.mp hu with hu | hu
    · exact ⟨_, List.mem_cons_self, _, hx, hu⟩
    · obtain ⟨depth, hm, tr, h1, h2⟩ := ih hu
      exact ⟨depth, List.mem_cons_of_mem _ hm, tr, h1, h2⟩

theorem NewTs.unt {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : Untouched d u := by
  obtain ⟨_, _, tr, h1, rfl⟩ := h.of_mem_roots hu
  exact h1.2.1

theorem NewTs.lt {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : u < d.vals.length :=
  (h.unt hu).lt

theorem NewTs.le {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : lo ≤ u := by
  obtain ⟨_, _, tr, h1, rfl⟩ := h.of_mem_roots hu
  exact h1.2.2.1

theorem NewTs.mono {d : DSt (spec lam K L)} {lo lo' : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) (hl : lo' ≤ lo) : NewTs d lo' ds trs :=
  List.Forall₂.imp (fun _ _ hx => hx.mono hl) h

/-- the same as `NewTree.keeps`, of all trees of the list -/
theorem NewTs.keeps {d d' : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    {e M : OracleName → ℕ} (h : NewTs d lo ds trs) (hr : Run NoTok NoTok NoTok e M d d') :
    NewTs d' lo ds trs :=
  List.Forall₂.imp (fun _ _ hx => hx.keeps hr) h

/-- the same as `NewTree.tts_tries`, of all trees of the list: the attempts hold all their roots -/
theorem NewTs.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs d lo ds trs) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o) {t : Tok}
    (ht : t < lo) {us tls : List Tok} (hrm : ∀ u ∈ trs.map TTree.root, u ∈ us)
    (hT : Tries (split lam K L) t us d os tls d') : List.Forall₂ (TTS d' n₀) ds trs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih =>
    exact List.Forall₂.cons (hx.tts_tries hn ho ht (hrm _ List.mem_cons_self) hT)
      (ih fun u hu => hrm u (List.mem_cons_of_mem _ hu))

/-- The tree over a component, if it has one, and then k: from a state with `TidyO` it is enough
that k is safe after any tree that is as safe_commitT leaves it, and after no tree. -/
theorem safe_withTree {β : Type} (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    (k : Option TTree → St lam K L β) (d : DSt (spec lam K L))
    (hd : TidyO (rulesB K L lam p) d) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ x d₁, TidyO (rulesB K L lam p) d₁ →
      Run NoTok NoTok NoTok zr
        (fun o =>
          cnt1 (S := spec lam K L) OracleName.leaf (2 ^ depth) o +
            cnt1 (S := spec lam K L) OracleName.node (2 ^ depth) o)
        d d₁ →
      NewT d₁ d.vals.length depth x → SafeO (rulesB K L lam p) (k x) d₁ Q) :
    SafeO (rulesB K L lam p) (withTree p.sMT has depth leaf k) d Q := by
  cases has with
  | true =>
    refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_commitT depth leaf d hd))
    rintro tr d₁ ⟨hd₁, hr₁, h⟩
    exact hk (some tr) d₁ hd₁ hr₁ fun tr' e => by cases e; exact h
  | false => exact hk none d hd (Run.refl d) fun _ e => by cases e

/-- The trees over a component, one after the other, and then k: from a state with `TidyO` it is
enough that k is safe after any trees that are as safe_commitT leaves them (`NewTs`). -/
theorem safe_withTrees {β : Type} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) (k : List TTree → St lam K L β)
      (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d →
      ∀ (Q : β → DSt (spec lam K L) → Prop),
      (∀ trs d₁, TidyO (rulesB K L lam p) d₁ →
        Run NoTok NoTok NoTok zr (MTrees lam K L ds) d d₁ →
        NewTs d₁ d.vals.length ds trs → SafeO (rulesB K L lam p) (k trs) d₁ Q) →
      SafeO (rulesB K L lam p) (withTrees p.sMT ds leaf k) d Q
  | [], _, _, d, hd, _, hk => hk [] d hd (Run.refl d) (NewTs.nil d _)
  | depth :: ds, leaf, k, d, hd, Q, hk => by
      rw [withTrees]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_commitT depth (leaf 0) d hd))
      rintro tr d₁ ⟨hd₁, hr₁, h⟩
      refine safe_withTrees ds (fun n => leaf (n + 1)) (fun trs => k (tr :: trs)) d₁ hd₁ Q
        fun trs d₂ hd₂ hr₂ hts => ?_
      have h₂ : NewTree d₂ d.vals.length depth tr := NewTree.keeps h hr₂
      exact hk (tr :: trs) d₂ hd₂
        (hr₁.trans hr₂ (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu)
          (fun _ => le_rfl) fun o => le_of_eq (MTrees_cons depth ds o).symm)
        (NewTs.cons h₂ (hts.mono hr₁.length_le))

/-- The set of tokens of a slot after a search whose attempts are charged to one of them and hold
the root of the new tree, if there is one, and perhaps shared tails. (not all hypotheses are named
here: see the statement below) dd: the tails of the failed attempts, the newest first; tl: the tail
of the final attempt. -/
theorem SlotF.after_tries {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {Op : Tok → Prop} {a0 : Acc0} {j : ℕ} {acc acc' : SlotAcc lam K Y}
    (hd : TidyO (rulesB K L lam p) d) (h : SlotF d n₀ done Op a0 j acc) {os : List OracleName}
    (ho : ∀ o ∈ os, o ≠ OracleName.rleaf) {t : Tok} {us : List Tok} {tr : Option TTree} {lo depth x : ℕ}
    (hn : n₀ ≤ lo) (hlo : lo ≤ d.vals.length) (ht : t < lo) (hts : ¬ Sealed d t)
    (hop : ∀ u, Op u → u = t ∨ u ∈ us) (hus : ∀ u ∈ us, u ∈ rtL tr ∨ u ∈ a0.toks)
    (hrm : ∀ u ∈ rtL tr, u ∈ us) (htr : NewT d lo depth tr) {dd : List Tok} {tl : Tok}
    (hT : Tries (split lam K L) t us d os (dd.reverse ++ [tl]) d')
    (htoks : acc'.toks = acc.toks ++ [tl]) (htrees : acc'.trees = acc.trees ++ [tr])
    (hdead : acc'.dead = dd ++ acc.dead) :
    SlotF d' n₀ (done ++ [(depth, x)]) (fun u => u = tl) a0 j acc' := by
  have hrun : Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) NoTok zr
      (fun o => os.count o) d d' := hT.run
  have hiff : ∀ u,
      InU a0 j acc' u ↔ (InU a0 j acc u ∨ u = tl ∨ u ∈ dd.reverse ∨ u ∈ us) := fun u => by
    unfold InU
    rw [htoks, htrees, hdead]
    constructor
    · rintro (h1 | h1 | ⟨tr', h1, h2⟩ | h1 | h1 | h1 | h1)
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Or.inl (List.mem_singleton.mp h1))
      · exact Or.inl (Or.inr (Or.inl h1))
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨tr', h1, h2⟩)))
        · exact Or.inr
            (Or.inr (Or.inr (hrm u (mem_rtL.2 ⟨tr', (List.mem_singleton.mp h1).symm, h2⟩))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inr (Or.inr (Or.inl (List.mem_reverse.mpr h1)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
    · rintro ((h1 | h1 | ⟨tr', h1, h2⟩ | h1 | h1 | h1 | h1) | h1 | h1 | h1)
      · exact Or.inl (List.mem_append_left _ h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl ⟨tr', List.mem_append_left _ h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append_right _ h1))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))
      · exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr h1))
      · exact Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append_left _ (List.mem_reverse.mp h1)))))))
      · rcases hus u h1 with h2 | h2
        · obtain ⟨tr', e, h3⟩ := mem_rtL.1 h2
          exact Or.inr
            (Or.inr (Or.inl ⟨tr', List.mem_append_right _ (List.mem_singleton.mpr e.symm), h3⟩))
        · exact Or.inr (Or.inl h2)
  have hoW : ∀ o ∈ os, ¬ Wk o := fun o hm => ho o hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (h.cl.extend_tries hd (t := t) (us := us) hoW (fun u hu => ?_) hT).congr hiff
      fun u _ hu => ?_
    · rcases hus u hu with h2 | h2
      · exact ⟨htr.lt h2, Or.inr ((htr.unt h2).deps [])⟩
      · exact ⟨h.cl.lt u (Or.inr (Or.inl h2)), Or.inl (Or.inr (Or.inl h2))⟩
    · rcases hu with hu | hu | ⟨h1 | h1, h2, h3⟩
      · exact Or.inl hu
      · exact Or.inr hu
      · exact absurd (hop u h1) (fun hh => hh.elim h2 h3)
      · exact Or.inr (h1.mono hrun.keeps)
  · intro u hu
    rcases (hiff u).1 hu with h1 | h1 | h1 | h1
    · exact h.new u h1
    · exact le_trans hn
        (le_trans hlo (hT.tail_ge u (h1 ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl))))
    · exact le_trans hn (le_trans hlo (hT.tail_ge u (List.mem_append_left _ h1)))
    · rcases hus u h1 with h2 | h2
      · exact le_trans hn (htr.le h2)
      · exact h.new u (Or.inr (Or.inl h2))
  · rw [htrees]
    exact forall₂_append (List.Forall₂.cons (htr.tts_tries hn hoW ht hrm hT) List.Forall₂.nil)
      (h.trees.keeps hrun fun u hu => hu ▸ hts)
  · rw [htoks]
    simp

/-- the same as `SlotF.after_tries` after one marked query: the search with one attempt -/
theorem SlotF.after_mark {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {Op : Tok → Prop}
    {a0 : Acc0} {j : ℕ} {acc acc' : SlotAcc lam K Y} (hd : TidyO (rulesB K L lam p) d)
    (h : SlotF d n₀ done Op a0 j acc) {o : OracleName} (ho : o ≠ OracleName.rleaf) {t : Tok} {us : List Tok}
    {tr : Option TTree} {lo depth x : ℕ} (hn : n₀ ≤ lo) (hlo : lo ≤ d.vals.length) (ht : t < lo)
    (hts : ¬ Sealed d t) (hop : ∀ u, Op u → u = t ∨ u ∈ us)
    (hus : ∀ u ∈ us, u ∈ rtL tr ∨ u ∈ a0.toks) (hrm : ∀ u ∈ rtL tr, u ∈ us)
    (htr : NewT d lo depth tr) (htoks : acc'.toks = acc.toks ++ [d.vals.length])
    (htrees : acc'.trees = acc.trees ++ [tr]) (hdead : acc'.dead = acc.dead)
    (P : (spec lam K L).Dom o) (r : (spec lam K L).Rng o) (T : Table (spec lam K L)) :
    SlotF (afterMark (split lam K L) d o t us P r T) n₀ (done ++ [(depth, x)])
      (fun u => u = d.vals.length) a0 j acc' :=
  h.after_tries (dd := []) hd (os := [o]) (fun _ ho' => (List.mem_singleton.mp ho') ▸ ho)
    hn hlo ht hts hop hus hrm htr (Tries.one d o P r T) htoks htrees hdead

/-! ## Part B. The rounds -/

/-- the other tokens of the Fiat-Shamir query of a slot in a local round; root: the root of the tree
over its component, if it has one -/
def usOf : PhT → Option Tok → List Tok
  | .shr tk0, root => tk0 :: root.toList
  | _, root => root.toList

/-- the other tokens of the Fiat-Shamir query of a slot in a local round; roots: the roots of the
trees over its component, in the order of the trees -/
def usOfRoots : PhT → List Tok → List Tok
  | .shr tk0, roots => tk0 :: roots
  | _, roots => roots

/-- At the list of one root, or of none, `usOfRoots` gives the tokens that `usOf` gives at that
root, or at none. -/
theorem usOfRoots_toList (ph : PhT) (root : Option Tok) :
    usOfRoots ph root.toList = usOf ph root := by
  cases ph <;> rfl

/-- the accumulator of a slot after a local round; nc: the number of the final attempt, if the round
has proof-of-work bits; dd: the tails of the failed attempts -/
def accLo (acc : SlotAcc lam K Y) (tl : Tok) (bl : List (Blk lam K)) (tr : Option TTree)
    (nc : Option ℕ) (dd : List Tok) : SlotAcc lam K Y :=
  { acc with
    tk := tl, blocks := bl, trees := acc.trees ++ [tr], toks := acc.toks ++ [tl],
    nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }

theorem osTry_ne_rleaf (t : Tag) (n : ℕ) : ∀ o ∈ osTry t n, o ≠ OracleName.rleaf := fun o ho e => by
  rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩ <;> cases e

theorem osTry_tl (lam K : ℕ) (L : BatchProtocol I X) (t : Tag) (n : ℕ) :
    ∀ o ∈ osTry t n, (split lam K L).tl o = lam := fun o ho => by
  rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩ <;> rfl

section Lo
variable {d d₁ : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0} {j : ℕ}
  {acc : SlotAcc lam K Y} {tr : Option TTree}

/-- what the attempts of a slot in a local round need of the state in which the search starts -/
theorem lo_pre (t : Tag) (h : SlotI p d₁ n₀ done ph a0 j acc) (hlt : live ph acc < d.vals.length)
    {depth : ℕ} (htr : NewT d₁ d.vals.length depth tr) :
    LoopPre p d₁ t (live ph acc) (usOf ph (tr.map TTree.root)) := by
  have hne : live ph acc ∉ rtL tr := fun hu => absurd (htr.le hu) (Nat.not_le.mpr hlt)
  cases ph with
  | shr tk0 =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h.cap
    refine ⟨fun u hu => ?_, fun hu => ?_, FreeAt.of_heldAt c1 c2 c3 (by simp),
      fun _ => FreeAt.of_heldAt c1 c2 c3 (by simp), ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact h.fin.cl.lt _ (Or.inr (Or.inl c6))
      · exact htr.lt hu
    · rcases List.mem_cons.mp hu with hu | hu
      · exact c7 hu
      · exact hne hu
    · rw [show live (PhT.shr tk0) acc = acc.c from rfl, c4.2]
      exact min_le_right _ _
  | first =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.first acc = acc.tk from rfl, c2.2]
    exact min_le_left _ _
  | loc =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.loc acc = acc.tk from rfl, c2.2]
    exact min_le_right _ _
  | aft =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.aft acc = acc.tk from rfl, c2.2]
    exact min_le_right _ _

/-- what the attempts of a slot in a local round need of the state in which the search starts, where
the component has a list of trees -/
theorem lo_preTrees (t : Tag) (h : SlotI p d₁ n₀ done ph a0 j acc)
    (hlt : live ph acc < d.vals.length) {ds : List ℕ} {trs : List TTree}
    (htr : NewTs d₁ d.vals.length ds trs) :
    LoopPre p d₁ t (live ph acc) (usOfRoots ph (trs.map TTree.root)) := by
  have hne : live ph acc ∉ trs.map TTree.root :=
    fun hu => absurd (htr.le hu) (Nat.not_le.mpr hlt)
  cases ph with
  | shr tk0 =>
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h.cap
    refine ⟨fun u hu => ?_, fun hu => ?_, FreeAt.of_heldAt c1 c2 c3 (by simp),
      fun _ => FreeAt.of_heldAt c1 c2 c3 (by simp), ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact h.fin.cl.lt _ (Or.inr (Or.inl c6))
      · exact htr.lt hu
    · rcases List.mem_cons.mp hu with hu | hu
      · exact c7 hu
      · exact hne hu
    · rw [show live (PhT.shr tk0) acc = acc.c from rfl, c4.2]
      exact min_le_right _ _
  | first =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.first acc = acc.tk from rfl, c2.2]
    exact min_le_left _ _
  | loc =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.loc acc = acc.tk from rfl, c2.2]
    exact min_le_right _ _
  | aft =>
    obtain ⟨c1, c2, _⟩ := h.cap
    refine ⟨fun u hu => htr.lt hu, hne, c1.freeAt _, fun _ => c1.freeAt _, ?_⟩
    rw [show live PhT.aft acc = acc.tk from rfl, c2.2]
    exact min_le_right _ _

/-- under `LoopPre`, `TidyO`: the state after the attempts of a search is orderly -/
theorem LoopPre.tidy {d d' : DSt (spec lam K L)} {t : Tag} {tk : Tok} {vs tls : List Tok} {n : ℕ}
    (h : LoopPre p d t tk vs) (hd : TidyO (rulesB K L lam p) d)
    (hT : Tries (split lam K L) tk vs d (osTry t n) tls d') : TidyO (rulesB K L lam p) d' :=
  hT.tidy hd h.lt h.not_mem h.free_all (osTry_nodup t n) (n := (d.val tk).length) ⟨h.free.lt, rfl⟩
    (fun o ho => by rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩ <;> exact h.bits)
    (fun o ho _ => by
      rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩
      · exact fb_mk t
      · exact fbw_mk t k)

/-- the slot after the attempts of a local round -/
theorem lo_post (t : Tag) (hd₁ : TidyO (rulesB K L lam p) d₁)
    (h : SlotI p d₁ n₀ done ph a0 j acc) (hn : n₀ ≤ d.vals.length)
    (hle : d.vals.length ≤ d₁.vals.length) (hlt : live ph acc < d.vals.length) {depth x : ℕ}
    (htr : NewT d₁ d.vals.length depth tr) (bl : List (Blk lam K)) (nc : Option ℕ) {n : ℕ}
    {dd : List Tok} {tl : Tok} {d' : DSt (spec lam K L)}
    (hT : Tries (split lam K L) (live ph acc) (usOf ph (tr.map TTree.root)) d₁ (osTry t n)
      (dd.reverse ++ [tl]) d') :
    SlotI p d' n₀ (done ++ [(depth, x)]) ph.afterLo a0 j (accLo acc tl bl tr nc dd) := by
  have hpre := lo_pre (p := p) t h hlt htr
  have hd' := hpre.tidy hd₁ hT
  have hF := h.fin.after_tries
    (acc' := accLo acc tl bl tr nc dd) (x := x) hd₁ (osTry_ne_rleaf t n) (t := live ph acc)
    (us := usOf ph (tr.map TTree.root)) hn hle hlt
    h.cap.not_sealed
    (fun u hu => by
      cases ph with
      | shr tk0 =>
        exact (show u = acc.c ∨ u = tk0 from hu).imp_right fun h1 => by
          rw [h1]; exact List.mem_cons_self
      | first => exact Or.inl hu
      | loc => exact Or.inl hu
      | aft => exact Or.inl hu)
    (fun u hu => by
      cases ph with
      | shr tk0 =>
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inr h.cap.2.2.2.2.2.1
        · exact Or.inl hu
      | first => exact Or.inl hu
      | loc => exact Or.inl hu
      | aft => exact Or.inl hu)
    (fun u hu => by
      cases ph with
      | shr tk0 => exact List.mem_cons_of_mem _ hu
      | first => exact hu
      | loc => exact hu
      | aft => exact hu) htr hT rfl rfl rfl
  have hcap : Untouched d' tl ∧ Len d' tl lam ∧ tl ∈ acc.toks ++ [tl] :=
    ⟨hT.untouched_last hd₁ (lt_of_lt_of_le hlt hle) hpre.lt,
      hT.len_last (osTry_tl lam K L t n),
      List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  have hal : ¬ Dead d' tl := hT.not_dead_last hd'
  cases ph with
  | shr tk0 => exact ⟨hF, hcap, hal⟩
  | first => exact ⟨hF, hcap, hal⟩
  | loc => exact ⟨hF, hcap, hal⟩
  | aft => exact ⟨hF, hcap, hal⟩

end Lo

/-- the Fiat-Shamir query of a slot in a local round, with proof-of-work bits or without: fbG,
charged to the live token, with the other tokens usOf -/
theorem safe_fbSlotG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (acc : SlotAcc lam K Y) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) {d : DSt (spec lam K L)}
    (h : LoopPre p d t (live ph acc) (usOf ph root)) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ nc dd bl tl d', Kept gr nc dd →
      Tries (split lam K L) (live ph acc) (usOf ph root) d (osTry t (nc.getD 0))
        (dd.reverse ++ [tl]) d' →
      SafeO (rulesB K L lam p) (k nc dd bl tl) d' Q) :
    SafeO (rulesB K L lam p) (fbSlotG gr chal t i cms x ph acc.tk acc.c root emb α k) d Q := by
  cases ph with
  | shr tk0 => exact safe_fbG (us := [tk0]) h gr k Q hk
  | first => exact safe_fbG (us := []) h gr k Q hk
  | loc => exact safe_fbG (us := []) h gr k Q hk
  | aft => exact safe_fbG (us := []) h gr k Q hk

/-- A local round, in one slot. -/
theorem safe_slotLo {r : Round} {s : Shape} (t : Tag) (cms : List (Dig lam))
    (xin : Y → Option X) (a : RAnn r) (w : WireRB lam K r a)
    (emb : (q : r.Pos) → r.Sym q → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) (d : DSt (spec lam K L)) (n₀ : ℕ)
    (done : List (ℕ × ℕ)) (a0 : Acc0) (j : ℕ) (hd : TidyO (rulesB K L lam p) d)
    (hn : n₀ ≤ d.vals.length) (h : SlotI p d n₀ done ph a0 j z.2) :
    SafeO (rulesB K L lam p) (slotLo p.sMT t cms xin a w emb plJ i ph z) d fun z' d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun u => u = live ph z.2) (OpenOf ph z.2) NoTok zr
        (MLo lam K L t w.depthJ (moreOf w.grJ)) d d' ∧
      SlotI p d' n₀ (done ++ [(w.depthJ, w.depth0)]) ph.afterLo a0 j z'.2 ∧
      d.vals.length ≤ z'.2.tk := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  show SafeO _
    (withTree p.sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      fbSlotG w.grJ w.chal t i cms (acc.x.bind xin) ph acc.tk acc.c (tr.map TTree.root) plJ
        (a.plain m.2).2 fun nc dd bl tl =>
          Step.pure (k (w.chal bl),
              { acc with
                tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr],
                toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }))
    d _
  refine safe_withTree w.hasJ w.depthJ _ _ d hd _ fun tr d₁ hd₁ hr₁ htr => ?_
  have hI₁ : SlotI p d₁ n₀ done ph a0 j acc := h.frame hd hr₁ (fun _ hu => hu.elim) (fun hu => hu)
  have hlt : live ph acc < d.vals.length := h.cap.lt
  have hpre := lo_pre (p := p) t hI₁ hlt htr
  refine safe_fbSlotG w.grJ w.chal t i cms _ ph acc _ plJ _ _ hpre _ fun nc dd bl tl d' hK hT => ?_
  have hnc : nc.getD 0 ≤ moreOf w.grJ := by
    cases hg : w.grJ with
    | none =>
      have h0 : nc = none := by
        have := hK.1
        rw [hg] at this
        cases nc with
        | none => rfl
        | some _ => cases this
      rw [h0]
      exact Nat.zero_le _
    | some g => exact hK.2.2 g hg
  refine ⟨hpre.tidy hd₁ hT,
    ?_,
    lo_post t hd₁ hI₁ hn hr₁.length_le hlt htr (acc.blocks ++ [bl]) nc hT,
    le_trans hr₁.length_le (hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl)))⟩
  refine (hr₁.mono (Cc := fun u => u = live ph acc) (Ch := OpenOf ph acc) (R := NoTok) (e := zr)
      (M := fun o => cnt1 OracleName.leaf (2 ^ w.depthJ) o + cnt1 OracleName.node (2 ^ w.depthJ) o)
      (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ => le_rfl)
      (fun _ => le_rfl)).trans
    (hT.run (R := NoTok) (e := zr)) (fun _ hu => Or.inl hu) (fun u hu => ?_) (fun _ hu => hu.elim)
    (fun _ => le_rfl) (fun o => Nat.add_le_add_left (count_osTry_le t hnc o) _)
  rcases hu with rfl | hu
  · refine Or.inl ?_
    cases ph with
    | shr tk0 => exact Or.inl rfl
    | first => rfl
    | loc => rfl
    | aft => rfl
  · cases ph with
    | shr tk0 =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (htr.le hu)
    | first => exact Or.inr (htr.le hu)
    | loc => exact Or.inr (htr.le hu)
    | aft => exact Or.inr (htr.le hu)

/-! ### All slots, in a local round -/

theorem AllFrom.mono_mem {σ : Type} {P Q : ℕ → σ → Prop} :
    ∀ (j : ℕ) (l : List σ), (∀ j a, a ∈ l → P j a → Q j a) → AllFrom P j l → AllFrom Q j l
  | _, [], _, _ => trivial
  | j, a :: t, h, hl =>
    ⟨h j a List.mem_cons_self hl.1,
      AllFrom.mono_mem (j + 1) t (fun j' b hb => h j' b (List.mem_cons_of_mem _ hb)) hl.2⟩

theorem AllFrom.of_mem {σ : Type} {P : ℕ → σ → Prop} :
    ∀ (j : ℕ) (l : List σ), AllFrom P j l → ∀ a ∈ l, ∃ j', P j' a
  | j, b :: t, hl, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨j, hl.1⟩
      · exact AllFrom.of_mem (j + 1) t hl.2 a ha

theorem live_afterLo (ph : PhT) (acc : SlotAcc lam K Y) : live ph.afterLo acc = acc.tk := by
  cases ph <;> rfl

theorem openOf_afterLo (ph : PhT) (acc : SlotAcc lam K Y) (u : Tok) :
    OpenOf ph.afterLo acc u ↔ u = acc.tk := by
  cases ph <;> exact Iff.rfl

/-- Under `SlotI`: the open ends of a slot exist. -/
theorem SlotI.open_lt {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI p d n₀ done ph a0 j acc)
    {u : Tok} (hu : OpenOf ph acc u) : u < d.vals.length := by
  cases ph with
  | shr tk0 =>
    rcases hu with rfl | rfl
    · exact h.cap.1
    · exact h.fin.cl.lt _ (Or.inr (Or.inl h.cap.2.2.2.2.2.1))
  | first => exact (show u = acc.tk from hu) ▸ h.cap.1.lt
  | loc => exact (show u = acc.tk from hu) ▸ h.cap.1.lt
  | aft => exact (show u = acc.tk from hu) ▸ h.cap.1.lt

/-- Under `SlotI` of the first slot: the live token of one slot is no open end of another, if their
live tokens differ. -/
theorem SlotI.live_not_open {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {ph : PhT} {a0 : Acc0} {j : ℕ} {acc acc' : SlotAcc lam K Y}
    (h : SlotI p d n₀ done ph a0 j acc) (hne : live ph acc ≠ live ph acc') :
    ¬ OpenOf ph acc' (live ph acc) := by
  cases ph with
  | shr tk0 => exact fun hu => hu.elim hne h.cap.2.2.2.2.2.2
  | first => exact hne
  | loc => exact hne
  | aft => exact hne

theorem safe_eachLo {r : Round} {s : Shape} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
    (a : RAnn r) (w : WireRB lam K r a)
    (emb : (q : r.Pos) → r.Sym q → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (a0 : Acc0) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (j : ℕ) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → n₀ ≤ d.vals.length →
    AllFrom (fun j z => SlotI p d n₀ done ph a0 j z.2) j zs → (zs.map fun z => live ph z.2).Nodup →
    SafeO (rulesB K L lam p) (eachM (slotLo p.sMT t cms xin a w emb plJ i ph) zs) d fun zs' d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun u => ∃ z ∈ zs, u = live ph z.2) (fun u => ∃ z ∈ zs, OpenOf ph z.2 u) NoTok zr
        (fun o => zs.length * MLo lam K L t w.depthJ (moreOf w.grJ) o) d d' ∧
      AllFrom (fun j z => SlotI p d' n₀ (done ++ [(w.depthJ, w.depth0)]) ph.afterLo a0 j z.2)
        j zs' ∧
      (zs'.map fun z => z.2.tk).Nodup ∧
      (∀ z ∈ zs', d.vals.length ≤ z.2.tk) ∧ zs'.length = zs.length
  | [], _, d, hd, _, _, _ =>
    ⟨hd, Run.refl d, trivial, List.nodup_nil, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | z :: zs, j, d, hd, hn, hall, hnd => by
      show SafeO _ ((slotLo p.sMT t cms xin a w emb plJ i ph z).bind fun b =>
        (eachM (slotLo p.sMT t cms xin a w emb plJ i ph) zs).bind fun r => Step.pure (b :: r)) d _
      have hnd' := List.nodup_cons.mp hnd
      have hne : ∀ x ∈ zs, live ph z.2 ≠ live ph x.2 := fun x hx he =>
        hnd'.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      refine SafeO.bind _ _ d
        (SafeO.mono ?_ _ d (safe_slotLo t cms xin a w emb plJ i ph z d n₀ done a0 j hd hn hall.1))
      rintro z' d₁ ⟨hd₁, hr₁, hI', hnew⟩
      have hall₁ : AllFrom (fun j z => SlotI p d₁ n₀ done ph a0 j z.2) (j + 1) zs :=
        AllFrom.mono_mem (j + 1) zs
          (fun j' x hx hIx =>
            hIx.frame hd hr₁ (fun u hu => hu ▸ ⟨hall.1.fit, hall.1.live_not_open (hne x hx)⟩)
              (hIx.live_not_open (hne x hx).symm)) hall.2
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁
          (safe_eachLo t cms xin a w emb plJ i ph n₀ done a0 zs (j + 1) d₁ hd₁
            (le_trans hn hr₁.length_le) hall₁ hnd'.2))
      rintro r' d₂ ⟨hd₂, hr₂, hall₂, hnd₂, hnew₂, hlen₂⟩
      have hz'lt : z'.2.tk < d₁.vals.length := live_afterLo ph z'.2 ▸ hI'.cap.lt
      refine ⟨hd₂, ?_, ⟨?_, hall₂⟩, ?_, ?_, by simp [hlen₂]⟩
      · refine (hr₁.mono (Cc := fun u => ∃ x ∈ z :: zs, u = live ph x.2)
            (Ch := fun u => ∃ x ∈ z :: zs, OpenOf ph x.2 u) (R := NoTok) (e := zr)
            (M := MLo lam K L t w.depthJ (moreOf w.grJ))
            (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩)
            (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩) (fun _ hu => hu.elim)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₂ (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩)
          (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩) (fun _ hu => hu.elim)
          (fun _ => le_rfl) (fun o => ?_)
        rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
      · refine hI'.frame hd₁ hr₂ (fun u ⟨x, hx, hu⟩ => ?_) (fun ⟨x, hx, hu⟩ => ?_)
        · obtain ⟨j', hIx⟩ := AllFrom.of_mem (j + 1) zs hall₁ x hx
          obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
          refine hu ▸ ⟨hIx.fit, fun ho => ?_⟩
          exact absurd hnew (Nat.not_le.mpr (((openOf_afterLo ph z'.2 _).1 ho) ▸ hIx0.cap.lt))
        · obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
          rw [live_afterLo] at hu
          exact absurd hnew (Nat.not_le.mpr (hIx0.open_lt hu))
      · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd₂⟩
        obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
        exact absurd (hnew₂ x hx) (Nat.not_le.mpr (he ▸ hz'lt))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnew
        · exact le_trans hr₁.length_le (hnew₂ x hx)

/-! ## Part C. What holds between two rounds -/

/-- Between two rounds. done: the depths of the trees of the rounds made; ph: the phase; a0: what
the shared part has gathered; zs: the slots. -/
structure ChainInv {s : Shape} (p : Params) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (ph : PhT) (a0 : Acc0) (zs : List (SlotSt lam K Y s)) : Prop where
  slots : AllFrom (fun j z => SlotI p d n₀ done ph a0 j z.2) 0 zs
  trees0 : Trees0 d n₀ done a0.trees
  nodup : (zs.map fun z => live ph z.2).Nodup
  le : n₀ ≤ d.vals.length
  /-- in the shared rounds: the last shared tail can be charged -/
  shr : ∀ tk0, ph = PhT.shr tk0 → Untouched d tk0 ∧ Len d tk0 lam ∧ ¬ Dead d tk0
  /-- before the chains join there is no request tree -/
  req : ph = PhT.first ∨ ph = PhT.loc → a0.req = none

end Compile.Batch.Disc
