-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineFinish.lean: the proof strings of the slots are made within the rules of
deferred programming, from a state with `TidyO`, `SlotF` in each slot, `Trees0` of the shared trees
and `TreeOKB` of the external trees (words of this library: lean/GLOSSARY.md).

For `Spec.safeProveB`: `finishSlot` and `finishAll` of Compile/Batch/Prover.lean. One reveal shows
the tokens of a slot, the tails of the failed proof-of-work attempts among them. The revealed list
holds exactly the tokens of the slot (`InU`, Compile/Batch/DisciplineSlot.lean; `mem_reveal_iff`,
under its hypotheses), and this set is closed (`SlotF.cl`), so the reveal is allowed. Then positions
are opened in the token trees of the slot and of the shared part
(Compile/Batch/DisciplineOpens.lean) and in the trees over the external strings. No query is made,
so what is known of the other slots, of the shared trees and of the external trees survives.

Notation:
  `n₀`: a natural number; `SlotF.new`: n₀ ≤ u for every token u of the slot
    (Compile/Batch/DisciplineSlot.lean);
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `acc`: a `SlotAcc` (Compile/Batch/Prover.lean): what a slot has accumulated;
  `Op`: a set of tokens; in `SlotF` (field `cl`, Compile/Batch/DisciplineSlot.lean), the open
    ends;
  `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
    Compile/Batch/Prover.lean);
  `c0`: an `H.Coin0`: the randomness of the shared part (`BatchHonestProver`, Iop/Batch.lean);
  `cj`: an `H.Coin`: the randomness of one slot (`BatchHonestProver`, Iop/Batch.lean);
  `Run Cc Ch R e M d d'` (Compile/Batch/DisciplineRun.lean): what a run does: Cc bounds the old
    tokens that it charges, Ch those that its queries hold; e and M count (R: see its doc comment);
  `pathOf lv j` (Compile/MerkleM.lean), `ancOf lv j` (Compile/Batch/TokTree.lean), `PA lv j`
    (Compile/Batch/DisciplineTree.lean): the siblings of leaf j, from the leaves upwards; the
    entries on the way from leaf j to the root, both included; the tokens beside the way from leaf j
    to the root, and those on it;
  `depthsOf s A W` (Compile/Batch/DisciplineSlot.lean): the depths of the two trees of each round.
-/
import Compile.Batch.DisciplineSlot

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type} {E : ExtSpec}

/-! ## The openings in the trees over the external strings, once more: with what they charge (first:
`safe_openE`, `safe_opensExtB`, Compile/Batch/DisciplineE.lean, with `GrowsO`; here with `Run`,
whose first argument bounds the old tokens that are charged: `NoTok` (no token)) -/

theorem run_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) {d : DSt (spec lam K L)}
    (hd : TidyO (rulesB K L lam p) d) (ht : TreeOKB d t) :
    SafeO (rulesB K L lam p) (openE (K := K) (L := L) t j a) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (TreeTok t) zr zr d d' := by
  unfold openE
  split
  · rename_i s s' heq
    have hm : some (s, s') ∈ t.salts := by
      rw [List.getD_eq_getElem?_getD] at heq
      cases h : t.salts[j]? with
      | none => rw [h] at heq; exact absurd heq (by simp)
      | some x =>
        rw [h] at heq
        have hx : x = some (s, s') := heq
        exact hx ▸ List.mem_of_getElem? h
    refine ⟨ht s s' hm,
      fun T =>
        ⟨hd.reveal (ht s s' hm) T,
          (Run.ofReveal (Cc := NoTok) (Ch := NoTok) (e := zr) (M := zr) d [s, s'] T).mono
            (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl ⟨s, s', hm, ?_⟩)
            (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)
  · exact ⟨hd, Run.refl d⟩

theorem run_opensExtB (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → (∀ tr ∈ trees, TreeOKB d tr) →
    SafeO (rulesB K L lam p) (opensExtB (K := K) (L := L) we y trees isRead ps) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok (fun u => ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | [], d, hd, _ => ⟨hd, Run.refl d⟩
  | q :: ps, d, hd, ht => by
      rw [opensExtB]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (run_opensExtB we y trees isRead ps d hd ht))
      rintro f d₁ ⟨hd₁, hg₁⟩
      split
      · refine SafeO.bind _ _ d₁
          (SafeO.mono ?_ _ d₁
            (run_openE (trees.getD (we.which q) ⟨[], []⟩) (we.leaf q) _ hd₁
              (treeOKB_of_mem_or (fun tr htr => (ht tr htr).grows hg₁.grows fun _ _ h => h)
                (Compile.Disc.Open.getD_mem_or trees _))))
        rintro op d₂ ⟨hd₂, hg₂⟩
        exact ⟨hd₂,
          hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun u hu =>
              Or.inl
                (Compile.Disc.Open.treeTok_of_mem_or (Compile.Disc.Open.getD_mem_or trees _) hu))
            (fun _ => le_rfl) (fun _ => le_rfl)⟩
      · exact ⟨hd₁, hg₁⟩

/-! ## The list that is revealed -/

theorem mem_rootToks : ∀ (l l' : List (Option TTree)), l.length = l'.length → ∀ u,
    u ∈ rootToks l l' ↔ (∃ tr, some tr ∈ l ∧ u = tr.root) ∨ ∃ tr, some tr ∈ l' ∧ u = tr.root
  | [], [], _, u => by
      constructor
      · exact fun h => absurd h List.not_mem_nil
      · rintro (⟨tr, h, -⟩ | ⟨tr, h, -⟩) <;> exact absurd h List.not_mem_nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, b :: l', h, u => by
      have ih := mem_rootToks l l' (Nat.succ.inj h) u
      have ha : ∀ o : Option TTree,
          u ∈ (o.map TTree.root).toList ↔ ∃ tr, some tr = o ∧ u = tr.root := fun o => by
        cases o with
        | none => simp
        | some tr => simp
      show u ∈ (a.map TTree.root).toList ++ (b.map TTree.root).toList ++ rootToks l l' ↔ _
      simp only [List.mem_append, ha, ih, List.mem_cons]
      constructor
      · rintro ((⟨tr, h1, h2⟩ | ⟨tr, h1, h2⟩) | ⟨tr, h1, h2⟩ | ⟨tr, h1, h2⟩)
        · exact Or.inl ⟨tr, Or.inl h1, h2⟩
        · exact Or.inr ⟨tr, Or.inl h1, h2⟩
        · exact Or.inl ⟨tr, Or.inr h1, h2⟩
        · exact Or.inr ⟨tr, Or.inr h1, h2⟩
      · rintro (⟨tr, h1 | h1, h2⟩ | ⟨tr, h1 | h1, h2⟩)
        · exact Or.inl (Or.inl ⟨tr, h1, h2⟩)
        · exact Or.inr (Or.inl ⟨tr, h1, h2⟩)
        · exact Or.inl (Or.inr ⟨tr, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨tr, h1, h2⟩)

/-- the list that finishSlot reveals, without the tails of the failed attempts -/
def revOld {Z : Type} (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z) : List Tok :=
  acc.toks.headD 0 ::
    (rootToks acc.trees a0.trees ++ (a0.req.map fun rq => pathOf rq.levels j).getD [] ++
      (a0.req.map TTree.root).toList ++
      (a0.req.map fun rq => ancOf rq.levels j).getD [] ++ acc.toks ++ a0.toks)

/-- the list that finishSlot reveals -/
def revList {Z : Type} (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z) : List Tok :=
  acc.toks.headD 0 ::
    (rootToks acc.trees a0.trees ++ (a0.req.map fun rq => pathOf rq.levels j).getD [] ++
      (a0.req.map TTree.root).toList ++ (a0.req.map fun rq => ancOf rq.levels j).getD [] ++
      acc.toks ++ a0.toks ++ (acc.dead ++ a0.dead))

theorem mem_revList {Z : Type} (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z) (u : Tok) :
    u ∈ revList a0 j acc ↔ u ∈ revOld a0 j acc ∨ u ∈ acc.dead ∨ u ∈ a0.dead := by
  unfold revList revOld
  rw [List.mem_cons, List.mem_cons, List.mem_append (t := acc.dead ++ a0.dead),
    List.mem_append (s := acc.dead), or_assoc]

/-- the tokens of the slot without the tails of the failed attempts -/
theorem mem_revOld_iff {Z : Type} (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z)
    (hl : acc.trees.length = a0.trees.length) (hne : acc.toks ≠ []) (u : Tok) :
    u ∈ revOld a0 j acc ↔
    (u ∈ acc.toks ∨ u ∈ a0.toks ∨
      (∃ tr, some tr ∈ acc.trees ∧ u = tr.root) ∨
      (∃ tr, some tr ∈ a0.trees ∧ u = tr.root) ∨
      ∃ rq, a0.req = some rq ∧ (u ∈ PA rq.levels j ∨ u = rq.root)) := by
  have hh : acc.toks.headD 0 ∈ acc.toks := by
    cases h : acc.toks with
    | nil => exact absurd h hne
    | cons a t => exact List.mem_cons_self
  unfold revOld
  simp only [List.mem_cons, List.mem_append, mem_rootToks _ _ hl]
  cases a0.req with
  | none =>
    simp only [Option.map_none, Option.getD_none, Option.toList_none, List.not_mem_nil, or_false,
      reduceCtorEq, false_and, exists_false]
    constructor
    · rintro (rfl | ((h | h) | h) | h)
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  | some rq =>
    simp only [Option.map_some, Option.getD_some, Option.toList_some, List.mem_singleton,
      Option.some.injEq, exists_eq_left', PA, List.mem_append]
    constructor
    · rintro (rfl | ((((((h | h) | h) | h) | h) | h) | h))
      · exact Or.inl hh
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h | h | (h | h) | h)
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))

/-- Under the hypotheses below: the list that finishSlot reveals holds exactly the tokens of the
slot. -/
theorem mem_reveal_iff {Z : Type} (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z)
    (hl : acc.trees.length = a0.trees.length) (hne : acc.toks ≠ []) (u : Tok) :
    u ∈ revList a0 j acc ↔ InU a0 j acc u := by
  rw [mem_revList, mem_revOld_iff a0 j acc hl hne u]
  unfold InU
  constructor
  · rintro ((h | h | h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rintro (h | h | h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr h

/-! ## One slot, all slots -/

variable (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (trees : List (TreeH lam)) (w : Wt)

/-- The proof string of one slot. -/
theorem safe_finishSlot (n₀ : ℕ) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    {Op : Tok → Prop} (hs : SlotF d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) Op a0 j acc)
    (h0 : Trees0 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) a0.trees)
    (htr : ∀ tr ∈ trees, TreeOKB d tr) :
    SafeO (rulesB K L lam p) (finishSlot Q H wq wp trees w c0 a0 j x cj acc) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d' := by
  have hl : acc.trees.length = a0.trees.length := hs.trees.length_eq.symm.trans h0.length_eq
  have hmem := mem_reveal_iff a0 j acc hl hs.ne
  unfold finishSlot
  dsimp only
  split
  · exact ⟨hd, Run.refl d⟩
  · have hc : ClosedO d (revList a0 j acc) :=
      ⟨fun t ht => hs.cl.lt t ((hmem t).mp ht),
        fun e he hce => Or.inl ((hmem _).mpr (hs.cl.closed e he ((hmem _).mp hce)).1),
        fun e he hce u hu => Or.inl ((hmem _).mpr ((hs.cl.closed e he ((hmem _).mp hce)).2 u hu))⟩
    refine ⟨hc, fun T => ?_⟩
    have hd₁ := hd.reveal hc T
    have hr₁ := Run.ofReveal (Cc := NoTok) (Ch := NoTok) (e := zr) (M := zr) d (revList a0 j acc) T
    refine SafeO.bind _ _ _
      (SafeO.mono ?_ _ _
        (safe_opensB n₀ Q.loc.shape Q.ann wq.sh _ acc.trees a0.trees _ _ hd₁
          ((hs.trees.keeps hr₁ fun _ h => h.elim).alJ _ _ _ _)
          ((h0.keeps hr₁ fun _ h => h.elim).al0 _ _ _ _)))
    rintro f d₂ ⟨hd₂, hr₂⟩
    refine SafeO.bind _ _ _
      (SafeO.mono ?_ _ _
        (run_opensExtB wq.ext (H.ext w) trees _ wq.ext.all d₂ hd₂
          (fun tr h => ((htr tr h).grows hr₁.grows fun _ _ h => h).grows hr₂.grows fun _ _ h => h)))
    rintro g d₃ ⟨hd₃, hr₃⟩
    exact ⟨hd₃,
      ((hr₁.mono (Cc := NoTok) (Ch := NoTok) (R := fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u)
            (e := zr) (M := zr) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun u hu => Or.inl (Or.inl (hs.new u ((hmem u).mp hu)))) (fun _ => le_rfl)
            (fun _ => le_rfl)).trans
          hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl (Or.inl hu))
          (fun _ => le_rfl) (fun _ => le_rfl)).trans
        hr₃ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl (Or.inr hu))
        (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- The proof strings of all slots. -/
theorem safe_finishAll (n₀ : ℕ) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d →
    AllFrom (fun j acc => ∃ Op, SlotF d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) Op a0 j acc) j zs →
    Trees0 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) a0.trees → (∀ tr ∈ trees, TreeOKB d tr) →
    SafeO (rulesB K L lam p) (finishAll Q H wq wp trees w fl c0 a0 j zs) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | _, [], d, hd, _, _, _ => ⟨hd, Run.refl d⟩
  | j, acc :: zs, d, hd, hall, h0, htr => by
      rw [finishAll]
      obtain ⟨⟨Op, hs⟩, hrest⟩ := hall
      have hone : SafeO (rulesB K L lam p) (match acc.x with
          | some (x, cj) =>
            if fl j then finishSlot Q H wq wp trees w c0 a0 j x cj acc else pure none
          | none => pure none) d fun _ d' =>
            TidyO (rulesB K L lam p) d' ∧
            Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d' := by
        split
        · split
          · exact safe_finishSlot Q H wq wp trees w n₀ c0 a0 j _ _ acc d hd hs h0 htr
          · exact ⟨hd, Run.refl d⟩
        · exact ⟨hd, Run.refl d⟩
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d hone)
      rintro π d₁ ⟨hd₁, hr₁⟩
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁
          (safe_finishAll n₀ fl c0 a0 (j + 1) zs d₁ hd₁
            (AllFrom.mono (fun _ _ ⟨Op', h⟩ => ⟨Op', h.keeps hr₁ fun _ hu => hu.elim⟩) _ _ hrest)
            (h0.keeps hr₁ fun _ hu => hu.elim)
            (fun tr h => (htr tr h).grows hr₁.grows fun _ _ hu => hu)))
      rintro r d₂ ⟨hd₂, hr₂⟩
      exact ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩

end Compile.Batch.Disc
