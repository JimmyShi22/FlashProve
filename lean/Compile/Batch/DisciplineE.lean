-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineE.lean: the trees over encoded indices, and their openings, obey the rules
of deferred programming, from a state with `TidyO` and, for the openings, `TreeOKB` of the trees
(words of this library: lean/GLOSSARY.md).

For `Spec.safeCB` and `Spec.safePB` (Compile/Batch/SpecDiscipline.lean): `showT`, `leafE`, `nodeE`,
`leavesE`, `commitE`, `openE`, `opensExtB` of Compile/Batch/TokTree.lean and
Compile/Batch/Prover.lean. A salted leaf: a new salt, one marked query that is charged to it, and
the digest, which nothing holds yet, is shown at once. Salt and digest can be revealed together from
then on (`TreeOKB`; `TreeOKB.grows`, under its hypotheses). Padding leaves and inner nodes are
ordinary queries. An opening makes no query and shows the two handles of a leaf (`TreeTok`).

Notation:
  encoded index: see lean/GLOSSARY.md, "encoded index";
  `TreeH lam` (Compile/Bcs.lean): what the prover keeps of one tree: all levels of digests, and
    for each salted leaf its salt token with the tail token;
  `TreeOKB d t` (Compile/Batch/SpecDiscipline.lean): `ClosedO d [s, s']` for each pair (salt,
    digest) of t;
  `TreeTok t u` (Compile/SpecDiscipline.lean): u is one of the tokens of the tree; `TreeNew n t`
    (Compile/Discipline.lean): all tokens of the tree are numbers from n on;
  `GrowsO Ch R e M d d'` (Compile/Batch/SpecDiscipline.lean): what a run may have added on the way
    from d to d'. Ch: the tokens of d that its marked queries may hold (charged or among the
    others); e o and M o: how many ordinary and marked queries to o it may have added (R: see its
    doc comment);
  `zr`, `NoTok` (Compile/Batch/DisciplineE.lean): no query; no token;
  `cnt1 o₀ n` (Compile/Discipline.lean): the count n at the oracle o₀ and 0 elsewhere;
  `eTreeE`, `mTreeE` (Compile/Batch/SpecDiscipline.lean): ordinary and marked queries of one tree
    over an encoded index (bounds).
-/
import Compile.Batch.DisciplineKit
import Compile.DisciplineOpen

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal nEv length_afterFresh length_afterMark cnt1
    TreeTok TreeNew cntLeaves)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params}

/-- no token -/
abbrev NoTok : Tok → Prop := fun _ => False
/-- no query -/
abbrev zr : OracleName → ℕ := fun _ => 0

theorem TreeOKB.grows {Ch R : Tok → Prop} {e M : OracleName → ℕ} {d d' : DSt (spec lam K L)} {t : TreeH lam}
    (h : TreeOKB d t) (hg : GrowsO Ch R e M d d') (hch : ∀ u, TreeTok t u → ¬ Ch u) :
    TreeOKB d' t := fun s s' hs =>
  (h s s' hs).grows hg fun u hu => hch u ⟨s, s', hs, by
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)⟩

theorem TreeOKB.lt {d : DSt (spec lam K L)} {t : TreeH lam} (h : TreeOKB d t)
    {u : Tok} (hu : TreeTok t u) : u < d.vals.length := by
  obtain ⟨s, s', hs, rfl | rfl⟩ := hu
  · exact (h _ s' hs).lt _ (List.mem_cons_self)
  · exact (h s _ hs).lt _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

/-- Under `TidyO`: showing one token that can be revealed alone obeys the rules. -/
theorem safe_showT (t : Tok) {d : DSt (spec lam K L)}
    (hd : TidyO (rulesB K L lam p) d) (hc : ClosedO d [t]) :
    SafeO (rulesB K L lam p) (showT (lam := lam) (K := K) (L := L) t) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok (fun u => u = t) zr zr d d' :=
  ⟨hc, fun T =>
      ⟨hd.reveal hc T,
        (GrowsO.ofReveal (Ch := NoTok) (e := zr) (M := zr) d [t] T).mono (fun _ h => Or.inl h)
          (fun _ hu => Or.inl (List.mem_singleton.mp hu)) (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩

/-- A salted leaf, before its digest is shown, under `TidyO`: a new salt, one marked query; the
digest is untouched. -/
private theorem safe_leafT_E
    (b : Body L) {d : DSt (spec lam K L)} (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (leafT (lam := lam) (K := K) p.sMT b) d fun x d' =>
      TidyO (rulesB K L lam p) d' ∧
      GrowsO NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      d.vals.length ≤ x.1 ∧
      d.vals.length ≤ x.2 ∧
      x.1 < d'.vals.length ∧ Untouched d' x.2 ∧ Deps d' x.1 [x.2] := by
  unfold leafT
  refine fun u => ?_
  have h1 := hd.fresh (List.ofFn u)
  have hu := Untouched.of_fresh hd (List.ofFn u)
  have hl := Len.of_fresh d u
  have hno : ∀ v ∈ ([] : List Tok), v < (afterFresh d (List.ofFn u)).vals.length := fun _ h =>
    absurd h (List.not_mem_nil)
  have hb : (rulesB K L lam p).bits OracleName.leaf ≤
      ((afterFresh d (List.ofFn u)).val d.vals.length).length :=
    le_of_eq hl.2.symm
  have hmk : OracleName.leaf ∈ osB ∨ ∃ t k, OracleName.leaf = OracleName.fbw t k := Or.inl (by decide)
  refine ⟨hno, List.not_mem_nil, hu.freeAt OracleName.leaf, hb, hmk, fun r T => ?_⟩
  refine ⟨h1.mark hno List.not_mem_nil (hu.freeAt OracleName.leaf) _ hb hmk r T, ?_, le_rfl, ?_, ?_,
    Untouched.of_tail h1 hu.lt hno _ r T, ?_⟩
  · exact (GrowsO.ofFresh (e := zr) (M := zr) d (List.ofFn u)).trans
      (GrowsO.ofMark (R := NoTok) (e := zr) _ OracleName.leaf _ _ _ r T)
      (fun t ht => Or.inr (by
        rcases ht with ht | ht
        · exact le_of_eq ht.symm
        · exact absurd ht (List.not_mem_nil))) (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => by rw [Nat.zero_add])
  · rw [length_afterFresh]
    exact Nat.le_succ _
  · rw [length_afterMark]
    exact Nat.lt_succ_of_lt hu.lt
  · exact Deps.of_mark (hu.deps []) _ r T

/-- Under `TidyO`: a salted leaf of a tree over an encoded index (`leafE` at true) obeys the rules
and keeps `TidyO`; it adds at most one marked query to `leaf`, which holds no old token, and no
ordinary query (`GrowsO NoTok NoTok zr (cnt1 OracleName.leaf 1)`); it returns a pair of new tokens with
`ClosedO`. -/
theorem safe_leafE_true (b : Body L) {d : DSt (spec lam K L)} (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (leafE (lam := lam) (K := K) p.sMT b true) d fun a d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      ∃ s s', a.2 = some (s, s') ∧ ClosedO d' [s, s'] ∧ d.vals.length ≤ s ∧ d.vals.length ≤ s' := by
  unfold leafE
  rw [if_pos rfl]
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leafT_E b hd))
  rintro x d₁ ⟨hd₁, hg₁, hn1, hn2, hlt, hun, hdep⟩
  have hc : ClosedO d₁ [x.2] :=
    ClosedO.of_deps (fun t ht => by rw [List.mem_singleton.mp ht]; exact hun.lt)
      (fun u hu =>
        ⟨[], by rw [List.mem_singleton.mp hu]; exact hun.deps [],
          fun _ h => absurd h (List.not_mem_nil)⟩)
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_showT x.2 hd₁ hc))
  rintro dg d₂ ⟨hd₂, hg₂⟩
  refine ⟨hd₂,
    hg₁.trans hg₂ (fun _ h => Or.inl h) (fun u hu => Or.inr (hu ▸ hn2))
      (fun _ => le_rfl) (fun _ => le_rfl),
    x.1, x.2, rfl, ?_, hn1, hn2⟩
  refine ClosedO.of_deps (fun t ht => ?_) (fun u hu => ?_)
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact lt_of_lt_of_le hlt hg₂.length_le
    · rw [List.mem_singleton.mp ht]
      exact lt_of_lt_of_le hun.lt hg₂.length_le
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨[x.2], hdep.grows hlt hg₂ (fun h => h), fun v hv => Or.inl (List.mem_cons_of_mem _ hv)⟩
    · rw [List.mem_singleton.mp hu]
      exact ⟨[],
        (hun.deps []).grows hun.lt hg₂ (fun h => h),
        fun _ h => absurd h (List.not_mem_nil)⟩

/-- A padding leaf: one ordinary query. -/
theorem safe_leafE_false (b : Body L) {d : DSt (spec lam K L)} (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (leafE (lam := lam) (K := K) p.sMT b false) d fun a d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.leaf 1) zr d d' ∧ a.2 = none := by
  unfold leafE
  rw [if_neg (by simp)]
  exact ⟨Or.inl rfl, fun r T => ⟨hd.plain OracleName.leaf T, GrowsO.ofPlain d OracleName.leaf T, rfl⟩⟩

theorem safe_leavesE : ∀ (l : List (Body L × Bool)) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d →
    SafeO (rulesB K L lam p) (leavesE (lam := lam) (K := K) p.sMT l) d fun a d' =>
      TidyO (rulesB K L lam p) d' ∧
      GrowsO NoTok NoTok (cnt1 OracleName.leaf (l.countP fun x => !x.2))
        (cnt1 OracleName.leaf (l.countP fun x => x.2)) d d' ∧
      a.1.length = l.length ∧
      ∀ s s', some (s, s') ∈ a.2 → ClosedO d' [s, s'] ∧ d.vals.length ≤ s ∧ d.vals.length ≤ s'
  | [], d, hd => ⟨hd, GrowsO.refl d, rfl, fun _ _ h => absurd h (List.not_mem_nil)⟩
  | (b, bl) :: t, d, hd => by
      show SafeO _
        ((leafE p.sMT b bl).bind fun x =>
          (leavesE p.sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2))
        d _
      refine SafeO.bind _ _ d ?_
      cases bl with
      | true =>
        refine SafeO.mono ?_ _ d (safe_leafE_true b hd)
        rintro x d₁ ⟨hd₁, hg₁, s₀, s₀', hx, hc₀, hn₀, hn₀'⟩
        refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_leavesE t d₁ hd₁))
        rintro r d₂ ⟨hd₂, hg₂, hlen, hcl⟩
        refine ⟨hd₂, hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ ?_,
          by simp [hlen], ?_⟩
        · intro o
          simp only [cnt1, List.countP_cons]
          split <;> simp
        · intro o
          simp only [cnt1, List.countP_cons]
          split <;> simp [Nat.add_comm]
        · intro s s' hs
          rcases List.mem_cons.mp hs with hs | hs
          · rw [hx] at hs
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
            exact ⟨hc₀.grows hg₂ (fun _ _ h => h), hn₀, hn₀'⟩
          · obtain ⟨a1, a2, a3⟩ := hcl s s' hs
            exact ⟨a1, le_trans hg₁.length_le a2, le_trans hg₁.length_le a3⟩
      | false =>
        refine SafeO.mono ?_ _ d (safe_leafE_false b hd)
        rintro x d₁ ⟨hd₁, hg₁, hx⟩
        refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_leavesE t d₁ hd₁))
        rintro r d₂ ⟨hd₂, hg₂, hlen, hcl⟩
        refine ⟨hd₂, hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ ?_,
          by simp [hlen], ?_⟩
        · intro o
          simp only [cnt1, List.countP_cons]
          split <;> simp [Nat.add_comm]
        · intro o
          simp only [cnt1, List.countP_cons]
          split <;> simp
        · intro s s' hs
          rcases List.mem_cons.mp hs with hs | hs
          · rw [hx] at hs
            exact absurd hs (by simp)
          · obtain ⟨a1, a2, a3⟩ := hcl s s' hs
            exact ⟨a1, le_trans hg₁.length_le a2, le_trans hg₁.length_le a3⟩

theorem safe_nodeE (a b : Dig lam) {d : DSt (spec lam K L)} (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (nodeE (K := K) (L := L) a b) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.node 1) zr d d' :=
  ⟨Or.inr rfl, fun _ T => ⟨hd.plain OracleName.node T, GrowsO.ofPlain d OracleName.node T⟩⟩

theorem safe_pairUpE : ∀ (l : List (Dig lam)) (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d →
    SafeO (rulesB K L lam p) (pairUp (nodeE (K := K) (L := L)) l) d fun a d' =>
      TidyO (rulesB K L lam p) d' ∧
      GrowsO NoTok NoTok (cnt1 OracleName.node (l.length / 2)) zr d d' ∧
      a.length = l.length - l.length / 2
  | [], d, hd => ⟨hd, GrowsO.refl d, by simp⟩
  | [_], d, hd => ⟨hd, GrowsO.refl d, by simp⟩
  | a :: b :: t, d, hd => by
      show SafeO _ ((nodeE a b).bind fun c => (pairUp nodeE t).bind fun r => Step.pure (c :: r)) d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_nodeE a b hd))
      rintro c d₁ ⟨hd₁, hg₁⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_pairUpE t d₁ hd₁))
      rintro r d₂ ⟨hd₂, hg₂, hlen⟩
      refine ⟨hd₂,
        hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ (fun _ => le_rfl),
        ?_⟩
      · intro o
        simp only [cnt1, List.length_cons]
        split
        · omega
        · exact le_rfl
      · simp only [List.length_cons, hlen]
        omega

theorem safe_levelsE : ∀ (n : ℕ) (l : List (Dig lam)) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d →
    SafeO (rulesB K L lam p) (levelsM (nodeE (K := K) (L := L)) n l) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.node l.length) zr d d'
  | 0, _, d, hd => ⟨hd, GrowsO.refl d⟩
  | n + 1, l, d, hd => by
      show SafeO _
        ((pairUp nodeE l).bind fun u => (levelsM nodeE n u).bind fun r => Step.pure (l :: r)) d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_pairUpE l d hd))
      rintro u d₁ ⟨hd₁, hg₁, hlen⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_levelsE n u d₁ hd₁))
      rintro r d₂ ⟨hd₂, hg₂⟩
      refine ⟨hd₂, hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ (fun _ => le_rfl)⟩
      intro o
      simp only [cnt1, hlen]
      split
      · omega
      · exact le_rfl

/-- Under `TidyO`: one tree over an encoded index (`commitE`) obeys the rules and keeps `TidyO`; its
ordinary and marked queries are within `eTreeE` and `mTreeE`, and hold no old token
(`GrowsO NoTok NoTok`); the tree has `TreeOKB`, and all its tokens are new (`TreeNew`). -/
theorem safe_commitE (depth : ℕ) (leaf : ℕ → Body L × Bool)
    {d : DSt (spec lam K L)} (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (commitE (lam := lam) (K := K) p.sMT depth leaf) d fun t d' =>
      TidyO (rulesB K L lam p) d' ∧
      GrowsO NoTok NoTok (eTreeE depth fun j => (leaf j).2)
        (mTreeE depth fun j => (leaf j).2) d d' ∧
      TreeOKB d' t ∧ TreeNew d.vals.length t := by
  show SafeO _ ((leavesE p.sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
    (levelsM nodeE depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam)) d _
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leavesE _ d hd))
  rintro x d₁ ⟨hd₁, hg₁, hlen, hcl⟩
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_levelsE depth x.1 d₁ hd₁))
  rintro lv d₂ ⟨hd₂, hg₂⟩
  refine ⟨hd₂, hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ ?_, ?_, ?_⟩
  · intro o
    rw [hlen, List.length_map, List.length_range, List.countP_map, List.countP_eq_length_filter]
    cases o <;> simp [cnt1, eTreeE, cntLeaves, Function.comp_def]
  · intro o
    rw [List.countP_map, List.countP_eq_length_filter]
    cases o <;> simp [cnt1, mTreeE, cntLeaves, Function.comp_def]
  · exact fun s s' hs => (hcl s s' hs).1.grows hg₂ fun _ _ h => h
  · rintro u ⟨s, s', hs, rfl | rfl⟩
    · exact (hcl _ s' hs).2.1
    · exact (hcl s _ hs).2.2

/-! ## Openings -/

theorem treeOKB_default (d : DSt (spec lam K L)) : TreeOKB d (⟨[], []⟩ : TreeH lam) := fun _ _ h =>
  absurd h (List.not_mem_nil)

theorem treeOKB_of_mem_or {d : DSt (spec lam K L)} {trees : List (TreeH lam)}
    (h : ∀ tr ∈ trees, TreeOKB d tr) {t : TreeH lam} (ht : t ∈ trees ∨ t = ⟨[], []⟩) :
    TreeOKB d t := by
  rcases ht with ht | rfl
  · exact h t ht
  · exact treeOKB_default d

/-- One opening: the two handles of the leaf (`TreeTok`) are revealed together, or there is nothing
to reveal. -/
theorem safe_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) {d : DSt (spec lam K L)}
    (hd : TidyO (rulesB K L lam p) d) (ht : TreeOKB d t) :
    SafeO (rulesB K L lam p) (openE (K := K) (L := L) t j a) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok (TreeTok t) zr zr d d' := by
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
          (GrowsO.ofReveal (Ch := NoTok) (e := zr) (M := zr) d [s, s'] T).mono (fun _ h => Or.inl h)
            (fun u hu => Or.inl ⟨s, s', hm, ?_⟩) (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)
  · exact ⟨hd, GrowsO.refl d⟩

/-- The openings in the trees over the external strings. -/
theorem safe_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → (∀ tr ∈ trees, TreeOKB d tr) →
    SafeO (rulesB K L lam p) (opensExtB (K := K) (L := L) we y trees isRead ps) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧ GrowsO NoTok (fun u => ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | [], d, hd, _ => ⟨hd, GrowsO.refl d⟩
  | q :: ps, d, hd, ht => by
      rw [opensExtB]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_opensExtB we y trees isRead ps d hd ht))
      rintro f d₁ ⟨hd₁, hg₁⟩
      split
      · refine SafeO.bind _ _ d₁
          (SafeO.mono ?_ _ d₁
            (safe_openE (trees.getD (we.which q) ⟨[], []⟩) (we.leaf q) _ hd₁
              (treeOKB_of_mem_or (fun tr htr => (ht tr htr).grows hg₁ fun _ _ h => h)
                (Compile.Disc.Open.getD_mem_or trees _))))
        rintro op d₂ ⟨hd₂, hg₂⟩
        exact ⟨hd₂,
          hg₁.trans hg₂ (fun _ h => Or.inl h)
            (fun u hu =>
              Or.inl
                (Compile.Disc.Open.treeTok_of_mem_or (Compile.Disc.Open.getD_mem_or trees _) hu))
            (fun _ => le_rfl) (fun _ => le_rfl)⟩
      · exact ⟨hd₁, hg₁⟩

end Compile.Batch.Disc
