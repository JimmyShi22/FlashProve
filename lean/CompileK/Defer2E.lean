-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2E.lean: the hash trees over encoded indices and their openings, for the lemma on
deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The library's
trees over encoded indices and their openings (Compile/Batch/TokTree.lean,
Compile/Batch/Prover.lean: `showT`, `leafE`, `nodeE`, `leavesE`, `commitE`, `openE`, `opensExtB`)
obey the discipline with joint charges (`SafeO2`); each under the hypotheses of its statement.

The analogues for `SafeO2` (CompileK/Defer2Safe.lean) of the theorems of
Compile/Batch/DisciplineE.lean, with `ClosedBoth` for `ClosedO` and `TreeOKB2` for `TreeOKB`
(CompileK/Defer2Kit.lean). Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.

This settles two of the four reveal sites of the base programs: showT [t] and openE [salt, digest].
Why: a salted leaf's digest is untouched when it is shown, and its salt is nobody's further token;
the inner nodes of these trees are plain evaluations on values: they hold no token: so salt and
digest stay nobody's further tokens as long as no later evaluation is allowed to hold them (the side
condition hch of `TreeOKB2.grows`, the same as in `TreeOKB.grows`).

Words used in this file. The discipline with joint charges, orderly both ways: the paragraph "Words
used in this file." of CompileK/Defer2Chain.lean's head holds here too.
-/
import CompileK.Defer2Kit

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal nEv length_afterFresh length_afterMark cnt1
    TreeTok TreeNew cntLeaves)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ}

theorem TreeOKB2.grows {Ch R : Tok → Prop} {e M : OracleName → ℕ}
    {d d' : DSt (spec lam K L)} {t : TreeH lam} (h : TreeOKB2 d t)
    (hg : GrowsO Ch R e M d d') (hch : ∀ u, TreeTok t u → ¬ Ch u) : TreeOKB2 d' t := fun s s' hs =>
  (h s s' hs).grows hg fun u hu => hch u ⟨s, s', hs, by
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)⟩

theorem TreeOKB2.lt {d : DSt (spec lam K L)} {t : TreeH lam} (h : TreeOKB2 d t)
    {u : Tok} (hu : TreeTok t u) : u < d.vals.length := by
  obtain ⟨s, s', hs, rfl | rfl⟩ := hu
  · exact (h _ s' hs).lt _ (List.mem_cons_self)
  · exact (h s _ hs).lt _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

/-- Show one token that can be revealed alone. -/
theorem safe2_showT (t : Tok) {d : DSt (spec lam K L)}
    (hd : TidyBoth p mG d) (hc : ClosedBoth d [t]) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (showT (lam := lam) (K := K) (L := L) t) d fun _ d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok (fun u => u = t) zr zr d d' :=
  ⟨hc.1, hc.2,
    fun T =>
      ⟨hd.reveal hc T,
        (GrowsO.ofReveal (Ch := NoTok) (e := zr) (M := zr) d [t] T).mono (fun _ h => Or.inl h)
          (fun _ hu => Or.inl (List.mem_singleton.mp hu)) (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩

/-- A salted leaf, before its digest is shown: a new salt, one marked evaluation; the digest is
untouched; from a state that is orderly both ways (hd). -/
private theorem safe2_leafT_E (b : Body L) {d : DSt (spec lam K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leafT (lam := lam) (K := K) p.sMT b) d fun x d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      d.vals.length ≤ x.1 ∧ d.vals.length ≤ x.2 ∧
      x.1 < d'.vals.length ∧ Untouched d' x.2 ∧
      Deps d' x.1 [x.2] ∧ RDep d' x.1 (fun _ => False) := by
  unfold leafT
  refine fun u => ?_
  have h1 := hd.fresh (List.ofFn u)
  have hu := Untouched.of_fresh hd.1 (List.ofFn u)
  have hl := Len.of_fresh d u
  have hno : ∀ v ∈ ([] : List Tok), v < (afterFresh d (List.ofFn u)).vals.length := fun _ h =>
    absurd h (List.not_mem_nil)
  have hb : (rulesT K L lam p mG).bits OracleName.leaf ≤
      ((afterFresh d (List.ofFn u)).val d.vals.length).length :=
    le_of_eq hl.2.symm
  have hmk : OracleName.leaf ∈ osBG mG := osB_sub mG (by decide)
  have hJl : Jt OracleName.leaf = false := by simp [Jt]
  refine ⟨hno, List.not_mem_nil, hu.freeAt OracleName.leaf, hb, hmk, jmark_none hJl _ _ _, fun r T => ?_⟩
  refine ⟨h1.markN hJl hno List.not_mem_nil (hu.freeAt OracleName.leaf) _ hb hmk r T, ?_, le_rfl, ?_, ?_,
    Untouched.of_tail h1.1 hu.lt hno _ r T, ?_, ?_⟩
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
  · intro e he _ hse
    rcases List.mem_append.1 (show e ∈ (afterFresh d (List.ofFn u)).evs ++ [_] from he) with he | he
    · exact absurd hse (hu.not_held e he).2
    · rw [List.mem_singleton.1 he] at hse
      exact absurd hse List.not_mem_nil

/-- A salted leaf of a tree over an encoded index. -/
theorem safe2_leafE_true (b : Body L) {d : DSt (spec lam K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leafE (lam := lam) (K := K) p.sMT b true) d fun a d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      ∃ s s',
          a.2 = some (s, s') ∧ ClosedBoth d' [s, s'] ∧ d.vals.length ≤ s ∧ d.vals.length ≤ s' := by
  unfold leafE
  rw [if_pos rfl]
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_leafT_E b hd))
  rintro x d₁ ⟨hd₁, hg₁, hn1, hn2, hlt, hun, hdep, hsR⟩
  have hc : ClosedBoth d₁ [x.2] :=
    ClosedBoth.of_deps (fun t ht => by rw [List.mem_singleton.mp ht]; exact hun.lt)
      (fun u hu =>
        ⟨[], by rw [List.mem_singleton.mp hu]; exact hun.deps [],
          fun _ h => absurd h (List.not_mem_nil)⟩)
      (fun u hu => by rw [List.mem_singleton.mp hu]; exact hun.rnone)
  refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_showT x.2 hd₁ hc))
  rintro dg d₂ ⟨hd₂, hg₂⟩
  refine ⟨hd₂,
    hg₁.trans hg₂ (fun _ h => Or.inl h) (fun u hu => Or.inr (hu ▸ hn2))
      (fun _ => le_rfl) (fun _ => le_rfl),
    x.1, x.2, rfl, ?_, hn1, hn2⟩
  refine ClosedBoth.of_deps (fun t ht => ?_) (fun u hu => ?_) (fun u hu => ?_)
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
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact (RDep.keeps hsR hlt hg₂ (fun h => h)).mono fun _ h => h.elim
    · rw [List.mem_singleton.mp hu]
      exact RDep.keeps hun.rnone hun.lt hg₂ (fun h => h)

/-- A padding leaf: one plain evaluation. -/
theorem safe2_leafE_false (b : Body L) {d : DSt (spec lam K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leafE (lam := lam) (K := K) p.sMT b false) d fun a d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.leaf 1) zr d d' ∧ a.2 = none := by
  unfold leafE
  rw [if_neg (by simp)]
  exact ⟨Or.inl rfl, fun r T => ⟨hd.plain OracleName.leaf T, GrowsO.ofPlain d OracleName.leaf T, rfl⟩⟩

theorem safe2_leavesE : ∀ (l : List (Body L × Bool)) (d : DSt (spec lam K L)), TidyBoth p mG d →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leavesE (lam := lam) (K := K) p.sMT l) d fun a d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok NoTok (cnt1 OracleName.leaf (l.countP fun x => !x.2))
        (cnt1 OracleName.leaf (l.countP fun x => x.2)) d d' ∧
      a.1.length = l.length ∧
      ∀ s s', some (s, s') ∈ a.2 → ClosedBoth d' [s, s'] ∧ d.vals.length ≤ s ∧ d.vals.length ≤ s'
  | [], d, hd => ⟨hd, GrowsO.refl d, rfl, fun _ _ h => absurd h (List.not_mem_nil)⟩
  | (b, bl) :: t, d, hd => by
      show SafeO2 _ _ _
        ((leafE p.sMT b bl).bind fun x =>
          (leavesE p.sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2))
        d _
      refine SafeO2.bind _ _ d ?_
      cases bl with
      | true =>
        refine SafeO2.mono ?_ _ d (safe2_leafE_true b hd)
        rintro x d₁ ⟨hd₁, hg₁, s₀, s₀', hx, hc₀, hn₀, hn₀'⟩
        refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_leavesE t d₁ hd₁))
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
        refine SafeO2.mono ?_ _ d (safe2_leafE_false b hd)
        rintro x d₁ ⟨hd₁, hg₁, hx⟩
        refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_leavesE t d₁ hd₁))
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

theorem safe2_nodeE (a b : Dig lam) {d : DSt (spec lam K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (nodeE (K := K) (L := L) a b) d fun _ d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.node 1) zr d d' :=
  ⟨Or.inr rfl, fun _ T => ⟨hd.plain OracleName.node T, GrowsO.ofPlain d OracleName.node T⟩⟩

theorem safe2_pairUpE : ∀ (l : List (Dig lam)) (d : DSt (spec lam K L)), TidyBoth p mG d →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (pairUp (nodeE (K := K) (L := L)) l) d fun a d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok NoTok (cnt1 OracleName.node (l.length / 2)) zr d d' ∧
      a.length = l.length - l.length / 2
  | [], d, hd => ⟨hd, GrowsO.refl d, by simp⟩
  | [_], d, hd => ⟨hd, GrowsO.refl d, by simp⟩
  | a :: b :: t, d, hd => by
      show SafeO2 _ _ _
        ((nodeE a b).bind fun c => (pairUp nodeE t).bind fun r => Step.pure (c :: r)) d _
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_nodeE a b hd))
      rintro c d₁ ⟨hd₁, hg₁⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_pairUpE t d₁ hd₁))
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

theorem safe2_levelsE : ∀ (n : ℕ) (l : List (Dig lam)) (d : DSt (spec lam K L)), TidyBoth p mG d →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (levelsM (nodeE (K := K) (L := L)) n l) d fun _ d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok NoTok (cnt1 OracleName.node l.length) zr d d'
  | 0, _, d, hd => ⟨hd, GrowsO.refl d⟩
  | n + 1, l, d, hd => by
      show SafeO2 _ _ _
        ((pairUp nodeE l).bind fun u => (levelsM nodeE n u).bind fun r => Step.pure (l :: r)) d _
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_pairUpE l d hd))
      rintro u d₁ ⟨hd₁, hg₁, hlen⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_levelsE n u d₁ hd₁))
      rintro r d₂ ⟨hd₂, hg₂⟩
      refine ⟨hd₂, hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) ?_ (fun _ => le_rfl)⟩
      intro o
      simp only [cnt1, hlen]
      split
      · omega
      · exact le_rfl

/-- One tree over an encoded index. -/
theorem safe2_commitE (depth : ℕ) (leaf : ℕ → Body L × Bool)
    {d : DSt (spec lam K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (commitE (lam := lam) (K := K) p.sMT depth leaf) d fun t d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok NoTok (eTreeE depth fun j => (leaf j).2)
        (mTreeE depth fun j => (leaf j).2) d d' ∧
      TreeOKB2 d' t ∧ TreeNew d.vals.length t := by
  show SafeO2 _ _ _ ((leavesE p.sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
    (levelsM nodeE depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam)) d _
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_leavesE _ d hd))
  rintro x d₁ ⟨hd₁, hg₁, hlen, hcl⟩
  refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_levelsE depth x.1 d₁ hd₁))
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

theorem treeOKB2_default (d : DSt (spec lam K L)) : TreeOKB2 d (⟨[], []⟩ : TreeH lam) :=
  fun _ _ h => absurd h (List.not_mem_nil)

theorem treeOKB2_of_mem_or {d : DSt (spec lam K L)} {trees : List (TreeH lam)}
    (h : ∀ tr ∈ trees, TreeOKB2 d tr) {t : TreeH lam} (ht : t ∈ trees ∨ t = ⟨[], []⟩) :
    TreeOKB2 d t := by
  rcases ht with ht | rfl
  · exact h t ht
  · exact treeOKB2_default d

/-- One opening: the two handles of the leaf are revealed together, or there is nothing to reveal.
-/
theorem safe2_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) {d : DSt (spec lam K L)}
    (hd : TidyBoth p mG d) (ht : TreeOKB2 d t) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (openE (K := K) (L := L) t j a) d fun _ d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok (TreeTok t) zr zr d d' := by
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
    refine ⟨(ht s s' hm).1,
      (ht s s' hm).2,
      fun T =>
        ⟨hd.reveal (ht s s' hm) T,
          (GrowsO.ofReveal (Ch := NoTok) (e := zr) (M := zr) d [s, s'] T).mono (fun _ h => Or.inl h)
            (fun u hu => Or.inl ⟨s, s', hm, ?_⟩) (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)
  · exact ⟨hd, GrowsO.refl d⟩

/-- The openings in the trees over the external oracles. -/
theorem safe2_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (d : DSt (spec lam K L)), TidyBoth p mG d → (∀ tr ∈ trees, TreeOKB2 d tr) →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (opensExtB (K := K) (L := L) we y trees isRead ps) d fun _ d' =>
      TidyBoth p mG d' ∧ GrowsO NoTok (fun u => ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | [], d, hd, _ => ⟨hd, GrowsO.refl d⟩
  | q :: ps, d, hd, ht => by
      rw [opensExtB]
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_opensExtB we y trees isRead ps d hd ht))
      rintro f d₁ ⟨hd₁, hg₁⟩
      split
      · refine SafeO2.bind _ _ d₁
          (SafeO2.mono ?_ _ d₁
            (safe2_openE (trees.getD (we.which q) ⟨[], []⟩) (we.leaf q) _ hd₁
              (treeOKB2_of_mem_or (fun tr htr => (ht tr htr).grows hg₁ fun _ _ h => h)
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
