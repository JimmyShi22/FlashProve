-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineTree.lean: from every state with `TidyO`, token trees over prover messages
obey the rules of deferred programming, and a path can be revealed (words of this library:
lean/GLOSSARY.md).

For `Spec.safeCB`, `Spec.safePB` (Compile/Batch/SpecDiscipline.lean): the programs of
Compile/Batch/TokTree.lean for trees over prover messages, and `rnodeT`. An inner node is a marked
query that is charged to its left child and holds its right child; the new token for its answer is
the parent. So the left child depends on the right child and on the parent, and the right child on
nothing (`PairOK`). Hence `deps_PA`, and with the salt of a leaf the tokens beside and on its way to
the root can be revealed together (`TTOK.open_`).

Notation: `lam`, `K`: natural numbers, `L`: an `BatchProtocol I X` (Iop/Batch.lean); in `spec lam K L`
(Compile/Batch/Oracles.lean): digests have `lam` bits, a Fiat-Shamir answer is K hash blocks and a
chaining value, `L` is the record of protocols; `Tok`: `ℕ` (Rom/Defer.lean); the value of token i is
at place i of `d.vals`; `d`, `d'`: a `DSt` (Rom/Defer.lean): the state of the experiment beside the
challenger's own; `SafeO Rl c d Q` (Compile/Batch/SpecDiscipline.lean): the program c obeys the
rules from the state d, and ends in Q, whatever the coins, the answers and the tables are;
`rulesB K L lam p` (the same file): the rules of the scheme; `Run Cc Ch R e M d d'`
(Compile/Batch/DisciplineRun.lean): what a run does; Cc, Ch, R: predicates on tokens; e, M: a number
for each oracle; `zr` (Compile/Batch/DisciplineE.lean): no query; `cnt1 o n`
(Compile/Discipline.lean): the count n at the oracle o and 0 elsewhere; `p`: a `Params`
(Compile/Star.lean); `p.sMT`: a natural number; in `rulesB`: leaves are charged to a salt of sMT
bits.
-/
import Compile.Batch.DisciplineRun
import Compile.Batch.DisciplineE

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params}

theorem getD_mem {l : List Tok} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- Some query to an oracle other than the leaf oracle of request trees holds u. -/
abbrev Sealed (d : DSt (spec lam K L)) (u : Tok) : Prop := SealedW (fun o => o = OracleName.rleaf) d u

/-! ## 1. One inner node -/

/-- what one inner node, at the oracle o, leaves behind -/
def NodePost (p : Params) (o : OracleName) (a b : Tok) (d : DSt (spec lam K L))
    (c : Tok) (d' : DSt (spec lam K L)) : Prop :=
  TidyO (rulesB K L lam p) d' ∧
  Run (fun t => t = a) (fun t => t = a ∨ t = b) NoTok zr (cnt1 o 1) d d' ∧ c = d.vals.length ∧
  Deps d' a [c, b] ∧ Untouched d' c ∧ Len d' c lam ∧ Sealed d' a ∧ Sealed d' b

private theorem run_mark2 (d : DSt (spec lam K L)) (o : OracleName) (a b : Tok) (P : (spec lam K L).Dom o)
    (r : (spec lam K L).Rng o) (T : Table (spec lam K L)) :
    Run (fun t => t = a) (fun t => t = a ∨ t = b) NoTok zr (cnt1 o 1) d
      (afterMark (split lam K L) d o a [b] P r T) :=
  (Run.ofMark (R := NoTok) (e := zr) d o a [b] P r T).mono (fun _ h => Or.inl h)
    (fun _ h => Or.inl (h.imp_right List.mem_singleton.mp)) (fun _ h => Or.inl h)
    (fun _ => le_rfl) (fun _ => le_rfl)

theorem safe_nodeT (a b : Tok) (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    (ha : Untouched d a) (hb : b < d.vals.length) (hab : a ≠ b) (hl : Len d a lam) :
    SafeO (rulesB K L lam p) (nodeT (lam := lam) (K := K) (L := L) a b)
      d (NodePost p OracleName.node a b d) := by
  have hus : ∀ u ∈ [b], u < d.vals.length := fun u hu => by rw [List.mem_singleton.mp hu]; exact hb
  have htu : a ∉ [b] := fun h => hab (List.mem_singleton.mp h)
  have hbit : (rulesB K L lam p).bits OracleName.node ≤ (d.val a).length := le_of_eq hl.2.symm
  have hmk : OracleName.node ∈ osB ∨ ∃ t k, OracleName.node = OracleName.fbw t k := Or.inl (by decide)
  exact ⟨hus, htu, ha.freeAt _, hbit, hmk,
    fun r T =>
      ⟨hd.mark hus htu (ha.freeAt _) _ hbit hmk r T,
        run_mark2 d _ a b _ r T,
        rfl,
        (ha.deps []).of_mark _ r T,
        Untouched.of_tail hd ha.lt hus _ r T,
        Len.of_tail d _ a [b] _ r T,
        SealedW.of_mark (by simp) d a [b] _ r T (Or.inl rfl),
        SealedW.of_mark (by simp) d a [b] _ r T (Or.inr (List.mem_singleton.mpr rfl))⟩⟩

theorem safe_rnodeT (a b : Tok) (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    (ha : Untouched d a) (hb : b < d.vals.length) (hab : a ≠ b) (hl : Len d a lam) :
    SafeO (rulesB K L lam p) (rnodeT (lam := lam) (K := K) (L := L) a b)
      d (NodePost p OracleName.rnode a b d) := by
  have hus : ∀ u ∈ [b], u < d.vals.length := fun u hu => by rw [List.mem_singleton.mp hu]; exact hb
  have htu : a ∉ [b] := fun h => hab (List.mem_singleton.mp h)
  have hbit : (rulesB K L lam p).bits OracleName.rnode ≤ (d.val a).length := le_of_eq hl.2.symm
  have hmk : OracleName.rnode ∈ osB ∨ ∃ t k, OracleName.rnode = OracleName.fbw t k := Or.inl (by decide)
  exact ⟨hus, htu, ha.freeAt _, hbit, hmk,
    fun r T =>
      ⟨hd.mark hus htu (ha.freeAt _) _ hbit hmk r T,
        run_mark2 d _ a b _ r T,
        rfl,
        (ha.deps []).of_mark _ r T,
        Untouched.of_tail hd ha.lt hus _ r T,
        Len.of_tail d _ a [b] _ r T,
        SealedW.of_mark (by simp) d a [b] _ r T (Or.inl rfl),
        SealedW.of_mark (by simp) d a [b] _ r T (Or.inr (List.mem_singleton.mpr rfl))⟩⟩

/-! ## 2. One level, all levels -/

/-- the tokens of a level before the level above is made: untouched, of lam bits, different from one
another -/
def Ready (lam : ℕ) (d : DSt (spec lam K L)) (l : List Tok) : Prop :=
  (∀ a ∈ l, Untouched d a ∧ Len d a lam) ∧ l.Nodup

/-- two neighbouring levels: a left child depends on its parent and on its right neighbour, a right
child on nothing -/
def PairOK (d : DSt (spec lam K L)) (l l' : List Tok) : Prop :=
  ∀ i < l'.length,
    Deps d (l.getD (2 * i) 0) [l'.getD i 0, l.getD (2 * i + 1) 0] ∧ Deps d (l.getD (2 * i + 1) 0) []

section Levels
variable (o : OracleName) (hN : Tok → Tok → St lam K L Tok)
  (H : ∀ (a b : Tok) (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d → Untouched d a →
    b < d.vals.length → a ≠ b → Len d a lam →
    SafeO (rulesB K L lam p) (hN a b) d (NodePost p o a b d))

include H in
theorem safe_pairUpT : ∀ (m : ℕ) (l : List Tok) (d : DSt (spec lam K L)),
    l.length = 2 * m → TidyO (rulesB K L lam p) d → Ready lam d l →
    SafeO (rulesB K L lam p) (pairUp hN l) d fun l' d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun t => t ∈ l) (fun t => t ∈ l) NoTok zr (cnt1 o m) d d' ∧
      l'.length = m ∧ PairOK d' l l' ∧
      Ready lam d' l' ∧ (∀ c ∈ l', d.vals.length ≤ c) ∧ ∀ x ∈ l, Sealed d' x
  | 0, l, d, hlen, hd, _ => by
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hlen
      exact ⟨hd, Run.refl d, rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
        ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩,
        fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | m + 1, l, d, hlen, hd, hr => by
      obtain ⟨a, b, t, rfl⟩ : ∃ a b t, l = a :: b :: t := by
        match l, hlen with
        | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩
      have hlt : t.length = 2 * m := by simp only [List.length_cons] at hlen; omega
      have ha := hr.1 a List.mem_cons_self
      have hb := hr.1 b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hnd := List.nodup_cons.mp hr.2
      have hnd2 := List.nodup_cons.mp hnd.2
      have hab : a ≠ b := fun h => hnd.1 (h ▸ List.mem_cons_self)
      have hat : a ∉ t := fun h => hnd.1 (List.mem_cons_of_mem _ h)
      show SafeO _ ((hN a b).bind fun c => (pairUp hN t).bind fun r => Step.pure (c :: r)) d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (H a b d hd ha.1 hb.1.lt hab ha.2))
      rintro c d₁ ⟨hd₁, hr₁, rfl, hdep, huc, hlc, hsa, hsb⟩
      have hrt : Ready lam d₁ t :=
        ⟨fun x hx =>
            ⟨((hr.1 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).1).grows hr₁.grows
                (fun h => h.elim (fun h => hat (h ▸ hx)) (fun h => hnd2.1 (h ▸ hx))) (fun h => h),
              ((hr.1 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).2).grows hr₁.grows⟩,
          hnd2.2⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_pairUpT m t d₁ hlt hd₁ hrt))
      rintro r d₂ ⟨hd₂, hr₂, hlen₂, hp₂, hrd₂, hnew₂, hse₂⟩
      have hct : d.vals.length ∉ t := fun h =>
        absurd ((hr.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))).1.lt) (lt_irrefl _)
      refine ⟨hd₂, ?_, by simp [hlen₂], ?_, ⟨?_, ?_⟩, ?_, ?_⟩
      · refine (hr₁.mono (Cc := fun x => x ∈ a :: b :: t) (Ch := fun x => x ∈ a :: b :: t)
            (R := NoTok) (e := zr) (M := cnt1 o 1) (fun x hx => Or.inl (hx ▸ List.mem_cons_self))
            (fun x hx => Or.inl ?_) (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₂ (fun x hx => Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
          (fun x hx => Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
          (fun _ h => Or.inl h) (fun _ => le_rfl) (fun o' => by rw [cnt1_add, Nat.add_comm])
        rcases hx with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · intro i hi
        cases i with
        | zero =>
          exact ⟨hdep.keeps (lt_of_lt_of_le ha.1.lt hr₁.length_le) hr₂.charges hat,
            (((hb.1.deps []).keeps hb.1.lt hr₁.charges (fun h => hab h.symm)).keeps
              (lt_of_lt_of_le hb.1.lt hr₁.length_le) hr₂.charges hnd2.1)⟩
        | succ i =>
          have hi' : i < r.length := by simpa using hi
          have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
          have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
          rw [e2, e1, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
            List.getD_cons_succ, List.getD_cons_succ]
          exact hp₂ i hi'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨huc.grows hr₂.grows hct (fun h => h), hlc.grows hr₂.grows⟩
        · exact hrd₂.1 x hx
      · exact List.nodup_cons.mpr ⟨fun h => absurd (hnew₂ _ h) (Nat.not_le.mpr huc.lt), hrd₂.2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact le_trans hr₁.length_le (hnew₂ x hx)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hsa.mono hr₂.keeps
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hsb.mono hr₂.keeps
          · exact hse₂ x hx

/-- all levels: neighbouring levels fit, every level is half as long as the one below, the tokens of
the top level are ready -/
def LevOK (lam : ℕ) (d : DSt (spec lam K L)) : List (List Tok) → Prop
  | [] => True
  | [top] => Ready lam d top
  | l :: l' :: ls => PairOK d l l' ∧ l.length = 2 * l'.length ∧ LevOK lam d (l' :: ls)

include H in
theorem safe_levelsT : ∀ (k : ℕ) (l : List Tok) (d : DSt (spec lam K L)),
    l.length = 2 ^ k → TidyO (rulesB K L lam p) d → Ready lam d l →
    SafeO (rulesB K L lam p) (levelsM hN k l) d fun lv d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun t => t ∈ l) (fun t => t ∈ l) NoTok zr (cnt1 o l.length) d d' ∧
      (∃ ls, lv = l :: ls) ∧
      LevOK lam d' lv ∧ (∀ l' ∈ lv, ∀ c ∈ l', c < d'.vals.length ∧ (c ∈ l ∨ d.vals.length ≤ c)) ∧
      (Untouched d' (rootOf lv) ∧ Len d' (rootOf lv) lam) ∧
      (rootOf lv ∈ l ∨ d.vals.length ≤ rootOf lv) ∧
      ∀ l' ∈ lv, ∀ c ∈ l', c = rootOf lv ∨ Sealed d' c
  | 0, l, d, hlen, hd, hr => by
      obtain ⟨a, rfl⟩ : ∃ a, l = [a] := List.length_eq_one_iff.mp (by simpa using hlen)
      exact ⟨hd, Run.refl d, ⟨[], rfl⟩, hr, fun l' hl' c hc => by
          rw [List.mem_singleton.mp hl'] at hc
          exact ⟨(hr.1 c hc).1.lt, Or.inl hc⟩, hr.1 a List.mem_cons_self,
            Or.inl List.mem_cons_self, fun l' hl' c hc => by
          rw [List.mem_singleton.mp hl'] at hc
          exact Or.inl (List.mem_singleton.mp hc)⟩
  | k + 1, l, d, hlen, hd, hr => by
      show SafeO _
        ((pairUp hN l).bind fun u => (levelsM hN k u).bind fun r => Step.pure (l :: r)) d _
      refine SafeO.bind _ _ d
        (SafeO.mono ?_ _ d
          (safe_pairUpT o hN H (2 ^ k) l d (by rw [hlen, pow_succ, Nat.mul_comm]) hd hr))
      rintro u d₁ ⟨hd₁, hr₁, hlu, hp₁, hru, hnew, hse₁⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_levelsT k u d₁ hlu hd₁ hru))
      rintro r d₂ ⟨hd₂, hr₂, ⟨ls, rfl⟩, hlv, hall, hroot, hrn, hse₂⟩
      have hlu' : ∀ x ∈ l, x ∉ u := fun x hx hxu =>
        absurd (hnew x hxu) (Nat.not_le.mpr (hr.1 x hx).1.lt)
      have hmem : ∀ i, i < l.length → l.getD i 0 ∈ l := fun i hi => getD_mem hi
      have hl2 : l.length = 2 * u.length := by rw [hlen, hlu, pow_succ, Nat.mul_comm]
      refine ⟨hd₂, ?_, ⟨_, rfl⟩, ⟨fun i hi => ?_, hl2, hlv⟩, ?_, ?_, ?_, ?_⟩
      · refine hr₁.trans hr₂ (fun x hx => Or.inr (hnew x hx)) (fun x hx => Or.inr (hnew x hx))
          (fun _ h => Or.inl h) (fun _ => le_rfl) (fun o' => ?_)
        rw [cnt1_add, hlu, hlen, pow_succ, Nat.mul_two]
      · have h0 := hmem (2 * i) (by omega)
        have h1 := hmem (2 * i + 1) (by omega)
        exact ⟨(hp₁ i hi).1.keeps (lt_of_lt_of_le (hr.1 _ h0).1.lt hr₁.length_le)
            hr₂.charges (hlu' _ h0),
          (hp₁ i hi).2.keeps (lt_of_lt_of_le (hr.1 _ h1).1.lt hr₁.length_le)
            hr₂.charges (hlu' _ h1)⟩
      · intro l' hl' c hc
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact ⟨lt_of_lt_of_le (hr.1 c hc).1.lt (le_trans hr₁.length_le hr₂.length_le), Or.inl hc⟩
        · refine ⟨(hall l' hl' c hc).1, Or.inr ?_⟩
          rcases (hall l' hl' c hc).2 with h | h
          · exact hnew c h
          · exact le_trans hr₁.length_le h
      · exact hroot
      · refine Or.inr ?_
        rcases hrn with h | h
        · exact hnew _ h
        · exact le_trans hr₁.length_le h
      · intro l' hl' c hc
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact Or.inr ((hse₁ c hc).mono hr₂.keeps)
        · exact hse₂ l' hl' c hc

end Levels

/-! ## 3. The way from a leaf to the root -/

/-- the tokens beside the way from leaf j to the root, and those on it -/
def PA (lv : List (List Tok)) (j : ℕ) : List Tok := pathOf lv j ++ ancOf lv j

theorem mem_PA_cons {l l' : List Tok} {ls : List (List Tok)} {j : ℕ} {u : Tok} :
    u ∈ PA (l :: l' :: ls) j ↔
    u = l.getD (if j % 2 = 0 then j + 1 else j - 1) 0 ∨
    u = l.getD j 0 ∨
    u ∈ PA (l' :: ls) (j / 2) := by
  show u ∈ (l.getD (if j % 2 = 0 then j + 1 else j - 1) 0 :: pathOf (l' :: ls) (j / 2)) ++
        (l.getD j 0 :: ancOf (l' :: ls) (j / 2)) ↔
    _
  unfold PA
  simp only [List.mem_append, List.mem_cons]
  tauto

theorem head_mem_PA (l : List Tok) (ls : List (List Tok)) (j : ℕ) : l.getD j 0 ∈ PA (l :: ls) j :=
  List.mem_append_right _ List.mem_cons_self

/-- Under the hypotheses below: every token beside or on the way is in some level. -/
theorem exists_mem_of_mem_PA (d : DSt (spec lam K L)) :
    ∀ (lv : List (List Tok)) (j : ℕ),
      LevOK lam d lv → j < (lv.headD []).length → ∀ u ∈ PA lv j, ∃ l ∈ lv, u ∈ l
  | [], _, _, _, _, hu => absurd hu List.not_mem_nil
  | [top], j, _, hj, u, hu => by
      have : u = top.getD j 0 := List.mem_singleton.mp hu
      exact ⟨top, List.mem_cons_self, this ▸ getD_mem hj⟩
  | l :: l' :: ls, j, h, hj, u, hu => by
      have hj' : j < l.length := hj
      rcases mem_PA_cons.mp hu with rfl | rfl | hu
      · refine ⟨l, List.mem_cons_self, getD_mem ?_⟩
        have := h.2.1
        split <;> omega
      · exact ⟨l, List.mem_cons_self, getD_mem hj'⟩
      · obtain ⟨x, hx, hux⟩ := exists_mem_of_mem_PA
          d (l' :: ls) (j / 2) h.2.2 (by have := h.2.1; show j / 2 < l'.length; omega) u hu
        exact ⟨x, List.mem_cons_of_mem _ hx, hux⟩

/-- Under the hypotheses below: the tokens beside and on the way from a leaf to the root depend only
on one another. -/
theorem deps_PA (d : DSt (spec lam K L)) :
    ∀ (lv : List (List Tok)) (j : ℕ),
      LevOK lam d lv → j < (lv.headD []).length → ∀ u ∈ PA lv j, Deps d u (PA lv j)
  | [], _, _, _, _, hu => absurd hu List.not_mem_nil
  | [top], j, h, hj, u, hu => by
      have : u = top.getD j 0 := List.mem_singleton.mp hu
      exact (h.1 u (this ▸ getD_mem hj)).1.deps _
  | l :: l' :: ls, j, h, hj, u, hu => by
      have hj' : j < l.length := hj
      have hl2 := h.2.1
      have hi : j / 2 < l'.length := by omega
      obtain ⟨hL, hR⟩ := h.1 (j / 2) hi
      have hpar : l'.getD (j / 2) 0 ∈ PA (l :: l' :: ls) j :=
        mem_PA_cons.mpr (Or.inr (Or.inr (head_mem_PA l' ls (j / 2))))
      by_cases hev : j % 2 = 0
      · have e0 : 2 * (j / 2) = j := by omega
        rw [e0] at hL hR
        rcases mem_PA_cons.mp hu with rfl | rfl | hu
        · rw [if_pos hev]
          exact hR.mono fun _ h => absurd h List.not_mem_nil
        · refine hL.mono fun v hv => ?_
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hpar
          · rw [List.mem_singleton.mp hv]
            exact mem_PA_cons.mpr (Or.inl (by rw [if_pos hev]))
        · exact (deps_PA d (l' :: ls) (j / 2) h.2.2 hi u hu).mono fun v hv =>
            mem_PA_cons.mpr (Or.inr (Or.inr hv))
      · have e0 : 2 * (j / 2) = j - 1 := by omega
        have e1 : 2 * (j / 2) + 1 = j := by omega
        rw [e1] at hL hR
        rw [e0] at hL
        rcases mem_PA_cons.mp hu with rfl | rfl | hu
        · rw [if_neg hev]
          refine hL.mono fun v hv => ?_
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hpar
          · rw [List.mem_singleton.mp hv]
            exact mem_PA_cons.mpr (Or.inr (Or.inl rfl))
        · exact hR.mono fun _ h => absurd h List.not_mem_nil
        · exact (deps_PA d (l' :: ls) (j / 2) h.2.2 hi u hu).mono fun v hv =>
            mem_PA_cons.mpr (Or.inr (Or.inr hv))

/-! ## 4. Trees over prover messages -/

theorem safe_leafT (b : Body L) (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (leafT (lam := lam) (K := K) p.sMT b) d fun x d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      x.1 = d.vals.length ∧
      x.2 = d.vals.length + 1 ∧
      x.1 < d'.vals.length ∧ Deps d' x.1 [x.2] ∧ Untouched d' x.2 ∧
      Len d' x.2 lam ∧ Sealed d' x.1 := by
  unfold leafT
  refine fun u => ?_
  have h1 := hd.fresh (List.ofFn u)
  have hu := Untouched.of_fresh hd (List.ofFn u)
  have hl := Len.of_fresh d u
  have hno : ∀ v ∈ ([] : List Tok), v < (afterFresh d (List.ofFn u)).vals.length := fun _ h =>
    absurd h List.not_mem_nil
  have hb : (rulesB K L lam p).bits OracleName.leaf ≤
      ((afterFresh d (List.ofFn u)).val d.vals.length).length :=
    le_of_eq hl.2.symm
  have hmk : OracleName.leaf ∈ osB ∨ ∃ t k, OracleName.leaf = OracleName.fbw t k := Or.inl (by decide)
  refine ⟨hno, List.not_mem_nil, hu.freeAt OracleName.leaf, hb, hmk, fun r T => ?_⟩
  have hlen : (afterFresh d (List.ofFn u)).vals.length = d.vals.length + 1 := length_afterFresh _ _
  refine ⟨h1.mark hno List.not_mem_nil (hu.freeAt OracleName.leaf) _ hb hmk r T, ?_, rfl, hlen, ?_, ?_, ?_,
    ?_, SealedW.of_mark (by simp) _ _ [] _ r T (Or.inl rfl)⟩
  · exact (Run.ofFresh (e := zr) (M := zr) d (List.ofFn u)).trans
      (Run.ofMark (R := NoTok) (e := zr) _ OracleName.leaf _ _ _ r T)
      (fun t ht => Or.inr (le_of_eq ht.symm)) (fun t ht => Or.inr (by
        rcases ht with ht | ht
        · exact le_of_eq ht.symm
        · exact absurd ht List.not_mem_nil)) (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => by simp)
  · show d.vals.length < _
    rw [length_afterMark, hlen]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  · exact (hu.deps []).of_mark _ r T
  · exact Untouched.of_tail h1 hu.lt hno _ r T
  · exact Len.of_tail _ OracleName.leaf _ [] _ r T

theorem safe_leavesT : ∀ (l : List (Body L)) (d : DSt (spec lam K L)), TidyO (rulesB K L lam p) d →
    SafeO (rulesB K L lam p) (leavesT (lam := lam) (K := K) p.sMT l) d fun x d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok NoTok zr (cnt1 OracleName.leaf l.length) d d' ∧
      x.1.length = l.length ∧
      Ready lam d' x.1 ∧
      (∀ c ∈ x.1, d.vals.length ≤ c) ∧
      ∀ i < l.length,
        Deps d' (x.2.getD i 0) [x.1.getD i 0] ∧
        d.vals.length ≤ x.2.getD i 0 ∧
        x.2.getD i 0 < d'.vals.length ∧
        x.2.getD i 0 ∉ x.1 ∧
        Sealed d' (x.2.getD i 0)
  | [], d, hd =>
    ⟨hd, Run.refl d, rfl, ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩,
      fun _ h => absurd h List.not_mem_nil, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | b :: t, d, hd => by
      show SafeO _
        ((leafT p.sMT b).bind fun x =>
          (leavesT p.sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
        d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leafT b d hd))
      rintro ⟨s, dg⟩ d₁ ⟨hd₁, hr₁, hs, hdg, hslt, hdep, hun, hln, hss⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_leavesT t d₁ hd₁))
      rintro r d₂ ⟨hd₂, hr₂, hl₂, hrd₂, hnew₂, hs₂⟩
      have hs' : s = d.vals.length := hs
      have hdg' : dg = d.vals.length + 1 := hdg
      have hslt : s < d₁.vals.length := hslt
      have hdep : Deps d₁ s [dg] := hdep
      have hun : Untouched d₁ dg := hun
      have hln : Len d₁ dg lam := hln
      have hdgr : dg ∉ r.1 := fun h => absurd (hnew₂ _ h) (Nat.not_le.mpr hun.lt)
      have hsr : s ∉ r.1 := fun h => absurd (hnew₂ _ h) (Nat.not_le.mpr hslt)
      refine ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun o' => by rw [cnt1_add, List.length_cons, Nat.add_comm]),
        by simp [hl₂],
        ⟨?_, List.nodup_cons.mpr ⟨hdgr, hrd₂.2⟩⟩,
        ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hun.grows hr₂.grows (fun h => h) (fun h => h), hln.grows hr₂.grows⟩
        · exact hrd₂.1 x hx
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdg' ▸ Nat.le_succ _
        · exact le_trans hr₁.length_le (hnew₂ x hx)
      · intro i hi
        cases i with
        | zero =>
          refine ⟨hdep.keeps hslt hr₂.charges (fun h => h), le_of_eq hs'.symm,
            lt_of_lt_of_le hslt hr₂.length_le, fun h => ?_, hss.mono hr₂.keeps⟩
          rcases List.mem_cons.mp h with h | h
          · have h' : s = dg := h
            rw [hs', hdg'] at h'
            exact absurd h' (Nat.ne_of_lt (Nat.lt_succ_self _))
          · exact hsr h
        | succ i =>
          obtain ⟨a1, a2, a3, a4, a5⟩ := hs₂ i (by simpa using hi)
          refine ⟨a1, le_trans hr₁.length_le a2, a3, fun h => ?_, a5⟩
          rcases List.mem_cons.mp h with h | h
          · have h' : r.2.getD i 0 = dg := h
            exact absurd a2 (Nat.not_le.mpr (h' ▸ hun.lt))
          · exact a4 h

/-- A tree over a prover message, once it is made: for each leaf, its salt and the tokens beside and
on its way to the root can be revealed together; all of them are at least n₀. -/
structure TTOK (d : DSt (spec lam K L)) (n₀ depth : ℕ) (t : TTree) : Prop where
  open_ : ∀ j < 2 ^ depth, ClosedO d (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))
  new : ∀ j < 2 ^ depth, ∀ u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j), n₀ ≤ u

theorem TTOK.keeps {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree} {Cc : Tok → Prop}
    (h : TTOK d n₀ depth t) (hc : Charges Cc d d') (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u) :
    TTOK d' n₀ depth t where
  open_ := fun j hj => (h.open_ j hj).keeps hc fun u hu hcu => by
    rcases hn u hcu with h1 | h1
    · exact absurd (h.new j hj u hu) (Nat.not_le.mpr h1)
    · exact absurd ((h.open_ j hj).lt u hu) (Nat.not_lt.mpr h1)
  new := h.new

theorem safe_commitT (depth : ℕ) (leaf : ℕ → Body L)
    (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (commitT (lam := lam) (K := K) p.sMT depth leaf) d fun t d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok NoTok zr
        (fun o => cnt1 OracleName.leaf (2 ^ depth) o + cnt1 OracleName.node (2 ^ depth) o) d d' ∧
      TTOK d' d.vals.length depth t ∧ Untouched d' t.root ∧ d.vals.length ≤ t.root ∧
      ∀ j < 2 ^ depth, ∀ u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j),
          u = t.root ∨ Sealed d' u := by
  show SafeO _ ((leavesT p.sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
    (levelsM nodeT depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree)) d _
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leavesT _ d hd))
  rintro x d₁ ⟨hd₁, hr₁, hl₁, hrd₁, hnew₁, hs₁⟩
  have hlen : ((List.range (2 ^ depth)).map leaf).length = 2 ^ depth := by simp
  rw [hlen] at hl₁ hs₁ hr₁
  refine SafeO.bind _ _ d₁
    (SafeO.mono ?_ _ d₁
      (safe_levelsT OracleName.node nodeT (fun a b d => safe_nodeT a b d) depth x.1 d₁ hl₁ hd₁ hrd₁))
  rintro lv d₂ ⟨hd₂, hr₂, ⟨ls, rfl⟩, hlv, hall, hroot, hrn, hse₂⟩
  rw [hl₁] at hr₂
  have hnewPA : ∀ j < 2 ^ depth,
      ∀ u ∈ PA (x.1 :: ls) j, u < d₂.vals.length ∧ d.vals.length ≤ u := fun j hj u hu => by
    obtain ⟨l, hl, hul⟩ :=
      exists_mem_of_mem_PA d₂ (x.1 :: ls) j hlv (by show j < x.1.length; rw [hl₁]; exact hj) u hu
    refine ⟨(hall l hl u hul).1, ?_⟩
    rcases (hall l hl u hul).2 with h | h
    · exact hnew₁ u h
    · exact le_trans hr₁.length_le h
  refine ⟨hd₂,
    hr₁.trans hr₂ (fun u hu => Or.inr (hnew₁ u hu)) (fun u hu => Or.inr (hnew₁ u hu))
      (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => le_rfl),
    ⟨fun j hj => ?_, fun j hj u hu => ?_⟩,
    hroot.1, ?_, fun j hj u hu => ?_⟩
  · obtain ⟨a1, a2, a3, a4, _⟩ := hs₁ j hj
    refine ClosedO.of_deps (fun u hu => ?_) (fun u hu => ?_)
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact lt_of_lt_of_le a3 hr₂.length_le
      · exact (hnewPA j hj u hu).1
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨_, a1.keeps a3 hr₂.charges a4, fun v hv => Or.inl (List.mem_cons_of_mem _ (by
          rw [List.mem_singleton.mp hv]
          exact head_mem_PA x.1 ls j))⟩
      · exact ⟨_, deps_PA d₂ (x.1 :: ls) j hlv (by show j < x.1.length; rw [hl₁]; exact hj) u hu,
          fun v hv => Or.inl (List.mem_cons_of_mem _ hv)⟩
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact (hs₁ j hj).2.1
    · exact (hnewPA j hj u hu).2
  · rcases hrn with h | h
    · exact hnew₁ _ h
    · exact le_trans hr₁.length_le h
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact Or.inr ((hs₁ j hj).2.2.2.2.mono hr₂.keeps)
    · obtain ⟨l, hl, hul⟩ :=
        exists_mem_of_mem_PA d₂ (x.1 :: ls) j hlv (by show j < x.1.length; rw [hl₁]; exact hj) u hu
      exact hse₂ l hl u hul

theorem safe_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) (d : DSt (spec lam K L))
    (hd : TidyO (rulesB K L lam p) d)
    (hc : ClosedO d (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))) :
    SafeO (rulesB K L lam p) (openT (lam := lam) (K := K) (L := L) t j a) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok (fun u => u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))
          zr zr d d' :=
  ⟨hc, fun T => ⟨hd.reveal hc T, Run.ofReveal d _ T⟩⟩

/-! ## 5. The trees of an execution, round by round -/

/-- The trees over the slots' components are in order, round by round, with the depths of the wire
record (the list is read as opensB reads it). -/
def AlJ (d : DSt (spec lam K L)) (n₀ : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (Option TTree) → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), l =>
    (∀ tr, l.headD none = some tr → TTOK d n₀ w.depthJ tr) ∧ AlJ d n₀ s A W l.tail

/-- The same for the trees over the shared components. -/
def Al0 (d : DSt (spec lam K L)) (n₀ : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (Option TTree) → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), l =>
    (∀ tr, l.headD none = some tr → TTOK d n₀ w.depth0 tr) ∧ Al0 d n₀ s A W l.tail

theorem AlJ.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {Cc : Tok → Prop} (hc : Charges Cc d d')
    (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      AlJ d n₀ s A W l → AlJ d' n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), l, h =>
    ⟨fun tr htr => (h.1 tr htr).keeps hc hn, AlJ.keeps hc hn s A W l.tail h.2⟩

theorem Al0.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {Cc : Tok → Prop} (hc : Charges Cc d d')
    (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      Al0 d n₀ s A W l → Al0 d' n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), l, h =>
    ⟨fun tr htr => (h.1 tr htr).keeps hc hn, Al0.keeps hc hn s A W l.tail h.2⟩

end Compile.Batch.Disc
