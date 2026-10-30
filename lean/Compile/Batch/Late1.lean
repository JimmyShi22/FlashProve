-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Late1.lean: the trees of the compiled prover (Compile/Batch/TokTree.lean) and their
late forms (Compile/Batch/Mirror.lean) are related by `Rom.Late` (what `Late` is for: the head of
Rom/DeferLate.lean), under the hypotheses below (words of this library: lean/GLOSSARY.md). A closure
(`Clo`, Rom/DeferLate.lean) is the function that makes the input of a marked query from the values
of its tokens; the context Γ (`Ctx`) records, by charged token and oracle, the one that the `Step`
program gave. What a context knows has the form `Cov`: each closure that it records for a token is
the one that a given context has.

Notation: `Late post n Γ P Q` (Rom/DeferLate.lean): P, a program of `Step`, and Q, one of `LStep`,
have the same constructors (what more it asks, at marked evaluations and at a reveal: its doc
comment); n is a lower bound on the number of tokens that exist; post relates the results, with the
bound and the context at the end (its arguments n', Γ', x, y); `St lam K L α`
(Compile/Batch/TokTree.lean), `Lp lam K L α`, `Cx lam K L` (Compile/Batch/Mirror.lean): `Step`,
`LStep`, `Ctx` over `spec lam K L`; `baseC` (Compile/Batch/Mirror.lean): the closures that hold no
data, for every token; `TTree` (Compile/Batch/TokTree.lean): all levels of tokens of digests, leaves
first; the token of the salt of each leaf (none in a request tree); `TreeH` (Compile/Bcs.lean): what
the prover keeps of one tree: all levels of digests, and for each salted leaf its salt token with
the tail token; names that end in T, E: the programs of Compile/Batch/TokTree.lean for trees over
prover messages and request trees, over an encoded index; in L, EL: their late forms.
-/
import Compile.Batch.Mirror

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## What a context knows -/

/-- no closure is recorded for a token that does not exist yet -/
def Fut (n : ℕ) (Γ : Cx lam K L) : Prop := ∀ t, n ≤ t → ∀ o, Γ t o = none

/-- every closure that Γ records for t is the one that the context P has for t -/
def Cov (Γ : Cx lam K L) (t : Tok) (P : Cx lam K L) : Prop :=
  ∀ o pt, Γ t o = some pt → P t o = some pt

/-- only closures without data are recorded for t -/
def Base (Γ : Cx lam K L) (t : Tok) : Prop := Cov Γ t baseC

/-- for the salt s of a leaf: the closure with the body b, and nothing else that holds data -/
def KSalt (Γ : Cx lam K L) (b : Body L) (s : Tok) : Prop :=
  Cov Γ s (baseC.set s OracleName.leaf (cloLeaf K b))

/-- results equal, bound and context as before -/
def Same {α : Type} (n : ℕ) (Γ : Cx lam K L) : ℕ → Cx lam K L → α → α → Prop := fun n' Γ' a b =>
  a = b ∧ n' = n ∧ Γ' = Γ

theorem Cov.congr {Γ Γ' P : Cx lam K L} {t : Tok} (h : Cov Γ t P) (e : Γ' t = Γ t) : Cov Γ' t P :=
  fun o pt hp => h o pt (by rw [← e]; exact hp)

theorem cov_of_none {Γ P : Cx lam K L} {t : Tok} (h : ∀ o, Γ t o = none) : Cov Γ t P :=
  fun o pt hp => by rw [h o] at hp; exact absurd hp (by simp)

theorem Fut.mono {n n' : ℕ} {Γ : Cx lam K L} (h : Fut n Γ) (hn : n ≤ n') : Fut n' Γ := fun t ht =>
  h t (le_trans hn ht)

theorem Fut.set {n n' : ℕ} {Γ : Cx lam K L} (h : Fut n Γ) {t : Tok} (ht : n' > t) (hn : n ≤ n')
    (o : OracleName) (pt : Clo (spec lam K L) o) :
    Fut n' (Γ.set t o pt) := fun u hu o' => by
  rw [Ctx.set_ne_tok Γ (Nat.ne_of_gt (lt_of_lt_of_le ht hu))]
  exact h u (le_trans hn hu) o'

/-- a new entry at t that P has too -/
theorem Cov.set {Γ P : Cx lam K L} {t : Tok} (h : Cov Γ t P) {o : OracleName}
    {pt : Clo (spec lam K L) o} (hP : P t o = some pt) :
    Cov (Γ.set t o pt) t P := fun o' pt' hp => by
  by_cases ho : o' = o
  · subst ho
    rw [Ctx.set_same] at hp
    rw [← hp]; exact hP
  · rw [Ctx.set_ne_oracle Γ t ho] at hp
    exact h o' pt' hp

theorem Cov.set_ne {Γ P : Cx lam K L} {t u : Tok} (h : Cov Γ u P) (hne : u ≠ t)
    (o : OracleName) (pt : Clo (spec lam K L) o) : Cov (Γ.set t o pt) u P :=
  h.congr (funext fun o' => Ctx.set_ne_tok Γ hne o pt o')

/-! ## Contexts that grow by closures without data -/

/-- below n, Γ' records nothing beyond Γ but closures without data -/
def Ext (n : ℕ) (Γ Γ' : Cx lam K L) : Prop :=
  ∀ t, t < n → ∀ o pt, Γ' t o = some pt → Γ t o = some pt ∨ baseC t o = some pt

/-- P has all closures without data for t -/
def BaseUp (P : Cx lam K L) (t : Tok) : Prop :=
  ∀ o pt, (baseC : Cx lam K L) t o = some pt → P t o = some pt

theorem Ext.refl (n : ℕ) (Γ : Cx lam K L) : Ext n Γ Γ := fun _ _ _ _ h => Or.inl h

theorem Ext.trans {n n' : ℕ} {Γ Γ' Γ'' : Cx lam K L} (h : Ext n Γ Γ')
    (h' : Ext n' Γ' Γ'') (hn : n ≤ n') : Ext n Γ Γ'' :=
  fun t ht o pt hp => (h' t (lt_of_lt_of_le ht hn) o pt hp).elim (h t ht o pt) Or.inr

theorem Ext.of_frame {n : ℕ} {Γ Γ' : Cx lam K L} (h : ∀ t, t < n → Γ' t = Γ t) : Ext n Γ Γ' :=
  fun t ht o pt hp => Or.inl (by rw [← h t ht]; exact hp)

theorem Ext.set {n : ℕ} (Γ : Cx lam K L) (t : Tok) {o : OracleName} {pt : Clo (spec lam K L) o}
    (hb : (baseC : Cx lam K L) t o = some pt) :
    Ext n Γ (Γ.set t o pt) := fun u _ o' pt' hp => by
  by_cases hu : u = t
  · subst hu
    by_cases ho : o' = o
    · subst ho
      rw [Ctx.set_same] at hp
      exact Or.inr (by rw [← hp]; exact hb)
    · rw [Ctx.set_ne_oracle Γ u ho] at hp
      exact Or.inl hp
  · rw [Ctx.set_ne_tok Γ hu] at hp
    exact Or.inl hp

theorem Cov.ext {n : ℕ} {Γ Γ' P : Cx lam K L} {t : Tok} (h : Cov Γ t P) (hE : Ext n Γ Γ')
    (ht : t < n) (hP : BaseUp P t) : Cov Γ' t P :=
  fun o pt hp => (hE t ht o pt hp).elim (h o pt) (hP o pt)

theorem baseUp_base (t : Tok) : BaseUp (baseC : Cx lam K L) t := fun _ _ h => h

theorem baseUp_set (P : Cx lam K L) {t : Tok} (h : BaseUp P t) (s : Tok) {o : OracleName}
    (pt : Clo (spec lam K L) o) (ho : ∀ u, (baseC : Cx lam K L) u o = none) :
    BaseUp (P.set s o pt) t := fun o' pt' hb => by
  have hne : o' ≠ o := fun e => by subst e; rw [ho t] at hb; exact absurd hb (by simp)
  by_cases hs : t = s
  · subst hs; rw [Ctx.set_ne_oracle P t hne]; exact h o' pt' hb
  · rw [Ctx.set_ne_tok P hs]; exact h o' pt' hb

theorem Base.ext {n : ℕ} {Γ Γ' : Cx lam K L} {t : Tok} (h : Base Γ t)
    (hE : Ext n Γ Γ') (ht : t < n) : Base Γ' t :=
  Cov.ext h hE ht (baseUp_base t)

theorem KSalt.ext {n : ℕ} {Γ Γ' : Cx lam K L} {b : Body L} {s : Tok} (h : KSalt Γ b s)
    (hE : Ext n Γ Γ') (hs : s < n) : KSalt Γ' b s :=
  Cov.ext h hE hs (baseUp_set _ (baseUp_base s) s _ fun _ => rfl)

/-! ## Leaves -/

theorem late_leafT (sMT : ℕ) (b : Body L) {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        x = y ∧ n ≤ x.1 ∧ (x.1 : ℕ) < (x.2 : ℕ) ∧ n' > x.2 ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧
        KSalt Γ' b x.1 ∧ ∀ o, Γ' x.2 o = none)
      n Γ (leafT sMT b) (leafL sMT) := by
  refine Late.fresh fun s hs => Late.marked fun _ d hd => Late.pure ?_
  have hsd : s < d := hd
  refine ⟨rfl, hs, hsd, Nat.lt_succ_self d, hF.set (Nat.lt_succ_of_lt hsd) (by omega) _ _,
    fun t ht => ?_, ?_, fun o => ?_⟩
  · exact funext fun o => Ctx.set_ne_tok Γ (Nat.ne_of_lt (lt_of_lt_of_le ht hs)) _ _ o
  · exact Cov.set (cov_of_none fun o => hF s hs o) (Ctx.set_same _ _ _ _)
  · rw [Ctx.set_ne_tok Γ (Nat.ne_of_gt hsd)]
    exact hF d (by omega) o

theorem late_leavesT (sMT : ℕ) :
    ∀ (l : List (Body L)) (n : ℕ) (Γ : Cx lam K L), Fut n Γ →
      Late (fun n' Γ' x y =>
          x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧
          (∀ t, t < n → Γ' t = Γ t) ∧
          x.1.length = l.length ∧
          x.2.length = l.length ∧
          (∀ j, j < l.length →
            KSalt Γ' (l.getD j none) (x.2.getD j 0) ∧ n ≤ x.2.getD j 0 ∧ n' > x.2.getD j 0) ∧
          ∀ u ∈ x.1, n ≤ u ∧ n' > u ∧ ∀ o, Γ' u o = none)
        n Γ (leavesT sMT l) (leavesL sMT l.length)
  | [], n, Γ, hF =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, rfl, rfl,
        fun j hj => absurd hj (by simp), fun u hu => absurd hu (by simp)⟩
  | b :: l, n, Γ, hF => by
      refine Late.bind (late_leafT sMT b hF) fun n1 Γ1 x y h1 => ?_
      obtain ⟨rfl, a1, a2, a3, hF1, fr1, hK1, hN1⟩ := h1
      refine Late.bind (late_leavesT sMT l n1 Γ1 hF1) fun n2 Γ2 r r' h2 => Late.pure ?_
      obtain ⟨rfl, b1, hF2, fr2, e1, e2, hK2, hD2⟩ := h2
      refine ⟨rfl, by omega, hF2, fun t ht => by rw [fr2 t (by omega), fr1 t ht],
        by simp [e1], by simp [e2], fun j hj => ?_, fun u hu => ?_⟩
      · cases j with
        | zero =>
          exact ⟨hK1.congr (fr2 x.1 (by omega)), a1, Nat.lt_of_lt_of_le (Nat.lt_trans a2 a3) b1⟩
        | succ j =>
          obtain ⟨c1, c2, c3⟩ := hK2 j (by simpa using hj)
          exact ⟨c1, by show n ≤ r.2.getD j 0; omega, c3⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨by omega, by omega, fun o => by rw [fr2 _ a3]; exact hN1 o⟩
        · obtain ⟨c1, c2, c3⟩ := hD2 u hu
          exact ⟨by omega, c2, c3⟩

/-! ## Inner nodes, for the node oracle and for the node oracle of request trees at once -/

/-- level i of a tree of depth d has 2^(d - i) entries -/
def Sized : ℕ → List (List Tok) → Prop
  | 0, [l] => l.length = 1
  | d + 1, l :: ls => l.length = 2 ^ (d + 1) ∧ Sized d ls
  | _, _ => False

section Levels
variable (o : OracleName) (clo : Clo (spec lam K L) o) (hb : ∀ t, (baseC : Cx lam K L) t o = some clo)
  (hP : Tok → Tok → St lam K L Tok) (hQ : Tok → Tok → Lp lam K L Tok)
  (hN : ∀ (a b : Tok) (n : ℕ) (Γ : Cx lam K L),
    Late (fun n' Γ' x y => x = y ∧ n ≤ x ∧ n' = x + 1 ∧ Γ' = Γ.set a o clo) n Γ (hP a b) (hQ a b))
include hb hN

theorem late_pairUp :
    ∀ (l : List Tok) (n₀ n : ℕ) (Γ : Cx lam K L), Fut n Γ → (∀ u ∈ l, n₀ ≤ u ∧ n > u ∧ Base Γ u) →
      Late (fun n' Γ' x y =>
          x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n₀ → Γ' t = Γ t) ∧ Ext n Γ Γ' ∧
          (∀ m, l.length = 2 * m → x.length = m) ∧ ∀ u ∈ x, n₀ ≤ u ∧ n' > u ∧ Base Γ' u)
        n Γ (pairUp hP l) (pairUp hQ l)
  | [], _, n, Γ, hF, _ =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, Ext.refl n Γ,
        fun m hm => by simp at hm; simp [hm], fun u hu => absurd hu (by simp)⟩
  | [a], _, n, Γ, hF, hl =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, Ext.refl n Γ, fun m hm => by simp at hm; omega, hl⟩
  | a :: b :: t, n₀, n, Γ, hF, hl => by
      obtain ⟨ha0, han, -⟩ := hl a (by simp)
      refine Late.bind (hN a b n Γ) fun n1 Γ1 c c' h1 => ?_
      obtain ⟨rfl, hc, rfl, rfl⟩ := h1
      have hE1 : Ext n Γ (Γ.set a o clo) := Ext.set Γ a (hb a)
      have hF1 : Fut (c + 1) (Γ.set a o clo) := hF.set (by omega) (by omega) _ _
      refine Late.bind (late_pairUp t n₀ (c + 1) _ hF1 fun u hu => ?_)
        fun n2 Γ2 r r' h2 => Late.pure ?_
      · obtain ⟨u1, u2, u3⟩ := hl u (by simp [hu])
        exact ⟨u1, by omega, u3.ext hE1 u2⟩
      · obtain ⟨rfl, b1, hF2, fr2, hE2, hlen, hD2⟩ := h2
        refine ⟨rfl, by omega, hF2, fun t' ht' => ?_, hE1.trans hE2 (by omega),
          fun m hm => ?_, fun u hu => ?_⟩
        · rw [fr2 t' ht']
          exact funext fun o' => Ctx.set_ne_tok Γ (Nat.ne_of_lt (lt_of_lt_of_le ht' ha0)) _ _ o'
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
          have := hlen m' (by simp at hm; omega)
          simp [this]
        · rcases List.mem_cons.1 hu with rfl | hu
          · refine ⟨by omega, by omega,
              Base.ext (n := u + 1) (cov_of_none fun o' => ?_) hE2 (Nat.lt_succ_self u)⟩
            rw [Ctx.set_ne_tok Γ (Nat.ne_of_gt (lt_of_lt_of_le han hc))]
            exact hF u hc o'
          · exact hD2 u hu

theorem late_levels :
    ∀ (d : ℕ) (l : List Tok) (n₀ n : ℕ) (Γ : Cx lam K L), Fut n Γ →
      (∀ u ∈ l, n₀ ≤ u ∧ n > u ∧ Base Γ u) → l.length = 2 ^ d →
      Late (fun n' Γ' x y =>
          x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n₀ → Γ' t = Γ t) ∧ Ext n Γ Γ' ∧ Sized d x ∧
          ∀ u ∈ x.flatten, n₀ ≤ u ∧ n' > u ∧ Base Γ' u)
        n Γ (levelsM hP d l) (levelsM hQ d l)
  | 0, l, _, n, Γ, hF, hl, hlen =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, Ext.refl n Γ,
        by simpa [Sized] using hlen, fun u hu => hl u (by simpa using hu)⟩
  | d + 1, l, n₀, n, Γ, hF, hl, hlen => by
      refine Late.bind (late_pairUp o clo hb hP hQ hN l n₀ n Γ hF hl) fun n1 Γ1 u u' h1 => ?_
      obtain ⟨rfl, a1, hF1, fr1, hE1, hl1, hD1⟩ := h1
      refine Late.bind (late_levels d u n₀ n1 Γ1 hF1 hD1 (hl1 _ (by rw [hlen, pow_succ]; ring)))
        fun n2 Γ2 r r' h2 => Late.pure ?_
      obtain ⟨rfl, a2, hF2, fr2, hE2, hS2, hD2⟩ := h2
      refine ⟨rfl, by omega, hF2, fun t ht => by rw [fr2 t ht, fr1 t ht], hE1.trans hE2 a1,
        ⟨hlen, hS2⟩, fun v hv => ?_⟩
      rw [List.flatten_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨v1, v2, v3⟩ := hl v hv
        exact ⟨v1, by omega, v3.ext (hE1.trans hE2 a1) v2⟩
      · exact hD2 v hv

end Levels

/-! ## Paths in a tree of the right size -/

theorem getD_mem {l : List Tok} {j : ℕ} (h : j < l.length) : l.getD j default ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem sized_mem : ∀ (d : ℕ) (lv : List (List Tok)) (j : ℕ), Sized d lv → j < 2 ^ d →
    ∀ u ∈ pathOf lv j ++ ancOf lv j, u ∈ lv.flatten
  | 0, [l], j, hS, hj, u, hu => by
      have hl : l.length = 1 := hS
      simp only [pathOf, ancOf, List.nil_append, List.mem_singleton] at hu
      subst hu
      simpa using getD_mem (l := l) (j := j) (by simpa [hl] using hj)
  | 0, [], _, hS, _, _, _ => absurd hS (by simp [Sized])
  | 0, _ :: _ :: _, _, hS, _, _, _ => absurd hS (by simp [Sized])
  | _ + 1, [], _, hS, _, _, _ => absurd hS (by simp [Sized])
  | d + 1, [l], _, hS, _, _, _ => by
      have : Sized d [] := hS.2
      cases d <;> exact absurd this (by simp [Sized])
  | d + 1, l :: l' :: ls, j, hS, hj, u, hu => by
      obtain ⟨hl, hS'⟩ := hS
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      have ih := sized_mem d (l' :: ls) (j / 2) hS' (by omega)
      rw [List.flatten_cons, List.mem_append]
      rw [show pathOf (l :: l' :: ls) j =
              l.getD (if j % 2 = 0 then j + 1 else j - 1) default :: pathOf (l' :: ls) (j / 2)
            from rfl,
        show ancOf (l :: l' :: ls) j = l.getD j default :: ancOf (l' :: ls) (j / 2) from rfl] at hu
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hu
      rcases hu with rfl | hu | rfl | hu
      · exact Or.inl (getD_mem (by split_ifs <;> omega))
      · exact Or.inr (ih u (List.mem_append.2 (Or.inl hu)))
      · exact Or.inl (getD_mem (by omega))
      · exact Or.inr (ih u (List.mem_append.2 (Or.inr hu)))

theorem sized_root : ∀ (d : ℕ) (lv : List (List Tok)), Sized d lv → rootOf lv ∈ lv.flatten
  | 0, [l], hS => by
      have hl : l.length = 1 := hS
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
      simp [rootOf]
  | 0, [], hS => absurd hS (by simp [Sized])
  | 0, _ :: _ :: _, hS => absurd hS (by simp [Sized])
  | _ + 1, [], hS => absurd hS (by simp [Sized])
  | d + 1, [l], hS => by
      have : Sized d [] := hS.2
      cases d <;> exact absurd this (by simp [Sized])
  | d + 1, l :: l' :: ls, hS => by
      have ih := sized_root d (l' :: ls) hS.2
      rw [List.flatten_cons, List.mem_append]
      refine Or.inr ?_
      have : rootOf (l :: l' :: ls) = rootOf (l' :: ls) := by simp [rootOf]
      rw [this]; exact ih

/-! ## Token trees -/

/-- what the context knows of a token tree that was made between the bounds n and n' -/
structure TreeK (Γ : Cx lam K L) (n n' depth : ℕ) (leaf : ℕ → Body L) (tr : TTree) : Prop where
  sized : Sized depth tr.levels
  salts : ∀ j, j < 2 ^ depth →
    KSalt Γ (leaf j) (tr.salts.getD j 0) ∧ n ≤ tr.salts.getD j 0 ∧ n' > tr.salts.getD j 0
  digs : ∀ u ∈ tr.levels.flatten, n ≤ u ∧ n' > u ∧ Base Γ u

theorem late_nodeT (a b : Tok) (n : ℕ) (Γ : Cx lam K L) :
    Late (fun n' Γ' x y => x = y ∧ n ≤ x ∧ n' = x + 1 ∧ Γ' = Γ.set a OracleName.node cloNode) n Γ
      (nodeT a b) (nodeL a b) :=
  Late.marked fun _ _ hd => Late.pure ⟨rfl, hd, rfl, rfl⟩

theorem late_rnodeT (a b : Tok) (n : ℕ) (Γ : Cx lam K L) :
    Late (fun n' Γ' x y => x = y ∧ n ≤ x ∧ n' = x + 1 ∧ Γ' = Γ.set a OracleName.rnode cloRnode) n Γ
      (rnodeT a b) (rnodeL a b) :=
  Late.marked fun _ _ hd => Late.pure ⟨rfl, hd, rfl, rfl⟩

theorem late_commitT (sMT depth : ℕ) (leaf : ℕ → Body L) {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧ TreeK Γ' n n' depth leaf x)
      n Γ (commitT sMT depth leaf) (commitL sMT depth) := by
  have h0 := late_leavesT sMT ((List.range (2 ^ depth)).map leaf) n Γ hF
  rw [List.length_map, List.length_range] at h0
  refine Late.bind h0 fun n1 Γ1 x y h1 => ?_
  obtain ⟨rfl, a1, hF1, fr1, e1, e2, hK1, hD1⟩ := h1
  refine Late.bind
    (late_levels OracleName.node cloNode (fun _ => rfl) nodeT nodeL late_nodeT depth x.1 n n1 Γ1 hF1
      (fun u hu => ⟨(hD1 u hu).1, (hD1 u hu).2.1, cov_of_none (hD1 u hu).2.2⟩) e1)
    fun n2 Γ2 lv lv' h2 => Late.pure ?_
  obtain ⟨rfl, a2, hF2, fr2, hE2, hS2, hD2⟩ := h2
  refine ⟨rfl, by omega, hF2, fun t ht => by rw [fr2 t ht, fr1 t ht], hS2, fun j hj => ?_, hD2⟩
  obtain ⟨c1, c2, c3⟩ := hK1 j hj
  have hb : ((List.range (2 ^ depth)).map leaf).getD j none = leaf j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj), Option.getD_some]
    simp
  rw [hb] at c1
  exact ⟨c1.ext hE2 c3, c2, by show n2 > x.2.getD j 0; omega⟩

theorem late_openT {σ : Type} (tr : TTree) (j : ℕ) (b : Body L) (a : σ) {n : ℕ} {Γ : Cx lam K L}
    (hs : KSalt Γ b (tr.salts.getD j 0))
    (hd : ∀ u ∈ pathOf tr.levels j ++ ancOf tr.levels j, Base Γ u) :
    Late (Same n Γ) n Γ (openT tr j a) (openL tr j b a) := by
  refine Late.reveal (fun u hu o pt hp => ?_) fun vs => Late.pure ⟨rfl, rfl, rfl⟩
  by_cases hus : u = tr.salts.getD j 0
  · rw [hus] at hp ⊢
    exact hs o pt hp
  · rw [Ctx.set_ne_tok _ hus]
    rcases List.mem_cons.1 hu with h | h
    · exact absurd h hus
    · exact hd u h o pt hp

theorem late_showT (t : Tok) {n : ℕ} {Γ : Cx lam K L} (h : Base Γ t) :
    Late (Same n Γ) n Γ (showT t) (showL t) :=
  Late.reveal (fun u hu o pt hp => by rw [List.mem_singleton.1 hu] at hp ⊢; exact h o pt hp)
    fun _ => Late.pure ⟨rfl, rfl, rfl⟩

/-! ## Request trees -/

theorem late_rleavesT : ∀ (cs : List Tok) (n : ℕ) (Γ : Cx lam K L), Fut n Γ → (∀ c ∈ cs, n > c) →
    Late (fun n' Γ' x y => x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ' ∧ x.length = cs.length ∧
        ∀ u ∈ x, n ≤ u ∧ n' > u ∧ Base Γ' u) n Γ (rleavesT cs) (rleavesL cs)
  | [], n, Γ, hF, _ =>
    Late.pure ⟨rfl, le_rfl, hF, Ext.refl n Γ, rfl, fun u hu => absurd hu (by simp)⟩
  | c :: cs, n, Γ, hF, hc => by
      have hcn : n > c := hc c (by simp)
      refine Late.marked fun _ d hd => ?_
      have hE1 : Ext n Γ (Γ.set c OracleName.rleaf cloRleaf) := Ext.set Γ c rfl
      have hF1 : Fut (d + 1) (Γ.set c OracleName.rleaf cloRleaf) := hF.set (by omega) (by omega) _ _
      refine Late.bind
        (late_rleavesT cs (d + 1) _ hF1 fun c' hc' => by have := hc c' (by simp [hc']); omega)
        fun n2 Γ2 r r' h2 => Late.pure ?_
      obtain ⟨rfl, b1, hF2, hE2, hl, hD2⟩ := h2
      refine ⟨rfl, by omega, hF2, hE1.trans hE2 (by omega), by simp [hl], fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · refine ⟨hd, by omega,
          Base.ext (n := u + 1) (cov_of_none fun o' => ?_) hE2 (Nat.lt_succ_self u)⟩
        rw [Ctx.set_ne_tok Γ (Nat.ne_of_gt (lt_of_lt_of_le hcn hd))]
        exact hF u hd o'
      · obtain ⟨u1, u2, u3⟩ := hD2 u hu
        exact ⟨by omega, u2, u3⟩

theorem late_reqT (depthReq : ℕ) (cs : List Tok) {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ)
    (hc : ∀ c ∈ cs, n > c) (hlen : cs.length = 2 ^ depthReq) :
    Late (fun n' Γ' x y =>
        x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ' ∧ Sized depthReq x.levels ∧
        ∀ u ∈ x.levels.flatten, n ≤ u ∧ n' > u ∧ Base Γ' u)
      n Γ (reqT depthReq cs) (reqL depthReq cs) := by
  refine Late.bind (late_rleavesT cs n Γ hF hc) fun n1 Γ1 x y h1 => ?_
  obtain ⟨rfl, a1, hF1, hE1, e1, hD1⟩ := h1
  refine Late.bind
    (late_levels OracleName.rnode cloRnode (fun _ => rfl) rnodeT rnodeL late_rnodeT depthReq x n n1 Γ1
      hF1 hD1 (e1.trans hlen))
    fun n2 Γ2 lv lv' h2 => Late.pure ?_
  obtain ⟨rfl, a2, hF2, -, hE2, hS2, hD2⟩ := h2
  exact ⟨rfl, by omega, hF2, hE1.trans hE2 a1, hS2, hD2⟩

/-! ## Trees over encoded indices -/

theorem late_pairUpE :
    ∀ (l : List (Dig lam)) (n : ℕ) (Γ : Cx lam K L),
      Late (Same n Γ) n Γ (pairUp nodeE l) (pairUp nodeEL l)
  | [], _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | [_], _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | a :: b :: t, n, Γ => by
      refine Late.plain fun c => ?_
      refine Late.bind (late_pairUpE t n Γ) fun n' Γ' r r' h => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Late.pure ⟨rfl, rfl, rfl⟩

theorem late_levelsE :
    ∀ (d : ℕ) (l : List (Dig lam)) (n : ℕ) (Γ : Cx lam K L),
      Late (Same n Γ) n Γ (levelsM nodeE d l) (levelsM nodeEL d l)
  | 0, _, _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | d + 1, l, n, Γ => by
      refine Late.bind (late_pairUpE l n Γ) fun n' Γ' u u' h => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine Late.bind (late_levelsE d u n' Γ') fun n'' Γ'' r r' h => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Late.pure ⟨rfl, rfl, rfl⟩

/-- what the context knows of the salted leaves of a tree over an encoded index -/
def ExtK (Γ : Cx lam K L) (n' : ℕ) (body : ℕ → Body L) (salts : List (Option (Tok × Tok))) : Prop :=
  ∀ j s d, salts.getD j none = some (s, d) → KSalt Γ (body j) s ∧ Base Γ d ∧ n' > s ∧ n' > d

theorem late_leafE (sMT : ℕ) (b : Body L) (bl : Bool) (hpad : bl = false → b = none) {n : ℕ}
    {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧
        ∀ s d, x.2 = some (s, d) → KSalt Γ' b s ∧ Base Γ' d ∧ n' > s ∧ n' > d)
      n Γ (leafE sMT b bl) (leafEL sMT bl) := by
  cases bl with
  | false =>
    rw [hpad rfl]
    exact Late.plain fun d =>
      Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, fun s d' h => absurd h (by simp)⟩
  | true =>
    refine Late.bind (late_leafT sMT b hF) fun n1 Γ1 x y h1 => ?_
    obtain ⟨rfl, a1, a2, a3, hF1, fr1, hK1, hN1⟩ := h1
    refine Late.bind (late_showT x.2 (cov_of_none hN1)) fun n2 Γ2 d d' h2 => Late.pure ?_
    obtain ⟨rfl, rfl, rfl⟩ := h2
    refine ⟨rfl, by omega, hF1, fr1, fun s d' h => ?_⟩
    obtain ⟨rfl, rfl⟩ : x.1 = s ∧ x.2 = d' := by
      have : x = (s, d') := Option.some.inj h
      rw [this]; exact ⟨rfl, rfl⟩
    exact ⟨hK1, cov_of_none hN1, by omega, a3⟩

theorem late_leavesE (sMT : ℕ) :
    ∀ (l : List (Body L × Bool)) (n : ℕ) (Γ : Cx lam K L), (∀ z ∈ l, z.2 = false → z.1 = none) →
      Fut n Γ →
      Late (fun n' Γ' x y =>
          x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧
          ExtK Γ' n' (fun j => (l.getD j (none, false)).1) x.2 ∧ x.2.length = l.length)
        n Γ (leavesE sMT l) (leavesEL sMT (l.map Prod.snd))
  | [], n, Γ, _, hF =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ => rfl, fun j s d h => absurd h (by simp), rfl⟩
  | (b, bl) :: l, n, Γ, hpad, hF => by
      refine Late.bind (late_leafE sMT b bl (hpad (b, bl) (by simp)) hF) fun n1 Γ1 x y h1 => ?_
      obtain ⟨rfl, a1, hF1, fr1, hK1⟩ := h1
      refine Late.bind (late_leavesE sMT l n1 Γ1 (fun z hz => hpad z (by simp [hz])) hF1)
        fun n2 Γ2 r r' h2 => Late.pure ?_
      obtain ⟨rfl, a2, hF2, fr2, hK2, hl2⟩ := h2
      refine ⟨rfl, by omega, hF2, fun t ht => by rw [fr2 t (by omega), fr1 t ht],
        fun j s d h => ?_, by simp [hl2]⟩
      cases j with
      | zero =>
        obtain ⟨c1, c2, c3, c4⟩ := hK1 s d h
        exact ⟨c1.congr (fr2 s c3), c2.congr (fr2 d c4), by omega, by omega⟩
      | succ j => exact hK2 j s d h

theorem late_commitE (sMT depth : ℕ) (leaf : ℕ → Body L × Bool)
    (hpad : ∀ j, (leaf j).2 = false → (leaf j).1 = none) {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        x = y ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧
        ExtK Γ' n' (fun j => (leaf j).1) x.salts)
      n Γ (commitE sMT depth leaf) (commitEL sMT depth fun j => (leaf j).2) := by
  have h0 := late_leavesE sMT ((List.range (2 ^ depth)).map leaf) n Γ
    (fun z hz => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz; exact hpad j) hF
  rw [List.map_map] at h0
  refine Late.bind h0 fun n1 Γ1 x y h1 => ?_
  obtain ⟨rfl, a1, hF1, fr1, hK1, hl1⟩ := h1
  refine Late.bind (late_levelsE depth x.1 n1 Γ1) fun n2 Γ2 lv lv' h2 => Late.pure ?_
  obtain ⟨rfl, rfl, rfl⟩ := h2
  refine ⟨rfl, a1, hF1, fr1, fun j s d h => ?_⟩
  have hk := hK1 j s d h
  by_cases hj : j < 2 ^ depth
  · have hb : ((List.range (2 ^ depth)).map leaf).getD j (none, false) = leaf j := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simpa using hj), Option.getD_some]
      simp
    simpa only [hb] using hk
  · exfalso
    have h' : x.2.getD j none = some (s, d) := h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl1]; simpa using hj)] at h'
    exact absurd h' (by simp)

theorem late_openE {σ : Type} (t : TreeH lam) (j : ℕ) (b : Body L) (a : σ) {n : ℕ} {Γ : Cx lam K L}
    (hk : ∀ s d, t.salts.getD j none = some (s, d) → KSalt Γ b s ∧ Base Γ d) :
    Late (Same n Γ) n Γ (openE t j a) (openEL t j b a) := by
  unfold openE openEL
  cases h : t.salts.getD j none with
  | none => exact Late.pure ⟨rfl, rfl, rfl⟩
  | some sd =>
    obtain ⟨s, d⟩ := sd
    obtain ⟨h1, h2⟩ := hk s d h
    refine Late.reveal (fun u hu o pt hp => ?_) fun vs => Late.pure ⟨rfl, rfl, rfl⟩
    by_cases hus : u = s
    · rw [hus] at hp ⊢
      exact h1 o pt hp
    · rw [Ctx.set_ne_tok _ hus]
      rcases List.mem_cons.1 hu with h' | h'
      · exact absurd h' hus
      · rw [List.mem_singleton.1 h'] at hp ⊢
        exact h2 o pt hp

end Compile.Batch
