-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Tree.lean: the hash trees over prover messages, for the lemma on deferred programming
of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The library's token trees
(Compile/Batch/TokTree.lean: `leafT`, `nodeT`, `rnodeT`, `leavesT`, `commitT`, `openT`: the scheme's
own programs) obey the discipline with joint charges (CompileK/Defer2Safe.lean: `SafeO2`) at the two
vertex oracles, both children counting: ℓ2 := 2 λ; each under the hypotheses of its statement.

Definitions and theorems: the analogues for `SafeO2` of `safe_nodeT`, `safe_rnodeT`, `safe_pairUpT`,
`safe_levelsT`, `deps_PA`, `safe_leafT`, `safe_leavesT`, `TTOK`, `safe_commitT`, `safe_openT`
(Compile/Batch/DisciplineTree.lean). Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.
Tokens, marked evaluations, charged and further tokens: the head of Rom/Defer.lean. The vertex
oracles are `OracleName.node`, `OracleName.rnode` (`Jt`): an inner vertex is a marked evaluation charged to its left
child, with its right child as the one further token.

Main names:
  `PairR`, `LevR`: two neighbouring levels, all levels: at the vertex oracles a right child is a
    further token only of the evaluation charged to its left neighbour; a left child, a token of the
    top level, is no evaluation's further token there.
  `rdeps_PA`: under the hypotheses of its statement, every evaluation at a vertex oracle that holds
    a token beside or on the way from a leaf to the root as a further token is charged to a token of
    that set (the mirror of `deps_PA`).
  `TTUp d depth t`: a tree that stands, upwards: the same with the leaf's salt.
  `UpClosed.of_rdeps`: so such a set can be revealed in the sense of `UpClosed`.
  `rulesT K L lam p mG`: the library's `rulesB` with "a marked point lies at one of the ten oracles
    or at a further name for a later try below mG" (`osBG mG`) for "at one of the ten or at any
    further name": stricter in that one clause, equal in the others (the hypothesis of
    CompileK/SpecDefer2.lean needs finitely many classes; a tree has no tries: mG is a parameter
    here, for the chains' sake).

Why: the way upwards. Compile/Batch/DisciplineTree.lean follows a token down its charges
(`Deps d u l`: the tail and the further tokens of every evaluation charged to u are in l). Here the
converse (`RDep`).
At the marking: `safe_nodeT` asks of the right child b only that it exists and is not a; its caller
has more: every token of a level is untouched, of λ bits, and the level has no repetition (`Ready`):
`safe2_nodeT` takes that in: b unshown, in no earlier point, |a| + |b| = 2 λ.

Limits: this file says nothing on request trees as wholes (`rnodeT` alone is here), the trees over
encoded indices, chains, the finish, any later storey.
-/
import CompileK.Defer2Safe
import Compile.Batch.DisciplineTree

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ}

/-- the rules of the scheme with batches, with the further names for later tries below mG only: so
that the oracles with marked evaluations are finitely many -/
def rulesT (K : ℕ) (L : BatchProtocol I X) (lam : ℕ) (p : Params) (mG : ℕ) : Rules (spec lam K L) :=
  { rulesB K L lam p with Mk := fun o _ => o ∈ osBG mG }

theorem osB_sub (mG : ℕ) {o : OracleName} (h : o ∈ osB) : o ∈ osBG mG := Finset.mem_union_left _ h

theorem osBG_mk {mG : ℕ} {o : OracleName} (h : o ∈ osBG mG) : o ∈ osB ∨ ∃ t k, o = OracleName.fbw t k := by
  rcases Finset.mem_union.1 h with h | h
  · exact Or.inl h
  · rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨_, _, rfl⟩
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨_, _, rfl⟩
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 h
      exact Or.inr ⟨_, _, rfl⟩

theorem SafeO2.rules_mono {S : OSpec} {sp : Split S} {α : Type} {Rl Rl' : Rules S} {Jo : S.ι → Bool}
    {ℓ2 : S.ι → ℕ} (hPl : ∀ o q, Rl.Pl o q → Rl'.Pl o q) (hMk : ∀ o q, Rl.Mk o q → Rl'.Mk o q)
    (hb : ∀ o, Rl'.bits o ≤ Rl.bits o) {Q : α → DSt S → Prop} (c : Step S sp α) :
    ∀ d, SafeO2 Rl Jo ℓ2 c d Q → SafeO2 Rl' Jo ℓ2 c d Q := by
  induction c with
  | pure a => exact fun d hd => hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hPl _ _ hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
    exact fun d ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨h1, h2, h3, le_trans (hb o) h4, hMk _ _ h5, h6, fun r T => ih _ _ _ (h7 r T)⟩
  | reveal ts k ih => exact fun d ⟨h1, h2, h3⟩ => ⟨h1, h2, fun T => ih _ _ (h3 T)⟩

/-- the oracles with joint charges: the inner vertices of token trees and of request trees -/
def Jt : OracleName → Bool := fun o => decide (o = OracleName.node ∨ o = OracleName.rnode)

/-- both children count -/
def ellT (lam : ℕ) : OracleName → ℕ := fun _ => 2 * lam

/-- what is `SafeO2` at `rulesT` is `SafeO2` at `rulesB` -/
theorem safe2_toB {α : Type} {Q : α → DSt (spec lam K L) → Prop}
    (c : Step (spec lam K L) (split lam K L) α) (d : DSt (spec lam K L))
    (h : SafeO2 (rulesT K L lam p mG) Jt (ellT lam) c d Q) :
    SafeO2 (rulesB K L lam p) Jt (ellT lam) c d Q :=
  SafeO2.rules_mono (Rl := rulesT K L lam p mG)
    (Rl' := rulesB K L lam p) (fun _ _ h => h) (fun _ _ h => osBG_mk h) (fun _ => le_rfl) c d h

/-- the state is orderly, both ways -/
def TidyBoth (p : Params) (mG : ℕ) (d : DSt (spec lam K L)) : Prop :=
  TidyO (rulesT K L lam p mG) d ∧ Tidy2 Jt (ellT lam) d

/-- every evaluation at a vertex oracle that holds b among its further tokens is charged to a token
in A -/
def RDep (d : DSt (spec lam K L)) (b : Tok) (A : Tok → Prop) : Prop :=
  ∀ e ∈ d.evs, Jt e.o = true → b ∈ e.others → A e.charged

theorem Untouched.rnone {d : DSt (spec lam K L)} {t : Tok} (h : Untouched d t) {A : Tok → Prop} :
    RDep d t A :=
  fun e he _ hb => absurd hb (h.not_held e he).2

theorem RDep.mono {d : DSt (spec lam K L)} {b : Tok} {A A' : Tok → Prop}
    (h : RDep d b A) (hA : ∀ c, A c → A' c) : RDep d b A' :=
  fun e he hJ hb => hA _ (h e he hJ hb)

theorem RDep.keeps {d d' : DSt (spec lam K L)} {b : Tok} {A Ch R : Tok → Prop} {e M : OracleName → ℕ}
    (h : RDep d b A) (hlt : b < d.vals.length) (hg : GrowsO Ch R e M d d') (hc : ¬ Ch b) :
    RDep d' b A := by
  intro e' he' hJ hb
  rcases hg.evs e' he' with ⟨e₀, he₀, ho, hch, hot, _⟩ | ⟨_, _, hnew⟩
  · rw [← hch]
    exact h e₀ he₀ (by rw [ho]; exact hJ) (by rw [hot]; exact hb)
  · rcases hnew b hb with h1 | h1
    · exact absurd h1 hc
    · exact absurd hlt (Nat.not_lt.mpr h1)

/-- what one inner node leaves behind, both ways -/
def NodePost2 (p : Params) (mG : ℕ) (o : OracleName) (a b : Tok) (d : DSt (spec lam K L))
    (c : Tok) (d' : DSt (spec lam K L)) : Prop :=
  TidyBoth p mG d' ∧ Run (fun t => t = a) (fun t => t = a ∨ t = b) NoTok zr (cnt1 o 1) d d' ∧
  c = d.vals.length ∧ Deps d' a [c, b] ∧ Untouched d' c ∧ Len d' c lam ∧ Sealed d' a ∧ Sealed d' b ∧
  RDep d' b (fun x => x = a) ∧ RDep d' a (fun _ => False)

/-- two neighbouring levels, upwards, at the vertex oracles: a right child is a further token only
of the evaluation charged to its left neighbour; a left child is nobody's further token -/
def PairR (d : DSt (spec lam K L)) (l l' : List Tok) : Prop :=
  ∀ i < l'.length,
    RDep d (l.getD (2 * i + 1) 0) (fun x => x = l.getD (2 * i) 0) ∧
    RDep d (l.getD (2 * i) 0) (fun _ => False)

def LevR (d : DSt (spec lam K L)) : List (List Tok) → Prop
  | [] => True
  | [top] => ∀ a ∈ top, RDep d a (fun _ => False)
  | l :: l' :: ls => PairR d l l' ∧ LevR d (l' :: ls)

theorem node_post2 (o : OracleName) (hJo : Jt o = true) (hmk : o ∈ osBG mG)
    (hbo : (rulesT K L lam p mG).bits o = lam) (htl : (split lam K L).tl o = lam) (a b : Tok)
    (d : DSt (spec lam K L)) (hd : TidyBoth p mG d) (ha : Untouched d a) (hb : Untouched d b)
    (hab : a ≠ b) (hl : Len d a lam) (hlb : Len d b lam)
    (pt : Bits → List Bits → (spec lam K L).Dom o)
    (hpt : ∀ v v' x x', pt v [x] = pt v' [x'] → v = v' ∧ x = x')
    (inj : ∀ vs, Function.Injective fun v => pt v vs) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
      (Step.marked (S := spec lam K L) (sp := split lam K L) o a [b] pt inj fun _ d => Step.pure d)
      d (NodePost2 p mG o a b d) := by
  have hus : ∀ u ∈ [b], u < d.vals.length :=
    fun u hu => by rw [List.mem_singleton.mp hu]; exact hb.lt
  have htu : a ∉ [b] := fun h => hab (List.mem_singleton.mp h)
  have hbit : (rulesT K L lam p mG).bits o ≤ (d.val a).length := by
    rw [hbo]; exact le_of_eq hl.2.symm
  have hJM : Jt o = true → JMark (ellT lam) d o a [b] pt := fun _ =>
    ⟨hpt, b, rfl, hb.not_shown, fun e he _ => ⟨(hb.not_held e he).1.symm, (hb.not_held e he).2⟩,
      by show 2 * lam ≤ _; rw [hl.2, hlb.2]; omega⟩
  refine ⟨hus, htu, ha.freeAt _, hbit, hmk, hJM,
    fun r T =>
      ⟨⟨hd.1.mark hus htu (ha.freeAt _) _ hbit hmk r T,
          Tidy2.mark hd.1 hd.2 hus (ha.freeAt _) hJM _ r T⟩,
        ?_, rfl,
    (ha.deps []).of_mark _ r T, Untouched.of_tail hd.1 ha.lt hus _ r T, (by have h := Len.of_tail (sp := split lam K L) d o a [b] (pt (d.val a) ([b].map d.val)) r T; rw [htl] at h; exact h), ?_, ?_, ?_, ?_⟩⟩
  · exact (Run.ofMark (R := NoTok) (e := zr) d o a [b] _ r T).mono (fun _ h => Or.inl h)
      (fun _ h => Or.inl (h.imp_right List.mem_singleton.mp)) (fun _ h => Or.inl h)
      (fun _ => le_rfl) (fun _ => le_rfl)
  · exact SealedW.of_mark (by rintro rfl; simp [Jt] at hJo) d a [b] _ r T (Or.inl rfl)
  · exact SealedW.of_mark (by rintro rfl; simp [Jt] at hJo) d a [b]
      _ r T (Or.inr (List.mem_singleton.mpr rfl))
  · intro e he _ hbe
    rcases List.mem_append.1 (show e ∈ d.evs ++ [_] from he) with he | he
    · exact absurd hbe (hb.not_held e he).2
    · rw [List.mem_singleton.1 he]
  · intro e he _ hae
    rcases List.mem_append.1 (show e ∈ d.evs ++ [_] from he) with he | he
    · exact absurd hae (ha.not_held e he).2
    · rw [List.mem_singleton.1 he] at hae
      exact hab (List.mem_singleton.1 hae)

theorem safe2_nodeT (a b : Tok) (d : DSt (spec lam K L)) (hd : TidyBoth p mG d) (ha : Untouched d a)
    (hb : Untouched d b) (hab : a ≠ b) (hl : Len d a lam) (hlb : Len d b lam) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (nodeT (lam := lam) (K := K) (L := L) a b)
      d (NodePost2 p mG OracleName.node a b d) :=
  node_post2 OracleName.node (by simp [Jt]) (osB_sub mG (by decide)) rfl rfl a b d hd ha hb hab hl hlb _
    (fun _ _ _ _ h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩) _

theorem safe2_rnodeT (a b : Tok) (d : DSt (spec lam K L)) (hd : TidyBoth p mG d)
    (ha : Untouched d a) (hb : Untouched d b) (hab : a ≠ b) (hl : Len d a lam) (hlb : Len d b lam) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (rnodeT (lam := lam) (K := K) (L := L) a b)
      d (NodePost2 p mG OracleName.rnode a b d) :=
  node_post2 OracleName.rnode (by simp [Jt]) (osB_sub mG (by decide)) rfl rfl a b d hd ha hb hab hl hlb _
    (fun _ _ _ _ h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩) _

section Levels2
variable (o : OracleName) (hN : Tok → Tok → St lam K L Tok)
  (H : ∀ (a b : Tok) (d : DSt (spec lam K L)), TidyBoth p mG d → Untouched d a → Untouched d b →
    a ≠ b → Len d a lam → Len d b lam →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (hN a b) d (NodePost2 p mG o a b d))

include H in
theorem safe2_pairUpT : ∀ (m : ℕ) (l : List Tok) (d : DSt (spec lam K L)),
    l.length = 2 * m → TidyBoth p mG d → Ready lam d l →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (pairUp hN l) d fun l' d' =>
      TidyBoth p mG d' ∧
      Run (fun t => t ∈ l) (fun t => t ∈ l) NoTok zr (cnt1 o m) d d' ∧
      l'.length = m ∧ PairOK d' l l' ∧
      Ready lam d' l' ∧ (∀ c ∈ l', d.vals.length ≤ c) ∧ (∀ x ∈ l, Sealed d' x) ∧ PairR d' l l'
  | 0, l, d, hlen, hd, _ => by
      obtain rfl : l = [] := List.length_eq_zero_iff.mp hlen
      exact ⟨hd, Run.refl d, rfl,
        fun i hi => absurd hi (Nat.not_lt_zero i),
        ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩,
        fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil,
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩
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
      show SafeO2 _ _ _ ((hN a b).bind fun c => (pairUp hN t).bind fun r => Step.pure (c :: r)) d _
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (H a b d hd ha.1 hb.1 hab ha.2 hb.2))
      rintro c d₁ ⟨hd₁, hr₁, rfl, hdep, huc, hlc, hsa, hsb, hRb, hRa⟩
      have hrt : Ready lam d₁ t :=
        ⟨fun x hx =>
            ⟨((hr.1 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).1).grows hr₁.grows
                (fun h => h.elim (fun h => hat (h ▸ hx)) (fun h => hnd2.1 (h ▸ hx))) (fun h => h),
              ((hr.1 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))).2).grows hr₁.grows⟩,
          hnd2.2⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_pairUpT m t d₁ hlt hd₁ hrt))
      rintro r d₂ ⟨hd₂, hr₂, hlen₂, hp₂, hrd₂, hnew₂, hse₂, hpR₂⟩
      have hct : d.vals.length ∉ t := fun h =>
        absurd ((hr.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))).1.lt) (lt_irrefl _)
      refine ⟨hd₂, ?_, by simp [hlen₂], ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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
      · intro i hi
        cases i with
        | zero =>
          exact ⟨hRb.keeps (lt_of_lt_of_le hb.1.lt hr₁.length_le) hr₂.grows hnd2.1,
            hRa.keeps (lt_of_lt_of_le ha.1.lt hr₁.length_le) hr₂.grows hat⟩
        | succ i =>
          have hi' : i < r.length := by simpa using hi
          have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
          have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
          rw [e2, e1, List.getD_cons_succ, List.getD_cons_succ,
            List.getD_cons_succ, List.getD_cons_succ]
          exact hpR₂ i hi'

include H in
theorem safe2_levelsT : ∀ (k : ℕ) (l : List Tok) (d : DSt (spec lam K L)),
    l.length = 2 ^ k → TidyBoth p mG d → Ready lam d l →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (levelsM hN k l) d fun lv d' =>
      TidyBoth p mG d' ∧
      Run (fun t => t ∈ l) (fun t => t ∈ l) NoTok zr (cnt1 o l.length) d d' ∧
      (∃ ls, lv = l :: ls) ∧
      LevOK lam d' lv ∧ (∀ l' ∈ lv, ∀ c ∈ l', c < d'.vals.length ∧ (c ∈ l ∨ d.vals.length ≤ c)) ∧
      (Untouched d' (rootOf lv) ∧ Len d' (rootOf lv) lam) ∧
      (rootOf lv ∈ l ∨ d.vals.length ≤ rootOf lv) ∧
      (∀ l' ∈ lv, ∀ c ∈ l', c = rootOf lv ∨ Sealed d' c) ∧ LevR d' lv
  | 0, l, d, hlen, hd, hr => by
      obtain ⟨a, rfl⟩ : ∃ a, l = [a] := List.length_eq_one_iff.mp (by simpa using hlen)
      exact ⟨hd, Run.refl d, ⟨[], rfl⟩, hr, fun l' hl' c hc => by
          rw [List.mem_singleton.mp hl'] at hc
          exact ⟨(hr.1 c hc).1.lt, Or.inl hc⟩, hr.1 a List.mem_cons_self,
            Or.inl List.mem_cons_self, fun l' hl' c hc => by
          rw [List.mem_singleton.mp hl'] at hc
          exact Or.inl (List.mem_singleton.mp hc), fun x hx => (hr.1 x hx).1.rnone⟩
  | k + 1, l, d, hlen, hd, hr => by
      show SafeO2 _ _ _
        ((pairUp hN l).bind fun u => (levelsM hN k u).bind fun r => Step.pure (l :: r)) d _
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d
          (safe2_pairUpT o hN H (2 ^ k) l d (by rw [hlen, pow_succ, Nat.mul_comm]) hd hr))
      rintro u d₁ ⟨hd₁, hr₁, hlu, hp₁, hru, hnew, hse₁, hpR₁⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_levelsT k u d₁ hlu hd₁ hru))
      rintro r d₂ ⟨hd₂, hr₂, ⟨ls, rfl⟩, hlv, hall, hroot, hrn, hse₂, hLR⟩
      have hlu' : ∀ x ∈ l, x ∉ u := fun x hx hxu =>
        absurd (hnew x hxu) (Nat.not_le.mpr (hr.1 x hx).1.lt)
      have hmem : ∀ i, i < l.length → l.getD i 0 ∈ l := fun i hi => getD_mem hi
      have hl2 : l.length = 2 * u.length := by rw [hlen, hlu, pow_succ, Nat.mul_comm]
      refine ⟨hd₂, ?_, ⟨_, rfl⟩, ⟨fun i hi => ?_, hl2, hlv⟩, ?_, ?_, ?_, ?_, ⟨fun i hi => ?_, hLR⟩⟩
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
      · have h0 := hmem (2 * i) (by omega)
        have h1 := hmem (2 * i + 1) (by omega)
        exact ⟨(hpR₁ i hi).1.keeps (lt_of_lt_of_le (hr.1 _ h1).1.lt hr₁.length_le) hr₂.grows
            (hlu' _ h1),
          (hpR₁ i hi).2.keeps (lt_of_lt_of_le (hr.1 _ h0).1.lt hr₁.length_le) hr₂.grows (hlu' _ h0)⟩

end Levels2

/-! ## The way from a leaf to the root, upwards -/

/-- Under the hypotheses below: every evaluation at a vertex oracle that holds a token beside or on
the way from a leaf to the root as a further token is charged to a token of that set. -/
theorem rdeps_PA (d : DSt (spec lam K L)) :
    ∀ (lv : List (List Tok)) (j : ℕ), LevOK lam d lv → LevR d lv → j < (lv.headD []).length →
      ∀ u ∈ PA lv j, RDep d u (fun c => c ∈ PA lv j)
  | [], _, _, _, _, _, hu => absurd hu List.not_mem_nil
  | [top], j, _, hR, hj, u, hu => by
      have : u = top.getD j 0 := List.mem_singleton.mp hu
      exact (hR u (this ▸ getD_mem hj)).mono fun _ h => h.elim
  | l :: l' :: ls, j, h, hR, hj, u, hu => by
      have hj' : j < l.length := hj
      have hl2 := h.2.1
      have hi : j / 2 < l'.length := by omega
      obtain ⟨hRr, hRl⟩ := hR.1 (j / 2) hi
      by_cases hev : j % 2 = 0
      · have e0 : 2 * (j / 2) = j := by omega
        rw [e0] at hRr hRl
        rcases mem_PA_cons.mp hu with rfl | rfl | hu
        · rw [if_pos hev]
          exact hRr.mono fun c hc => hc ▸ mem_PA_cons.mpr (Or.inr (Or.inl rfl))
        · exact hRl.mono fun _ h => h.elim
        · exact (rdeps_PA d (l' :: ls) (j / 2) h.2.2 hR.2 hi u hu).mono fun v hv =>
            mem_PA_cons.mpr (Or.inr (Or.inr hv))
      · have e0 : 2 * (j / 2) = j - 1 := by omega
        have e1 : 2 * (j / 2) + 1 = j := by omega
        rw [e1] at hRr
        rw [e0] at hRr hRl
        rcases mem_PA_cons.mp hu with rfl | rfl | hu
        · rw [if_neg hev]
          exact hRl.mono fun _ h => h.elim
        · exact hRr.mono fun c hc => hc ▸ mem_PA_cons.mpr (Or.inl (by rw [if_neg hev]))
        · exact (rdeps_PA d (l' :: ls) (j / 2) h.2.2 hR.2 hi u hu).mono fun v hv =>
            mem_PA_cons.mpr (Or.inr (Or.inr hv))

theorem UpClosed.of_rdeps {d : DSt (spec lam K L)} {ts : List Tok}
    (h : ∀ u ∈ ts, RDep d u (fun c => c ∈ ts)) : UpClosed Jt d ts :=
  fun e he hJ b hb hbt => Or.inl (h b hbt e he hJ hb)

/-! ## Trees over prover messages -/

theorem safe2_leafT (b : Body L) (d : DSt (spec lam K L)) (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leafT (lam := lam) (K := K) p.sMT b) d fun x d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok NoTok zr (cnt1 OracleName.leaf 1) d d' ∧
      x.1 = d.vals.length ∧ x.2 = d.vals.length + 1 ∧
      x.1 < d'.vals.length ∧ Deps d' x.1 [x.2] ∧ Untouched d' x.2 ∧ Len d' x.2 lam ∧
      Sealed d' x.1 ∧ RDep d' x.1 (fun _ => False) := by
  unfold leafT
  refine fun u => ?_
  have h1 := hd.1.fresh (List.ofFn u)
  have h12 := Tidy2.fresh hd.1 hd.2 (List.ofFn u)
  have hu := Untouched.of_fresh hd.1 (List.ofFn u)
  have hJM : Jt OracleName.leaf = true →
      JMark (ellT lam) (afterFresh d (List.ofFn u)) OracleName.leaf d.vals.length
        [] (fun v _ => (⟨b, v⟩ : LeafIn L)) :=
    fun h => by simp [Jt] at h
  have hl := Len.of_fresh d u
  have hno : ∀ v ∈ ([] : List Tok), v < (afterFresh d (List.ofFn u)).vals.length := fun _ h =>
    absurd h List.not_mem_nil
  have hb : (rulesT K L lam p mG).bits OracleName.leaf ≤
      ((afterFresh d (List.ofFn u)).val d.vals.length).length :=
    le_of_eq hl.2.symm
  have hmk : OracleName.leaf ∈ osBG mG := osB_sub mG (by decide)
  refine ⟨hno, List.not_mem_nil, hu.freeAt OracleName.leaf, hb, hmk, hJM, fun r T => ?_⟩
  have hlen : (afterFresh d (List.ofFn u)).vals.length = d.vals.length + 1 := length_afterFresh _ _
  refine ⟨⟨h1.mark hno List.not_mem_nil (hu.freeAt OracleName.leaf) _ hb hmk r T,
      Tidy2.mark h1 h12 hno (hu.freeAt OracleName.leaf) hJM _ r T⟩,
    ?_, rfl, hlen, ?_, ?_, ?_, ?_, SealedW.of_mark (by simp) _ _ [] _ r T (Or.inl rfl), ?_⟩
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
  · intro e he _ hse
    rcases List.mem_append.1 (show e ∈ (afterFresh d (List.ofFn u)).evs ++ [_] from he) with he | he
    · exact absurd hse (hu.not_held e he).2
    · rw [List.mem_singleton.1 he] at hse
      exact absurd hse List.not_mem_nil

theorem safe2_leavesT : ∀ (l : List (Body L)) (d : DSt (spec lam K L)), TidyBoth p mG d →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (leavesT (lam := lam) (K := K) p.sMT l) d fun x d' =>
      TidyBoth p mG d' ∧
      Run NoTok NoTok NoTok zr (cnt1 OracleName.leaf l.length) d d' ∧
      x.1.length = l.length ∧
      Ready lam d' x.1 ∧
      (∀ c ∈ x.1, d.vals.length ≤ c) ∧
      ∀ i < l.length,
        Deps d' (x.2.getD i 0) [x.1.getD i 0] ∧
        d.vals.length ≤ x.2.getD i 0 ∧
        x.2.getD i 0 < d'.vals.length ∧
        x.2.getD i 0 ∉ x.1 ∧
        Sealed d' (x.2.getD i 0) ∧
        RDep d' (x.2.getD i 0) (fun _ => False)
  | [], d, hd =>
    ⟨hd, Run.refl d, rfl, ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩,
      fun _ h => absurd h List.not_mem_nil, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | b :: t, d, hd => by
      show SafeO2 _ _ _
        ((leafT p.sMT b).bind fun x =>
          (leavesT p.sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
        d _
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_leafT b d hd))
      rintro ⟨s, dg⟩ d₁ ⟨hd₁, hr₁, hs, hdg, hslt, hdep, hun, hln, hss, hsR⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_leavesT t d₁ hd₁))
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
          refine ⟨hdep.keeps hslt hr₂.charges (fun h => h),
            le_of_eq hs'.symm,
            lt_of_lt_of_le hslt hr₂.length_le,
            fun h => ?_, hss.mono hr₂.keeps,
            RDep.keeps (show RDep d₁ s (fun _ => False) from hsR) hslt hr₂.grows (fun h => h)⟩
          rcases List.mem_cons.mp h with h | h
          · have h' : s = dg := h
            rw [hs', hdg'] at h'
            exact absurd h' (Nat.ne_of_lt (Nat.lt_succ_self _))
          · exact hsr h
        | succ i =>
          obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hs₂ i (by simpa using hi)
          refine ⟨a1, le_trans hr₁.length_le a2, a3, fun h => ?_, a5, a6⟩
          rcases List.mem_cons.mp h with h | h
          · have h' : r.2.getD i 0 = dg := h
            exact absurd a2 (Nat.not_le.mpr (h' ▸ hun.lt))
          · exact a4 h

/-- a tree that stands, upwards: for each leaf: who holds its salt, or a token beside or on its way
to the root, as a further token at a vertex oracle is charged to a token of that set -/
def TTUp (d : DSt (spec lam K L)) (depth : ℕ) (t : TTree) : Prop :=
  ∀ j < 2 ^ depth, ∀ u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j),
    RDep d u (fun c => c ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))

theorem TTUp.keeps {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree} {Ch R : Tok → Prop}
    {e M : OracleName → ℕ} (h : TTUp d depth t) (hok : TTOK d n₀ depth t) (hg : GrowsO Ch R e M d d')
    (hn : ∀ u, Ch u → u < n₀ ∨ d.vals.length ≤ u) :
    TTUp d' depth t := fun j hj u hu =>
  (h j hj u hu).keeps ((hok.open_ j hj).lt u hu) hg fun hcu => by
    rcases hn u hcu with h1 | h1
    · exact absurd (hok.new j hj u hu) (Nat.not_le.mpr h1)
    · exact absurd ((hok.open_ j hj).lt u hu) (Nat.not_lt.mpr h1)

theorem safe2_commitT (depth : ℕ) (leaf : ℕ → Body L)
    (d : DSt (spec lam K L)) (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (commitT (lam := lam) (K := K) p.sMT depth leaf) d fun t d' =>
      TidyBoth p mG d' ∧
      Run NoTok NoTok NoTok zr
        (fun o => cnt1 OracleName.leaf (2 ^ depth) o + cnt1 OracleName.node (2 ^ depth) o) d d' ∧
      TTOK d' d.vals.length depth t ∧ TTUp d' depth t ∧
      Untouched d' t.root ∧ d.vals.length ≤ t.root ∧
      ∀ j < 2 ^ depth, ∀ u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j),
          u = t.root ∨ Sealed d' u := by
  show SafeO2 _ _ _ ((leavesT p.sMT ((List.range (2 ^ depth)).map leaf)).bind fun x =>
    (levelsM nodeT depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree)) d _
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_leavesT _ d hd))
  rintro x d₁ ⟨hd₁, hr₁, hl₁, hrd₁, hnew₁, hs₁⟩
  have hlen : ((List.range (2 ^ depth)).map leaf).length = 2 ^ depth := by simp
  rw [hlen] at hl₁ hs₁ hr₁
  refine SafeO2.bind _ _ d₁
    (SafeO2.mono ?_ _ d₁
      (safe2_levelsT OracleName.node nodeT (fun a b d => safe2_nodeT a b d) depth x.1 d₁ hl₁ hd₁ hrd₁))
  rintro lv d₂ ⟨hd₂, hr₂, ⟨ls, rfl⟩, hlv, hall, hroot, hrn, hse₂, hLR⟩
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
    fun j hj u hu => ?_, hroot.1, ?_, fun j hj u hu => ?_⟩
  · obtain ⟨a1, a2, a3, a4, _, _⟩ := hs₁ j hj
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
  · rcases List.mem_cons.mp hu with rfl | hu
    · obtain ⟨_, _, a3, a4, _, a6⟩ := hs₁ j hj
      exact (a6.keeps a3 hr₂.grows a4).mono fun _ h => h.elim
    · exact (rdeps_PA d₂ (x.1 :: ls) j hlv hLR
          (by show j < x.1.length; rw [hl₁]; exact hj) u hu).mono
        fun v hv => List.mem_cons_of_mem _ hv
  · rcases hrn with h | h
    · exact hnew₁ _ h
    · exact le_trans hr₁.length_le h
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact Or.inr ((hs₁ j hj).2.2.2.2.1.mono hr₂.keeps)
    · obtain ⟨l, hl, hul⟩ :=
        exists_mem_of_mem_PA d₂ (x.1 :: ls) j hlv (by show j < x.1.length; rw [hl₁]; exact hj) u hu
      exact hse₂ l hl u hul

theorem safe2_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ)
    (d : DSt (spec lam K L)) (hd : TidyBoth p mG d)
    (hc : ClosedO d (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j)))
    (hu : UpClosed Jt d (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (openT (lam := lam) (K := K) (L := L) t j a) d fun _ d' =>
      TidyBoth p mG d' ∧
      Run NoTok NoTok (fun u => u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))
        zr zr d d' :=
  ⟨hc, hu, fun T => ⟨⟨hd.1.reveal hc T, Tidy2.reveal hd.2 hu T⟩, Run.ofReveal d _ T⟩⟩

end Compile.Batch.Disc
