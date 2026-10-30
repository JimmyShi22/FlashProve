-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineLoop.lean: the rules of deferred programming in a round with proof-of-work
bits: the search over nonces as one unit (words of this library: lean/GLOSSARY.md).

A Fiat-Shamir query with proof-of-work bits (`fbG`, Compile/Batch/Prover.lean) is a search: marked
queries that are all charged to one token and hold the same other tokens, at different oracles:
attempt 0 at `fb t`, attempt k + 1 at the ghost name `fbw t k`. Between two attempts the invariants
of the chains (Compile/Batch/DisciplineSlot.lean) do not hold: the charged token is sealed
(`SealedW`, Compile/Batch/DisciplineRun.lean) and is charged again. So nothing is asked inside a
search. It is described by where it starts and where it ends: `Tries sp t us d os tls d'`, with os
and the tails tls in the order of the attempts.

Part 1, generic in the family of oracles, has what follows from `Tries`, each under its own
hypotheses: the tails are the new tokens, the last tail the newest; the queries of d' are those of d
and one for each tail, and nothing is shown; t can still be charged at an oracle that is not among
os; the state stays orderly (`TidyO`), if t could be charged at the start at each of the oracles,
which are different; the last tail is untouched (`Untouched`, Compile/Batch/DisciplineKit.lean), has
its length and is not dead, the other tails are dead (`DeadW`); t and the others are sealed.

Part 2, the scheme: `safe_fbG`: the search obeys the rules from d, and ends in Q, if its tokens
exist, the charged token is none of the others, it can be charged at `fb t` and at every `fbw t j`,
it is long enough (`LoopPre`); and if what follows is safe from every state that `Tries` allows, for
what the search can pass on (`Kept`, Compile/Batch/ProverG.lean). dd, the tails of the failed
attempts, comes newest first: the tails in their order are dd.reverse ++ [tl].
-/
import Compile.Batch.DisciplineRun
import Compile.Batch.DisciplineCnt
import Compile.Batch.ProverG

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterMark mem_evs_afterMark cnt1 length_afterMark)

/-! ## Part 1. Generic -/

section Generic
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {t : Tok} {us : List Tok}

/-- d' comes from d by marked queries that are charged to t and hold the others us, at the oracles
os; tls: their tails. -/
inductive Tries (sp : Split S) (t : Tok) (us : List Tok) :
    DSt S → List S.ι → List Tok → DSt S → Prop
  | one (d : DSt S) (o : S.ι) (P : S.Dom o) (r : S.Rng o) (T : Table S) :
      Tries sp t us d [o] [d.vals.length] (afterMark sp d o t us P r T)
  | snoc {d d₁ : DSt S} {os : List S.ι} {tls : List Tok} (h : Tries sp t us d os tls d₁) (o : S.ι)
      (P : S.Dom o) (r : S.Rng o) (T : Table S) :
      Tries sp t us d (os ++ [o]) (tls ++ [d₁.vals.length]) (afterMark sp d₁ o t us P r T)

namespace Tries
variable {d d' : DSt S} {os : List S.ι} {tls : List Tok}

theorem length (h : Tries sp t us d os tls d') : d'.vals.length = d.vals.length + tls.length := by
  induction h with
  | one o P r T => exact length_afterMark d o t us P r T
  | snoc h o P r T ih =>
    rw [length_afterMark, ih, List.length_append, List.length_singleton, Nat.add_assoc]

theorem length_le (h : Tries sp t us d os tls d') : d.vals.length ≤ d'.vals.length :=
  h.length ▸ Nat.le_add_right _ _

theorem tail_ge (h : Tries sp t us d os tls d') : ∀ u ∈ tls, d.vals.length ≤ u := by
  induction h with
  | one o P r T => exact fun u hu => (List.mem_singleton.mp hu) ▸ le_rfl
  | snoc h o P r T ih =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact ih u hu
    · exact (List.mem_singleton.mp hu) ▸ h.length_le

theorem tail_lt (h : Tries sp t us d os tls d') : ∀ u ∈ tls, u < d'.vals.length := by
  induction h with
  | one o P r T =>
    intro u hu
    rw [length_afterMark, List.mem_singleton.mp hu]
    exact Nat.lt_succ_self _
  | snoc h o P r T ih =>
    intro u hu
    rw [length_afterMark]
    rcases List.mem_append.mp hu with hu | hu
    · exact Nat.lt_succ_of_lt (ih u hu)
    · exact (List.mem_singleton.mp hu) ▸ Nat.lt_succ_self _

/-- The last tail is the newest token; the other tails are smaller. -/
theorem last {l : List Tok} {tl : Tok} (h : Tries sp t us d os (l ++ [tl]) d') :
    tl + 1 = d'.vals.length ∧ ∀ u ∈ l, u < tl := by
  generalize hq : l ++ [tl] = q at h
  cases h with
  | one o P r T =>
    have e := List.append_inj' (s₁ := l) (t₁ := [tl]) (s₂ := []) (t₂ := [d.vals.length]) hq rfl
    rw [length_afterMark, e.1, List.singleton_inj.mp e.2]
    exact ⟨rfl, fun u hu => absurd hu List.not_mem_nil⟩
  | snoc h₁ o P r T =>
    have e := List.append_inj' hq rfl
    rw [length_afterMark, e.1, List.singleton_inj.mp e.2]
    exact ⟨rfl, h₁.tail_lt⟩

theorem mem_evs (h : Tries sp t us d os tls d') :
    ∀ e ∈ d'.evs, e ∈ d.evs ∨ (e.charged = t ∧ e.others = us ∧ e.tail ∈ tls ∧ e.o ∈ os) := by
  induction h with
  | one o P r T =>
    intro e he
    rcases mem_evs_afterMark he with he | rfl
    · exact Or.inl he
    · exact Or.inr ⟨rfl, rfl, List.mem_singleton.mpr rfl, List.mem_singleton.mpr rfl⟩
  | snoc h o P r T ih =>
    intro e he
    rcases mem_evs_afterMark he with he | rfl
    · exact (ih e he).imp_right fun ⟨a, b, c, f⟩ =>
        ⟨a, b, List.mem_append_left _ c, List.mem_append_left _ f⟩
    · exact Or.inr
        ⟨rfl, rfl,
          List.mem_append_right _ (List.mem_singleton.mpr rfl),
          List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

theorem old (h : Tries sp t us d os tls d') : ∀ e ∈ d.evs, e ∈ d'.evs := by
  induction h with
  | one o P r T => exact fun e he => List.mem_append_left _ he
  | snoc h o P r T ih => exact fun e he => List.mem_append_left _ (ih e he)

/-- each tail has its query -/
theorem has (h : Tries sp t us d os tls d') :
    ∀ u ∈ tls, ∃ e ∈ d'.evs, e.tail = u ∧ e.charged = t ∧ e.others = us ∧ e.o ∈ os := by
  induction h with
  | one o P r T =>
    intro u hu
    exact ⟨⟨o, P, r, t, us, d.vals.length, false⟩,
      List.mem_append_right _ (List.mem_singleton.mpr rfl), (List.mem_singleton.mp hu).symm,
      rfl, rfl, List.mem_singleton.mpr rfl⟩
  | @snoc d₁ os tls h o P r T ih =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨e, he, a, b, c, f⟩ := ih u hu
      exact ⟨e, List.mem_append_left _ he, a, b, c, List.mem_append_left _ f⟩
    · exact ⟨⟨o, P, r, t, us, d₁.vals.length, false⟩,
        List.mem_append_right _ (List.mem_singleton.mpr rfl),
        (List.mem_singleton.mp hu).symm,
        rfl, rfl,
        List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

theorem shown (h : Tries sp t us d os tls d') : d'.shown = d.shown := by
  induction h with
  | one o P r T => rfl
  | snoc h o P r T ih => exact ih

theorem ne_nil (h : Tries sp t us d os tls d') : os ≠ [] := by
  cases h with
  | one o P r T => exact List.cons_ne_nil _ _
  | snoc h o P r T => exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- What the search does, as a run. -/
theorem run {R : Tok → Prop} {e : S.ι → ℕ} (h : Tries sp t us d os tls d') :
    Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) R e (fun o => os.count o) d d' := by
  induction h with
  | one o P r T =>
    refine (Run.ofMark (R := R) (e := e) d o t us P r T).mono (fun _ h => Or.inl h)
      (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ => le_rfl) fun o' => ?_
    unfold cnt1
    split
    · rename_i e; rw [e, List.count_singleton_self]
    · exact Nat.zero_le _
  | @snoc d₁ os tls h o P r T ih =>
    refine ih.trans (e₂ := fun _ => 0) (Run.ofMark (R := R) d₁ o t us P r T) (fun _ h => Or.inl h)
      (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ => le_rfl) fun o' => ?_
    rw [List.count_append]
    refine Nat.add_le_add_left ?_ _
    unfold cnt1
    split
    · rename_i e; rw [e, List.count_singleton_self]
    · exact Nat.zero_le _

/-- t can still be charged at an oracle at which the search has not charged it -/
theorem freeAt (h : Tries sp t us d os tls d') {o : S.ι} (hf : FreeAt d o t) (ho : o ∉ os) :
    FreeAt d' o t where
  lt := lt_of_lt_of_le hf.lt h.length_le
  not_shown := h.shown ▸ hf.not_shown
  fresh := fun e he heo => by
    rcases h.mem_evs e he with he | ⟨_, _, _, hm⟩
    · exact hf.fresh e he heo
    · exact absurd (heo ▸ hm) ho

/-- Under the hypotheses below: the state stays orderly. -/
theorem tidy (h : Tries sp t us d os tls d') (hd : TidyO Rl d) (hus : ∀ u ∈ us, u < d.vals.length)
    (htu : t ∉ us) (hf : ∀ o ∈ os, FreeAt d o t) (hnd : os.Nodup) {n : ℕ} (hl : Len d t n)
    (hb : ∀ o ∈ os, Rl.bits o ≤ n) (hP : ∀ o ∈ os, ∀ P, Rl.Mk o P) : TidyO Rl d' := by
  induction h with
  | one o P r T =>
    exact hd.mark hus htu (hf o (List.mem_singleton.mpr rfl)) P
      (hl.2 ▸ hb o (List.mem_singleton.mpr rfl)) (hP o (List.mem_singleton.mpr rfl) P) r T
  | @snoc d₁ os tls h o P r T ih =>
    have hnd' := List.nodup_append.mp hnd
    have ho : o ∉ os := fun hm => hnd'.2.2 o hm o (List.mem_singleton.mpr rfl) rfl
    have hd₁ := ih (fun o' ho' => hf o' (List.mem_append_left _ ho')) hnd'.1
      (fun o' ho' => hb o' (List.mem_append_left _ ho'))
      (fun o' ho' => hP o' (List.mem_append_left _ ho'))
    have hl₁ : Len d₁ t n := hl.grows (h.run (R := fun _ => False) (e := fun _ => 0)).grows
    exact hd₁.mark (fun u hu => lt_of_lt_of_le (hus u hu) h.length_le) htu
      (h.freeAt (hf o (List.mem_append_right _ (List.mem_singleton.mpr rfl))) ho) P
      (hl₁.2 ▸ hb o (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
      (hP o (List.mem_append_right _ (List.mem_singleton.mpr rfl)) P) r T

/-- Under the hypotheses below: the last tail is untouched. -/
theorem untouched_last {l : List Tok} {tl : Tok} (h : Tries sp t us d os (l ++ [tl]) d')
    (hd : TidyO Rl d) (ht : t < d.vals.length) (hus : ∀ u ∈ us, u < d.vals.length) :
    Untouched d' tl where
  lt := h.tail_lt tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  not_shown := fun hs =>
    absurd (hd.shown_lt _ (h.shown ▸ hs))
      (Nat.not_lt.mpr (h.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))))
  not_held := fun e he => by
    have hge := h.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    rcases h.mem_evs e he with he | ⟨a, b, _, _⟩
    · exact ⟨fun hc => absurd (hc ▸ hd.charged_lt e he) (Nat.not_lt.mpr hge),
        fun hu => absurd (hd.others_lt e he _ hu) (Nat.not_lt.mpr hge)⟩
    · exact ⟨fun hc => absurd ((a.symm.trans hc) ▸ ht) (Nat.not_lt.mpr hge),
        fun hu => absurd (hus _ (b ▸ hu)) (Nat.not_lt.mpr hge)⟩

/-- the last tail has the length of the tails, if all oracles of the search have tails of one length
-/
theorem len_last {l : List Tok} {tl : Tok} {n : ℕ}
    (h : Tries sp t us d os (l ++ [tl]) d') (hn : ∀ o ∈ os, sp.tl o = n) : Len d' tl n := by
  generalize hq : l ++ [tl] = q at h
  cases h with
  | one o P r T =>
    have e := List.append_inj' (s₁ := l) (t₁ := [tl]) (s₂ := []) (t₂ := [d.vals.length]) hq rfl
    rw [List.singleton_inj.mp e.2, ← hn o (List.mem_singleton.mpr rfl)]
    exact Len.of_tail d o t us P r T
  | @snoc d₁ os₁ tls₁ h₁ o P r T =>
    have e := List.append_inj' hq rfl
    rw [List.singleton_inj.mp e.2, ← hn o (List.mem_append_right _ (List.mem_singleton.mpr rfl))]
    exact Len.of_tail d₁ o t us P r T

theorem not_dead_last {W : S.ι → Prop} {l : List Tok} {tl : Tok}
    (h : Tries sp t us d os (l ++ [tl]) d') (hd' : TidyO Rl d') : ¬ DeadW W d' tl :=
  not_deadW_last hd' (le_of_eq h.last.1.symm)

/-- The other tails are dead (if no oracle of the search is in W). -/
theorem dead {W : S.ι → Prop} {l : List Tok} {tl : Tok}
    (h : Tries sp t us d os (l ++ [tl]) d') (hW : ∀ o ∈ os, ¬ W o) :
    ∀ u ∈ l, DeadW W d' u := fun u hu => by
  obtain ⟨e, he, a1, a2, _, a4⟩ := h.has u (List.mem_append_left _ hu)
  obtain ⟨e', he', b1, b2, _, _⟩ := h.has tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  exact ⟨e, he, e', he', a1, hW _ a4, b2.trans a2.symm, b1 ▸ h.last.2 u hu⟩

/-- The charged token and the others are sealed (if no oracle of the search is in W). -/
theorem sealed {W : S.ι → Prop} (h : Tries sp t us d os tls d') (hW : ∀ o ∈ os, ¬ W o)
    {u : Tok} (hu : u = t ∨ u ∈ us) : SealedW W d' u := by
  cases h with
  | one o P r T => exact SealedW.of_mark (hW o (List.mem_singleton.mpr rfl)) d t us P r T hu
  | @snoc d₁ os₁ tls₁ h₁ o P r T =>
    exact SealedW.of_mark
      (hW o (List.mem_append_right _ (List.mem_singleton.mpr rfl))) d₁ t us P r T hu

end Tries

end Generic

/-! ## Part 2. The scheme: the search and the rules -/

section Scheme
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {β C P : Type} {chal : Blk lam K → C}
  {t : Tag} {i : ℕ} {tk : Tok} {us : List Tok} {root : Option Tok}
  {hd : List Bits → Bits → Head lam X} {hinj : ∀ vs, Function.Injective (hd vs)}
  {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}

theorem fbw_not_mem_osTry (t : Tag) (j : ℕ) : OracleName.fbw t j ∉ osTry t j := fun h => by
  rcases mem_osTry.mp h with e | ⟨k, hk, e⟩
  · cases e
  · exact absurd (OracleName.fbw.inj e).2 (Nat.ne_of_gt hk)

/-- what every attempt of a search needs of the state in which the search starts -/
structure LoopPre (p : Params) (d : DSt (spec lam K L)) (t : Tag) (tk : Tok) (vs : List Tok) :
    Prop where
  lt : ∀ u ∈ vs, u < d.vals.length
  not_mem : tk ∉ vs
  free : FreeAt d (OracleName.fb t) tk
  freeW : ∀ j, FreeAt d (OracleName.fbw t j) tk
  bits : min p.sFS lam ≤ (d.val tk).length

theorem LoopPre.free_all {d : DSt (spec lam K L)} {vs : List Tok}
    (h : LoopPre p d t tk vs) {n : ℕ} :
    ∀ o ∈ osTry t n, FreeAt d o tk := fun o ho => by
  rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩
  · exact h.free
  · exact h.freeW k

/-- a later attempt, from a state that the search has reached -/
theorem safe_fbTw {d d₁ : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList)) {j : ℕ}
    {tls : List Tok} (hT : Tries (split lam K L) tk (us ++ root.toList) d (osTry t j) tls d₁)
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β)
    (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ bl d',
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t (j + 1))
        (tls ++ [d₁.vals.length]) d' →
      SafeO (rulesB K L lam p) (k bl d₁.vals.length) d' Q) :
    SafeO (rulesB K L lam p) (fbTw t j i tk us root hd hinj pl k) d₁ Q := by
  have hl : Len d₁ tk (d.val tk).length :=
    (show Len d tk (d.val tk).length from ⟨h.free.lt, rfl⟩).grows
      (hT.run (R := fun _ => False) (e := fun _ => 0)).grows
  refine ⟨fun u hu => lt_of_lt_of_le (h.lt u hu) hT.length_le, h.not_mem,
    hT.freeAt (h.freeW j) (fbw_not_mem_osTry t j), ?_, fbw_mk t j, fun r T => ?_⟩
  · show min p.sFS lam ≤ _
    rw [hl.2]
    exact h.bits
  · exact hk _ _ (osTry_succ t j ▸ Tries.snoc hT (OracleName.fbw t j) _ r T)

theorem safe_fbW {d : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList)) (g : GrW C P)
    (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ m dd bl tl d', dd.length = m → m ≤ g.more →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t m) (dd.reverse ++ [tl]) d' →
      SafeO (rulesB K L lam p) (k m dd bl tl) d' Q) :
    ∀ (n j : ℕ) (dd : List Tok) (d₁ : DSt (spec lam K L)), dd.length = j + 1 → j + 1 + n = g.more →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t j) dd.reverse d₁ →
      SafeO (rulesB K L lam p) (fbW g chal t i tk us root hd hinj emb α k n j dd) d₁ Q
  | 0, j, dd, d₁, h1, h2, hT =>
    safe_fbTw h hT _ _ Q fun bl d' hT' => hk _ _ bl _ d' h1 (by omega) hT'
  | n + 1, j, dd, d₁, h1, h2, hT => safe_fbTw h hT _ _ Q fun bl d' hT' => by
      split
      · exact hk _ _ bl _ d' h1 (by omega) hT'
      · exact safe_fbW h g k Q hk n (j + 1) (d₁.vals.length :: dd) d' (by simp [h1])
          (by omega) (by rw [List.reverse_cons]; exact hT')

/-- the first attempt -/
theorem safe_fbT0 {d : DSt (spec lam K L)}
    (h : LoopPre p d t tk (us ++ root.toList)) (pl : PlainPart (shapeOf L t) (annOf L t))
    (k : Blk lam K → Tok → St lam K L β) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ bl d', Tries (split lam K L) tk (us ++ root.toList) d (osTry t 0) [d.vals.length] d' →
      SafeO (rulesB K L lam p) (k bl d.vals.length) d' Q) :
    SafeO (rulesB K L lam p) (fbT t i tk us root hd hinj pl k) d Q :=
  ⟨h.lt, h.not_mem, h.free, h.bits, fb_mk t, fun r T => hk _ _ (Tries.one d (OracleName.fb t) _ r T)⟩

/-- Under `LoopPre`: a Fiat-Shamir query, with proof-of-work bits or without, obeys the rules, and
ends in Q, if what follows is safe from every state that the search can reach, for what the search
can pass on. -/
theorem safe_fbG {d : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList))
    (gr : Option (GrW C P)) (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β)
    (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ nc dd bl tl d', Kept gr nc dd →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t (nc.getD 0)) (dd.reverse ++ [tl]) d' →
      SafeO (rulesB K L lam p) (k nc dd bl tl) d' Q) :
    SafeO (rulesB K L lam p) (fbG gr chal t i tk us root hd hinj emb α k) d Q := by
  cases gr with
  | none =>
    show SafeO _ (fbT t i tk us root hd hinj (emb α) (k none [])) d Q
    exact safe_fbT0 h _ _ Q fun bl d' hT => hk none [] bl _ d' ⟨rfl, rfl, fun g e => by cases e⟩ hT
  | some g =>
    have hk' : ∀ m dd bl tl d', dd.length = m → m ≤ g.more →
        Tries (split lam K L) tk (us ++ root.toList) d (osTry t m) (dd.reverse ++ [tl]) d' →
        SafeO (rulesB K L lam p) (k (some m) dd bl tl) d' Q := fun m dd bl tl d' h1 h2 hT =>
      hk (some m) dd bl tl d' ⟨rfl, h1, fun g' e => by cases e; exact h2⟩ hT
    show SafeO _ (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m)) d Q
    unfold fbTG
    split
    · exact safe_fbT0 h _ _ Q fun bl d' hT => hk' 0 [] bl _ d' rfl (Nat.zero_le _) hT
    · rename_i n hn
      refine safe_fbT0 h _ _ Q fun bl d' hT => ?_
      split
      · exact hk' 0 [] bl _ d' rfl (Nat.zero_le _) hT
      · exact safe_fbW h g (fun m => k (some m)) Q hk' n 0 [d.vals.length] d' rfl (by omega) hT

end Scheme

end Compile.Batch.Disc
