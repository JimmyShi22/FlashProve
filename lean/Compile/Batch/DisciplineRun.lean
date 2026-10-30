-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineRun.lean: the rules of deferred programming for marked queries that hold
several tokens (the charged one and the others): which old tokens a run charges, and at which
oracles a token is held (tokens and marked queries: `Step`, `Ev`, Rom/Defer.lean; `Deps`:
Compile/Batch/DisciplineKit.lean; words of this library: lean/GLOSSARY.md).

`GrowsO` (Compile/Batch/SpecDiscipline.lean) bounds the old tokens that new queries hold. What a
token depends on (`Deps`), and whether tokens can be revealed together (`ClosedO`), changes only
when a token is charged (in this sense: `Deps.keeps`, `ClosedO.keeps`, under their hypotheses): the
root of a tree over a component is held by a Fiat-Shamir query or by the query to g (`gT`,
Compile/Batch/Prover.lean) and is never charged (the request root is charged: format (F4),
Compile/Batch/DisciplineJoin.lean). So here:

  `Charges`, `Run`  The old tokens that a run charges; that, `GrowsO` and `Persist` together, with
                    sequential composition.
  `HeldAt`  Every query that holds t goes to an oracle in P. Use: a slot value is held at the leaf
            oracle of request trees and can still be charged at the Fiat-Shamir oracle.
  `DeadW`  The tail of a failed attempt in a round with proof-of-work bits. This persists where no
           query disappears (`Persist`), and from a state with `TidyO` a run that charges no sealed
           token makes no old token dead.

Generic in the family of oracles.
-/
import Compile.Batch.DisciplineKit

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal mem_evs_afterMark cnt1 length_afterMark markDue
    markDue_o markDue_charged markDue_others markDue_tail)

section Kit
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {Cc Cc₂ Ch R Ch₂ R₂ : Tok → Prop}
  {e M e₁ M₁ e₂ M₂ : S.ι → ℕ} {d d' d'' : DSt S}

/-- Every query of d' is one of d, or is charged to a new token or to one in Cc. -/
structure Charges (Cc : Tok → Prop) (d d' : DSt S) : Prop where
  vals : d.vals <+: d'.vals
  shown_old : ∀ t ∈ d.shown, t ∈ d'.shown
  evs : ∀ e' ∈ d'.evs,
    (∃ e₀ ∈ d.evs, e₀.charged = e'.charged ∧ e₀.others = e'.others ∧ e₀.tail = e'.tail) ∨
    Cc e'.charged ∨
    d.vals.length ≤ e'.charged

theorem GrowsO.charges (h : GrowsO Ch R e M d d') : Charges Ch d d' where
  vals := h.vals
  shown_old := h.shown_old
  evs := fun e' he' => by
    rcases h.evs e' he' with ⟨e₀, he₀, _, hc, hu, ht⟩ | ⟨_, hc, _⟩
    · exact Or.inl ⟨e₀, he₀, hc, hu, ht⟩
    · exact Or.inr hc

theorem Charges.trans (h₁ : Charges Cc d d') (h₂ : Charges Cc₂ d' d'')
    (hCc : ∀ t, Cc₂ t → Cc t ∨ d.vals.length ≤ t) : Charges Cc d d'' where
  vals := h₁.vals.trans h₂.vals
  shown_old := fun t ht => h₂.shown_old t (h₁.shown_old t ht)
  evs := fun e'' he'' => by
    rcases h₂.evs e'' he'' with ⟨e', he', hc, hu, ht⟩ | hc | hc
    · rcases h₁.evs e' he' with ⟨e₀, he₀, hc', hu', ht'⟩ | hc'
      · exact Or.inl ⟨e₀, he₀, hc'.trans hc, hu'.trans hu, ht'.trans ht⟩
      · exact Or.inr (hc ▸ hc')
    · exact Or.inr (hCc _ hc)
    · exact Or.inr (Or.inr (le_trans h₁.vals.length_le hc))

theorem Charges.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Charges (fun t' => t' = t) d (afterMark sp d o t us P r T) where
  vals := List.prefix_append _ _
  shown_old := fun _ h => h
  evs := fun e' he' => by
    rcases mem_evs_afterMark he' with h | rfl
    · exact Or.inl ⟨e', h, rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl rfl)

theorem Deps.keeps {u : Tok} {l : List Tok} (hd : Deps d u l) (hlt : u < d.vals.length)
    (h : Charges Cc d d') (hc : ¬ Cc u) : Deps d' u l :=
  fun e' he' hce => by
    rcases h.evs e' he' with ⟨e₀, he₀, hc₀, hu₀, ht₀⟩ | h1 | h1
    · exact ⟨ht₀ ▸ (hd e₀ he₀ (hc₀.trans hce)).1, hu₀ ▸ (hd e₀ he₀ (hc₀.trans hce)).2⟩
    · exact absurd (hce ▸ h1) hc
    · exact absurd hlt (Nat.not_lt.mpr (hce ▸ h1))

theorem ClosedO.keeps {ts : List Tok} (hc : ClosedO d ts)
    (h : Charges Cc d d') (hch : ∀ t ∈ ts, ¬ Cc t) : ClosedO d' ts where
  lt := fun t ht => lt_of_lt_of_le (hc.lt t ht) h.vals.length_le
  tail := fun e' he' hce => by
    rcases h.evs e' he' with ⟨e₀, he₀, hc₀, _, ht₀⟩ | h1 | h1
    · exact ht₀ ▸ (hc.tail e₀ he₀ (hc₀ ▸ hce)).imp_right (h.shown_old _)
    · exact absurd h1 (hch _ hce)
    · exact absurd (hc.lt _ hce) (Nat.not_lt.mpr h1)
  others := fun e' he' hce v hv => by
    rcases h.evs e' he' with ⟨e₀, he₀, hc₀, hu₀, _⟩ | h1 | h1
    · exact (hc.others e₀ he₀ (hc₀ ▸ hce) v (hu₀ ▸ hv)).imp_right (h.shown_old _)
    · exact absurd h1 (hch _ hce)
    · exact absurd (hc.lt _ hce) (Nat.not_lt.mpr h1)

/-- Queries do not disappear. -/
def Persist (d d' : DSt S) : Prop :=
  ∀ e₀ ∈ d.evs,
    ∃ e' ∈ d'.evs, e'.o = e₀.o ∧ e'.charged = e₀.charged ∧ e'.others = e₀.others ∧ e'.tail = e₀.tail

theorem Persist.refl (d : DSt S) : Persist d d := fun e₀ h => ⟨e₀, h, rfl, rfl, rfl, rfl⟩

theorem Persist.trans (h₁ : Persist d d') (h₂ : Persist d' d'') : Persist d d'' := fun e₀ h => by
  obtain ⟨e', he', a1, a2, a3, a4⟩ := h₁ e₀ h
  obtain ⟨e'', he'', b1, b2, b3, b4⟩ := h₂ e' he'
  exact ⟨e'', he'', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

theorem Persist.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Persist d (afterMark sp d o t us P r T) :=
  fun e₀ h => ⟨e₀, List.mem_append_left _ h, rfl, rfl, rfl, rfl⟩

theorem Persist.ofReveal (d : DSt S) (ts : List Tok) (T : Table S) :
    Persist d (afterReveal d ts T) := fun e₀ h =>
  ⟨markDue (d.shown ++ ts) e₀, List.mem_map_of_mem h, markDue_o _ _, markDue_charged _ _,
    markDue_others _ _, markDue_tail _ _⟩

/-- What a run does: Cc bounds the old tokens that it charges, Ch those that its queries hold, R
those that it shows; e and M count: e o and M o: how many ordinary and marked queries to o it may
have added (`GrowsO`, Compile/Batch/SpecDiscipline.lean); no query disappears. -/
structure Run (Cc Ch R : Tok → Prop) (e M : S.ι → ℕ) (d d' : DSt S) : Prop where
  grows : GrowsO Ch R e M d d'
  charges : Charges Cc d d'
  keeps : Persist d d'

theorem Run.length_le (h : Run Cc Ch R e M d d') : d.vals.length ≤ d'.vals.length :=
  h.grows.length_le

theorem Run.refl (d : DSt S) : Run Cc Ch R e M d d :=
  ⟨GrowsO.refl d, (GrowsO.refl (Ch := Cc) (R := R) (e := e) (M := M) d).charges, Persist.refl d⟩

theorem Run.trans (h₁ : Run Cc Ch R e₁ M₁ d d') (h₂ : Run Cc₂ Ch₂ R₂ e₂ M₂ d' d'')
    (hCc : ∀ t, Cc₂ t → Cc t ∨ d.vals.length ≤ t)
    (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t)
    (he : ∀ o, e₁ o + e₂ o ≤ e o) (hM : ∀ o, M₁ o + M₂ o ≤ M o) : Run Cc Ch R e M d d'' :=
  ⟨h₁.grows.trans h₂.grows hCh hR he hM, h₁.charges.trans h₂.charges hCc, h₁.keeps.trans h₂.keeps⟩

theorem Run.mono (h : Run Cc₂ Ch₂ R₂ e₂ M₂ d d') (hCc : ∀ t, Cc₂ t → Cc t ∨ d.vals.length ≤ t)
    (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t)
    (he : ∀ o, e₂ o ≤ e o) (hM : ∀ o, M₂ o ≤ M o) : Run Cc Ch R e M d d' :=
  (Run.refl (Cc := Cc) (Ch := Ch) (R := R) (e := fun _ => 0) (M := fun _ => 0) d).trans h hCc hCh hR
    (fun o => by rw [Nat.zero_add]; exact he o) (fun o => by rw [Nat.zero_add]; exact hM o)

theorem Run.ofFresh (d : DSt S) (v : Bits) : Run Cc Ch R e M d (afterFresh d v) :=
  ⟨GrowsO.ofFresh d v,
    (GrowsO.ofFresh (Ch := Cc) (R := R) (e := e) (M := M) d v).charges,
    fun e₀ h => ⟨e₀, h, rfl, rfl, rfl, rfl⟩⟩

theorem Run.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) R e (cnt1 o 1)
      d (afterMark sp d o t us P r T) :=
  ⟨GrowsO.ofMark d o t us P r T, Charges.ofMark d o t us P r T, Persist.ofMark d o t us P r T⟩

theorem Run.ofReveal (d : DSt S) (ts : List Tok) (T : Table S) :
    Run Cc Ch (fun t => t ∈ ts) e M d (afterReveal d ts T) :=
  ⟨GrowsO.ofReveal d ts T,
    (GrowsO.ofReveal (Ch := Cc) (e := e) (M := M) d ts T).charges,
    Persist.ofReveal d ts T⟩

/-! ### At which oracles a token is held -/

/-- Every query that holds t goes to an oracle in P. -/
def HeldAt (d : DSt S) (t : Tok) (P : S.ι → Prop) : Prop :=
  ∀ e ∈ d.evs, (e.charged = t ∨ t ∈ e.others) → P e.o

theorem Untouched.heldAt {t : Tok} (h : Untouched d t) (P : S.ι → Prop) :
    HeldAt d t P := fun e he hh => by
  rcases hh with hh | hh
  · exact absurd hh (h.not_held e he).1
  · exact absurd hh (h.not_held e he).2

theorem HeldAt.grows {t : Tok} {P : S.ι → Prop} (hh : HeldAt d t P) (hlt : t < d.vals.length)
    (h : GrowsO Ch R e M d d') (hc : ¬ Ch t) :
    HeldAt d' t P := fun e' he' hh' => by
  rcases h.evs e' he' with ⟨e₀, he₀, ho₀, hc₀, hu₀, _⟩ | ⟨_, h1, h2⟩
  · exact ho₀ ▸ hh e₀ he₀ (by rw [hc₀, hu₀]; exact hh')
  · rcases hh' with hh' | hh'
    · rcases h1 with h1 | h1
      · exact absurd (hh' ▸ h1) hc
      · exact absurd hlt (Nat.not_lt.mpr (hh' ▸ h1))
    · rcases h2 t hh' with h1 | h1
      · exact absurd h1 hc
      · exact absurd hlt (Nat.not_lt.mpr h1)

theorem HeldAt.of_mark {t : Tok} {P : S.ι → Prop} (hh : HeldAt d t P) (o : S.ι) (t' : Tok)
    (us : List Tok) (Q : S.Dom o) (r : S.Rng o) (T : Table S) :
    HeldAt (afterMark sp d o t' us Q r T) t fun o' => P o' ∨ o' = o := fun e he hh' => by
  rcases mem_evs_afterMark he with he | rfl
  · exact Or.inl (hh e he hh')
  · exact Or.inr rfl

theorem FreeAt.of_heldAt {t : Tok} {P : S.ι → Prop} {o : S.ι} (hlt : t < d.vals.length)
    (hs : t ∉ d.shown) (hh : HeldAt d t P) (ho : ¬ P o) :
    FreeAt d o t :=
  ⟨hlt, hs,
    fun e he heo =>
      ⟨fun hc => ho (heo ▸ hh e he (Or.inl hc)), fun hu => ho (heo ▸ hh e he (Or.inr hu))⟩⟩

theorem not_shown_grows {t : Tok} (hlt : t < d.vals.length) (hs : t ∉ d.shown)
    (h : GrowsO Ch R e M d d') (hr : ¬ R t) : t ∉ d'.shown :=
  fun hs' => by
    rcases h.shown t hs' with h1 | h1 | h1
    · exact hs h1
    · exact hr h1
    · exact absurd hlt (Nat.not_lt.mpr h1)

/-! ### Sealed tokens
W is a set of "weak" oracles. A token that a query of another oracle holds is sealed. Outside a
search (Compile/Batch/DisciplineLoop.lean) the programs charge only tokens that are not sealed; so
what is known of a sealed token is final. -/

/-- Some query to an oracle outside W holds u. -/
def SealedW (W : S.ι → Prop) (d : DSt S) (u : Tok) : Prop :=
  ∃ e ∈ d.evs, (e.charged = u ∨ u ∈ e.others) ∧ ¬ W e.o

theorem SealedW.mono {W : S.ι → Prop} {u : Tok} (h : SealedW W d u) (hp : Persist d d') :
    SealedW W d' u := by
  obtain ⟨e₀, he₀, hh, hw⟩ := h
  obtain ⟨e', he', a1, a2, a3, _⟩ := hp e₀ he₀
  exact ⟨e', he', by rw [a2, a3]; exact hh, by rw [a1]; exact hw⟩

theorem SealedW.of_mark {W : S.ι → Prop} {o : S.ι} (ho : ¬ W o) (d : DSt S) (t : Tok)
    (us : List Tok) (P : S.Dom o) (r : S.Rng o) (T : Table S) {u : Tok} (hu : u = t ∨ u ∈ us) :
    SealedW W (afterMark sp d o t us P r T) u :=
  ⟨⟨o, P, r, t, us, d.vals.length, false⟩,
    List.mem_append_right _ (List.mem_singleton.mpr rfl),
    hu.imp_left Eq.symm, ho⟩

theorem HeldAt.not_sealed {W : S.ι → Prop} {t : Tok} (h : HeldAt d t W) : ¬ SealedW W d t :=
  fun ⟨e, he, hh, hw⟩ => hw (h e he hh)

theorem Untouched.not_sealed {W : S.ι → Prop} {t : Tok} (h : Untouched d t) : ¬ SealedW W d t :=
  (h.heldAt W).not_sealed

/-! ### Dead tails
A round with proof-of-work bits makes several queries that are charged to one token, at different
oracles (Compile/Batch/Prover.lean: fbG). The chain goes on from the tail of the last of them. The
tails of the others are never held by any query: so they are not sealed; and they are never charged.
What tells them from the tail on which a chain goes on is in the state: the token to which their
query is charged has a later query. -/

/-- u is the tail of a query, to an oracle outside W, whose charged token has a later query. -/
def DeadW (W : S.ι → Prop) (d : DSt S) (u : Tok) : Prop :=
  ∃ e ∈ d.evs, ∃ e' ∈ d.evs, e.tail = u ∧ ¬ W e.o ∧ e'.charged = e.charged ∧ u < e'.tail

theorem DeadW.mono {W : S.ι → Prop} {u : Tok} (h : DeadW W d u) (hp : Persist d d') :
    DeadW W d' u := by
  obtain ⟨e, he, e', he', h1, h2, h3, h4⟩ := h
  obtain ⟨f, hf, a1, a2, _, a4⟩ := hp e he
  obtain ⟨f', hf', _, b2, _, b4⟩ := hp e' he'
  exact ⟨f, hf, f', hf', a4.trans h1, by rw [a1]; exact h2,
    by rw [b2, a2]; exact h3, by rw [b4]; exact h4⟩

/-- Under the hypotheses below: a run that charges no sealed token makes no old token dead. -/
theorem DeadW.keeps_not {W : S.ι → Prop} {u : Tok} (hn : ¬ DeadW W d u) (hd : TidyO Rl d)
    (hlt : u < d.vals.length) (hr : Run Cc Ch R e M d d') (hc : ∀ t, Cc t → ¬ SealedW W d t) :
    ¬ DeadW W d' u := by
  rintro ⟨f, hf, f', hf', h1, h2, h3, h4⟩
  rcases hr.grows.evs f hf with ⟨e₀, he₀, a1, a2, _, a4⟩ | ⟨hnew, _, _⟩
  · rcases hr.charges.evs f' hf' with ⟨e₁, he₁, b2, _, b4⟩ | hcc | hcc
    · exact hn ⟨e₀, he₀, e₁, he₁, a4.trans h1, by rw [a1]; exact h2,
          by rw [b2, a2]; exact h3, by rw [b4]; exact h4⟩
    · exact hc _ hcc ⟨e₀, he₀, Or.inl (by rw [a2, h3]), by rw [a1]; exact h2⟩
    · exact absurd (hd.charged_lt e₀ he₀) (Nat.not_lt.mpr (by rw [a2, ← h3]; exact hcc))
  · exact absurd hlt (Nat.not_lt.mpr (h1 ▸ hnew))

/-- Under `TidyO`, the newest token is not dead. -/
theorem not_deadW_last {W : S.ι → Prop} {u : Tok} (hd : TidyO Rl d) (hu : d.vals.length ≤ u + 1) :
    ¬ DeadW W d u := by
  rintro ⟨_, _, e', he', _, _, _, h4⟩
  exact absurd h4 (Nat.not_lt.mpr (Nat.lt_succ_iff.mp (lt_of_lt_of_le (hd.tail_lt e' he') hu)))

/-- A set of tokens that is closed: the tail and the others of every query charged in V are in V;
its tokens exist; each is sealed or one of the open ends Op. -/
structure ClS (W : S.ι → Prop) (d : DSt S) (V Op : Tok → Prop) : Prop where
  closed : ∀ e ∈ d.evs, V e.charged → V e.tail ∧ ∀ v ∈ e.others, V v
  lt : ∀ u, V u → u < d.vals.length
  sealed : ∀ u, V u → SealedW W d u ∨ Op u

/-- A closed set stays closed along a run that charges no sealed token and none of its open ends. -/
theorem ClS.keeps {W : S.ι → Prop} {V Op : Tok → Prop} (h : ClS W d V Op)
    (hr : Run Cc Ch R e M d d') (hc : ∀ t, Cc t → ¬ SealedW W d t ∧ ¬ Op t) : ClS W d' V Op where
  closed := fun e' he' hV => by
    rcases hr.charges.evs e' he' with ⟨e₀, he₀, hc₀, hu₀, ht₀⟩ | h1 | h1
    · have := h.closed e₀ he₀ (hc₀ ▸ hV)
      exact ⟨ht₀ ▸ this.1, hu₀ ▸ this.2⟩
    · rcases h.sealed _ hV with h2 | h2
      · exact absurd h2 (hc _ h1).1
      · exact absurd h2 (hc _ h1).2
    · exact absurd (h.lt _ hV) (Nat.not_lt.mpr h1)
  lt := fun u hu => lt_of_lt_of_le (h.lt u hu) hr.length_le
  sealed := fun u hu => (h.sealed u hu).imp_left fun hs => hs.mono hr.keeps

theorem cnt1_add (o : S.ι) [DecidableEq S.ι] (a b : ℕ) (o' : S.ι) :
    cnt1 o a o' + cnt1 o b o' = cnt1 o (a + b) o' := by
  unfold cnt1
  split <;> rfl

end Kit

end Compile.Batch.Disc
