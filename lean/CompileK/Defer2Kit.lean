-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Kit.lean: book-keeping shared by the files on the compiled prover's programs, for the
lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). Tools
for the files that prove the discipline with joint charges (CompileK/Defer2Safe.lean: `SafeO2`) of
the scheme's programs: "can be revealed together, both ways" (`ClosedBoth` := `ClosedO` and
`UpClosed`) with `ClosedO`'s interface; the four actions (a marked evaluation: at oracles without
joint charges) on "orderly both ways" (`TidyBoth`); the handles of a tree over an encoded index
(`TreeOKB2`); what a run may have added at the vertex oracles (`GJ`); a tree over a message that
stands both ways (`TTOK2`, `AlJ2`, `Al02`).

Definitions and small theorems. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs. "Both ways": the condition of Compile/Batch/, which follows a token
down its charges, and its converse at the vertex oracles `OracleName.node`, `OracleName.rnode`
(CompileK/Defer2Tree.lean: `Jt`, `RDep`). For `TidyBoth` the second half is `Tidy2`, for
`ClosedBoth` it is `UpClosed` (both CompileK/Defer2Safe.lean).

Why: the definitions, but for `GJ`, have the shape of those of Compile/Batch/, and laws of the same
names, some with further premises on the vertex oracles, so that the proofs of this family can
follow those of Compile/Batch/ step by step.

Notation: `d`, `d'`: `DSt (spec lam K L)` (Rom/Defer.lean): states of the experiment beside the
challenger's own; `Tok`: `ℕ` (Rom/Defer.lean); at `DSt.vals` there: the value of token i stands at
place i; `charged : Tok`, `others : List Tok`: fields of `Ev` (Rom/Defer.lean), the record of one
marked evaluation; `others`: its further tokens (the doc comment of `GJ`); `Jt`: `OracleName → Bool`
(CompileK/Defer2Tree.lean): the oracles with joint charges; `Ch`, `R`, `Cc`, `ChJ`: `Tok → Prop`:
sets of tokens; `e`, `M`: `OracleName → ℕ`; in `GrowsO Ch R e M d d'` (Compile/Batch/SpecDiscipline.lean),
what a run may have added: e o and M o: how many plain and marked evaluations of o.
-/
import CompileK.Defer2Req
import Compile.Batch.DisciplineE

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal nEv length_afterFresh length_afterMark cnt1
    TreeTok TreeNew cntLeaves)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ}

/-- the tokens ts can be revealed together, both ways -/
def ClosedBoth (d : DSt (spec lam K L)) (ts : List Tok) : Prop := ClosedO d ts ∧ UpClosed Jt d ts

theorem ClosedBoth.lt {d : DSt (spec lam K L)} {ts : List Tok} (h : ClosedBoth d ts) :
    ∀ t ∈ ts, t < d.vals.length := h.1.lt

theorem UpClosed.grows {d d' : DSt (spec lam K L)} {ts : List Tok} {Ch R : Tok → Prop}
    {e M : OracleName → ℕ} (hu : UpClosed Jt d ts) (hlt : ∀ t ∈ ts, t < d.vals.length)
    (h : GrowsO Ch R e M d d') (hch : ∀ t ∈ ts, ¬ Ch t) : UpClosed Jt d' ts := by
  intro e' he' hJ b hb hbt
  rcases h.evs e' he' with ⟨e₀, he₀, ho, hc₀, hot, _⟩ | ⟨_, _, hnew⟩
  · rw [← hc₀]
    exact (hu e₀ he₀ (by rw [ho]; exact hJ) b (by rw [hot]; exact hb) hbt).imp_right (h.shown_old _)
  · rcases hnew b hb with h1 | h1
    · exact absurd h1 (hch b hbt)
    · exact absurd (hlt b hbt) (Nat.not_lt.mpr h1)

theorem ClosedBoth.grows {d d' : DSt (spec lam K L)} {ts : List Tok} {Ch R : Tok → Prop}
    {e M : OracleName → ℕ} (hc : ClosedBoth d ts) (h : GrowsO Ch R e M d d') (hch : ∀ t ∈ ts, ¬ Ch t) :
    ClosedBoth d' ts :=
  ⟨hc.1.grows h hch, hc.2.grows hc.1.lt h hch⟩

theorem ClosedBoth.of_deps {d : DSt (spec lam K L)} {ts : List Tok}
    (hlt : ∀ t ∈ ts, t < d.vals.length)
    (h : ∀ u ∈ ts, ∃ l, Deps d u l ∧ ∀ v ∈ l, v ∈ ts ∨ v ∈ d.shown)
    (hr : ∀ u ∈ ts, RDep d u (fun c => c ∈ ts)) : ClosedBoth d ts :=
  ⟨ClosedO.of_deps hlt h, UpClosed.of_rdeps hr⟩

theorem TidyBoth.plain {d : DSt (spec lam K L)} (h : TidyBoth p mG d)
    (o : OracleName) (T : Table (spec lam K L)) :
    TidyBoth p mG (afterPlain d o T) :=
  ⟨h.1.plain o T, h.2.plain o T⟩

theorem TidyBoth.fresh {d : DSt (spec lam K L)} (h : TidyBoth p mG d) (v : Bits) :
    TidyBoth p mG (afterFresh d v) :=
  ⟨h.1.fresh v, Tidy2.fresh h.1 h.2 v⟩

theorem TidyBoth.reveal {d : DSt (spec lam K L)} (h : TidyBoth p mG d) {ts : List Tok}
    (hc : ClosedBoth d ts) (T : Table (spec lam K L)) :
    TidyBoth p mG (afterReveal d ts T) :=
  ⟨h.1.reveal hc.1 T, Tidy2.reveal h.2 hc.2 T⟩

/-- no joint charge at o: nothing more is asked -/
theorem jmark_none {d : DSt (spec lam K L)} {o : OracleName} (hJ : Jt o = false) (t : Tok) (us : List Tok)
    (pt : Bits → List Bits → (spec lam K L).Dom o) :
    Jt o = true → JMark (ellT lam) d o t us pt :=
  fun h => by rw [hJ] at h; simp at h

theorem TidyBoth.markN {d : DSt (spec lam K L)} (h : TidyBoth p mG d) {o : OracleName} (hJ : Jt o = false)
    {t : Tok} {us : List Tok} (hus : ∀ u ∈ us, u < d.vals.length) (htu : t ∉ us) (ht : FreeAt d o t)
    (P : (spec lam K L).Dom o) (hb : (rulesT K L lam p mG).bits o ≤ (d.val t).length)
    (hP : (rulesT K L lam p mG).Mk o P) (r : (spec lam K L).Rng o) (T : Table (spec lam K L)) :
    TidyBoth p mG (afterMark (split lam K L) d o t us P r T) :=
  ⟨h.1.mark hus htu ht P hb hP r T,
    Tidy2.mark (pt := fun _ _ => P) h.1 h.2 hus ht (jmark_none hJ t us _) P r T⟩

/-- The handles of a tree over an encoded index can be revealed, both ways. -/
def TreeOKB2 (d : DSt (spec lam K L)) (t : TreeH lam) : Prop :=
  ∀ s s', some (s, s') ∈ t.salts → ClosedBoth d [s, s']

theorem TreeOKB2.toOK {d : DSt (spec lam K L)} {t : TreeH lam} (h : TreeOKB2 d t) : TreeOKB d t :=
  fun s s' hs => (h s s' hs).1

/-! ### What a run may have added at the vertex oracles -/

/-- every evaluation of d' at a vertex oracle is one of d, or its further tokens are in ChJ or new.
(GrowsO does not say at which oracle a new evaluation stands; a Fiat-Shamir evaluation may hold a
tree's root, and is none of these.) -/
structure GJ (ChJ : Tok → Prop) (d d' : DSt (spec lam K L)) : Prop where
  len : d.vals.length ≤ d'.vals.length
  evs : ∀ e' ∈ d'.evs, Jt e'.o = true →
    (∃ e₀ ∈ d.evs, e₀.o = e'.o ∧ e₀.charged = e'.charged ∧ e₀.others = e'.others) ∨
    ∀ u ∈ e'.others, ChJ u ∨ d.vals.length ≤ u

theorem GJ.of_grows {d d' : DSt (spec lam K L)} {Ch R : Tok → Prop}
    {e M : OracleName → ℕ} (h : GrowsO Ch R e M d d') : GJ Ch d d' :=
  ⟨h.length_le,
    fun e' he' _ => (h.evs e' he').imp (fun ⟨e₀, a, b, c, f, _⟩ => ⟨e₀, a, b, c, f⟩) fun x => x.2.2⟩

theorem GJ.refl (ChJ : Tok → Prop) (d : DSt (spec lam K L)) : GJ ChJ d d :=
  ⟨le_rfl, fun e' he' _ => Or.inl ⟨e', he', rfl, rfl, rfl⟩⟩

theorem GJ.trans {ChJ ChJ₂ : Tok → Prop} {d d' d'' : DSt (spec lam K L)} (h₁ : GJ ChJ d d')
    (h₂ : GJ ChJ₂ d' d'') (hC : ∀ t, ChJ₂ t → ChJ t ∨ d.vals.length ≤ t) : GJ ChJ d d'' := by
  refine ⟨le_trans h₁.len h₂.len, fun e'' he'' hJ => ?_⟩
  rcases h₂.evs e'' he'' hJ with ⟨e', he', ho, hc, hot⟩ | hnew
  · rcases h₁.evs e' he' (by rw [ho]; exact hJ) with ⟨e₀, he₀, a, b, c⟩ | hnew
    · exact Or.inl ⟨e₀, he₀, a.trans ho, b.trans hc, c.trans hot⟩
    · exact Or.inr fun u hu => hnew u (by rw [hot]; exact hu)
  · exact Or.inr fun u hu => (hnew u hu).elim (hC u) fun h => Or.inr (le_trans h₁.len h)

theorem RDep.keepsJ {d d' : DSt (spec lam K L)} {b : Tok} {A ChJ : Tok → Prop} (h : RDep d b A)
    (hlt : b < d.vals.length) (hg : GJ ChJ d d') (hc : ¬ ChJ b) : RDep d' b A := by
  intro e' he' hJ hb
  rcases hg.evs e' he' hJ with ⟨e₀, he₀, ho, hch, hot⟩ | hnew
  · rw [← hch]
    exact h e₀ he₀ (by rw [ho]; exact hJ) (by rw [hot]; exact hb)
  · rcases hnew b hb with h1 | h1
    · exact absurd h1 hc
    · exact absurd hlt (Nat.not_lt.mpr h1)

/-- a tree over a prover message that stands, both ways -/
def TTOK2 (d : DSt (spec lam K L)) (n₀ depth : ℕ) (t : TTree) : Prop :=
  TTOK d n₀ depth t ∧ TTUp d depth t

theorem TTOK2.keeps {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree} {Cc ChJ : Tok → Prop}
    (h : TTOK2 d n₀ depth t) (hc : Charges Cc d d') (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u)
    (hj : GJ ChJ d d') (hnj : ∀ u, ChJ u → u < n₀ ∨ d.vals.length ≤ u) : TTOK2 d' n₀ depth t :=
  ⟨h.1.keeps hc hn, fun j hj' u hu => (h.2 j hj' u hu).keepsJ ((h.1.open_ j hj').lt u hu) hj fun hcu => by
    rcases hnj u hcu with h1 | h1
    · exact absurd (h.1.new j hj' u hu) (Nat.not_le.mpr h1)
    · exact absurd ((h.1.open_ j hj').lt u hu) (Nat.not_lt.mpr h1)⟩

/-- The trees over the slots' components stand both ways, round by round. -/
def AlJ2 (d : DSt (spec lam K L)) (n₀ : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (Option TTree) → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), l =>
    (∀ tr, l.headD none = some tr → TTOK2 d n₀ w.depthJ tr) ∧ AlJ2 d n₀ s A W l.tail

/-- The same for the trees over the shared components. -/
def Al02 (d : DSt (spec lam K L)) (n₀ : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (Option TTree) → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), l =>
    (∀ tr, l.headD none = some tr → TTOK2 d n₀ w.depth0 tr) ∧ Al02 d n₀ s A W l.tail

theorem AlJ2.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {Cc ChJ : Tok → Prop} (hc : Charges Cc d d')
    (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u) (hj : GJ ChJ d d')
    (hnj : ∀ u, ChJ u → u < n₀ ∨ d.vals.length ≤ u) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      AlJ2 d n₀ s A W l → AlJ2 d' n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), l, h =>
    ⟨fun tr htr => (h.1 tr htr).keeps hc hn hj hnj, AlJ2.keeps hc hn hj hnj s A W l.tail h.2⟩

theorem Al02.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {Cc ChJ : Tok → Prop} (hc : Charges Cc d d')
    (hn : ∀ u, Cc u → u < n₀ ∨ d.vals.length ≤ u) (hj : GJ ChJ d d')
    (hnj : ∀ u, ChJ u → u < n₀ ∨ d.vals.length ≤ u) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      Al02 d n₀ s A W l → Al02 d' n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), l, h =>
    ⟨fun tr htr => (h.1 tr htr).keeps hc hn hj hnj, Al02.keeps hc hn hj hnj s A W l.tail h.2⟩

end Compile.Batch.Disc
