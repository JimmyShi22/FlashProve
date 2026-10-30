-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTied.lean: THE LINK's THREE PIECES, TIED TO THE TABLE OF CONDITIONS
BETWEEN BLOCKS: `link_table` (LinkTable.lean) laid into what the table asks at a block (`TiedAt`,
Johnson/Desc/Sound/ChainOfPromises.lean). One list of seven debts a piece, five relations by name,
and four theorems.

Why. The rule for a file takes the first chain's pieces between the table's own promises and
relations. At block number k the table asks: the kind's law in its own words, between conditions o,
o' and relations R, R' that the kind chooses; five ties of these to the table; and two facts on the
block's text. `link_table` is the law of the link's three pieces in words near the table's. Here
these words are laid for o, o', R, R', and what is then still asked stands as a list, a field a
debt.

What is said.
  `TieOwes N Mg links ps get k q o o' R R'`: the seven clauses of `TiedAt` behind the law, to the
    letter, a field each; each field's docstring begins «OWES ‹a role›:», so that a program can
    print the list. `tiedAt_of`: the law and the seven give `TiedAt`. `relAt_ins`, `t4_of_parts`:
    the fourth tie from two parts: what the row closes itself, and what it reads; «no mark» is had
    at an unmarked statement. `relForms`, `relTotB`, `relTotB'`, `relTot`, `relRow`: the relations
    of `link_table`, by name. `link_tied`: **from `LinkOwes` and `TableOwes` as `link_table` takes
    them, and `TieOwes` at each of the three pieces: `EachTied … k [pb, pq, pe]`.**

Limits. AN IMPLICATION: shown of no record of the protocol: three times seven debts stand beside
those of `LinkOwes` and `TableOwes`. The pieces stand over the first chain's bare record; get reads
it beside what was handed to the chain. k is free: nothing here says that the batching's block is
block number k of the table's list of places. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.Sound.ChainOfPromises

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-! ## What the table asks at a block, behind the kind's law -/

/-- **SEVEN DEBTS A PIECE**: the clauses of TiedAt behind the law, to the letter. -/
structure TieOwes {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop) : Prop where
  /-- OWES the table of conditions between blocks: at an unmarked statement the table's promise in
  front gives the kind's own condition in front -/
  t1 : ∀ a, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → o a
  /-- OWES the batching kind's law with the table of conditions: the table's promise in front, the
  block's yes and the kind's own condition behind give the table's promise behind -/
  t2 : ∀ a τ b, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b
  /-- OWES the filling of the table's letters: what the block's row opens, with what it reads and
  «no mark», gives the kind's own relation behind -/
  t3 : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w → R' b w
  /-- OWES the filling of the table's letters: the kind's own relation in front gives what the
  block's row closes, with what it reads and «no mark» -/
  t4 : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
    R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)
  /-- OWES what rides over the block: an item that is open behind the block and that its row does
  not close holds in front -/
  t5 : ∀ a τ b w i, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
    relQ N Mg links ps get (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg get i a (q.ext a τ w)
  /-- OWES the block's own text: a mark stays -/
  mark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
    (get b.1).2.failed ≠ none
  /-- OWES the block's own text: «the stored table decodes with the record» rides -/
  dec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
    Mg.decodes (get b.1) (strsOf Fr b.2)

/-- The law and the seven give what the table asks at the block. -/
theorem tiedAt_of {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S} {k : ℕ} {q : Piece C Fr A Cl W}
    {o o' : A × Fr.E.Str → Prop} {R R' : A × Fr.E.Str → W → Prop} (hl : q.GoodIn o o' R R')
    (T : TieOwes N Mg links ps get k q o o' R R') : TiedAt N Mg links ps get k q :=
  ⟨o, o', R, R', hl, T.t1, T.t2, T.t3, T.t4, T.t5, T.mark, T.dec⟩

/-- What a row closes, in three parts: what it closes itself, what it reads, and «no mark»: the
third is had at an unmarked statement. -/
theorem relAt_ins {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) (a : A × Fr.E.Str) (w : W)
    (hu : ¬ (get a.1).2.failed ≠ none)
    (h1 : ∀ i ∈ (rowQ links ps k).ins, meansQ N Mg get i a w)
    (h2 : ∀ i ∈ (rowQ links ps k).ctx, meansQ N Mg get i a w) :
    relAt (meansQ N Mg get) (insQ links ps k) a w := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · exact h1 i hi
    · exact h2 i hi
  · obtain rfl := List.mem_singleton.1 hi
    exact Classical.not_not.1 hu

/-- (t4) from its two parts: what the row closes itself, and what it reads. -/
theorem t4_of_parts {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (o' : A × Fr.E.Str → Prop) (R : A × Fr.E.Str → W → Prop)
    (hins : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → ∀ i ∈ (rowQ links ps k).ins, meansQ N Mg get i a (q.ext a τ w))
    (hctx : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → ∀ i ∈ (rowQ links ps k).ctx, meansQ N Mg get i a (q.ext a τ w)) :
    ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w) :=
  fun a τ b w ha hu hb ho hO hR =>
    relAt_ins N Mg links ps get k a _ hu (hins a τ b w ha hu hb ho hO hR)
      (hctx a τ b w ha hu hb ho hO hR)

/-! ## The relations of the link's three laws, by name -/

variable {α W : Type} {F : Frame}

/-- In front of the batching's piece: the forms of every listed item hold. -/
def relForms (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String)) : S × F.E.Str → W → Prop :=
  fun a w => ∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)

/-- In front of the piece behind it: the ledger's one sum behind the runs that follow is 0; and the
public sentence. α: the type of the fixed part's first half: the frame's move does not read it. -/
def relTotB' (α : Type) (L : Link S Claim) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (Rw : S × F.E.Str → Prop) : S × F.E.Str → W → Prop :=
  fun a w => totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own a.1 (rdW w) ∧ Rw a

/-- Behind the batching's piece: the same, and the context. -/
def relTotB (α : Type) (L : Link S Claim) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (Rw : S × F.E.Str → Prop) (ctx : S × F.E.Str → W → Prop) : S × F.E.Str → W → Prop :=
  fun b w => relTotB' α L own rdW Rw b w ∧ ctx b w

/-- Between the second piece and the third: the ledger's one sum is 0; and the public sentence. -/
def relTot (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (Rw : S × F.E.Str → Prop) :
    S × F.E.Str → W → Prop :=
  fun a w => totalQ own a.1 (rdW w) ∧ Rw a

/-- Behind the third piece: the group's last row holds. -/
def relRow (own : List (ℕ × ℕ)) (N : ℕ) (rdW : W → ℕ × ℕ → MsgQ) : S × F.E.Str → W → Prop :=
  fun e w => rowEqQ own N e.1 (rdW w)

/-! ## The three pieces, tied -/

/-- **THE LINK's THREE PIECES, TIED TO THE TABLE.** k: the number, in the table's list of places, at
which the ties of the batching's piece are shown. -/
theorem link_tied {P : Type} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (get : S → P × First.S) (k : ℕ)
    (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes L φ tmOf lenOf on0 on1 on2 Rd own rdW items)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a)
    (Tb : TieOwes Nm Mg links pl get k pb on0 on1 (relForms Rd own rdW items)
      (relTotB α L own rdW Rw ctx))
    (Tq : TieOwes Nm Mg links pl get (k + 1) pq on1 on2 (relTotB' α L own rdW Rw)
      (relTot own rdW Rw))
    (Te : TieOwes Nm Mg links pl get (k + 1 + 1) pe on2 on3 (relTot own rdW Rw)
      (relRow own N rdW)) :
    EachTied Nm Mg links pl get k [pb, pq, pe] := by
  obtain ⟨g1, g2, g3⟩ := link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃ pb pq pe on0 on1
    on2 on3 ctx Rd own rdW items A T h01 hR1 hR2 hR3
  exact ⟨tiedAt_of g1 Tb, tiedAt_of g2 Tq, tiedAt_of g3 Te, trivial⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tiedAt_of
#print axioms VerifiableInference.Desc.LinkJoin.relAt_ins
#print axioms VerifiableInference.Desc.LinkJoin.t4_of_parts
#print axioms VerifiableInference.Desc.LinkJoin.link_tied
