-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstHitDef.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), for its main lemma (`Spec.mixClose`, Rom/StateFirstMix.lean): definitions,
and the two statements from which it follows, `Spec.mainLe` and `Spec.psiLe`. Nothing is proved
here.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) A mixed program (over `mixSpec`) makes typed
queries (the honest side's, to the first family) and raw queries (an adversary's, to the second).
The ideal interpretations (`ideal`) are programs over the first family, in which a reduction answers
the raw expansion queries from a table (`Book`). (`real`, `real'`: Rom/StateFirstMix.lean.) hid is
the second block of a state. `MixBound C c t r`: at most t typed queries at chain oracles and r raw
queries; `HidFreeM`: typed continuations do not depend on hid.

A raw expansion query at a state that the honest side has made and the adversary has not been shown
is answered by the true hash block in the real interpretation and by a coin in the reduction's. A
typed query with such a state is called hidden. `Psi` adds up, along a run of the reduction's
interpretation under lazy sampling, the probabilities of such a raw query; `Ghost` relates the
reduction's table to a table of all chain answers, which no program holds (exactly: neither program
of `Spec.mainLe`; `shadow`, Rom/StateFirstMix.lean, keeps such a table): it exists only in the
proof.

Notation:
  `ideal C false` (Rom/StateFirstMix.lean): the ideal interpretations: typed queries go to the first
      family; a raw query for a state becomes the typed query, of whose answer the state is
      returned; with `all` = false only the raw queries are entered in the table (what a reduction
      can do)
  `real'` (Rom/StateFirstMix.lean): the real interpretation in which a raw query for a state is also
      followed by the expansion queries, whose answers are discarded
  `Rel C Tp T b` (Rom/StateFirstColl.lean): the lazily sampled tables Tp (second family), T (first)
      and a table b of all chain answers (a `Book`) are consistent
  `bnd lam n m` (Rom/StateFirstColl2.lean): the error term n (m + n) / 2^(2 lam)
  `drVal` (Rom/StateFirstMix.lean): what a table answers at a query to dr without a coin: its own
      earlier answer; else the hash block of the oldest entered answer with that state that has such
      a hash block
  `findMade` (Rom/StateFirst.lean): the stored answer at the query (o, q)
  `Dg lam`: a hash block, `Fin lam → Bool` (Rom/NeedA.lean)
  `nDg lam` (Rom/StateFirstMix.lean): the number of values of a hash block, 2^lam, less one
  `digE lam : Fin (nDg lam + 1) ≃ Dg lam` (Rom/StateFirstMix.lean): a uniform sample with 2^lam
      outcomes is a hash block
  `Book` (Rom/StateFirstMix.lean): the reduction's table: the chain answers seen, oldest first
      (`made`), and the answers that it has itself given for dr at other queries (`loose`)
  `b.note` (`Book.note`, Rom/StateFirstMix.lean): a chain answer is entered, once
-/
import Rom.StateFirstKit2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

/-- a query to a family: an oracle and an input -/
abbrev PtS (S : OSpec) : Type := Σ o : S.ι, S.Dom o

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {α : Type}

/-- σ is the state of the table's answer at one of the queries of H -/
def hitAt (T : Table S) (H : List (PtS S)) (σ : Dg lam × Dg lam) : Prop :=
  ∃ h ∈ H, ∃ r, T h.1 h.2 = some r ∧ (C h.1).stateOf r = some σ

open Classical in
/-- The expected number of raw expansion queries of c at states of hidden queries. The run is that
of `ideal C false c b` from the table T; a new typed query to a chain oracle becomes hidden; a raw
query for its state takes it out of H. -/
def Psi : OComp (mixSpec C) α → Table S → Book S lam → List (PtS S) → ℝ≥0∞
  | .pure _, _, _, _ => 0
  | .sample n k, T, b, H => expect (unif (Fin (n + 1))) fun x => Psi (k x) T b H
  | .query (.inl o) q k, T, b, H =>
      match T o q with
      | some r => Psi (k r) T b H
      | none =>
        expect (unif (S.Rng o)) fun r =>
          Psi (k r) (T.set o q r) b (if (C o).isPlain = true then H else ⟨o, q⟩ :: H)
  | .query (.inr (.inl o)) q k, T, b, H =>
      match T o q with
      | some r => Psi (k ((C o).toAns r)) T (b.note C o q r) (H.erase ⟨o, q⟩)
      | none =>
        expect (unif (S.Rng o)) fun r => Psi (k ((C o).toAns r)) (T.set o q r) (b.note C o q r) H
  | .query (.inr (.inr _)) p k, T, b, H =>
      (if hitAt C T H p.1 then 1 else 0) +
        match drVal C b p with
        | some v => Psi (k v) T b H
        | none =>
          expect (unif (Fin (nDg lam + 1))) fun x =>
            Psi (k (digE lam x)) T { b with loose := (p, digE lam x) :: b.loose } H

/-- The relation between the reduction's table bF, the table bT of all chain answers and the hidden
queries H:
  `loose`: the same own answers for dr;
  `sub`: bF's entries are bT's;
  `cover`: an entry of bT is in bF or its query is hidden;
  `hid`: a hidden query is not in bF;
  `madeF`: at a query to a chain oracle that is not hidden bF holds exactly what the table T holds;
  `true`: the entries of bT are T's;
  `inj`: their states are pairwise different;
  `nodup`, `chain`, `live`: the hidden queries are distinct queries to chain oracles at which T has
      entries. -/
structure Ghost (T : Table S) (bT bF : Book S lam) (H : List (PtS S)) : Prop where
  loose : bT.loose = bF.loose
  sub : ∀ e ∈ bF.made, e ∈ bT.made
  cover : ∀ e ∈ bT.made, e ∈ bF.made ∨ (⟨e.1, e.2.1⟩ : PtS S) ∈ H
  hid : ∀ h ∈ H, findMade bF.made h.1 h.2 = none
  madeF : ∀ o q, (⟨o, q⟩ : PtS S) ∉ H → (C o).isPlain = false → findMade bF.made o q = T o q
  true : ∀ e ∈ bT.made, T e.1 e.2.1 = some e.2.2
  inj : ∀ e ∈ bT.made,
    ∀ e' ∈ bT.made, ∀ σ, (C e.1).stateOf e.2.2 = some σ → (C e'.1).stateOf e'.2.2 = some σ → e = e'
  nodup : H.Nodup
  live : ∀ h ∈ H, T h.1 h.2 ≠ none
  chain : ∀ h ∈ H, (C h.1).isPlain = false

/-- From related tables (`Rel`, `Ghost`), under `MixBound`: Pr[real' ∈ E] ≤ Pr[the reduction's
interpretation ∈ E] + n (m + n) / 2^(2 lam) + Psi, where n = t + r and m bounds the entries of bT.
`Psi` is still to be bounded. -/
def Spec.mainLe : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (C : ∀ o, Link lam (S.Rng o)) (α : Type)
      (c : OComp (mixSpec C) α) (t r m : ℕ) (Tp : Table (stSpec S lam C)) (T : Table S)
      (bT bF : Book S lam) (H : List (PtS S)),
    MixBound C c t r → Rel C Tp T bT → Ghost C T bT bF H → bT.made.length + bT.loose.length ≤ m →
    ∀ E : Set α, pr ((real' C c).runLazy Tp) {x | x.1 ∈ E} ≤
      pr ((ideal C false c bF).runLazy T) {x | x.1.1 ∈ E} + bnd lam (t + r) m + Psi C c T bF H

namespace Link
variable {R : Type}
/-- the answer with another last block (hid) -/
def setHid : Link lam R → R → Dg lam → R
  | .plain, r, _ => r
  | .chain _ e, r, u => e.symm ((e r).1, (e r).2.1, u)
end Link

/-- the table with another hid at one query -/
def Table.reHid (T : Table S) (h : PtS S) (u : Dg lam) : Table S :=
  match T h.1 h.2 with
  | some r => T.set h.1 h.2 ((C h.1).setHid r u)
  | none => T

/-- the average over fresh uniform hids at the queries of a list -/
def avgH : List (PtS S) → (Table S → ℝ≥0∞) → Table S → ℝ≥0∞
  | [], F, T => F T
  | h :: H, F, T => expect (unif (Dg lam)) fun u => avgH H F (Table.reHid C T h u)

/-- Under `MixBound` and `HidFreeM`, for distinct hidden queries at which the table has entries: the
average of `Psi` over fresh uniform hids at them is at most (hidden queries + t) · r / 2^lam. -/
def Spec.psiLe : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (C : ∀ o, Link lam (S.Rng o)) (α : Type) (c : OComp (mixSpec C) α)
      (t r : ℕ) (T : Table S) (b : Book S lam) (H : List (PtS S)),
    MixBound C c t r → HidFreeM C c → H.Nodup → (∀ h ∈ H, T h.1 h.2 ≠ none) →
    avgH C H (fun T' => Psi C c T' b H) T ≤ (((H.length + t) * r : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ lam)⁻¹

end Rom
