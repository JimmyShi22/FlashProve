-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Debts.lean: kind K14, the kind's own four sub-protocols that have
a round. WHAT IS PROVED: wherever chainSteps returns at the one member (hl), the first half that is
found at the member's place holds the kind's own part, lifted, and no other (hf), and the challenges
fit the member's round (hfit), play and fillCols return, at all coins; at "LOC" fillCols returns
where, besides, the committed table has its columns. This is the rows' lemma in the terms in which a
chain's thread asks it (Honest/Thread/Pays.lean: the prover's side of a member's step): at the steps
that chainSteps lays for the one member at the place, at the coins that the book lends. No thread is
named: the statements are at the frame's own functions, so that they can be laid at any thread's
fields.

  declares3       where the library's blocks P returns eight sub-protocols (hb): what "LIN point",
                  "LOC" and "LIN zeta" (the first, fourth and seventh) declare, written out,
                  whether the shape splits or not: one round each, no oracle message, no tree
                  opened; "LOC" reads the committed table's columns, the two others read nothing
  declares_split  the like of "SPLIT" (the eighth), under hb, where the shape splits: its round cuts
                  one element
  quiet_moved     "LIN point", "LIN zeta": wherever chainSteps returns at the member, under hf and
                  hfit, play and fillCols return, at all coins; nothing is sent; no column is read
  loc_moved       "LOC": the like; the columns are laid, where the committed table has a column of
                  the declared width at every position below its length (by filled,
                  Honest/Law/Fill.lean)
  split_moved     "SPLIT": the like as quiet_moved; the one element scalarAt
                  (Honest/K14/PartsFit.lean) is sent, at the coin that the book lends

In all three the round as played and the stand behind it are written out as terms. b is the member:
any sub-protocol with these rounds and oracle messages (one round, one empty list of oracle
messages; the round's items, and that it opens no tree, are premises too): so the one in the IOP as
written in Lean, however it is wrapped.

What is not claimed. That chainSteps returns. That the half is found at the place, or that the
challenges fit: both are premises. That a member's step accepts. Nothing on what holds behind the
place. Where the shape does not split "SPLIT" has no round: nothing is said of it there.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import Johnson.Desc.ProofFile.Honest.K13.DebtsKit
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.K14.Law.RoundsMake
import Johnson.Desc.ProofFile.Honest.Law.Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place OpenedColumn)
open Desc.K14 (P14 St blocks entries)
open Desc.K14.Law (entryAt)
open ProofFile.Honest.K13 (chainSteps_one)

variable {S Cl W₀ Rc Ky X : Type}

/-- **What "LIN point", "LOC" and "LIN zeta" declare**, written out, at both sorts of shape, where
blocks P returns the eight sub-protocols (hb). entryAt: Johnson/Desc/K14/Law/RoundsMake.lean. -/
theorem declares3 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (entryAt P 0).cut = [] ∧ (entryAt P 1).cut = [] ∧ (entryAt P 2).cut = [] ∧
      b1.rounds = [{ entry := entryAt P 0 }] ∧ b1.oracles = [[]] ∧
      b4.rounds = [{ entry := entryAt P 1, stored := [Desc.K14.readsAtLoc P.S.fold P.item] }] ∧
      b4.oracles = [[]] ∧
      b7.rounds = [{ entry := entryAt P 2 }] ∧ b7.oracles = [[]] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, rfl⟩ <;>
  · unfold entryAt entries Desc.K14.rounds Desc.K14.whys
    split <;> simp [Desc.K14.Round.entry, Desc.K14.Says.bytes, Fmt.Entry.cut]

/-- **What "SPLIT" declares**, where blocks P returns the eight sub-protocols (hb) and the shape
splits (hS). -/
theorem declares_split (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) :
    (entryAt P 3).cut = [.e] ∧ b8.rounds = [{ entry := entryAt P 3 }] ∧ b8.oracles = [[]] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨?_, ?_, by simp [hS]⟩ <;>
  · unfold entryAt entries Desc.K14.rounds Desc.K14.whys
    simp [hS, Desc.K14.Round.entry, Desc.K14.Says.bytes, Fmt.Entry.cut]

/-- **"LIN point", "LIN zeta": played**, where the member has one round and one empty list of oracle
messages (hr, ho), the round declares no item, opens no tree and reads no committed table (hd, hop,
hst), the first half found at the member's place holds quietPart, lifted, alone (hf), chainSteps
returns at the member (hl) and the challenges fit the round (hfit). Then there is one challenge,
play returns the round written out, with nothing sent, and fillCols returns no column. -/
theorem quiet_moved (A : Data) (weights : W₀ → Weights) (b : Block S Cl) (d : Fmt.DeclaredRound)
    (hr : b.rounds = [d]) (ho : b.oracles = [[]]) (hd : d.items = []) (hop : d.opens = [])
    (hst : d.stored = []) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option Empty}
    {hs : List (Placed Empty (Common W₀ Rc Ky) X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftK14 A weights quietPart] })
    {l : List (Step (Common W₀ Rc Ky) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    (m : Mid (Common W₀ Rc Ky) X) (ds : List Fmt.Drawn) (hfit : drawsFit b.rounds ds = true) :
    ∃ x, ds = [x] ∧
      play l ds [] m = .ok ([playedBy b [] [] x], pastOf m [] x) ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨c, -, rfl⟩ := chainSteps_one hf hl
  obtain ⟨x, rfl, -⟩ := drawsFit_one (d := d) (ds := ds) (by rw [← hr]; exact hfit)
  refine ⟨x, rfl, quiet_plays A weights b d (by rw [hr, ho]; rfl) hd v c m x,
    fun chain ft stored tree => ?_⟩
  rw [hr, reads_none chain ft stored tree d x hop hst]
  rfl

/-- **"SPLIT": played**, under quiet_moved's premises, but that the round declares one element of
the extension field (hd) and the half holds splitPart A, lifted, alone (hf). Then lendRow returns,
play returns the round written out, with the one element scalarAt sent, and fillCols returns no
column. c: the coins that the book lends the row. -/
theorem split_moved (A : Data) (weights : W₀ → Weights) (b : Block S Cl) (d : Fmt.DeclaredRound)
    (hr : b.rounds = [d]) (ho : b.oracles = [[]]) (hd : d.items = [.e]) (hop : d.opens = [])
    (hst : d.stored = []) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option Empty}
    {hs : List (Placed Empty (Common W₀ Rc Ky) X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftK14 A weights (splitPart A)] })
    {l : List (Step (Common W₀ Rc Ky) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    (m : Mid (Common W₀ Rc Ky) X) (ds : List Fmt.Drawn) (hfit : drawsFit b.rounds ds = true) :
    ∃ x c, ds = [x] ∧
      lendRow B rows look b.place
        [(liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X)] 0 = .ok c ∧
      play l ds [] m =
        .ok ([playedBy b [.e (OnBytes.Slice.ofE (scalarAt A c.1 (askOf A weights m.st)))] [] x],
        pastOf m [.e (OnBytes.Slice.ofE (scalarAt A c.1 (askOf A weights m.st)))] x) ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨c, hc, rfl⟩ := chainSteps_one hf hl
  obtain ⟨x, rfl, -⟩ := drawsFit_one (d := d) (ds := ds) (by rw [← hr]; exact hfit)
  refine ⟨x, c, rfl, hc, split_plays A weights b d (by rw [hr, ho]; rfl) hd v c m x,
    fun chain ft stored tree => ?_⟩
  rw [hr, reads_none chain ft stored tree d x hop hst]
  rfl

/-- **"LOC": played**, under quiet_moved's premises but hst (the round may read committed tables),
and the columns are laid, where the committed table of each item that the round reads has a column
of the declared width at every position below the table's length. -/
theorem loc_moved (A : Data) (weights : W₀ → Weights) (b : Block S Cl) (d : Fmt.DeclaredRound)
    (hr : b.rounds = [d]) (ho : b.oracles = [[]]) (hd : d.items = []) (hop : d.opens = [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option Empty}
    {hs : List (Placed Empty (Common W₀ Rc Ky) X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftK14 A weights quietPart] })
    {l : List (Step (Common W₀ Rc Ky) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    (m : Mid (Common W₀ Rc Ky) X) (ds : List Fmt.Drawn) (hfit : drawsFit b.rounds ds = true) :
    ∃ x, ds = [x] ∧
      play l ds [] m = .ok ([playedBy b [] [] x], pastOf m [] x) ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        (∀ s ∈ d.stored, ∀ p < 2 ^ s.sh.a, ∃ w, stored s.item p = some w ∧ w.length = s.sh.W) →
        ∃ cols, fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols := by
  obtain ⟨c, -, rfl⟩ := chainSteps_one hf hl
  obtain ⟨x, rfl, -⟩ := drawsFit_one (d := d) (ds := ds) (by rw [← hr]; exact hfit)
  refine ⟨x, rfl, quiet_plays A weights b d (by rw [hr, ho]; rfl) hd v c m x,
    fun chain ft stored tree hcol => ?_⟩
  rw [hr]
  refine filled chain ft stored tree [d] [x] fun d' hd' => ?_
  obtain rfl : d' = d := by simpa using hd'
  exact ⟨hcol, fun o ho' => by rw [hop] at ho'; cases ho'⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.declares3
#print axioms ProofFile.Honest.K14.declares_split
#print axioms ProofFile.Honest.K14.quiet_moved
#print axioms ProofFile.Honest.K14.split_moved
#print axioms ProofFile.Honest.K14.loc_moved
