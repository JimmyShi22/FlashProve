-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/LentInside.lean: WHERE THE BOOK LENDS A ROW ITS COINS, EVERY
SPENDING ENTRY OF THE ROW LIES INSIDE ITS OWNER'S COUNT; SO A ROW WHOSE ENTRIES ARE ONE STRETCH HAS
THAT STRETCH INSIDE. On the frame's own lend, lendPart, lendRow, Cs.cut (Honest/Frame.lean),
rowEntries, runOn, oneStretch (Honest/BookStretch.lean): GENERAL IN THE BOOK, THE COINS AND THE ROW:
no sub-protocol is named but in the last lemma. The frame's authors' to take, if it serves.
WHAT IT IS NOT. THAT ANY BOOK LENDS ANY ROW ANYTHING IS NOT SHOWN. Coins of the extension field
alone. Entries that are spent, not those that are carried. Nothing on whether the verifier accepts a
proof, on soundness, on completeness or on what a proof hides. No example.
WHY. The frame's lemma on the number of coins that a row spends (Law/Rule/TiesLen.lean:
rowSpent_length) asks that the stretch lie inside its owner's count; so Law/SpentIsTakes.lean's
cnt_is_takes asked it too, and whoever wanted "cnt is takesOf" in order to show that bound went in a
circle. But lend returns only where it has cut each entry's run off its owner's coins, at the
entry's own count, and Cs.cut answers only inside.
  cut_inside          where Cs.cut answers, the run lies inside the count.
  lend_inside         where lend returns, each of the entries that it walked lies inside (the steps
                      are those of the frame's lend_first, Law/Rule/SpentInside.lean, which says
                      the like of the first entry; that file is not imported).
  lendRow_inside      where lendRow returns, each of the row's spending entries lies inside.
  runOn_inside, oneStretch_inside   entries that are one stretch of one owner's, each inside: the
                      stretch lies inside.
  stretch_of_lent     THE JOIN: lendRow returns, and the row's entries are one stretch (o, s0, cnt):
                      s0 + cnt is no more than the owner's count at these coins.
  cnt_is_takes_of_lent   at the output head's row: cnt = takesOf p from these two alone:
                      Law/SpentIsTakes.lean's cnt_is_takes without its premise on room.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.SpentIsTakes
import Johnson.Desc.ProofFile.Honest.BookStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.Desc.Kinds.Head.Law (takesOf)

variable {V W X W₀ Rc Tr : Type}

/-- Where the cut answers, the run lies inside the count. -/
theorem cut_inside {d a n : Due} {c : Cs d} {x : Cs n} (h : c.cut a n = some x) :
    a.e + n.e ≤ d.e := by
  unfold Cs.cut at h
  split at h
  · rename_i hle
    exact hle.2
  · cases h

/-- **Where lend returns, each entry lies inside its owner's count.** -/
theorem lend_inside (look : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (E : List Ahead) (x : CsAll ds), lend look ds E = .ok x →
    ∀ e ∈ E, e.start.e + e.count.e ≤ (look e.owner).1.e
  | [], [], _, _ => fun _ he => by cases he
  | [], _ :: _, _, h => by simp [lend] at h
  | _ :: _, [], _, h => by simp [lend] at h
  | d :: ds, a :: l, x, h => by
    simp only [lend] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    rename_i x' hcut
    obtain ⟨y, hy, -⟩ := exMap_ok h
    have e2 : a.count = d.2 := by simpa using h2
    have ih := lend_inside look ds l y hy
    intro e he
    rcases List.mem_cons.1 he with rfl | he'
    · rw [e2]
      exact cut_inside hcut
    · exact ih e he'

/-- **Where lendRow returns, each of the row's spending entries lies inside its owner's count.** -/
theorem lendRow_inside (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (p : Place) : ∀ (ps : List (Part V W X)) (j : Nat) (c : RowCoins ps),
    lendRow Bk rows look p ps j = .ok c →
    ∀ e ∈ rowEntries Bk p ps.length j, e.start.e + e.count.e ≤ (look e.owner).1.e
  | [], _, _, _ => fun _ he => by cases he
  | q :: ps, j, c, h => by
    simp only [lendRow] at h
    obtain ⟨c₁, h1, h'⟩ := exBind_ok h
    obtain ⟨r, hr, -⟩ := exMap_ok h'
    obtain ⟨c₀, h0⟩ : ∃ c₀, lendPart Bk rows look ⟨p, j⟩ q = .ok c₀ := by
      cases hq : lendPart Bk rows look ⟨p, j⟩ q with
      | error s =>
        rw [hq] at h1
        cases h1
      | ok c₀ => exact ⟨c₀, rfl⟩
    intro e he
    have he' : e ∈ spentE Bk ⟨p, j⟩ ++ rowEntries Bk p ps.length (j + 1) := he
    rcases List.mem_append.1 he' with h2 | h2
    · exact lend_inside look q.spends _ c₀.2.1 (lendPart_ok h0).2.1 e h2
    · exact lendRow_inside Bk rows look p ps (j + 1) r hr e h2

/-- The walk, at entries that lie inside. -/
theorem runOn_inside (look : Addr → (d : Due) × Cs d) (o : Addr) (s : Nat) :
    ∀ (fs : List Ahead) (c c' : Nat), runOn o s c fs = some c' → s + c ≤ (look o).1.e →
    (∀ f ∈ fs, f.start.e + f.count.e ≤ (look f.owner).1.e) → s + c' ≤ (look o).1.e
  | [], c, c', h, hc, _ => by
    obtain rfl : c = c' := Option.some.inj h
    exact hc
  | f :: fs, c, c', h, _, hin => by
    simp only [runOn] at h
    split at h
    · rename_i hf
      refine runOn_inside look o s fs (c + f.count.e) c' h ?_
        (fun g hg => hin g (List.mem_cons_of_mem f hg))
      have h1 := hin f List.mem_cons_self
      rw [hf.1, hf.2] at h1
      omega
    · cases h

/-- **Entries that are one stretch, each inside its owner's count: the stretch lies inside.** -/
theorem oneStretch_inside (look : Addr → (d : Due) × Cs d) {es : List Ahead} {o : Addr}
    {s₀ cnt : Nat} (hS : oneStretch es = some (o, s₀, cnt))
    (hin : ∀ e ∈ es, e.start.e + e.count.e ≤ (look e.owner).1.e) :
    s₀ + cnt ≤ (look o).1.e := by
  cases es with
  | nil => cases hS
  | cons e es =>
    simp only [oneStretch] at hS
    obtain ⟨c, hc, e'⟩ := Option.map_eq_some_iff.1 hS
    obtain ⟨rfl, rfl, rfl⟩ : e.owner = o ∧ e.start.e = s₀ ∧ c = cnt := by
      simpa [Prod.ext_iff] using e'
    exact runOn_inside look e.owner e.start.e es e.count.e c hc (hin e List.mem_cons_self)
      (fun g hg => hin g (List.mem_cons_of_mem e hg))

/-- **WHERE THE BOOK LENDS A ROW WHOSE ENTRIES ARE ONE STRETCH, THE STRETCH LIES INSIDE ITS OWNER'S
COUNT AT THESE COINS.** -/
theorem stretch_of_lent {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {p : Place} {ps : List (Part V W X)} {c : RowCoins ps} {o : Addr} {s₀ cnt : Nat}
    (hl : lendRow Bk rows look p ps 0 = .ok c)
    (hS : oneStretch (rowEntries Bk p ps.length 0) = some (o, s₀, cnt)) :
    s₀ + cnt ≤ (look o).1.e :=
  oneStretch_inside look hS (lendRow_inside Bk rows look p ps 0 c hl)

/-- **AT THE OUTPUT HEAD'S ROW: cnt = takesOf p FROM THE LENDING AND THE ONE STRETCH ALONE.** -/
theorem cnt_is_takes_of_lent {Bk : ProverCoinCounts} (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par)
    (at_ : Place) {ch : Nat} {o : Addr} {s₀ cnt : Nat} {rows : List (Addr × Due)} (k : Coins Bk)
    {c : RowCoins (headRow (X := X) wit p at_)}
    (hS : oneStretch (rowEntries Bk at_ (headRow (X := X) wit p at_).length 0) = some (o, s₀, cnt))
    (hl : lendRow Bk rows (k.look ch) at_ (headRow wit p at_) 0 = .ok c) : cnt = takesOf p :=
  cnt_is_takes wit p at_ k hS (stretch_of_lent hl hS) hl

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.cut_inside
#print axioms ProofFile.Honest.K6.lend_inside
#print axioms ProofFile.Honest.K6.lendRow_inside
#print axioms ProofFile.Honest.K6.runOn_inside
#print axioms ProofFile.Honest.K6.oneStretch_inside
#print axioms ProofFile.Honest.K6.stretch_of_lent
#print axioms ProofFile.Honest.K6.cnt_is_takes_of_lent
