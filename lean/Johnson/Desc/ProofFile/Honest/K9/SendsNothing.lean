-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/SendsNothing.lean: THE SUB-PROTOCOLS OF THE KIND K9 SEND NOTHING AND READ NO COLUMN: under the
library's hypothesis `AtMgA`, at every number of the first chain at which the written list of places has a place of the kind K9:
no round of the sub-protocol there declares a root, or any item but roots; it declares no oracle message; and its rounds read no
column.

What it is for. A simulator, or a prover's side, is owed at a sub-protocol only if one of its rounds sends something. The two
tests with code that ask this of a prover's lists pass a sub-protocol without a side where every round has `d.entry.roots = 0`
(`rooted`, Honest/Law/PlanGives.lean) and where `(d.items.filter (· != .root)).isEmpty` (`halved`, Honest/Law/Run.lean). Both
are stated here in these very forms.

  `k9NumbersB`, `k9_numbers`, `k9_number`   on the written list of places, by Lean's kernel: a number with a place of the kind
                        K9 is a segment's batching's (14 l + `IM.nAt l` + 2), its "one equation"'s (+ 4) or its "the segment is
                        shut"'s (+ 6)
  `k9PlacesB`, `k9_places`   a control: at each of these 75 numbers the list does have such a place, so the statements below are
                        not idle
  `k9_block`          which sub-protocol stands there: the seated batching, with one round that sends nothing and draws one
                      element; or one of the two without a round
  **`k9_sends_nothing`**   THE STATEMENT on roots, items and oracle messages
  **`k9_reads_nothing`**   THE STATEMENT on columns: `readsOf` over the sub-protocol's rounds is empty, whatever is stored and
                        drawn
  `k9_rooted`, `k9_halved`   so the clause of each of the two tests at such a sub-protocol is true at every list of sides

How. The seats are the library's (`seated_at_head`, Honest/K9/AtHead.lean; `SeatedFree.shape`, AtSeatAll.lean; `close_at_head`,
`SeatedClose.quiet`, CloseKeeps.lean); the round's items and reads: `bat_items`, `bat_reads` (Honest/K9/PlayLaw.lean).

Limits. The first chain alone: of the other two chains nothing is said here. The full size and the hash function `secondHashFunction` alone:
the hypothesis's. Nothing on what a prover's lists hold. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.ProofFile.Honest.K9.PlayLaw
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 On the written list of places -/

/-- Along the list: the place at a number is not of the kind K9, or the number is one of a segment's three. -/
def k9NumbersB : Bool :=
  (List.range P5J.At.ps.length).all fun b =>
    (P5J.At.ps[b]?).all fun p =>
      p.kind != KindName.K9 || (List.range 25).any fun l =>
        b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6

/-- It accepts: by Lean's kernel. -/
theorem k9_numbers : k9NumbersB = true := by decide +kernel

/-- **A number at which the list has a place of the kind K9 is one of a segment's three.** -/
theorem k9_number {b : ℕ} {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) :
    ∃ l, l < 25 ∧ (b = 14 * l + IM.nAt l + 2 ∨ b = 14 * l + IM.nAt l + 4 ∨ b = 14 * l + IM.nAt l + 6) := by
  have hb : b < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have h0 : ((P5J.At.ps[b]?).all fun p =>
      p.kind != KindName.K9 || (List.range 25).any fun l =>
        b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6) = true :=
    List.all_eq_true.1 k9_numbers b (List.mem_range.2 hb)
  rw [hp] at h0
  have h1 : (p.kind != KindName.K9 || (List.range 25).any fun l =>
      b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6) = true := h0
  rw [hk] at h1
  rcases Eq.mp (Bool.or_eq_true _ _) h1 with h2 | h2
  · exact absurd h2 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h2
    refine ⟨l, List.mem_range.1 hl, ?_⟩
    rcases Eq.mp (Bool.or_eq_true _ _) e with e1 | e1
    · rcases Eq.mp (Bool.or_eq_true _ _) e1 with e2 | e2
      · exact Or.inl (beq_iff_eq.1 e2)
      · exact Or.inr (Or.inl (beq_iff_eq.1 e2))
    · exact Or.inr (Or.inr (beq_iff_eq.1 e1))

/-- A control: at each of the 75 numbers the list has a place of the kind K9. -/
def k9PlacesB : Bool :=
  (List.range 25).all fun l =>
    [2, 4, 6].all fun i => (P5J.At.ps[14 * l + IM.nAt l + i]?).any fun p => p.kind == KindName.K9

/-- It accepts: by Lean's kernel. -/
theorem k9_places : k9PlacesB = true := by decide +kernel

/-! ## 2 Under the hypothesis -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Which sub-protocol stands at such a number: one with the batching's one round and one empty list of oracle messages,
or one without a round and without an oracle message. -/
theorem k9_block (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) :
    (∃ q : Desc.K9.Where, blk.rounds = [{ entry := Desc.K9.entry q }] ∧ blk.oracles = [[]]) ∨
      (blk.rounds = [] ∧ blk.oracles = []) := by
  obtain ⟨l, hl, hc⟩ := k9_number hp hk
  obtain ⟨Lk, q, w, Sd₀⟩ := seated_at_head h l hl
  have Sd : SeatedFree cF Zp l (IM.nAt l) Lk q w := Sd₀
  obtain ⟨Lk', q', Qc, bE, bS, Hc⟩ := close_at_head h l hl
  obtain rfl : Lk = Lk' := Option.some.inj (Sd.link.symm.trans Hc.link)
  obtain ⟨c1, c2, c3, c4⟩ := Hc.quiet
  rcases hc with rfl | rfl | rfl
  · obtain rfl := Option.some.inj (Sd.batching.symm.trans hb)
    exact Or.inl ⟨q, Sd.shape.1, Sd.shape.2.1⟩
  · have e := Hc.atE
    rw [Sd.hears] at e
    obtain rfl := Option.some.inj (e.symm.trans hb)
    exact Or.inr ⟨c1, c2⟩
  · have e := Hc.atS
    rw [Sd.hears] at e
    obtain rfl := Option.some.inj (e.symm.trans hb)
    exact Or.inr ⟨c3, c4⟩

/-- **NO ROOT, NO ITEM BUT ROOTS, NO ORACLE MESSAGE.** -/
theorem k9_sends_nothing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) :
    (∀ d ∈ blk.rounds, d.entry.roots = 0 ∧ (d.items.filter (· != .root)).isEmpty = true) ∧
      blk.oracles.flatMap id = [] := by
  rcases k9_block h hp hk hb with ⟨q, e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
    refine ⟨fun d hd => ?_, rfl⟩
    obtain rfl := List.mem_singleton.1 hd
    exact ⟨rfl, by rw [bat_items q]; rfl⟩
  · rw [e1, e2]
    exact ⟨fun d hd => (nomatch hd), rfl⟩

/-- **NO COLUMN IS READ.** -/
theorem k9_reads_nothing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) :
    readsOf chain ft stored tree blk.rounds ds = [] := by
  rcases k9_block h hp hk hb with ⟨q, e1, -⟩ | ⟨e1, -⟩
  · rw [e1]
    exact bat_reads q chain ft stored tree ds
  · rw [e1]
    cases ds <;> rfl

/-- The clause of `rooted` at such a sub-protocol, at every list of sides. -/
theorem k9_rooted (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) : (blk.rounds.all fun d => d.entry.roots == 0) = true :=
  List.all_eq_true.2 fun d hd => beq_iff_eq.2 ((k9_sends_nothing h hp hk hb).1 d hd).1

/-- The clause of `halved` at such a sub-protocol, at every list of sides. -/
theorem k9_halved (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : ℕ} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) :
    (blk.rounds.all fun d => (d.items.filter (· != .root)).isEmpty) = true :=
  List.all_eq_true.2 fun d hd => ((k9_sends_nothing h hp hk hb).1 d hd).2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_numbers
#print axioms ProofFile.Honest.K9.k9_number
#print axioms ProofFile.Honest.K9.k9_places
#print axioms ProofFile.Honest.K9.k9_block
#print axioms ProofFile.Honest.K9.k9_sends_nothing
#print axioms ProofFile.Honest.K9.k9_reads_nothing
#print axioms ProofFile.Honest.K9.k9_rooted
#print axioms ProofFile.Honest.K9.k9_halved
