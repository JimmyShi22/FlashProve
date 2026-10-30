-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CutOfBook.lean: where the frame has lent a part its random values
(`lendPart`, Johnson/Desc/ProofFile/Honest/Frame.lean), and one entry of the book of random values
passes a public test, the stretch that the part carries by that entry is the sender's own values cut
from a message's offset on, by the message's count: the premise `SameCut` (TreeIsColumnAt.lean).
General in the book, the run's values, the part and the sending. It imports Mathlib.

  `carriedOf`    the entries by which the part at an address carries, in the book's order: as
                 `lendPart` takes them
  `cutFits`      the public test on the book: carried entry number n of the part at an address: its
                 owner is the sending's part; among the extension field's values it starts at
                 message k's offset (`offsetOf`, Johnson/Desc/ProofFile/Honest/K14/Sendings.lean)
                 and has that message's count (`dueOf`); it lies within the sender's count
                 (`takesOf`)
  `cut_at`       value number i of a cut is the purse's value number start + i
  `lend_cut`     what `lend` hands over for its entry number n is a cut at that entry's own owner,
                 start and count
  `carried_of_lendPart`, `lendRow_snd`   what `lendPart` hands over as carried is `lend` at
                 `carriedOf`; the second part of a row of two is lent by `lendPart`
  `coinsE_at`    the sender's values as words (`coinsE`, Johnson/Desc/ProofFile/Honest/Sum.lean), by
                 number, decoded
  `sameCut_of_book`   the statement

`(coinsE own).toArray` is what the moves of `sendingPart` (K14/Sendings.lean) hand to
`SendJob.rows`; `stretches p.carries c.2.2` is what `restCoins` (Parts.lean) and `carriedCoins`
(Sim/Row.lean) read.

`cut_at` and `lend_cut` say what `cut_e` and `lend_stretch` of AgreeBook.lean say; they stand here
anew so that this file does not import that file's ground.

Limits. No book is shown to pass `cutFits`, at a small plan or at the real size. In the maker of the
book that goes with the frame (`bookRaw`; its file does not lie beneath this one) an entry's start
and count are that maker's own count (`sendDue`, `msgDue`): another text than `offsetOf` and
`dueOf`; nothing here relates the two. The base field's values are not treated: the two sendings
take none. Nothing on how a value is sampled. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (zeroE)
open OnBytes.Slice (ofE toE readE readE_ofTriple toE_ofE)
open ProofFile.Honest.K14 (SendJob dueOf offsetOf takesOf)

variable {V W X : Type}

/-! ## 1 The test on the book -/

/-- The entries by which the part at an address carries, in the book's order. -/
def carriedOf (Bk : ProverCoinCounts) (a : Addr) : List Ahead :=
  (Bk.ahead.filter fun e => e.spender == a).filter (!·.once)

/-- **The public test on the book.** a: the part that carries. n: the entry's number among those by
which it carries. sender: the sending's part. k: the message's number in the sending. -/
def cutFits (Bk : ProverCoinCounts) (a : Addr) (n : ℕ) (sender : Addr) (J : SendJob) (k : ℕ) : Bool :=
  match (carriedOf Bk a)[n]? with
  | some e => e.owner == sender && e.start.e == offsetOf J.Q.codes J.Q.sent J.sort k &&
      e.count.e == dueOf J.Q.codes (shapeAt J k) (J.sort k) &&
      decide (e.start.e + e.count.e ≤ (takesOf J.Q.codes J.Q.sent J.sort).e)
  | none => false

/-! ## 2 What the frame lends -/

theorem cut_at {d : Due} (c : Cs d) (a n : Due) (x : Cs n) (h : c.cut a n = some x) (i : ℕ)
    (hi : i < n.e) : (stretchOf x).e i = (stretchOf c).e (a.e + i) := by
  unfold Cs.cut at h
  split at h
  · rename_i hb
    cases h
    have h2 : a.e + i < d.e := by
      have := hb.2
      omega
    simp only [stretchOf, dif_pos hi, dif_pos h2]
  · cases h

theorem lend_cut (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y → ∀ (n : ℕ) (a : Ahead),
    l[n]? = some a →
      ∃ x : Cs a.count, (look a.owner).2.cut a.start a.count = some x ∧
        stretches ds y n = stretchOf x
  | [], [], _, _, n, a, hn => by simp at hn
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h
  | d :: ds, e :: l, y, h, n, a, hn => by
    simp only [lend] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hcount
    split at h
    · cases h
    rename_i x hx
    cases hy : lend look ds l with
    | error _ =>
      rw [hy] at h
      cases h
    | ok y' =>
      rw [hy] at h
      cases h
      cases n with
      | zero =>
        obtain rfl : e = a := Option.some.inj hn
        have hc : e.count = d.2 := by simpa using hcount
        obtain ⟨dn, dd⟩ := d
        obtain ⟨en, eo, es, ec, ep, eb⟩ := e
        obtain rfl : ec = dd := hc
        exact ⟨x, hx, rfl⟩
      | succ m => exact lend_cut look ds l y' hy m a hn

theorem carried_of_lendPart (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) (c : p.Coins)
    (h : lendPart Bk rows look a p = .ok c) : lend look p.carries (carriedOf Bk a) = .ok c.2.2 := by
  unfold lendPart at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  cases h1 : lend look p.spends ((Bk.ahead.filter fun e => e.spender == a).filter (·.once)) with
  | error _ =>
    rw [h1] at h
    cases h
  | ok sp =>
    rw [h1] at h
    cases h2 : lend look p.carries ((Bk.ahead.filter fun e => e.spender == a).filter (!·.once)) with
    | error _ =>
      change Except.map _ (lend look p.carries _) = _ at h
      rw [h2] at h
      cases h
    | ok ca =>
      change Except.map _ (lend look p.carries _) = _ at h
      rw [h2] at h
      cases h
      exact h2

/-- The second part of a row of two is lent its values by `lendPart` at the part's own address. -/
theorem lendRow_snd (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : VerifiableInference.Desc.Place) (p q : Part V W X) (c : RowCoins [p, q])
    (h : lendRow Bk rows look a [p, q] 0 = .ok c) : lendPart Bk rows look ⟨a, 1⟩ q = .ok c.2.1 := by
  simp only [lendRow] at h
  cases h0 : lendPart Bk rows look ⟨a, 0⟩ p with
  | error _ =>
    rw [h0] at h
    cases h
  | ok c0 =>
    rw [h0] at h
    cases h1 : lendPart Bk rows look ⟨a, 1⟩ q with
    | error _ =>
      change Except.map _ (Except.bind (Except.mapError _ (lendPart Bk rows look ⟨a, 1⟩ q)) _) =
        _ at h
      rw [h1] at h
      cases h
    | ok c1 =>
      change Except.map _ (Except.bind (Except.mapError _ (lendPart Bk rows look ⟨a, 1⟩ q)) _) =
        _ at h
      rw [h1] at h
      cases h
      rfl

/-- The sender's values as words, by number, decoded. -/
theorem coinsE_at {d : Due} (c : Cs d) (j : ℕ) (hj : j < d.e) :
    readE ((coinsE c).toArray.getD j zeroE) = (stretchOf c).e j := by
  have e : (coinsE c).toArray.getD j zeroE = OnBytes.E.ofTriple (ofE (c.e ⟨j, hj⟩)) := by
    simp [coinsE, hj]
  rw [e, readE_ofTriple, toE_ofE]
  simp only [stretchOf, dif_pos hj]

/-! ## 3 The statement -/

/-- **The book's entry gives the cut.** own: the sender's own values, as `lendPart` cuts them out of
its purse. -/
theorem sameCut_of_book (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) (c : p.Coins) (hl : lendPart Bk rows look a p = .ok c)
    (sender : Addr) (J : SendJob) (own : Cs (takesOf J.Q.codes J.Q.sent J.sort))
    (hown : (look sender).2.cut ⟨0, 0⟩ (takesOf J.Q.codes J.Q.sent J.sort) = some own) (n k : ℕ)
    (hf : cutFits Bk a n sender J k = true) :
    SameCut J k (coinsE own).toArray (stretches p.carries c.2.2 n) := by
  unfold cutFits at hf
  split at hf
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨ho, hs⟩, hc⟩, hin⟩ := hf
    obtain ⟨x, hx, hst⟩ := lend_cut look _ _ _ (carried_of_lendPart Bk rows look a p c hl) n e he
    intro i hi
    have hi' : i < e.count.e := by
      rw [hc]
      exact hi
    have hj : e.start.e + i < (takesOf J.Q.codes J.Q.sent J.sort).e := by omega
    rw [hst, cut_at _ _ _ x hx i hi', ← hs, coinsE_at own _ hj, cut_at _ _ _ own hown _ hj, ho]
    show (stretchOf (look sender).2).e (0 + (e.start.e + i)) = _
    rw [Nat.zero_add]
  · cases hf

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.carriedOf
#print axioms ProofFile.Honest.K12.Light.cutFits
#print axioms ProofFile.Honest.K12.Light.cut_at
#print axioms ProofFile.Honest.K12.Light.lend_cut
#print axioms ProofFile.Honest.K12.Light.carried_of_lendPart
#print axioms ProofFile.Honest.K12.Light.lendRow_snd
#print axioms ProofFile.Honest.K12.Light.coinsE_at
#print axioms ProofFile.Honest.K12.Light.sameCut_of_book
