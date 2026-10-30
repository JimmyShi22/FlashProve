-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieKit.lean: the closing of a segment (K10): three small laws for the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean).

  `closingFrom_base`   the number of the next stretch that the walk over the folds in front returns (`closingFrom`,
                     Honest/K2/Closing.lean): the number it began at, plus the messages of the segments walked
  `cut_in`             a cut of coins that lies inside the cut from 0 on is a cut of that cut
  **`carried_in_own`**   a carried stretch is a cut of its owner's own coins: there is such a cut, where the book's entry lies inside
                     the owner's count

Limits. That the entry lies inside the count is a premise. One look-up of coins serves both sides.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchLent
import Johnson.Desc.ProofFile.Honest.K2.Closing
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.K2.Honest (Left)
open ProofFile.Honest.K2 (SegmentPub Stretch FreshTable closingFrom)
open ProofFile.Honest.K2.Reads (bind_ok')

/-- The number of the next stretch behind the segments walked. -/
theorem closingFrom_base {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape))
      (x : Option (Left × List OnBytes.OracleShape) × Nat),
      closingFrom table own heard k segs j base prev = .ok x → x.2 = base + (segs.map (·.messages)).sum
  | [], _, base, prev, x, h => by
    obtain rfl : (prev, base) = x := Except.ok.inj h
    simp
  | S :: rest, j, base, prev, x, h => by
    have h' : (K2.segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind
        (fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)) = .ok x := h
    obtain ⟨W, -, h2⟩ := bind_ok' h'
    rw [closingFrom_base rest (j + 1) (base + S.messages) (some W) x h2, List.map_cons, List.sum_cons]
    omega

/-- A cut that lies inside the cut from 0 on is a cut of that cut. -/
theorem cut_in {d t a n : Due} {c : Cs d} {c₁ : Cs t} {x : Cs n} (h1 : c.cut ⟨0, 0⟩ t = some c₁)
    (h2 : c.cut a n = some x) (hf : a.f + n.f ≤ t.f) (he : a.e + n.e ≤ t.e) : c₁.cut a n = some x := by
  unfold Cs.cut at h1 h2 ⊢
  split at h1
  · cases h1
    split at h2
    · cases h2
      rw [dif_pos ⟨hf, he⟩]
      refine congrArg some ?_
      congr 1
      · funext i
        exact congrArg c.f (Fin.ext (Nat.zero_add _))
      · funext i
        exact congrArg c.e (Fin.ext (Nat.zero_add _))
    · cases h2
  · cases h1

/-- **A carried stretch is a cut of its owner's own coins.** -/
theorem carried_in_own {look : Addr → (d : Due) × Cs d} {ds : List (String × Due)} {l : List Ahead} {y : CsAll ds}
    (h : lend look ds l = .ok y) {n : Nat} {a : Ahead} (hn : l[n]? = some a) {t : Due} {c₁ : Cs t}
    (h1 : (look a.owner).2.cut ⟨0, 0⟩ t = some c₁) (hf : a.start.f + a.count.f ≤ t.f)
    (he : a.start.e + a.count.e ≤ t.e) :
    ∃ c' : Cs a.count, c₁.cut a.start a.count = some c' ∧ Stretch.carried ds y n = .ok ⟨a.count, c'⟩ := by
  obtain ⟨x, hx, hs⟩ := carried_cut look ds l y h n a hn
  exact ⟨x, cut_in h1 hx hf he, hs⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closingFrom_base
#print axioms ProofFile.Honest.K10.cut_in
#print axioms ProofFile.Honest.K10.carried_in_own
