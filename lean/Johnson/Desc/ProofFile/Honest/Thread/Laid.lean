-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Laid.lean: the book gives each sub-protocol's `Step`s their
coins, at all coins, from one return of `ready`. `Plays` (Honest/Thread/Pays.lean) has the equation
"`chainSteps` … [blk] hs = .ok l" as a hypothesis of its own, and `Behind`, `Exchange`, `MadeNext`
and `Accepted` have it, under "there is an l", inside `Thread.Moved`: they hold vacuously where the
book or the prover's side does not fit; `good_at_thr` (Honest/Thread/GoodAt.lean) takes "at all
coins there is such an l" as a hypothesis. Here that condition is obtained, for every sub-protocol
of the three chains' flat lists, from one return of `ready` (Honest/Frame.lean) at any one input and
any one run's coins: so no kind's author has to prove it. Lemmas on the functions of
Honest/Frame.lean; general in the description, the book and the prover.

  `laid_cut`, `laid_member`   a chain's `Step`s are prepared without an error: so are one
     sub-protocol's
  `laid_first`, `laid_shared`, `laid_second`   at a file, at all coins and whatever the prover's
     sides see
  `lent_first`, `lent_shared`, `lent_second`   so `lendRow` returns for a list of parts, at all
     coins

By `chainSteps_append` (Honest/Law/Cut.lean) and `chainSteps_any`, `look_due`
(Honest/Law/ReadyAny.lean): the book gives coins by names and counts alone.

Limits.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Xi W₀ Rc Ky Tr X₀ X : Type}

theorem laid_cut {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} {pre t : List (Block S Cl)} {b : Block S Cl}
    {l : List (Step W Y)} (h : chainSteps B rows look v (pre ++ b :: t) hs = .ok l) :
    ∃ l', chainSteps B rows look v [b] hs = .ok l' := by
  rw [chainSteps_append hs pre (b :: t)] at h
  obtain ⟨l₁, -, h2⟩ := exBind_ok h
  obtain ⟨l₂, h3, -⟩ := exMap_ok h2
  have h4 : chainSteps B rows look v ([b] ++ t) hs = .ok l₂ := h3
  rw [chainSteps_append hs [b] t] at h4
  obtain ⟨l₃, h5, -⟩ := exBind_ok h4
  exact ⟨l₃, h5⟩

theorem laid_member {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    {l : List (Step W Y)} (hj : bs[j]? = some b) (h : chainSteps B rows look v bs hs = .ok l) :
    ∃ l', chainSteps B rows look v [b] hs = .ok l' := by
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 hj
  have hc : bs = bs.take j ++ b :: bs.drop (j + 1) := by
    rw [← e, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  rw [hc] at h
  exact laid_cut h

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **Each sub-protocol of the first chain.** -/
theorem laid_first (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₁ F.Cl}
    (hj : F.first.blocksInOrder[j]? = some blk) (c' : Coins B) (v : Option (Local W₀ Rc Xi Tr)) :
    ∃ l, chainSteps B (B.rowsOf 0) (c'.look 0) v [blk] H.first = .ok l := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok h
  obtain ⟨l₁, e₁⟩ := laid_member hj s1
  exact chainSteps_any (look_due c c' 0) B (B.rowsOf 0) _ v H.first _ _ e₁

/-- **Each sub-protocol of the shared chain.** -/
theorem laid_shared (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₂ F.Cl}
    (hj : F.shared.blocksInOrder[j]? = some blk) (c' : Coins B) (v : Option Empty) :
    ∃ l, chainSteps B (B.rowsOf 1) (c'.look 1) v [blk] H.shared = .ok l := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok h
  obtain ⟨l₁, e₁⟩ := laid_member hj s2
  exact chainSteps_any (look_due c c' 1) B (B.rowsOf 1) _ v H.shared _ _ e₁

/-- **Each sub-protocol of the second chain.** -/
theorem laid_second (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₃ F.Cl}
    (hj : F.second.blocksInOrder[j]? = some blk) (c' : Coins B) (v : Option (Local W₀ Rc Xi Tr)) :
    ∃ l, chainSteps B (B.rowsOf 2) (c'.look 2) v [blk] H.second = .ok l := by
  obtain ⟨-, tr, -, -, -, -, -, s3⟩ := ready_ok h
  obtain ⟨l₁, e₁⟩ := laid_member hj s3
  exact chainSteps_any (look_due c c' 2) B (B.rowsOf 2) _ v H.second _ _ e₁

/-! ### The book gives each list of parts its coins -/

/-- **`lendRow` returns**, at all coins: at a sub-protocol of the first chain at whose place a
prover's side is defined. By `steps_one_half` (Honest/Law/Thread.lean). -/
theorem lent_first (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₁ F.Cl}
    (hj : F.first.blocksInOrder[j]? = some blk) {g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X}
    (hf : (H.first.find? fun g => g.place == blk.place) = some g) (c' : Coins B) :
    ∃ u, lendRow B (B.rowsOf 0) (c'.look 0) blk.place g.parts 0 = .ok u := by
  obtain ⟨l, hl⟩ := laid_first h hj c' none
  obtain ⟨u, hu, -⟩ := steps_one_half hf hl
  exact ⟨u, hu⟩

theorem lent_shared (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₂ F.Cl}
    (hj : F.shared.blocksInOrder[j]? = some blk) {g : Placed Empty (Common W₀ Rc Ky) X₀}
    (hf : (H.shared.find? fun g => g.place == blk.place) = some g) (c' : Coins B) :
    ∃ u, lendRow B (B.rowsOf 1) (c'.look 1) blk.place g.parts 0 = .ok u := by
  obtain ⟨l, hl⟩ := laid_shared h hj c' none
  obtain ⟨u, hu, -⟩ := steps_one_half hf hl
  exact ⟨u, hu⟩

theorem lent_second (h : ready F B H w₀ rc x c = .ok R) {j : Nat} {blk : Block F.S₃ F.Cl}
    (hj : F.second.blocksInOrder[j]? = some blk) {g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X}
    (hf : (H.second.find? fun g => g.place == blk.place) = some g) (c' : Coins B) :
    ∃ u, lendRow B (B.rowsOf 2) (c'.look 2) blk.place g.parts 0 = .ok u := by
  obtain ⟨l, hl⟩ := laid_second h hj c' none
  obtain ⟨u, hu, -⟩ := steps_one_half hf hl
  exact ⟨u, hu⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.laid_cut
#print axioms ProofFile.Honest.laid_member
#print axioms ProofFile.Honest.laid_first
#print axioms ProofFile.Honest.laid_shared
#print axioms ProofFile.Honest.laid_second
#print axioms ProofFile.Honest.lent_first
#print axioms ProofFile.Honest.lent_shared
#print axioms ProofFile.Honest.lent_second
