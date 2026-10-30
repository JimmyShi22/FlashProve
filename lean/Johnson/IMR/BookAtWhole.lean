-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookAtWhole.lean:
bookAt (Johnson/Desc/First/Borders.lean: a fixed clause of the
promise at every
border of the first chain) AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST, TO THE CHAIN's END, IN THE
GOALS' SCOPE, FROM THE FOLD's RETURN ALONE, UNDER K1Told AND K2Told.

MARK WELL: through BookAtCut.lean this file stands over two further files
(see that file's head).



  bookAt_scope: **InScope P · readFiles P = .ok pp · O : Open OnBytes.secondHashFunction … · K1Told · K2Told · k
      ≤ 353 · borderOf ps ps[k]? = k · blocksOk (c.blocksInOrder.take k) = true · foldBlocks 0 (c.blocksInOrder.take
      k) (ProofFile.startS Z p) R C = .ok r ⇒ bookAt (N.withTold ps (toldOf c.blocksInOrder)) ps[k]? r.1 = true**,
      at every N and ps.
  bookAt_whole: **the same at every k ≤ 358.** (It holds bookAt_scope within itself; the elder stays
      for whoever has called it.)
THE THREE CONJUNCTS at a cut behind the last link: Johnson/IMR/MsgsBehind.lean's counts_at_cut and
roots_trees_at_cut; Johnson/IMR/BookAtCut.lean's treesTold_eq and msgsTold_eq.
PREMISES, AND WHO CAN PAY. K1Told · K2Told: see Johnson/IMR/MsgsScope.lean's head. borderOf ps
ps[k]? = k:
holds where the list of places has no place twice in front of k: the caller's ps. blocksOk:
F.planOk.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope;
not verify(). User: the table; across_M4 [not in this library], which asks bookAt at border 356; the
field "book" of the seats. Letters: N, ps.
OVER WHICH BYTES: as Johnson/IMR/MsgsBehind.lean and Johnson/IMR/BookAtCut.lean. Compiled with the whole library.
Limits. In scope alone; ft = 0. No member. Book-keeping. Nothing on
soundness.
-/
import Johnson.IMR.MsgsBehind
import Johnson.IMR.BookAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S bookAt borderOf Numbers treesTold msgsTold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN THE GOALS' SCOPE: PART 5's bookAt AT EVERY SUCH CUT.** -/
theorem bookAt_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (N : Numbers) (ps : List Place) {k : Nat} (hk : k ≤ 353) (hb : borderOf ps ps[k]? = k)
    (hp : blocksOk (c.blocksInOrder.take k) = true) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    bookAt (N.withTold ps (toldOf c.blocksInOrder)) ps[k]? r.1 = true :=
  bookAt_at_cut O h1 N ps k (by rw [front_len hS hR O]; exact hk) hb hp 0 p R C
    (hM_scope hS hR O hT hk (fun b hb' => by
      have t := List.all_eq_true.1 hp b hb'
      rw [Bool.and_eq_true] at t
      exact t.1) p R C) r h

/-- **IN THE GOALS' SCOPE: PART 5's bookAt AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST, TO ITS
END.** -/
theorem bookAt_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (N : Numbers) (ps : List Place) {k : Nat} (hk : k ≤ 358) (hb : borderOf ps ps[k]? = k)
    (hp : blocksOk (c.blocksInOrder.take k) = true) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    bookAt (N.withTold ps (toldOf c.blocksInOrder)) ps[k]? r.1 = true := by
  have hpl : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true := fun b hb' => by
    have t := List.all_eq_true.1 hp b hb'
    rw [Bool.and_eq_true] at t
    exact t.1
  obtain ⟨e4, e3, e1⟩ := counts_at_cut hS hR O h1 hT p R C k hk hpl r h
  have e2 := roots_trees_at_cut O k hpl 0 p R C r h
  unfold bookAt
  show (r.1.book.trees.size == treesTold (toldOf c.blocksInOrder) (borderOf ps ps[k]?) &&
    r.1.book.place.size == r.1.st.oracles.size &&
    r.1.st.oracles.size == msgsTold (toldOf c.blocksInOrder) (borderOf ps ps[k]?)) = true
  rw [hb, treesTold_eq _ _ hp, msgsTold_eq, ← e2, e1, e3, e4]
  simp

#print axioms bookAt_scope
#print axioms bookAt_whole

end Meaning.Carry
