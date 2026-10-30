-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/AtBook.lean: the closing of a segment (kind K10) at a whole book of
coins. No entry of a book that `bookWhole` returns spends a coin of the closing's part, so
`closing_good_at_scope` (Honest/K10/RowsOfClosingsAtScope.lean) holds at such a book with its premise
on the book paid.
`Good` is stated at A := B := False and says of `exact` the spender's half alone, as
Honest/K10/RowsOfClosings.lean says.

  `closing_no_seed`   no round of the kind is a round "SEND seed"
  `closing_spent_of_open`   no entry of a whole book spends a coin of the part
  `closing_good_at_book`   the statement at every link below 25

That the description passes `placesOk` is a premise. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.RowsOfClosingsAtScope
import Johnson.Desc.ProofFile.Honest.BookOwners

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- No round of the kind is a round "SEND seed". -/
theorem closing_no_seed (Q : Par) :
    ∀ r ∈ (closeRounds Q).map (·.1), r.entry.name ≠ "SEND seed" := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  unfold closeRounds at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  show e.name ≠ "SEND seed"
  unfold VerifiableInference.Desc.First.Close.entries at he
  rcases List.mem_cons.1 he with rfl | he
  · show "BAT" ≠ "SEND seed"
    decide
  rcases List.mem_cons.1 he with rfl | he
  · show "FOLD epsilon" ≠ "SEND seed"
    decide
  · obtain rfl := List.eq_of_mem_replicate he
    show "FOLD round" ≠ "SEND seed"
    decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
  {Bk : ProverCoinCounts}

/-- **No entry of a whole book spends a coin of the part**, at a closing tied to the chain c of
`IM.Open`. -/
theorem closing_spent_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay' KL : ByteArray}
    (O : IM.Open o pol lay' KL F Z Bs base c A B) (hw : bookWhole F p0 p1 p2 M = .ok Bk)
    (hp : F.placesOk = true) {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
    {b : Block S ProofFile.Cl} (hT : Tied c Z l p Q b) (q : Addr) :
    Bk.spentBy ⟨closePlace Q, 0⟩ q = [] := by
  obtain ⟨-, -, h3, -, -, hpl, hr, -⟩ := hT
  have hm : b ∈ c.blocksInOrder := List.mem_of_getElem? h3
  obtain rfl := O.desc
  have h := bookWhole_spent_nil hw hp (b := b) hm (by rw [hr]; exact closing_no_seed Q) 0 q
  rwa [hpl] at h

/-- **AT EVERY LINK BELOW 25, IN SCOPE, AT A BOOK THAT `bookWhole` RETURNS.** -/
theorem closing_good_at_book {W₀ Rc Xi Tr X : Type} (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hw : bookWhole F p0 p1 p2 M = .ok Bk) (hp : F.placesOk = true) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b ∧
      (b.planOk = true → ∀ fs : List (Fall S),
        ∃ σ : Side S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
          Side.seated c.blocksInOrder (closePlace Q) (closingPairs (closingJob readers rows stAt Z G Q)) fs =
            some σ ∧
          σ.block = b ∧
          ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (ord : List Place)
            (chain firstTree : Nat),
            Good pre Face.own σ Bk ord chain firstTree (fun _ _ _ _ => False)
              (fun _ _ _ _ => False) (closeOn true (closingJob readers rows stAt Z G Q)) closeBud ∧
            ShowsSome pre Face.own σ chain firstTree
              (closeOn true (closingJob readers rows stAt Z G Q)) closeBud) := by
  obtain ⟨p, Q, b, hT, hall⟩ := closing_good_at_scope (X := X) readers rows stAt G hS hR O l hl
  refine ⟨p, Q, b, hT, fun hb fs => ?_⟩
  obtain ⟨σ, hσ, hbl, hs, hg⟩ := hall hb fs
  exact ⟨σ, hσ, hbl, fun pre ord chain firstTree =>
    ⟨hg pre Bk ord chain firstTree (closing_spent_of_open O hw hp hT), hs pre chain firstTree⟩⟩

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closing_no_seed
#print axioms ProofFile.Honest.K10.closing_spent_of_open
#print axioms ProofFile.Honest.K10.closing_good_at_book
