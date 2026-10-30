-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/ReaderFour.lean: THE FOUR PREMISES ON THE CHAIN's STATE IN FRONT under which
the reader through the chain state's own book reads the rows on the table alike over a block that
sends (`OwedReader4`, Johnson/Desc/K13/Law/OwedReader4.lean, and its like at kind K1's later
places) ARE HAD FROM THE PROMISE. One statement with its proof; free of any kind of block.
  `reader_four`: at a filling with kind K13's premises on the letters (`MgK13`) and the plan's
    test "the plan's places name trees that are there" (`PlanK13.below`): where every public item
    of a list Q holds that has "K13.pileMasks" and "K12.seatsCarried", the index masks' message is
    there, and the book stands as the plan says of a place: the rows on the table name that
    message alone; its number is below the number of the statement's messages; the book has a
    place for every message; its place names a tree that is there.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MgK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)
open VerifiableInference.Desc.K12.Door (seatsCarriedB place_in_book)

/-- **The four, from the promise.** -/
theorem reader_four {Pp Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub)
    (hMg : MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hPl : PlanK13 Pp N cs ms M L)
    (hkIn : pileMasksItem ∈ Q) (hsIn : seatsItem ∈ Q) (x : Pp × S) (p : Option Place)
    (hQ : ∀ q ∈ Q, Mg.pub q x = true) (hit : Mg.pub .indexThere x = true)
    (hbk : First.bookAt N p x.2 = true) :
    pileMasksC x.2 = true ∧ x.2.out.indexMasks < x.2.st.oracles.size ∧
      x.2.book.place.size = x.2.st.oracles.size ∧
      ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size := by
  have h₃ : seatsCarriedB L x.2.book = true := by rw [← hMg.seats]; exact hQ _ hsIn
  have hk : pileMasksC x.2 = true := by rw [← hMg.masks]; exact hQ _ hkIn
  have hthere : x.2.out.indexMasks < x.2.st.oracles.size := by
    have h := hit
    rw [hMg.ours.indexThere] at h
    unfold K1.indexThereB at h
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at h
    cases h
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  refine ⟨hk, hthere, hbk'.1.2, fun q hq => ?_⟩
  obtain ⟨q', hq', hlt⟩ := place_in_book h₃ hbk'.1.2 (hPl.below x p hbk h₃) _ hthere
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  exact hlt

end VerifiableInference.Desc.K13.Law
