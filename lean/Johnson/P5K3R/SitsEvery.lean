-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5K3R/SitsEvery.lean: THE ROW K03_sits AT THE PROOF FILE, WITHOUT A SCOPE: at every o in the
second hash's place, at every three files at which `ProofFile.onlineDescription` returns a description, at every
link of its first chain, however many there are. One lemma and one theorem with their proofs.

THE ROW (in a list that is not in this library): "the entry of the description's list of blocks at
each place of the kind is the constant of which K03_law speaks, at the plan's numbers, under the
seat's wrappers alone, or its yes gives that law's premise".

A joining. `k03_sits` (Johnson/P5K3R/Sits.lean) says the row in scope, at the fifty
numbers 14 l + i + 2 of the flat list. What needs no scope in it is
`seat_open` and `k3_alone` (Johnson/IMR/SeatOpen.lean, K3Seat.lean), `alone_underR`, `alone_planOk`
and `yes_alone` (SeatForm.lean). Here these are called at every link, and nothing else is.

  `k3Index`: in the driver's list of a link's hearing kinds K3 stands at no index but from 1 to 8.
  **`k03_sits_every`**: `onlineDescription o pol lay KL = .ok F` gives F's letters, each by the call that
    made it (`IM.Open`), and, for every part sub at a number l of the plan's list of parts and every
    index i at which the driver's `kindsBeforeBatching` names K3: the link Lk at l, its hearing block b at i,
    and b': `K3.theStated` at the lot's own letters, off the public files' record, at the driver's
    address (chain 1, link l, piece i + 1) IS b'; b is b' under the seat's three wrappers and
    nothing else (`LaidAlone`: another name and place; the mark's guard; the guard on the reply's
    seat); b narrows b'; b's test on the plan IS b''s; a yes of b leaves no mark.

Limits. Nothing on soundness; no law of the kind is called. That the plan's list of parts has a
member is not said: where it had none the sentence would be idle (a chain that is made has one: the
driver's `linksOk`). THAT NO OTHER ENTRY OF THE THREE FLAT LISTS BEARS THE KIND IS NOT SAID HERE. NO
MEMBER: that `onlineDescription` returns anywhere is a run's word.
Terms: lean/GLOSSARY.md.

-/
import Johnson.IMR.K3Seat
import Johnson.Desc.Sound.SeatNarrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- In a link's list of hearing kinds K3 stands at no index but from 1 to 8. -/
theorem k3Index (sub : ModelPart) (first : Bool) (i : ℕ)
    (hk : (kindsBeforeBatching sub first)[i]? = some KindName.K3) : 2 ≤ i + 1 ∧ i + 1 ≤ 9 := by
  have hlen : i < (kindsBeforeBatching sub first).length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hk
    exact nomatch hk
  have h9 : (kindsBeforeBatching sub first).length ≤ 9 := by cases sub <;> cases first <;> decide
  have h0 : i ≠ 0 := by
    rintro rfl
    revert hk
    cases sub <;> cases first <;> decide
  omega

/-- **K03_sits, at the proof file, without a scope.** -/
theorem k03_sits_every {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl)
        (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open o pol lay KL F Z Bs base c A B ∧
      ∀ (l : ℕ) (sub : ModelPart), (ProofFile.subsOf Z)[l]? = some sub →
      ∀ i : ℕ, (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K3 →
        ∃ (Lk : Link S Cl) (b b' : Block S Cl),
          c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
          VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W
            Z.first.codes Z.first.shape
            { chain := 1, link := some l, piece := i + 1, kind := .K3 } = some b' ∧
          IM.LaidAlone ProofFile.sameReply b b' b.name
            { chain := 1, link := some l, piece := i + 1, kind := .K3 } ∧
          b.Narrows b' ∧ b.planOk = b'.planOk ∧
          ∀ s rs gs t, b.decide s rs gs = .ok t → t.failed = none := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l sub hl i hk => ?_⟩
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_alone O l sub hl i hk (k3Index sub _ i hk)
  refine ⟨Lk, b, b', h1, h2, h3, h4, IM.alone_underR h4, IM.alone_planOk h4, ?_⟩
  intro s rs gs t hy
  exact ((IM.yes_alone h4 (fun e => nomatch e) s t rs gs).1 hy).2.1

end K3Lot

#print axioms K3Lot.k3Index
#print axioms K3Lot.k03_sits_every
