-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskSwitchHead.lean: CONDITIONAL, under the library's
hypothesis h on the public input (`P5J.AtMgA`): `covers_mask_switch_at_book` (MaskSwitchBook.lean in
this folder) AT MESSAGE NUMBER 3 OF THE SENDING OF A CODE SWITCH OF THE PLAN THAT LEADS INTO SEGMENT
2 g + 1, g < 12: the lot with that message's text covers K5's lot on the mask row (`Covers`,
Covers.lean in this folder). ITS FOUR PUBLIC PREMISES AT THE SWITCH (hn, hl, h1, hN) ARE DERIVED
UNDER h AND hG, AT THE CHOICE n := 3; its premise hT on the book stands with written numbers. No
definition; one theorem.

THE PREMISES, ALL OF THEM.
  h: the library's hypothesis: a letter of `maskLot`; here also spent (`switch_numbers_head`,
    `own_numbers_head`, `elems_head`).
  hG: G is the maker's own ground. hg: g < 12. ea: a is group g's stored plan. PUBLIC.
  hx, hZ: TIES BETWEEN LETTERS: the seat Z5 has the group's own rounds, and the link 2 g + 1: a
    caller's seat has both by its text. hx is spent for the number of parts alone.
  hp, hl: PUBLIC: p is one of the plan's switches, and leads into segment 2 g + 1. Under h and hG
    such a p is there, and just one (`switch_there_head`, `one_switch_written`, MaskRowWritten.lean
    in this folder).
  hnum: num IS K5's NUMBER OF ITS MASK MESSAGE kM (`maskNo5 h x₁ kM hk`); num is a free letter: THE
    LAW LAYS THAT NUMBER ON A LOT WITH THE TEXT OF THE SWITCH's MESSAGE 3 BY FIAT. THAT MESSAGE 3 IS
    THE ONE THAT BEARS THAT NUMBER, AN EQUATION BETWEEN n AND kM, IS NOT SAID, HERE OR IN THE ELDER
    LAW: NAMED, NOT HAD: here «3» is a choice.
  hT: ON THE BOOK: A TEST WITH CODE: what the row at K5's place ⟨1, 2 g + 1, 3, K5⟩, of 13 parts,
    spends is one stretch: of the part 0 at ⟨1, 2 g + 1, 1, K2⟩, from entry 2251, of 1072 entries.
    RUN HERE AT NO BOOK.
  hR: ON THE BOOK: A TEST WITH CODE: the frame's test on the lending at K5's row. Bk IS A FREE
    LETTER HERE: so hR is a premise; where a book is a return of the book's maker,
    `lendsRow_of_rowNamed` (LendsRow5.lean in this folder) has it from other tests.
  hS: AT EVERY RUN AND INPUT of which `Covers` speaks: THAT the switch's text answers wherever
    `maskAnswers` says yes, not what.
  D₁, rd, closing, fx, cells, x₁, kM, hk, Vd, N ARE LETTERS.

How. `switch_numbers_head`: p's place; five messages; one mask row at message 3; its entries begin
at 439 and are 8192. `own_numbers_head` with hx: 13 parts. `elems_head` (ForestAtHead.lean in this
folder): `Forest.elems a.fs` = 1812. So 3 < 5, 3 ≠ 4, 439 + 1812 = 2251, and 1812 + j < 8192 at j <
1072. `Seat5.place` is ⟨1, the link, 3, K5⟩ by its text. Then the elder law at n := 3, cnt := 1072,
ν₅ := `Forest.elems a.fs`.

Limits. CONDITIONAL. FOUR PUBLIC PREMISES ON SIZES GO, AND SEVEN THAT NAME LETTERS OF THE PLAN COME
(hG, hg, ea, hx, hZ, hp, hl): the count of binders does not fall. 1072 IS NOT SPENT AS `slotsOf
(script a.own)`: the law below ties its count to hT and hN alone; `own_numbers_head` has that the
two are one number under h: at another count hT and hR could not both hold at one book. IT MAY HOLD
EMPTILY: where hT, hR or hS fails; where K5's text is silent (`Covers` is one-way). That hT or hR
holds at any book is not said. That a lot with that number and text stands in the frame's list is
not said. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the
files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitchBook
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskRowWritten
import Johnson.Desc.ProofFile.Honest.K5.Law.ForestAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **UNDER THE HEAD, AT THE PLAN's SWITCH INTO SEGMENT 2 g + 1: THE LOT WITH THE TEXT OF ITS
MESSAGE 3 COVERS K5's LOT ON THE MASK ROW.** CONDITIONAL: under the hypothesis h; hG, hg, ea, hp,
hl: public; hx, hZ: the seat is the group's; hnum: the two lots bear one number, by fiat; hT, hR:
tests on the book; hS: wherever `maskAnswers` says yes, the switch's text answers. -/
theorem covers_mask_switch_head {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) (hx : Z5.P.x = a.own) (hZ : Z5.link = 2 * g + 1)
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) (hl : p.link = 2 * g + 1) {num : ℕ}
    (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (hT : oneStretch (rowEntries Bk ⟨1, some (2 * g + 1), 3, .K5⟩ 13 0) =
      some (⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩, 2251, 1072))
    (cells : Tr → Cells) (hR : lendsRow Bk 0 Z5.place (k5Row Z5) = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 (OnBytes.Model.Forest.elems a.fs) mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd closing p 3 k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p 3⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 (OnBytes.Model.Forest.elems a.fs)) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := switch_numbers_head h hG hp hg hl
  have e13 : (H2K5.Honest.shapes Z5.P.x).length = 13 := by
    rw [hx]
    exact (own_numbers_head h hg ea).2
  have eν : OnBytes.Model.Forest.elems a.fs = 1812 := elems_head h hg ea
  have ePl : Z5.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    unfold Seat5.place
    rw [hZ]
  refine covers_mask_switch_at_book h D₁ rd closing p (n := 3) (cnt := 1072) fx hnum ?_ ?_ e3 ?_ ?_
    cells hR hS
  · rw [e2]
    decide
  · rw [e2]
    decide
  · rw [ePl, e13, e1, e4, eν]
    exact hT
  · intro j hj
    rw [e5, eν]
    omega

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.covers_mask_switch_head
