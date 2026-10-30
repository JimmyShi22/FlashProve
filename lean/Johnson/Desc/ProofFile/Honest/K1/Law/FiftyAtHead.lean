-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean: the kind K1's fifty later sendings (every
link's reads and digits), under the library's head: six of the ten premises of xk_later_at
(Johnson/Desc/ProofFile/Honest/K1/Law/FormBehind.lean) are proved, and three more are replaced by
one test at the state behind the step.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), l < 25, d a Boolean (false: the reads; true: the digits), and blk
whatever stands at the number noL l d in the first chain's flat list.
  - paid_later_head: blk stands under the lot's own sub-protocol blkL, and the four premises on the
    numbers (hinj, trees, msgs, hP) hold at h.𝔇.N. No premise is left but h, l < 25 and the entry.
  - mark_later_head: behind an accepting step of blk the state has no mark (the premise h1).
  - xk_later_six_head: the table's six tests on the verifier's state (IM.XK,
    Johnson/IMR/HandsDef.lean) hold at the next border behind an accepting step of blk. Its
    premises: no mark and the six tests at the state in front; the open link's frame's group there
    (hg); and the further test E at the next border at the state behind (h6). It holds for every
    further test E. xk_later_six_W is the same at the letters P5J.At.N Zp cF, IM.linksW and
    IM.placesW.
  - head_N_is: h.𝔇.N = P5J.At.N Zp cF, by unfolding.
No thread, no prover and no file's string occurs. No definition. Statements and proofs.

How it fits. xk_later_at has ten premises beside the step and what stands in front: the seat (hu),
hinj, trees, msgs, hP, hg, hOrd, hRide, hNew, h1. The first five come from sealed lemmas: the
opening from the head (LaidAt.opened, Johnson/P5J/LaidOpens.lean); the seat by k01_flat
(Johnson/Desc/K1/Law/LettersAtFifty.lean); the four on the numbers by hinj_of, trees_of, msgs_of and
hP_of (Johnson/Desc/K1/Law/CallsC.lean) at planK1_head, whose six fields come from
Johnson/Desc/K1/Law/TestsAtAll.lean, Johnson/Desc/K1/Law/PinsAtHead.lean and
Johnson/Desc/K1/Law/TellsAtFifty.lean. h1 comes from k01_flat_reads and k01_flat_digits
(Johnson/Desc/K1/Law/K01LawTied.lean) and IM.alone_noMark (Johnson/IMR/MemberPath.lean). The
library's IM.case_noMark, in that file, goes through all ten forms of an entry, from the premise
FlatCase: no mark behind, or the entry is number 0, or it stands behind a link's batching. Its arm
"hear" makes the same call. hOrd, hRide and hNew fall for h6 by xk_of_four
(Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindSix.lean): the four tests on the book-keeping are
had at a further test that is true at the next border (handsPt_later_four, by hands_later,
Johnson/Desc/AtSeats/HandsAtLater.lean).

Names (namespace ProofFile.Honest.K1).
  handsPt_later_four, xk_later_six   general in the numbers N and in E: what one later sending owes
    at such a test, at one state in front; the six tests behind, from h6.
  planK1_head   PlanK1 (Johnson/Desc/K1/Law/CallsC.lean) at h.𝔇.N and toldBy cF.blocksInOrder, under the head
    and the opening.
  paid_later_head, mark_later_head, xk_later_six_head, head_N_is, xk_later_six_W   as above.

Limits, the weightiest first.
  1. xk_later_six_head by itself is less than "the six behind from the six in front": h6 is a
    premise at the state behind the step. At E := P1K2.EQ (Johnson/P1K2R/TieTwo.lean) it says "in
    order" and the public tests of the items that are open or tied at the next border. This file
    does not prove it there.
  2. hg is a premise at the state in front. This file does not prove it.
  3. This file shows no value of the head h, and no state at which a premise of xk_later_six_head
    holds. That blk accepts anywhere is not shown here.
  4. At the written list of links linksFull (IM.linksW is that list: IM.linksW_full,
    Johnson/IMR/K8Owed.lean). Nothing on the first segment's opening (number 2) or on W's sending
    (number 356).
  5. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehindSix
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.K1.Law.TellsAtFifty
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.CallsC
import Johnson.Desc.AtSeats.HandsAtLater
import Johnson.Desc.AtSeats.HandsAtThree
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.IMR.MemberPath
import Johnson.IMR.K8Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull toldBy)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1 (blkL parL noL momL laterSeatsB layOf PlanK1)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open HashBuild (handsPt_of_all)

/-! ## 1 General in the numbers and in the further test -/

/-- **What one later sending owes at a further test that is true at the next border, at one state
in front.** -/
theorem handsPt_later_four (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (c : Block S ProofFile.Cl) (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (s₀ : S)
    (hg : s₀.failed = none → ∀ L, s₀.link? = some L → L.check.frame.group = N.groupAt l) :
    IM.HandsPt N linksFull (flatPlacesOf linksFull true)
      (fun j t => decide (j = noL l d + 1) || E j t) ft (noL l d) c s₀ :=
  handsPt_of_all s₀ fun E₀ h1 h2 =>
    K1.hands_later N E₀ ft Z G l hl d X arrs c hu hinj trees msgs hP
      (fun s h0 hx => by
        obtain ⟨rfl, _⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hg h0)
      fun s s' _ _ _ _ => by
        rw [h2]
        show (decide (noL l d + 1 = noL l d + 1) || E (noL l d + 1) s') = true
        rw [decide_eq_true rfl, Bool.true_or]

/-- **The six tests at the next border, behind an accepting step**: from the six in front, facts at
that one state, and the further test at the state behind (h6). -/
theorem xk_later_six (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (c : Block S ProofFile.Cl) (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (s s' : S)
    (hg : s.failed = none → ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hy : IM.Yes ft c s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksFull (flatPlacesOf linksFull true) E (noL l d) s = true)
    (h6 : E (noL l d + 1) s' = true) :
    IM.XK N linksFull (flatPlacesOf linksFull true) E (noL l d + 1) s' = true :=
  xk_of_four (handsPt_later_four N E ft Z G l hl d X arrs c hu hinj trees msgs hP s hg) hy h0 h1 hx
    h6

/-! ## 2 Under the library's head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **What the kind's law asks of the plan's side (PlanK1), under the head and the opening.** -/
theorem planK1_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    PlanK1 h.𝔇.N (toldBy cF.blocksInOrder) Zp Bs.G₀
      (fun l d => h.𝔇.N.treesAt (flatPlacesOf linksFull true)[noL l d]?) where
  rows := K1.hRows_atAll h
  book := K1.hBook_atAll h O
  fence := K1.hFence_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)
  sent := K1.hSent_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)
  tells := fun l hl d => by
    cases d with
    | true => exact K1.tells_digits h.scope h.reads O (fun b hb => (K1.hOk_atAll h O b hb).1) l hl
    | false => exact K1.tells_reads h.scope h.reads O (fun b hb => (K1.hOk_atAll h O b hb).1) l hl
  base := fun _ _ _ => rfl

/-- **Five of xk_later_at's ten premises, proved under the head**: the seat and the four on the
numbers, at whatever stands at the place's number in the first chain's flat list. -/
theorem paid_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk) :
    ∃ (Bs : ProofFile.PureBase) (X : LinkH) (arrs : Option (List ℕ)),
      blk.UnderR ((blkL Zp Bs.G₀ l d X arrs).retype : Block S ProofFile.Cl) ∧
      (∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
        h.𝔇.N.groupAt m' = h.𝔇.N.groupAt l → m' = l) ∧
      h.𝔇.N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
        h.𝔇.N.treesAt (flatPlacesOf linksFull true)[noL l d]? +
          (layOf (parL Zp Bs.G₀ l d)).shapes.size ∧
      h.𝔇.N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
        h.𝔇.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Zp Bs.G₀ l d).sent.size ∧
      laterSeatsB h.𝔇.N (parL Zp Bs.G₀ l d) l (momL d)
        (h.𝔇.N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨e, X, arrs, he, hu⟩ := K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have H := planK1_head h O
  exact ⟨Bs, X, arrs, hu, K1.hinj_of H l hl d, K1.trees_of H l hl d, K1.msgs_of H l hl d,
    K1.hP_of H (K1.hs_atAll h O (K1.pin1_atAll h)) l hl d⟩

/-- **No mark behind an accepting step** of what stands there. -/
theorem mark_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft blk s s') : s'.failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, gs, hd⟩ := HashBuild.yes_decides hy
  cases d with
  | true =>
    obtain ⟨e, digits, he, hla⟩ := K1.k01_flat_digits h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact (IM.alone_noMark hla hd).2
  | false =>
    obtain ⟨e, Xl, reads, he, -, hla⟩ := K1.k01_flat_reads h.scope h.reads O l hl
    obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
    exact (IM.alone_noMark hla hd).2

/-- **The six tests at the next border, behind an accepting step of what stands there**, under the
head: from the six in front, the open link's frame's group at the state in front (hg), and the
further test at the state behind (h6). -/
theorem xk_later_six_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk) (E : ℕ → S → Bool)
    (ft : ℕ) {s s' : S}
    (hg : s.failed = none → ∀ L, s.link? = some L → L.check.frame.group = h.𝔇.N.groupAt l)
    (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK h.𝔇.N linksFull (flatPlacesOf linksFull true) E (noL l d) s = true)
    (h6 : E (noL l d + 1) s' = true) :
    IM.XK h.𝔇.N linksFull (flatPlacesOf linksFull true) E (noL l d + 1) s' = true := by
  obtain ⟨Bs, X, arrs, hu, hinj, trees, msgs, hP⟩ := paid_later_head h hl d hb
  exact xk_later_six h.𝔇.N E ft Zp Bs.G₀ l hl d X arrs blk hu hinj trees msgs hP s s' hg hy h0
    (mark_later_head h hl d hb ft hy) hx h6

/-- The numbers under the head are the library's At.N. -/
theorem head_N_is (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : h.𝔇.N = P5J.At.N Zp cF := rfl

/-- The same at the letters P5J.At.N, IM.linksW and IM.placesW. -/
theorem xk_later_six_W (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk) (E : ℕ → S → Bool)
    (ft : ℕ) {s s' : S}
    (hg : s.failed = none →
      ∀ L, s.link? = some L → L.check.frame.group = (P5J.At.N Zp cF).groupAt l)
    (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW E (noL l d) s = true)
    (h6 : E (noL l d + 1) s' = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW E (noL l d + 1) s' = true := by
  rw [IM.placesW_full, IM.linksW_full, ← head_N_is h] at hx ⊢
  rw [← head_N_is h] at hg
  exact xk_later_six_head h hl d hb E ft hg hy h0 hx h6

end ProofFile.Honest.K1
