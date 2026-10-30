-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeAtReach.lean

It states no goal. No property of the protocol is claimed.

«finish_lays» UNDER THE HEAD: at every state without a mark
that is reached by the members' own steps at border 354 of the proof file's first chain, and at which the promise's test
`membersHeld` says yes, THE LOCAL SHAPE IN FRONT OF THE CLOSING TEST IS THE WRITTEN ONE: group 25, carrier 185, mask
186, tree 76, each as a whole record. No closed shape of the state is used or made.

  `accept_at_353`               what is reached at 354 stands behind an accept of the last code switch's place, from a
                                state reached at 353
  `closingGroupLaid_at_reach`   THE STATEMENT

By what. `reach_last`, `seat353_open` (Johnson/Loose/H2K12/GroupAt354.lean, Seat353AtMg.lean), `step_decides`;
`finish_lays_of_public`, `finish_public_written`, `finish_values_written` (LotLShapePublic.lean); at the state in front
(353): `Meaning.K2.shape_field`, `groups_field`, `codes_field` (Johnson/IMR/AtReach.lean), `count_fin`
(Johnson/IMR/FinCount.lean), `FoldFacts.rowsSent`, `bookFits`, `bookInOrder` by `foldFacts_raw`
(Honest/Thread/ReachFacts.lean). THE NUMBERS COME BACKWARDS FROM 354: the carrier is 185 since the group's one member is
(`closingMemberAtReach`, LotLSeatMember.lean); the tree is 76 since the listed place of 185 is (76, 0)
(`place_of_seats`); the tree's number is 76 since the book is in order (`numbers_of_book0`).

IMPORTS OF Johnson.Top.H0.*: none by name.

Hypotheses. h: the library's head at the format's second hash function. reached, unmarked, members: as in
`closingMemberAtReach`.

What stands under ∃. n: how many generator rows lie open behind the plain one. τ: the new tree's shape, tied by
`treesOfFinish shapeFull codesFull2 = some lay`, `lay.shapes = #[τ]`.

Limits.
- The full size alone.
- members is a clause of the promise: a thread's stand gives it; a bare reach does not.
- Nothing on what a row holds of. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapePublic
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatMember
import Johnson.Loose.H2K12.Seat353AtMg
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.LotL
open OnBytes (Group)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Ground.Sh (stSh bookSh freshOrc grp_get tree_get)
open VerifiableInference.Desc.First (S membersHeld)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open VerifiableInference.Desc.K12.Door (atFirstBook atFirstSeats atFirstFits place_of_seats numbers_of_book0
  roots_of_book)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (bookFitsB_iff)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (codesFull2)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **What is reached at 354 stands behind an accept of the last code switch's place.** -/
theorem accept_at_353 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {p : ProofFile.InstPub} {s' : S}
    (reached : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s')) :
    ∃ (s : S) (q : P2) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 353 (p, s) ∧ q.stands = .finish ∧
        (finishPlace q : Block S Unit).decide s rs gs = .ok s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, q, hb, hK⟩ := H2K12.seat353_open h.scope h.reads O h.laid.planOk
  obtain ⟨s, b', h0, hb', hy⟩ := H2K12.reach_last reached
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨R, c, -, e⟩ := hy
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides 0 b s s' R c _ e
  exact ⟨s, q, _, gs, h0, hK.1, hK.2 _ _ _ _ hd⟩

/-- **THE LOCAL SHAPE IN FRONT OF THE CLOSING TEST IS THE WRITTEN ONE.** -/
theorem closingGroupLaid_at_reach (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {p : ProofFile.InstPub}
    {s' : S} (reached : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s')) (unmarked : s'.failed = none)
    (members : membersHeld (P5J.At.N Zp cF) H2K12.O354 s' = true) :
    ∃ n o lay τ, treesOfFinish shapeFull codesFull2 = some lay ∧ lay.shapes = #[τ] ∧
      s'.here = .fin o ∧ o.mask = some 186 ∧ o.fr.group = 25 ∧ s'.st.codes = codesFull2 ∧
      s'.roots = 77 ∧
      ClosingGroupLaid ⟨stSh s'.st, bookSh s'.book, s'.roots⟩ 25 185 186 76
        ⟨0, 0, [185], [false], .plain :: List.replicate n .generator, false⟩
        ⟨H2K12.shL, true, 1, [(OnBytes.Part.main, 8388607)], [25],
          OnBytes.Slice.freshLedger codesFull2 H2K12.shL, false⟩
        (freshOrc (maskNoticeOfShape shapeFull)) ⟨τ, 76, .own 76, [185, 186], true, 0⟩ := by
  obtain ⟨s, q, rs, gs, h0, hq, accept⟩ := accept_at_353 h reached
  have hs : s.failed = none := (mark_kept q hq accept).symm.trans unmarked
  have W := writtenAtHead h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P5J.flat_ok h
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h
    (fun k (a : ProofFile.InstPub × P5J.TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ q => q) (P5J.laid_at_head h) (P5J.startB_at_head h)
    (P5J.sendsB_of_madeRow h (P5J.madeRow_at_head h))
  -- the state in front
  have hshape : s.check.frame.shape = shapeFull :=
    (_root_.Meaning.K2.shape_field h.scope h.reads O hp _ id (fun _ _ q => q) 353 (p, s) h0 hs).trans
      W.shape
  have hgroups : s.check.frame.groups = OnBytes.reqGroups s.check.frame.shape :=
    _root_.Meaning.K2.groups_field h.scope h.reads O hp _ id (fun _ _ q => q) 353 (p, s) h0 hs
  have hcodes : s.st.codes = codesFull2 :=
    (_root_.Meaning.K2.codes_field h.scope h.reads O hp _ id (fun _ _ q => q) 353 (p, s) h0 hs).trans
      W.codes
  have hg25 : s.st.groups.size = 25 := by
    obtain ⟨-, R, C, f⟩ := Reach.fold h0
    exact _root_.Meaning.K2.count_fin h.scope h.reads O f
  have hlive : s.live = s.check := by
    unfold VerifiableInference.Desc.First.S.live VerifiableInference.Desc.First.S.link?
    rw [between_in_front q accept]
  have hold : ∀ o ∈ (OnBytes.singleRowsOracles s.check.frame.rows).toList, o < s.book.place.size := by
    intro o ho
    have e := F.rowsSent 353 (p, s) h0 hs o
    rw [hlive] at e
    exact e (Array.mem_toList_iff.1 ho)
  have hbelow : ∀ (i : ℕ) (x : ℕ × ℕ), s.book.place[i]? = some x → x.1 < s.book.trees.size := by
    intro i x hx
    obtain ⟨t, ht, -⟩ := (bookFitsB_iff _).1 (F.bookFits 353 (p, s) h0 hs) i x hx
    exact (Array.getElem?_eq_some_iff.1 ht).1
  obtain ⟨places, n, o, lay, τ, hlay, hτ, hpad, hhere, hmask, hgrp, hc', hroots, -, L⟩ :=
    finish_lays_of_public q hq accept hgroups
      (by rw [hshape, hcodes]; exact finish_public_written) hold hbelow
  rw [hshape, hcodes] at hlay hpad
  rw [hshape, hcodes, hg25] at L
  rw [hg25] at hgrp
  -- the written values
  have hv := finish_values_written
  simp only [Prod.mk.injEq] at hv
  obtain ⟨v₁, v₂, v₃, v₄⟩ := hv
  rw [hpad] at v₄
  have v₄' : (places.map fun x => (x.part, x.index)) = [(OnBytes.Part.main, 8388607)] :=
    Option.some.inj v₄
  rw [v₁, v₂, v₃, v₄'] at L
  -- the numbers, backwards from 354
  obtain ⟨G, hG, hGs⟩ := Option.map_eq_some_iff.1 ((grp_get s'.st 25).symm.trans L.groupIs)
  have hone := (closingMemberAtReach h reached unmarked members hG).1
  have hn : s.st.oracles.size = 185 := by
    have e : G.members.toList = [s.st.oracles.size] := congrArg (·.members) hGs
    rw [hone] at e
    exact (List.head_eq_of_cons_eq e).symm
  rw [hn] at L hmask
  have hseats : atFirstSeats LFull s' = true := F.seatsCarried 354 (p, s') reached unmarked
  have hplace : s'.book.place[185]? = some (s.book.trees.size, 0) := by
    rw [← Array.getElem?_toList]
    exact L.carrierPlace
  have htb : s.book.trees.size = 76 := by
    have e := place_of_seats hseats 185 (Array.getElem?_eq_some_iff.1 hplace).1
    rw [hplace, placesWritten, (Prod.mk.inj H2K12.index_full).2] at e
    exact congrArg Prod.fst (Option.some.inj e)
  rw [htb] at L
  have hr353 : s.roots = 76 :=
    (roots_of_book (F.bookInOrder 353 (p, s) h0 hs)).trans htb
  rw [hr353] at L hroots
  obtain ⟨T, hT, hTs⟩ := Option.map_eq_some_iff.1 ((tree_get s'.book 76).symm.trans L.treeIs)
  have hnum : q.firstTree + 76 = 76 := by
    have e : T.number = q.firstTree + 76 := congrArg (·.number) hTs
    rw [← e]
    exact numbers_of_book0 (F.bookInOrder 354 (p, s') reached unmarked) 76 T hT
  rw [hnum] at L
  exact ⟨n, o, lay, τ, hlay, hτ, hhere, hmask, hgrp, hc'.trans hcodes, hroots, L⟩

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.accept_at_353
#print axioms ProofFile.Honest.K12.LotL.closingGroupLaid_at_reach
