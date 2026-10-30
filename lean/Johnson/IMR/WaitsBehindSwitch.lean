-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/WaitsBehindSwitch.lean

Lemma along the first chain's fold, in the goals' scope, at the concrete earlier hash: in each of
the 25 links, at every state reached at a border strictly behind the link's code switching (kind K2;
in link 0: behind its first sending, kind K1) and up to the border in front of its batching, no
count of rows waits (S.noneWaits, Johnson/Desc/First/State.lean). No premise beyond the scope and
IM.Open. The borders, that is: 14 l + 3 ≤ k ≤ 14 l + 9 for l < 24; 340 ≤ k ≤ 347 for l = 24: 176 of
the 359 borders.
This file states no goal.

Words. A border is a number k from 0 to 358: the place between the sub-protocols number k - 1 and k
of the first chain's flat list c.blocksInOrder. A state is reached at border k if the fold of the first k
sub-protocols returns it from the start (Reach, Johnson/Top/H0/Walk/Reach.lean). Link l, l < 25, has
its hearing sub-protocols at the numbers 14 l + i + 2, i < IM.nAt l (7; at the head's link, l = 24:
9), and its batching at 14 l + IM.nAt l + 2.

Main definitions and theorems:
* "k2Number l": the number of link l's code switching, for 1 ≤ l ≤ 24: 14 l + 2; at the head's
  link, where the reply (K7) stands in front of it, 339. At l = 0: 2, the number of link 0's first
  sending (kind K1); link 0 has no code switching.
* "yesGives_owes_none": behind what a yes of a code switching gives (P1K2.YesGives,
  Johnson/P1K2R/Sits.lean), in each of its three forms, nothing is owed.
* "switch_owes_none": behind a yes of the sub-protocol number k2Number l, 1 ≤ l < 25, as it stands
  in c.blocksInOrder, nothing is owed, whatever stood in front.
* "first_sending_owes_none": the like at the number 2.
* "waits_behind_switch": the lemma of the first paragraph.

How. The weight is in lemmas of the library. VerifiableInference.Desc.First.K2.nothingWaits
(Johnson/Top/H0/Tw/K2C/Laws.lean): a yes of the kind's own decision leaves rowsOwed = none. What the
chain lays around the kind's text: IM.k2_link_sits (Johnson/IMR/FirstSeats.lean) and IM.k2_head_of
(Johnson/IMR/K2Seat.lean) with P1K2.yes_joined_gives and P1K2.yes_alone_gives
(Johnson/P1K2R/Sits.lean). What stands behind the kind's text keeps the field: opened_keeps
(Johnson/Top/H0/Walk/FrameOpened.lean), P1K2.head_shape and P1K2.finish_shape
(Johnson/P1K2R/HandsEnds.lean). Link 0: IM.first_sits (Johnson/IMR/FirstSeats.lean),
HashBuild.joined_under (Johnson/Desc/AtSeats/BackAtThree.lean), firstAtS_tl
(Johnson/Desc/K1/Law/TlAtRecord.lean), openedZeroGives (Johnson/Top/H0/Walk/FrameTiedRec.lean). From
there to the batching: hear_along (Johnson/IMR/WaitsInLink.lean). Along the fold: andThen_yes,
fold_next, fold_back (Johnson/IMR/FoldTools.lean), fold_cut (Johnson/IMR/GroupRest.lean).

Limits. Nothing at the border k2Number l itself or in front of it. (A state there from which the
switch goes on has none waiting, by the first half of nothingWaits; of a state at which the chain
stops nothing is known. Not stated here.) Nothing at a border behind a batching; at the two next
behind it a count may wait (mayWait, Johnson/Desc/First/Borders.lean). The concrete earlier hash
alone. This file shows of no state that it is reached. The library has it wherever the proof file's
decision accepts: at an opening, where F.run accepts, every border is reached at some state from
the instance's own public part (IM.reach_of_run), and in scope from the gate's yes alone, with hR
and the opening (IM.member_of_gate; both Johnson/IMR/MemberOfGate.lean). Neither is called here.
Whether the decision accepts anywhere is not known to this file.

Not claimed: anything on what a verifier accepts or on an honest prover; any property of the
protocol.

-/
import Johnson.IMR.WaitsInLink
import Johnson.IMR.GroupRest
import Johnson.P1K2R.Sits
import Johnson.P1K2R.HandsEnds
import Johnson.Top.H0.Walk.FrameOpened
import Johnson.Desc.AtSeats.BackAtThree
import Johnson.Desc.K1.Law.TlAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The number, in the first chain's flat list, of the code switching (kind K2) of link l, for
1 ≤ l ≤ 24. It is the link's first hearing sub-protocol, but at the head's link (l = 24), where the
reply (K7) stands in front of it. At l = 0 the value is 2: the number of link 0's first sending, of
kind K1: link 0 has no code switching. -/
def k2Number (l : ℕ) : ℕ := 14 * l + (if l = 24 then 1 else 0) + 2

/-- Behind what a yes of a code switching gives, in each of its three forms, nothing is owed. -/
theorem yesGives_owes_none {G : ProofFile.Ground} {a : Place} {nm : String} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : P1K2.YesGives Z G a nm s t rs gs) : t.rowsOwed = none := by
  obtain ⟨Q, n, -, -, h⟩ := h
  rcases h with ⟨-, s₁, s₂, rs', gs', -, hd, hb⟩ | ⟨l, HP, m, rs', gs', hh, -, -, -, hd, ho⟩ |
    ⟨l, -, -, hd⟩
  · rw [(P1K2.finish_shape hb).2.2]
    exact (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd).2
  · rw [(P1K2.head_shape ho).2.2]
    exact (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd).2
  · exact (VerifiableInference.Desc.First.K2.nothingWaits _ _ _ _ _ _ hd).2

/-- **Behind a yes of a link's code switching, as it stands in the chain's flat list, nothing is
owed**, whatever stood in front. -/
theorem switch_owes_none (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h1 : 1 ≤ l)
    (hl : l < 25) {b : Block S Cl} (hb : c.blocksInOrder[k2Number l]? = some b) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t) :
    t.rowsOwed = none := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b₀, x, e1, e2, -, hla, hi⟩ := IM.k2_head_of hS hR O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
    have hb' : c.blocksInOrder[14 * 24 + 1 + 2]? = some b := hb
    obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
    exact yesGives_owes_none (P1K2.yes_alone_gives hla (by decide) hi d).1
  · obtain ⟨Lk, b₀, x, e1, e2, -, hJ, hi⟩ := IM.k2_link_sits hS hR O l h1 (by omega)
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
    have hb' : c.blocksInOrder[14 * l + 0 + 2]? = some b := by
      unfold k2Number at hb
      rwa [if_neg h24] at hb
    obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
    obtain ⟨fs, f, m, rs', gs', hfs, hf', hY, -, ho, -, -⟩ := P1K2.yes_joined_gives hJ hi d
    rw [(Johnson.Desc.First.Walk.Tied.opened_keeps hfs hf' ho).2.2.2.1]
    exact yesGives_owes_none hY

/-- **Behind a yes of link 0's first sub-protocol, its first sending, nothing is owed**, whatever
stood in front. -/
theorem first_sending_owes_none (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S Cl}
    (hb : c.blocksInOrder[2]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t) : t.rowsOwed = none := by
  obtain ⟨Lk, b₀, e1, e2, L, hL, b', hb', ep, hJ⟩ :=
    IM.first_sits hS hR O 0 (by omega) KindName.K1 rfl
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb₂ : c.blocksInOrder[14 * 0 + 0 + 2]? = some b := hb
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb₂)
  obtain ⟨X, -, hu⟩ := HashBuild.joined_under hS hR O ⟨L, hL, hb'⟩ ep hJ
  obtain ⟨v, a1, a2⟩ := andThen_yes (hu.2 s rs gs t d)
  have a2' : Johnson.Desc.First.Walk.openLayZero X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol v = .ok t := a2
  rw [(Johnson.Desc.First.Walk.Tied.openedZeroGives X _ _ v t a2').2.2.1.2.2.2.2.2.1]
  exact (VerifiableInference.Desc.K1.firstAtS_tl _ _ s v _ _ a1).2

/-- **In every link, strictly behind its code switching (in link 0: behind its first sending) and
up to its batching, no count of rows waits at a reached state.** -/
theorem waits_behind_switch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {k : ℕ} (hk1 : k2Number l < k) (hk2 : k ≤ 14 * l + IM.nAt l + 2) {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) : s.noneWaits = true := by
  obtain ⟨d, rfl⟩ : ∃ d, k = k2Number l + 1 + d := ⟨k - (k2Number l + 1), by omega⟩
  obtain ⟨hle, rs, cols, f⟩ := h.fold
  have f0 : foldBlocks 0 (c.blocksInOrder.take (k2Number l + 1 + d)) (ProofFile.startS Z z) rs cols =
      .ok (s, [], []) := f
  obtain ⟨v, Rv, Cv, fv⟩ := fold_cut (k := k2Number l + 1) d f0
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := k2Number l) fv
  obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[k2Number l]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : k2Number l < c.blocksInOrder.length)⟩
  obtain ⟨rs', gs', dd⟩ := fold_next hb fu fv
  have ov : v.rowsOwed = none := by
    by_cases h0 : l = 0
    · subst h0
      exact first_sending_owes_none hS hR O hb dd
    · exact switch_owes_none hS hR O (by omega) hl hb dd
  have wv : v.noneWaits = true := by
    unfold S.noneWaits
    rw [ov]
  have e1 : k2Number l + 1 = 14 * l + ((if l = 24 then 1 else 0) + 1) + 2 := by
    unfold k2Number
    omega
  rw [e1] at fv
  refine hear_along hS hR O hl (by omega) (fun e => by simp [e]) fv wv d ?_ s [] [] ?_
  · unfold k2Number at hk2
    omega
  · rw [← e1]
    exact f0

end Meaning.K2

#print axioms Meaning.K2.yesGives_owes_none
#print axioms Meaning.K2.switch_owes_none
#print axioms Meaning.K2.first_sending_owes_none
#print axioms Meaning.K2.waits_behind_switch
