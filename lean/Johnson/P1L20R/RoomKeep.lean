-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeep.lean:
THE KEEPING BENEATH THE FACT ALONG THE FOLD "the index-mask message's ledger is not
closed and has just free0 entries less the pending rows laid so far" (room_at_reach,
RoomFold.lean): THE FIELD keep OF RoomOwes, FROM SHARES, EACH IN ITS OWN KIND'S CONSTANTS.
A RULE OVER SHARES: IT PAYS ONE THING BY ITSELF ("opened" behind a link's first sub-protocol).

  KeepsAt c start k b   what one sub-protocol owes at number k: from a REACHED state at which the
                    index-mask message is a member of no group and its ledger is not closed and has
                    n entries left, an accepting step hands both on, at every n
  KeepsAt.under     the debt of a seated sub-protocol is that of its lot's own
  numberOf p        the number in the flat list of the place p of chain 1
  KeepShares Z G c start   THE SHARES: a field a kind for the sub-protocols that a lot of the seat
                    makes (K1, but not the maker at link 0's first place; K2; K3; K4; K5; K6; K7;
                    K8; K11; K12), and three for a link's batching, the runs behind it and its
                    closing's three
  opened_ledger, opened_out   PAID: at a link behind link 0 the frame's "opened" leaves the ledger
                    as it was, and the second clause
  lot_keeps         from a kind of a link's list to its field
  room_kept_of_shares   in the goals' scope: KeepShares gives the field keep of RoomOwes, to the
                    letter: at the 303 numbers from 3 to 354 that are not the frame's own
  room_owes         with the make: RoomOwes

THE WALK. The case split over the flat list is that of flat_cases (Johnson/IMR/FlatCases.lean, in a
state that may differ from the one that ships), typed again between the numbers 3 and 354, with
KeepsAt as its end. flat_cases is not called here, though the proof of room_kept_of_shares could
fall to a case split over it.


Limits. NO SHARE IS PAID HERE. Whether each can be paid at every sub-protocol that its field binds
is not settled here: a field binds every sub-protocol of a lot of the seat at chain 1 of its
kind, at the reached states in front of its own number. WHOEVER JOINS A MESSAGE TO A GROUP (K1's
sendings; K2's code switches) owes that it is not the index masks'. In the goals' scope alone, at
OnBytes.secondHashFunction alone. No soundness statement.

-/
import Johnson.P1L20R.RoomFold
import Johnson.IMR.FirstSeats
import Johnson.IMR.CloseSeat
import Johnson.IMR.BackSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching closeKinds backKinds)
open Johnson.Desc.First.Walk.Tied
open Johnson.Desc.First.Walk.Seat (framesOf framesOf_arms LinkFrame)
open ProofFile (Cl)

/-- What is handed on from s to s': where the ledger is not closed and has n entries left: that, and
the second clause. -/
def Hands2 (s s' : S) : Prop :=
  ∀ n, leftIsB n s = true → leftIsB n s' = true ∧ outOfGroupsB s' = true

/-- Where the ledger, the groups and the index-mask message's number are as they were. -/
theorem hands2_same {s s' : S}
    (h1 : Johnson.Desc.First.Walk.Law.ledgerAt s' = Johnson.Desc.First.Walk.Law.ledgerAt s)
    (h2 : s'.st.groups = s.st.groups) (h3 : s'.out.indexMasks = s.out.indexMasks)
    (ho : outOfGroupsB s = true) : Hands2 s s' :=
  fun n hn => ⟨by rw [leftIsB_of_ledger h1]; exact hn, by rw [outOfGroupsB_same h2 h3]; exact ho⟩

/-- **What one sub-protocol owes at number k.** -/
def KeepsAt {Q : Type} (c : Chain S Cl) (start : Q → S) (k : ℕ) (b : Block S Cl) : Prop :=
  ∀ z s s', Reach 0 c.blocksInOrder start k (z, s) → StepYes 0 b s s' → outOfGroupsB s = true → Hands2 s s'

/-- The debt of a seated sub-protocol is that of its lot's own. -/
theorem KeepsAt.under {Q : Type} {c : Chain S Cl} {start : Q → S} {k : ℕ} {b b' : Block S Cl}
    (hU : b.UnderR b') (H : KeepsAt c start k b') : KeepsAt c start k b := by
  rintro z s s' hr ⟨R, cc, hl, e⟩
  exact H z s s' hr ⟨R, cc, by rw [← hU.1]; exact hl, VerifiableInference.Desc.step_under hU e⟩

/-- The number in the flat list of a place of chain 1: inside link l: 14 l + piece + 1; behind the
links: 352 + piece. -/
def numberOf (p : Place) : ℕ :=
  match p.link with
  | some l => 14 * l + p.piece + 1
  | none => 352 + p.piece

/-- Every sub-protocol of the kind K that a lot of the seat makes for chain 1 keeps, at its own
number. -/
def LotKeeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (start : Q → S)
    (K : KindName) : Prop :=
  ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) → b'.place.chain = 1 →
    b'.place.kind = K → KeepsAt c start (numberOf b'.place) b'

/-- How many sub-protocols a link has in front of its batching. -/
def nA (l : ℕ) : ℕ := if l = 24 then 9 else 7

/-- **THE SHARES.** -/
structure KeepShares {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl)
    (start : Q → S) : Prop where
  /-- the later sendings inside a link (50): not the maker, which stands at a link's first place;
  not the sending behind the links -/
  k1 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) → b'.place.chain = 1 →
    b'.place.kind = KindName.K1 → b'.place.link ≠ none → b'.place.piece ≠ 1 →
    KeepsAt c start (numberOf b'.place) b'
  /-- the code switches (24) and the one behind the links (number 353) -/
  k2 : LotKeeps Z G₀ c start KindName.K2
  k3 : LotKeeps Z G₀ c start KindName.K3
  k4 : LotKeeps Z G₀ c start KindName.K4
  k5 : LotKeeps Z G₀ c start KindName.K5
  k6 : LotKeeps Z G₀ c start KindName.K6
  k7 : LotKeeps Z G₀ c start KindName.K7
  k8 : LotKeeps Z G₀ c start KindName.K8
  k11 : LotKeeps Z G₀ c start KindName.K11
  /-- number 354 -/
  k12 : LotKeeps Z G₀ c start KindName.K12
  /-- a link's batching, at the link's own gatherer (25) -/
  batch : ∀ l < 25, ∀ (Lk : Link S Cl) p, c.links[l]? = some Lk → IM.k9At Z l = some p →
    KeepsAt c start (14 * l + nA l + 2)
      (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
        (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order))
  /-- the runs behind a link's batching (25) -/
  behind : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ z s t,
    Reach 0 c.blocksInOrder start (14 * l + nA l + 3) (z, s) → Lk.runBehind s = .ok t →
    outOfGroupsB s = true → Hands2 s t
  /-- a link's closing's three (75) -/
  close : ∀ l < 25, ∀ p Q j (x : Block S Unit), IM.k9At Z l = some p →
    ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q →
    (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x →
    KeepsAt c start (14 * l + nA l + 4 + j) (x.retype : Block S Cl)

/-- **PAID: at a link behind link 0 "opened" leaves the ledger as it was.** -/
theorem opened_ledger {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : ℕ}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) (hl : l ≠ 0) {m u : S}
    (hy : f.opened m = .ok u) :
    Johnson.Desc.First.Walk.Law.ledgerAt u = Johnson.Desc.First.Walk.Law.ledgerAt m := by
  rcases framesOf_arms h hf with ⟨X, _, _, e⟩ | ⟨h0, _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, _, _, e, _⟩
  · subst e
    obtain rfl : m = u := Except.ok.inj hy
    rfl
  · exact absurd h0 hl
  · rw [e] at hy
    obtain ⟨_, _, g3, g4, _⟩ := openedAttGives Q m u hy
    exact ledger_same g3.2.2.1 g4
  · rw [e] at hy
    obtain ⟨_, _, g3, g4, _⟩ := openedLayGives Q m u hy
    exact ledger_same g3.2.2.1 g4

/-- **PAID: and the groups and the index-mask message's number.** -/
theorem opened_out {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : ℕ}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) (hl : l ≠ 0) {m u : S}
    (hy : f.opened m = .ok u) : outOfGroupsB u = outOfGroupsB m := by
  rcases framesOf_arms h hf with ⟨X, _, _, e⟩ | ⟨h0, _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, _, _, e, _⟩
  · subst e
    obtain rfl : m = u := Except.ok.inj hy
    rfl
  · exact absurd h0 hl
  · rw [e] at hy
    obtain ⟨_, _, g3, g4, _⟩ := openedAttGives Q m u hy
    exact outOfGroupsB_same (by rw [g3.2.2.1]) (by rw [g4])
  · rw [e] at hy
    obtain ⟨_, _, g3, g4, _⟩ := openedLayGives Q m u hy
    exact outOfGroupsB_same (by rw [g3.2.2.1]) (by rw [g4])

/-- From a kind of a link's list to its field. -/
theorem lot_keeps {Q : Type} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl} {start : Q → S}
    (Sh : KeepShares Z G₀ c start)
    {sub : ModelPart} {f : Bool} {i : ℕ} {k : KindName} (hk : (kindsBeforeBatching sub f)[i]? = some k)
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) (hc : b'.place.chain = 1)
    (hkk : b'.place.kind = k) (hl : b'.place.link ≠ none)
    (h1 : b'.place.piece ≠ 1 ∨ k ≠ KindName.K1) : KeepsAt c start (numberOf b'.place) b' := by
  have hm := List.mem_of_getElem? hk
  cases k <;> first
    | exact Sh.k1 b' lot hc hkk hl (h1.resolve_right fun h => h rfl)
    | exact Sh.k2 b' lot hc hkk
    | exact Sh.k3 b' lot hc hkk
    | exact Sh.k4 b' lot hc hkk
    | exact Sh.k5 b' lot hc hkk
    | exact Sh.k6 b' lot hc hkk
    | exact Sh.k7 b' lot hc hkk
    | exact Sh.k8 b' lot hc hkk
    | exact Sh.k11 b' lot hc hkk
    | exact absurd hm (by cases sub <;> cases f <;> decide)

theorem clearIx_nA (l : ℕ) : clearIx l = 14 * l + nA l + 7 := rfl

theorem nA_le (l : ℕ) : nA l ≤ 9 := by
  unfold nA
  split <;> omega

theorem ours_laid {l : ℕ} (hl : l < 25) : isOurs (14 * l + 1) = true := by
  unfold isOurs
  exact List.any_eq_true.2 ⟨l, List.mem_range.2 hl, by simp⟩

theorem ours_cleared {l : ℕ} (hl : l < 25) : isOurs (14 * l + nA l + 7) = true := by
  unfold isOurs
  refine List.any_eq_true.2 ⟨l, List.mem_range.2 hl, ?_⟩
  rw [clearIx_nA]
  simp

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Every sub-protocol of the flat list from number 3 to number 354 that is not the frame's own
keeps. -/
theorem keepsAt_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Type} {start : Q → S}
    (Sh : KeepShares Z Bs.G₀ c start) {k : ℕ} (h3 : 3 ≤ k) (h355 : k < 355)
    (ho : isOurs k = false) {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) :
    KeepsAt c start k b := by
  have hcase : (∃ l j, l < 25 ∧ j < nA l + 7 ∧ k = 14 * l + 1 + j) ∨
      (∃ j, j < 2 ∧ k = 353 + j) := by
    by_cases h1 : k ≤ 336
    · refine Or.inl ⟨(k - 1) / 14, (k - 1) % 14, by omega, ?_, by omega⟩
      unfold nA
      rw [if_neg (by omega)]
      omega
    by_cases h2 : k ≤ 352
    · exact Or.inl ⟨24, k - 337, by omega, by unfold nA; rw [if_pos rfl]; omega, by omega⟩
    · exact Or.inr ⟨k - 353, by omega, by omega⟩
  rcases hcase with ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, -, -, -, -, -, -, iB, -, dB, -, -, -⟩ := hall l hl
    have hn' : Lk.hear.length = nA l := hn
    have hsub := IM.subs_scope hS hR O l hl
    have hj' : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ nA l) ∨ j = nA l + 1 ∨ j = nA l + 2 ∨
        (∃ q, q < 3 ∧ j = nA l + 3 + q) ∨ j = nA l + 6 := by
      by_cases a : j ≤ nA l + 2
      · omega
      · by_cases a2 : j ≤ nA l + 5
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨j - (nA l + 3), by omega, by omega⟩)))))
        · omega
    rcases hj' with rfl | rfl | ⟨j2, jn⟩ | rfl | rfl | ⟨q, hq, rfl⟩ | rfl
    · -- "laid": the frame's own
      rw [show 14 * l + 1 + 0 = 14 * l + 1 from rfl, ours_laid hl] at ho
      cases ho
    · -- the link's first place: l is not 0
      have hl0 : l ≠ 0 := by omega
      obtain ⟨k0, hk0⟩ : ∃ k0, (kindsBeforeBatching (IM.subAt l) (l == 0))[0]? = some k0 := by
        cases (IM.subAt l) <;> cases (l == 0) <;> exact ⟨_, rfl⟩
      obtain ⟨Lk', b0, e1', e2, L, hL, b', hb', ep, hjn⟩ := IM.first_sits hS hR O l hl k0 hk0
      have hix := IM.hear_at_flat e1' e2
      rw [IM.flatIx_scope hS hR O (by omega) 0] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      have hk1 : k0 ≠ KindName.K1 := by
        have hf0 : (l == 0) = false := by simp [hl0]
        rw [hf0] at hk0
        rintro rfl
        revert hk0
        generalize IM.subAt l = sub
        cases sub <;> decide
      have hK := lot_keeps Sh hk0 ⟨L, hL, hb'⟩ (by rw [ep]) (by rw [ep])
        (by rw [ep]; exact fun h => nomatch h) (Or.inr hk1)
      rw [ep] at hK
      rintro z s s' hr ⟨R, cc, hlen, e⟩ hout n hnn
      obtain ⟨fs', f', m, hfs', hf', g3, _, g5, _⟩ := hjn.step e
      obtain ⟨m1, m2⟩ := hK z s m hr ⟨R, cc, by rw [← hjn.rounds]; exact hlen, g3⟩ hout n hnn
      refine ⟨?_, by rw [opened_out hfs' hf' hl0 g5]; exact m2⟩
      rw [leftIsB_of_ledger (opened_ledger hfs' hf' hl0 g5)]
      exact m1
    · -- a sub-protocol in front of the batching, behind the first place
      obtain ⟨Lk9, -, -, -, e9, -, -, -, -, -, -, -, -, -, -, -, -, hlen9, -⟩ :=
        (IM.k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      obtain ⟨k1, hk1⟩ : ∃ k1, (kindsBeforeBatching (IM.subAt l) (l == 0))[j - 1]? = some k1 :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hlen9, hn']; omega)⟩
      have hm1 := List.mem_of_getElem? hk1
      have h9 : k1 ≠ KindName.K9 := by
        rintro rfl
        revert hm1
        cases (IM.subAt l) <;> cases (l == 0) <;> decide
      have h10 : k1 ≠ KindName.K10 := by
        rintro rfl
        revert hm1
        cases (IM.subAt l) <;> cases (l == 0) <;> decide
      have hn9 := nA_le l
      obtain ⟨Lk', b0, e1', e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
        IM.chain_hear_alone O.made O.places O.chain l (IM.subAt l) hsub (j - 1) k1 hk1 h9 h10
          ⟨by omega, by omega⟩
      have hix := IM.hear_at_flat e1' e2
      rw [IM.flatIx_scope hS hR O (by omega) (j - 1),
        show 14 * l + (j - 1) + 2 = 14 * l + 1 + j by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      have hK := lot_keeps Sh hk1 ⟨L, hL, hb'⟩ (by rw [ep]) (by rw [ep])
        (by rw [ep]; exact fun h => nomatch h) (Or.inl (by rw [ep]; show j - 1 + 1 ≠ 1; omega))
      rw [ep, show numberOf { chain := 1, link := some l, piece := j - 1 + 1, kind := k1 } =
        14 * l + 1 + j by show 14 * l + (j - 1 + 1) + 1 = _; omega] at hK
      exact hK.under (IM.alone_underR hla)
    · -- the batching
      obtain ⟨Lk9, p, -, -, e9, hp, -, -, -, -, hal, i9, -⟩ := (IM.k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      rw [hn', show 14 * l + nA l + 2 = 14 * l + 1 + (nA l + 1) by omega] at i9
      obtain rfl := Option.some.inj (i9.symm.trans hb)
      have hK := Sh.batch l hl Lk p e1 hp
      rw [show 14 * l + nA l + 2 = 14 * l + 1 + (nA l + 1) by omega] at hK
      exact hK.under (IM.alone_underR (hal _))
    · -- the runs behind the batching
      rw [hn', show 14 * l + nA l + 3 = 14 * l + 1 + (nA l + 2) by omega] at iB
      obtain rfl : bB = b := Option.some.inj (iB.symm.trans hb)
      intro z s s' hr hy hout
      obtain ⟨rs, gs, e⟩ := stepYes_decide hy
      rw [dB] at e
      rw [show 14 * l + 1 + (nA l + 2) = 14 * l + nA l + 3 by omega] at hr
      exact Sh.behind l hl Lk e1 z s s' hr e hout
    · -- the closing's three
      obtain ⟨LkC, p, Q, eC, hp, hQ, hcl⟩ := IM.close_of hS hR O l hl
      obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
      obtain ⟨kq, hkq⟩ : ∃ kq, closeKinds[q]? = some kq :=
        ⟨_, List.getElem?_eq_getElem (by show q < 3; exact hq)⟩
      obtain ⟨b0, x, e2, ex, hla⟩ := hcl q kq hkq
      have hix := IM.close_numbers hS hR O hl e1 e2
      rw [hn', show 14 * l + nA l + 4 + q = 14 * l + 1 + (nA l + 3 + q) by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      have hK := Sh.close l hl p Q q x hp hQ ex
      rw [show 14 * l + nA l + 4 + q = 14 * l + 1 + (nA l + 3 + q) by omega] at hK
      exact hK.under (IM.alone_underR hla)
    · -- "cleared": the frame's own
      rw [show 14 * l + 1 + (nA l + 6) = 14 * l + nA l + 7 by omega, ours_cleared hl] at ho
      cases ho
  · -- behind the links: numbers 353 and 354
    obtain ⟨-, -, -, hallB⟩ := IM.base_made O.made
    obtain ⟨several, hsev, -, hbk⟩ :=
      IM.chain_back_any hallB (IM.makers_K9 Z Bs.G₀) O.places O.chain
    obtain rfl : several = true := hsev.2 (IM.base_has_K13 O)
    have hkj : ∃ kj, (backKinds true)[j]? = some kj ∧ (kj = KindName.K2 ∨ kj = KindName.K12) := by
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨KindName.K2, by decide, Or.inl rfl⟩
      · exact ⟨KindName.K12, by decide, Or.inr rfl⟩
    obtain ⟨kj, hkj, hor⟩ := hkj
    have hk9 : kj ≠ KindName.K9 := by
      rcases hor with rfl | rfl <;> decide
    obtain ⟨b0, e0, sp, -, L, hL, b', hb', -, ep, hla⟩ := hbk j kj hkj hk9
    have hix := (IM.back_numbers hS hR O).1 j b0 e0
    obtain rfl := Option.some.inj (hix.symm.trans hb)
    have hU0 : b0.UnderR b' := IM.alone_underR hla
    have hU : ({ b0 with planOk := b0.planOk && b0.hasNoClaimsAndNothingAfter } : Block S Cl).UnderR b' := hU0
    have hnum : numberOf b'.place = 353 + j := by
      rw [ep]
      show 352 + (j + 1) = 353 + j
      omega
    rcases hor with rfl | rfl
    · have hK := Sh.k2 b' ⟨L, hL, hb'⟩ (by rw [ep]) (by rw [ep])
      rw [hnum] at hK
      exact hK.under hU
    · have hK := Sh.k12 b' ⟨L, hL, hb'⟩ (by rw [ep]) (by rw [ep])
      rw [hnum] at hK
      exact hK.under hU

/-- **THE FIELD keep OF RoomOwes, TO THE LETTER, FROM THE SHARES.** -/
theorem room_kept_of_shares (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Type} {start : Q → S}
    (Sh : KeepShares Z Bs.G₀ c start) :
    ∀ k, 3 ≤ k → k < 355 → isOurs k = false → ∀ b z s s', Reach 0 c.blocksInOrder start k (z, s) →
      c.blocksInOrder[k]? = some b → StepYes 0 b s s' → outOfGroupsB s = true →
      ∀ n, leftIsB n s = true → leftIsB n s' = true ∧ outOfGroupsB s' = true :=
  fun _ h3 h355 ho _ z s s' hr hb hy hout => keepsAt_flat hS hR O Sh h3 h355 ho hb z s s' hr hy hout

/-- With the make: RoomOwes. -/
theorem room_owes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Type} {start : Q → S}
    (Sh : KeepShares Z Bs.G₀ c start) {free0 : ℕ}
    (make : ∀ b z s', c.blocksInOrder[2]? = some b → StepYes 0 b (start z) s' →
      leftIsB free0 s' = true ∧ outOfGroupsB s' = true) : RoomOwes c start free0 :=
  ⟨make, room_kept_of_shares hS hR O Sh⟩

end

end P1L20

#print axioms P1L20.opened_ledger
#print axioms P1L20.lot_keeps
#print axioms P1L20.opened_out
#print axioms P1L20.keepsAt_flat
#print axioms P1L20.room_kept_of_shares
#print axioms P1L20.room_owes
