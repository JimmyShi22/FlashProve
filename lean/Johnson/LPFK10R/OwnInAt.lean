-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/OwnInAt.lean: THE ONE PREMISE OF room_close (RoomClose.lean), OwnIn, SHOWN AT THE REAL CHAIN AND ITS OWN START AT 24 OF THE 25 LINKS; SO THE FIELD close OF KeepShares (Johnson/P1L20R/RoomKeep.lean), TO THE LETTER, THERE, FROM THE HEAD's LINK's SENTENCE ALONE. A definition, statements and proofs.
  OwnInAt c start l   OwnIn's sentence at one link: at every state reached in front of link l's one equation (number 14 l + nA l + 4) every one of the link's own messages (L.check.frame.own) is a member of some group of the statement. ownIn_iff: OwnIn is that at all l < 25 (by the make).
  ownIn_at            InScope P · readFiles P = .ok pp · IM.Open secondHashFunction P.pol lay P.KL F Z Bs base c A B · l < 24: OwnInAt c (ProofFile.startS Z) l.
  room_close_at       the field's sentence at ONE link l, all three j, from OwnInAt c start l. room_close_later: at j = 1 | 2 (K10; "the segment is shut"), at every number: NO premise.
  room_close_below    the same three premises as ownIn_at, l < 24: the field's sentence at l, all three j: 72 of the 75 numbers. With room_close_later at l = 24: 74. THE ONE LEFT: the head's link's one equation.
  ownIn_real          the same three, with H24 : OwnInAt c (ProofFile.startS Z) 24: OwnIn c (ProofFile.startS Z).
  room_close_real     the same four: THE FIELD's OWN TEXT at start := ProofFile.startS Z.
BY: reach_fold (Johnson/Top/H0/Walk/Reach.lean: reached = a fold of the first k sub-protocols returns) · members_at (Johnson/IMR/FrameEntry.lean) at its n = 8: the link's group's members are pre ++ keptBefore ++ own.
LIMITS. **H24, THE HEAD's LINK, IS A PREMISE**
(shown in Johnson/LPFK10R/HeadLinkJoins.lean (ownIn_head),
under ownIn_at's three premises).
At the start ProofFile.startS Z alone: OwnIn is general in the start, members_at is not. In scope; at OnBytes.secondHashFunction.
No soundness statement.

-/
import Johnson.LPFK10R.RoomClose
import Johnson.IMR.FrameEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK10

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P1L20 (nA)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- OwnIn's sentence at one link. -/
def OwnInAt {Q : Type} (c : Chain S Cl) (start : Q → S) (l : ℕ) : Prop :=
  ∀ z s, Reach 0 c.blocksInOrder start (14 * l + nA l + 4) (z, s) → ∀ L, s.link? = some L →
    ∀ o ∈ L.check.frame.own, ∃ G ∈ s.st.groups, o ∈ G.members

theorem ownIn_iff {Q : Type} (c : Chain S Cl) (start : Q → S) :
    OwnIn c start ↔ ∀ l < 25, OwnInAt c start l := Iff.rfl

/-- **The field's sentence at ONE link, from OwnIn's sentence at that link.** (room_close's proof, link by link.) -/
theorem room_close_at {Q : Type} (c : Chain S Cl) (start : Q → S) {l : ℕ}
    (H : OwnInAt c start l) (p : VerifiableInference.Desc.K9.Where)
    (Qp : VerifiableInference.Desc.First.Close.Par) (j : ℕ) (x : Block S Unit)
    (hx : (VerifiableInference.Desc.K9.closeOf p Qp : List (Block S Unit))[j]? = some x) :
    P1L20.KeepsAt c start (14 * l + nA l + 4 + j) (x.retype : Block S Cl) := by
  intro z s s' hr hy hout
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have ho := P1L20.outOfGroupsB_iff.1 hout
  rcases j with _ | _ | _ | j
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨a1, a2, -⟩ := VerifiableInference.Desc.First.Close.oneEquation_ledger (Cl := Unit) p s
      s' rs gs e ho (H z s hr)
    exact hands2_of a1 a2
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨a1, a2, -⟩ :=
      VerifiableInference.Desc.First.Close.closing_ledger (Cl := Unit) Qp s s' rs gs e ho
    exact hands2_of a1 a2
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨e1, e2⟩ :=
      VerifiableInference.Desc.First.Close.shut_same (Cl := Unit) p (Qp.piece + 1) s s' rs gs e
    exact P1L20.hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout
  · cases hx

/-- **The second and the third closing sub-protocol (K10; "the segment is shut") at EVERY number k: no premise.** -/
theorem room_close_later {Q : Type} (c : Chain S Cl) (start : Q → S) (k : ℕ)
    (p : VerifiableInference.Desc.K9.Where) (Qp : VerifiableInference.Desc.First.Close.Par)
    (j : ℕ) (x : Block S Unit)
    (hx : (VerifiableInference.Desc.K9.closeOf p Qp : List (Block S Unit))[j + 1]? = some x) :
    P1L20.KeepsAt c start k (x.retype : Block S Cl) := by
  intro z s s' _ hy hout
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have ho := P1L20.outOfGroupsB_iff.1 hout
  rcases j with _ | _ | j
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨a1, a2, -⟩ :=
      VerifiableInference.Desc.First.Close.closing_ledger (Cl := Unit) Qp s s' rs gs e ho
    exact hands2_of a1 a2
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨e1, e2⟩ :=
      VerifiableInference.Desc.First.Close.shut_same (Cl := Unit) p (Qp.piece + 1) s s' rs gs e
    exact P1L20.hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout
  · cases hx

/-- **IN SCOPE, AT THE REAL CHAIN AND ITS OWN START, AT EVERY LINK BUT THE HEAD's.** -/
theorem ownIn_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24) :
    OwnInAt c (ProofFile.startS Z) l := by
  intro z s hr L hL o ho
  obtain ⟨-, rs, cols, g⟩ := reach_fold.1 hr
  have e : 14 * l + nA l + 4 = 14 * l + 3 + 8 := by
    unfold nA
    rw [if_neg (by omega)]
  rw [e] at g
  obtain ⟨L', G, pre, h1, -, -, h4, -, h6, -, -⟩ :=
    Meaning.K2.members_at hS hR O h24 (n := 8) (by omega) g
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans h1)
  refine ⟨G, Array.mem_of_getElem? h4, ?_⟩
  rw [h6]
  exact Array.mem_append_right _ ho

/-- **THE FIELD's SENTENCE AT EVERY LINK l < 24, ALL THREE j: NO PREMISE BEYOND SCOPE AND Open.** -/
theorem room_close_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24)
    (p : VerifiableInference.Desc.K9.Where) (Qp : VerifiableInference.Desc.First.Close.Par)
    (j : ℕ) (x : Block S Unit)
    (hx : (VerifiableInference.Desc.K9.closeOf p Qp : List (Block S Unit))[j]? = some x) :
    P1L20.KeepsAt c (ProofFile.startS Z) (14 * l + nA l + 4 + j) (x.retype : Block S Cl) :=
  room_close_at c (ProofFile.startS Z) (ownIn_at hS hR O h24) p Qp j x hx

/-- So OwnIn at the real chain, from the head's link's sentence alone. -/
theorem ownIn_real (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (H24 : OwnInAt c (ProofFile.startS Z) 24) : OwnIn c (ProofFile.startS Z) := by
  intro l hl
  by_cases h : l < 24
  · exact ownIn_at hS hR O h
  · obtain rfl : l = 24 := by omega
    exact H24

/-- **THE FIELD close OF KeepShares, TO THE LETTER, AT THE REAL CHAIN AND ITS OWN START, FROM THE HEAD's LINK's SENTENCE ALONE.** -/
theorem room_close_real (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (H24 : OwnInAt c (ProofFile.startS Z) 24) :
    ∀ l < 25, ∀ p Q j (x : Block S Unit), IM.k9At Z l = some p →
      ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q →
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x →
      P1L20.KeepsAt c (ProofFile.startS Z) (14 * l + nA l + 4 + j) (x.retype : Block S Cl) :=
  room_close Z c (ProofFile.startS Z) (ownIn_real hS hR O H24)

end LPFK10

#print axioms LPFK10.ownIn_at
#print axioms LPFK10.room_close_at
#print axioms LPFK10.room_close_later
#print axioms LPFK10.room_close_below
#print axioms LPFK10.ownIn_real
#print axioms LPFK10.room_close_real
