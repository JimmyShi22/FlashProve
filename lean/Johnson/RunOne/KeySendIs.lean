-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendIs.lean, CARRIED ONTO THE DRESSED BLOCKS (Johnson/Desc/Key/One.lean): THEOREMS. **THE KEY FILE's THREE PLACES OF A SENDING ON ITS FIRST CHAIN ARE SENDINGS: IsSend, BY ITS OWN NAME**: over the OWN texts at their TRUE names (the plain ground, K1, K13, the law on K1, and
GoodSend1–3 moved into true names by program) and the blocks in their library dress (Johnson/Desc/Key/State.lean | One.lean).
This file's text is made by program.
  isSend_idxAt · isSend_msgAt · isSend_wAt     **IsSend P st₁ b** at the three joined blocks: the one premise of send_goodIn that speaks of the block
What is not claimed. send_goodIn's other premises; that the piece at the seat is sendPiece. Nothing on soundness.

-/
import Johnson.Desc.Key.One
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.K13.Keeps

set_option autoImplicit false

namespace Johnson.RunOne.KeyKeeps

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowP addRowsP addRowsFrom)
open VerifiableInference.Desc.Keeps (ebind_ok emap_ok named_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.K1 (SameMsgs IsSend decideSend)
open _root_.Desc.Plain (DState)

variable {β Cl : Type}

/-- The statement in the first chain's state. -/
def st₁ (s : ChainState β) : Statement := s.d.st


/-- **K13's seat.** -/
theorem lens_lensSt : VerifiableInference.Desc.K13.LensSt (batchLens (β := β)) st₁ where
  enter := by
    intro t t' h
    simp only [batchLens] at h
    split at h
    · cases h
    · rw [← Option.some.inj h]; rfl
  get := by
    intro t p h
    simp only [batchLens] at h
    split at h
    · rw [← Option.some.inj h]; rfl
    · cases h
  set := fun _ _ _ _ => rfl


/-- **K1's seat's yes is a yes of K1's own decision.** -/
theorem k1At_sent {name : String} {P : VerifiableInference.Desc.K1.Par} {s t : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendingSeat (β := β) (Cl := Cl) name P).decide s rs gs = .ok t) :
    ∃ ids d', VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat)) rs = .ok (ids, d') ∧ t.d.st = d'.st ∧ t.sent = ids := by
  obtain ⟨y, hy, he⟩ := emap_ok h
  obtain ⟨x, hx, hxy⟩ := emap_ok hy
  obtain ⟨ids, d'⟩ := x
  rw [← he, ← hxy]
  exact ⟨ids, d', hx, rfl, rfl⟩


theorem same_refl (A : Statement) : SameMsgs A A := ⟨rfl, fun _ => rfl⟩

theorem same_trans {A B C : Statement} (h1 : SameMsgs A B) (h2 : SameMsgs B C) : SameMsgs A C := ⟨h2.1.trans h1.1, fun j => (h2.2 j).trans (h1.2 j)⟩

theorem same_size {A B : Statement} (h : SameMsgs A B) : B.oracles.size = A.oracles.size := by
  have key : ∀ j : Nat, j < B.oracles.size ↔ j < A.oracles.size := by
    intro j
    have e := congrArg Option.isSome (h.2 j)
    simp only [Option.isSome_map] at e
    constructor
    · intro hj
      by_contra hn
      rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
    · intro hj
      by_contra hn
      rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
  rcases Nat.lt_trichotomy B.oracles.size A.oracles.size with hlt | heq | hgt
  · exact absurd ((key _).2 hlt) (Nat.lt_irrefl _)
  · exact heq
  · exact absurd ((key _).1 hgt) (Nat.lt_irrefl _)

variable {L : Type}

theorem newGroupP_same {d d' : DState L} {code maskCode n : Nat} (h : newGroupP d code maskCode = some (n, d')) : SameMsgs d.st d'.st := by
  unfold newGroupP at h
  split at h
  · have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    rw [← this.2]
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

theorem joinP_same {d d' : DState L} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d') : SameMsgs d.st d'.st := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨rfl, fun j => ?_⟩
    show ((d.st.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[j]?).map _ = _
    rw [Array.getElem?_modify]
    split
    · cases d.st.oracles[j]? <;> rfl
    · rfl
  · cases h

theorem addRowP_same {d d' : DState L} {g : Nat} {row : Row} (h : addRowP d g row = some d') : SameMsgs d.st d'.st := by
  unfold addRowP at h
  split at h
  · rw [← Option.some.inj h]
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

theorem addRowsFrom_same (g : Nat) : ∀ (l : List Row) (d d' : DState L), addRowsFrom g l d = some d' → SameMsgs d.st d'.st
  | [], d, d', h => by rw [← Option.some.inj h]; exact same_refl _
  | row :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact same_trans (addRowP_same h1) (addRowsFrom_same g l d₁ d' h2)

theorem addRowsP_same {d d' : DState L} {g : Nat} {rows : List Row} (h : addRowsP d g rows = some d') : SameMsgs d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_same g rows d d' h
  · cases h

theorem wfGroup_same {one : OneTime} {m t : ChainState β} (h : openRangesGroup one m = .ok t) : SameMsgs m.d.st t.d.st := by
  unfold openRangesGroup at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨n, d₀⟩ := g
  rw [← Except.ok.inj h]
  exact same_trans (newGroupP_same (named_ok hg)) (joinP_same (named_ok hd))

theorem joinAll13_same (g : Nat) : ∀ (l : List Nat) (d d' : VerifiableInference.Desc.K13.St), VerifiableInference.Desc.K13.joinAll g l d = .ok d' → SameMsgs d.st d'.st
  | [], d, d', h => by rw [← Except.ok.inj h]; exact same_refl _
  | o :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := bind_ok h
    exact same_trans (joinP_same (VerifiableInference.Desc.K13.there_ok h1)) (joinAll13_same g l d₁ d' h2)

/-- K13's text behind W's commitment leaves every message's shape, mark and sample rows. -/
theorem rows13_same {S : LinShape} {claim : LinClaim} {ids : Array Nat} {d : VerifiableInference.Desc.K13.St} {y : LinFirst × VerifiableInference.Desc.K13.St}
    (h : VerifiableInference.Desc.K13.rows S claim ids d = .ok y) : SameMsgs d.st y.2.st := by
  unfold VerifiableInference.Desc.K13.rows at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  obtain ⟨d₁, h1, h⟩ := bind_ok h
  obtain ⟨d₂, h2, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨d₃, h3, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨d₄, h4, h⟩ := bind_ok h
  obtain ⟨n, d₀⟩ := b
  rw [← Except.ok.inj h]
  have e3 : SameMsgs d₂.st d₃.st := by
    have h3' := VerifiableInference.Desc.K13.there_ok h3
    split at h3'
    · exact joinP_same h3'
    · rw [← Option.some.inj h3']; exact same_refl _
  exact same_trans (same_trans (same_trans (same_trans (newGroupP_same (VerifiableInference.Desc.K13.there_ok hb)) (joinAll13_same _ _ _ _ h1))
    (joinP_same (VerifiableInference.Desc.K13.there_ok h2))) e3) (addRowsP_same (VerifiableInference.Desc.K13.there_ok h4))

/-- **idx.1.send is a sending.** -/
theorem idx_send (one : OneTime) (N : Pieces) (groups : List (List Nat)) : ∀ (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (sendIndexMasks (Cl := Cl) one N groups).decide s [r₁, r₂] gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat),
        decideSend (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) owed d [r₁, r₂] = .ok (ids, d') ∧ SameMsgs d'.st (st₁ s') ∧ (st₁ s').oracles.size = d'.st.oracles.size := by
  intro s s' r₁ r₂ gs h
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  obtain ⟨_, _, h2⟩ := bind_ok h2
  have e : st₁ s' = d'.st := by rw [← Except.ok.inj h2]; exact e1
  exact ⟨_, _, d', _, ids, hd, by rw [e]; exact same_refl _, by rw [e]⟩

/-- **msg.1.send is a sending.** -/
theorem msg_send (one : OneTime) (N : Pieces) (groups : List (List Nat)) : ∀ (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (sendOwnMessage (Cl := Cl) one N groups).decide s [r₁, r₂] gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat),
        decideSend (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) owed d [r₁, r₂] = .ok (ids, d') ∧ SameMsgs d'.st (st₁ s') ∧
          (st₁ s').oracles.size = d'.st.oracles.size := by
  intro s s' r₁ r₂ gs h
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  have hs : SameMsgs d'.st (st₁ s') := by rw [← e1]; exact wfGroup_same h2
  exact ⟨_, _, d', _, ids, hd, hs, same_size hs⟩

/-- **w.1.send is a sending**, whatever block wAt gives. -/
theorem w_send {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)} {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw) :
    ∃ msg, linMessageW one.lin = some msg ∧ ∀ (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))), bw.decide s [r₁, r₂] gs = .ok s' →
      ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat),
        decideSend (sendingPar one N.w "W and what rides with it" msg groups) owed d [r₁, r₂] = .ok (ids, d') ∧ SameMsgs d'.st (st₁ s') ∧ (st₁ s').oracles.size = d'.st.oracles.size := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none => rw [hm] at hb; cases hb
  | some msg =>
    rw [hm] at hb
    have hb' := Option.some.inj hb
    subst hb'
    refine ⟨msg, rfl, fun s s' r₁ r₂ gs h => ?_⟩
    obtain ⟨m₃, h₃, hr⟩ := ebind_ok h
    obtain ⟨m₂, h₂, hq₂⟩ := ebind_ok h₃
    obtain ⟨m₁, hq₁, hk⟩ := ebind_ok h₂
    obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent hk
    have e₃ := Except.ok.inj hq₂
    -- K13's part behind
    obtain ⟨p, hp, hr⟩ := bind_ok hr
    obtain ⟨l, _, hr⟩ := bind_ok hr
    obtain ⟨o, ho, hr⟩ := bind_ok hr
    have hpd : p.d.st = st₁ m₃ := lens_lensSt.get _ _ (VerifiableInference.Desc.K13.part_ok hp)
    have hs' : st₁ s' = o.2.st := by rw [← Except.ok.inj hr]; rfl
    have hs : SameMsgs d'.st (st₁ s') := by
      rw [hs', ← e1]
      have : st₁ m₃ = m₂.d.st := by rw [← e₃]; rfl
      rw [← this, ← hpd]
      exact rows13_same ho
    exact ⟨_, _, d', _, ids, hd, hs, same_size hs⟩


/-- **idx.1.send is a sending, by the law's own name.** -/
theorem isSend_idxAt (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    IsSend (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) (st₁ (β := β)) (sendIndexMasks (Cl := Cl) one N groups) := idx_send one N groups

theorem isSend_msgAt (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    IsSend (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) (st₁ (β := β)) (sendOwnMessage (Cl := Cl) one N groups) := msg_send one N groups

theorem isSend_wAt {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)} {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw) :
    ∃ msg, linMessageW one.lin = some msg ∧ IsSend (sendingPar one N.w "W and what rides with it" msg groups) st₁ bw := w_send hb

end Johnson.RunOne.KeyKeeps

#print axioms Johnson.RunOne.KeyKeeps.isSend_idxAt
#print axioms Johnson.RunOne.KeyKeeps.isSend_msgAt
#print axioms Johnson.RunOne.KeyKeeps.isSend_wAt
