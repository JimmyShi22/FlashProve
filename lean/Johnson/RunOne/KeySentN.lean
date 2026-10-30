-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySentN.lean: THE GENERAL FORM, TYPED ONCE: WHAT A YES OF THE SEAT OF A SENDING LAYS ON THE FIRST CHAIN's STATE, AT ANY PLACE P AND ANY STATE IN FRONT: THE SIZES ADD; THE OLDER MESSAGES, TREES AND PLACES ARE KEPT. So that 1.1 · 1.17 (and, at their own state, 2.2 · 2.5) are calls. BOOK-KEEPING: no chance, no game.
OBJECT: sendingSeat name P's decision on two rounds · USER: the rows' (yes) · LETTERS: β Cl · name P.
  seat_yes    PROVED: a yes of the seat on two rounds IS a yes of K1's decideSend at the state's record; the state behind written out
  SentN       what it lays: SendLaid (Johnson/Desc/Key/Laid/SendLaid.lean) in the state's own fields: ids · codes · groups · sizes · older · new · the book's Seated · what the seat leaves (base · idx · grp · rider · atEnd · pile · msgW · ids · lin) · owed · sent
  sentN_of    PROVED: by send_laid
  sentN_order PROVED: by send_order: a statement in order stays in order
KIN: k1At_sent (in Johnson/RunOne/KeySendIs.lean) is seat_yes's core at any name and P: it gives the statement and «sent» behind; seat_yes writes out the whole state. That file's newGroupP_same | joinP_same | wfGroup_same (:86-126) say SameMsgs across the ranges' group's opening.
Nothing on soundness.
-/
import Johnson.Desc.Key.One
import Johnson.Desc.Key.Laid.SendLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.K1 (Par decideSend planOkOwn)
open VerifiableInference.Desc.Key.LaidW (SendLaid send_laid send_order)
open VerifiableInference.Desc.Book (Seated)

variable {β Cl : Type}

/-- **A yes of the seat of a sending, written out.** -/
theorem seat_yes (name : String) (P : Par) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendingSeat name P : Block (ChainState β) Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ (ids : Array Nat) (d' : _root_.Desc.Plain.DState (Array Nat)),
      decideSend P s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂] = .ok (ids, d') ∧
      s' = { s with d := withLoc ({ d' with loc := ids } : _root_.Desc.Plain.DState (Array Nat)) (), owed := none, sent := ids } := by
  have h' : ((decideSend P s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂]).map fun x =>
      ({ owed := none, held := { x.2 with loc := x.1 } } : K1.Owing (_root_.Desc.Plain.DState (Array Nat)))).map (fun y =>
        { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc }) = .ok s' := h
  cases hd : decideSend P s.debt (withLoc s.d (#[] : Array Nat)) [r₁, r₂] with
  | error e => rw [hd] at h'; cases h'
  | ok x =>
    rw [hd] at h'
    exact ⟨x.1, x.2, rfl, (Except.ok.inj h').symm⟩

/-- **What a sending's seat lays on the chain's state.** -/
structure SentN (P : Par) (s s' : ChainState β) : Prop where
  sent : s'.sent = (Array.range P.sent.size).map (· + s.d.st.oracles.size)
  plan : s.d.st.codes = P.codes
  codes : s'.d.st.codes = s.d.st.codes
  groups : s'.d.st.groups = s.d.st.groups
  size : s'.d.st.oracles.size = s.d.st.oracles.size + P.sent.size
  /-- every older message is as it was -/
  older : ∀ o, o < s.d.st.oracles.size → s'.d.st.oracles[o]? = s.d.st.oracles[o]?
  /-- each new message -/
  new : ∀ (i : Nat) (n : OracleNotice), P.sent[i]? = some n →
    ∃ x : OnBytes.Oracle, s'.d.st.oracles[s.d.st.oracles.size + i]? = some x ∧
    x.shape = n.shape ∧ x.groups = [] ∧ x.spentAsMask = false ∧
    (n.shape.answers = 0 → x.sampled = false ∧ x.sampleRows = #[]) ∧
    (n.shape.answers ≠ 0 → x.sampled = true ∧ x.sampleRows.size = n.shape.answers)
  /-- the book: Seated: the older places and trees are kept; the new ones are laid -/
  book : ∃ lay, layTrees s.d.st.codes P.sent = some lay ∧
    Seated s.d.book s'.d.book P.sent.size s.d.st.oracles.size lay (fun τ => P.gp.firstTree + (s.d.roots + τ)) (fun τ => .own (s.d.roots + τ))
  /-- the count of roots: as many more as the layout has trees: SendLaid.roots -/
  roots : ∀ lay, layTrees s.d.st.codes P.sent = some lay → s'.d.roots = s.d.roots + lay.shapes.size
  /-- what the seat leaves -/
  base : s'.base = s.base
  idx : s'.idx = s.idx
  grp : s'.grp = s.grp
  rider : s'.rider = s.rider
  atEnd : s'.atEnd = s.atEnd
  pile : s'.pile = s.pile
  lin : s'.lin = s.lin

theorem sentN_of (name : String) (P : Par) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendingSeat name P : Block (ChainState β) Cl).decide s [r₁, r₂] gs = .ok s') : SentN P s s' := by
  obtain ⟨ids, d', hyes, rfl⟩ := seat_yes name P s s' r₁ r₂ gs h
  have L := send_laid _ _ _ _ _ _ _ hyes
  exact
    { sent := L.idsAre, plan := L.plan, codes := L.codes, groups := L.groups, size := L.size, older := L.older, new := L.new, book := L.book, roots := L.roots
      base := rfl, idx := rfl, grp := rfl, rider := rfl, atEnd := rfl, pile := rfl, lin := rfl }

theorem sentN_order (name : String) (P : Par) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hB : planOkOwn P = true) (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (h : (sendingSeat name P : Block (ChainState β) Cl).decide s [r₁, r₂] gs = .ok s') (hI : Means.InOrder s.d.st) : Means.InOrder s'.d.st := by
  obtain ⟨ids, d', hyes, rfl⟩ := seat_yes name P s s' r₁ r₂ gs h
  exact (send_order P s.debt (withLoc s.d (#[] : Array Nat)) d' r₁ r₂ ids hB hfit hyes hI : Means.InOrder d'.st)

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.seat_yes
#print axioms Johnson.RunOne.KeyRows1.sentN_of
#print axioms Johnson.RunOne.KeyRows1.sentN_order
