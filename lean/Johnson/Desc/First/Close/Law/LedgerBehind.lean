-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LedgerBehind.lean (kind K10; for the keeping of the index masks' ledger
along the chain): PAST K10, AND PAST THE SUB-PROTOCOL "the segment is shut" BEHIND IT, THE LEDGER OF
A MESSAGE THAT IS A MEMBER OF NO GROUP STAYS TO THE SIGN, AND IT IS STILL A MEMBER OF NO GROUP.
Statements and proofs.

Why. The beginning of a group's test closes the ledger of every member of the group (`closeLedgers`,
OnBytes/Slice/BlkBegin.lean). Other files keep, along the whole chain, "the index masks'
message's ledger is not closed and has n entries left"; by a reading K10 can hand this
on only for a message outside the groups. This file is K10's share, in plain terms: no name of those
files is used.
  `closeLedgers_other`: closing the ledgers of a list of messages leaves every message that is not
    in the list as it was.
  `behind_ledger`: in the statement behind a closing (`spent (begun S g G) id`, StBehind.lean,
    beside this file) a message that is no member of G has the ledger that it had in S. (`spent`
    turns the field spentAsMask alone: so this holds of the fresh mask too.)
  `k10_ledger`: at a yes of the frame's closing at what K10 reads of the state s, for every number o
    that is a member of no group of s.st: behind K10's writing: o's ledger is as it was; o is a
    member of no group; what was put out is as it was.
  `closing_ledger`: the same at a yes of the decision of `K9.closing Q`, at o := s.out.indexMasks,
    in the words of those other files' two tests unfolded.
  `shut_same`: a yes of the decision of `K9.shut p piece` leaves the statement and what was put out.
Limits. Nothing on the first of a link's three closing sub-protocols (the one equation): there mask
entries ARE taken from a ledger: that of the link's own message with the mask row. Nothing on
whether a message is outside the groups at any state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.RidesMore
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- Closing the ledgers of a list of messages leaves every other message as it was. -/
theorem closeLedgers_other : ∀ (l : List ℕ) (T : Statement) (o : ℕ), o ∉ l →
    (closeLedgers T l).oracles[o]? = T.oracles[o]?
  | [], _, _, _ => rfl
  | a :: l, T, o, h => by
    have ha : a ≠ o := fun e => h (e ▸ List.mem_cons_self)
    have hl : o ∉ l := fun e => h (List.mem_cons_of_mem _ e)
    show (closeLedgers _ l).oracles[o]? = _
    rw [closeLedgers_other l _ o hl]
    show (T.oracles.modify a _)[o]? = _
    rw [Array.getElem?_modify, if_neg ha]

/-- **Behind a closing a message outside the group has the ledger that it had.** -/
theorem behind_ledger (T : Statement) (g : ℕ) (G : Group) (id o : ℕ) (ho : o ∉ G.members) :
    ((spent (begun T g G) id).oracles[o]?).bind (·.ledger) = (T.oracles[o]?).bind (·.ledger) := by
  have hl : o ∉ G.members.toList := fun e => ho (Array.mem_toList_iff.1 e)
  show (((closeLedgers T G.members.toList).oracles.modify id _)[o]?).bind _ = _
  rw [Array.getElem?_modify, closeLedgers_other _ T o hl]
  split
  · cases T.oracles[o]? <;> rfl
  · rfl

/-- **PAST K10.** -/
theorem k10_ledger (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (x : ReqFrame × Statement)
    (hx : closeFrame (recOf s).owed (recOf s).frame (recOf s).st es rs = .ok x) (o : ℕ)
    (ho : ∀ G ∈ s.st.groups, o ∉ G.members) :
    ((putRec s ⟨none, x.1, x.2⟩).st.oracles[o]?).bind (·.ledger) =
        (s.st.oracles[o]?).bind (·.ledger) ∧
      (∀ G ∈ (putRec s ⟨none, x.1, x.2⟩).st.groups, o ∉ G.members) ∧
      (putRec s ⟨none, x.1, x.2⟩).out = s.out := by
  obtain ⟨G, id, -, hG, e⟩ := closeFrame_st hx
  obtain ⟨h1, -, -, -, -, -, h7⟩ := k10_rides_more s es rs x hx
  have hGm : G ∈ s.st.groups := Array.mem_of_getElem? hG
  refine ⟨?_, fun G' hG' => ?_, h1⟩
  · show (x.2.oracles[o]?).bind _ = _
    rw [e]
    exact behind_ledger _ _ G id o (ho G hGm)
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hG'
    have k := h7 i
    rw [Array.getElem?_eq_getElem hi, Option.map_some] at k
    cases hs : s.st.groups[i]? with
    | none => rw [hs] at k; cases k
    | some G₀ =>
      rw [hs, Option.map_some] at k
      have km : ((putRec s ⟨none, x.1, x.2⟩).st.groups[i]).members = G₀.members :=
        congrArg Prod.fst (Option.some.inj k)
      rw [km]
      exact ho G₀ (Array.mem_of_getElem? hs)

/-- **At a yes of K10's decision, at the index masks' message.** -/
theorem closing_ledger {Cl : Type} (Q : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.K9.closing (Cl := Cl) Q).decide s rs gs = .ok s')
    (ho : ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members) :
    (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) =
        (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) ∧
      (∀ G ∈ s'.st.groups, s'.out.indexMasks ∉ G.members) ∧ s'.out = s.out := by
  obtain ⟨x, hx, rfl⟩ := closing_writes Q s s' rs gs h
  obtain ⟨a, b, c⟩ := k10_ledger s _ rs x hx _ ho
  rw [c]
  exact ⟨a, b, rfl⟩

/-- "The segment is shut" leaves the statement and what was put out. -/
theorem shut_same {Cl : Type} (p : VerifiableInference.Desc.K9.Where) (piece : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.K9.shut (Cl := Cl) p piece).decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out := by
  simp only [VerifiableInference.Desc.K9.shut] at h
  cases hL : s.link? with
  | none => rw [hL] at h; cases h
  | some L =>
    rw [hL] at h
    obtain rfl := Except.ok.inj h
    unfold S.putLink
    split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.behind_ledger
#print axioms VerifiableInference.Desc.First.Close.k10_ledger
#print axioms VerifiableInference.Desc.First.Close.closing_ledger
#print axioms VerifiableInference.Desc.First.Close.shut_same
