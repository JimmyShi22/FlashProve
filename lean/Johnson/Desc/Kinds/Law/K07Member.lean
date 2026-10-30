-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07Member.lean: A TOY FOR THE ROW K07_law: THE PREMISES OF THE NEXT TOKEN's LAW (K07Statement.lean) CAN BE MET
TOGETHER. K07Member: there are a record type, a seat that gives back what is laid, public parameters,
numbers T r e asked, records s, s', sHead, sEnd, rounds and letters at which ALL premises of both halves hold:
the next token's block returns from s to s'; the seat holds at the head's record sHead what it holds at s'
(no premise of the law: it ties the two halves to one token) and at the last record sEnd; at sHead the head's
letters are there; at sEnd the last test's part says yes.
sHead = s' and sEnd = s' are not asked: no run of the first chain can pay that (the reply is heard
before the link is opened, the head's letters want it opened).
k07Member_spends: the clauses are the law's premises: the law applies to a member with nothing else in hand.
WHAT IT IS NOT. k07Member's own witness is a toy: a record that is the seat alone (there the three records are one),
a made-up point of the lookup, a vocabulary of ten, two positions. Nothing of a real run, of the first chain's
record or of the fold. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.K07Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)

/-- **The premises of K07LawStatement, met together, about one token.** -/
def K07Member : Prop :=
  ∃ (S : Type) (L : Seat S) (p : Par) (T r e asked : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (sHead sEnd : S) (g : Given),
    (∀ s x, L.reply (L.setReply s x) = some x) ∧
    Reply.decide p.sizes.V L.toSeat s rs = some s' ∧
    L.reply sHead = L.reply s' ∧
    L.reply sHead = L.reply sEnd ∧
    given p L sHead = .ok g ∧
    Reply.fin p.sizes.V T r e asked L.toSeat sEnd = true

namespace K07Toy

/-- A point of four coordinates, made up. -/
def z4 : Point := #[E.mk3 3 0 0, E.mk3 5 0 0, E.mk3 7 0 0, E.mk3 11 0 0]

/-- Public parameters, made up: a vocabulary of 10; T = 2 positions. -/
def p : Par :=
  { sizes := { lt := 1, ls := 1, d := 2, MF := 24, KF := 17, epsF := 1, V := 10, sh := 7, F := 24 }
    policy := ⟨128, 128, 0⟩, sT := 3, floor := 0, work := 0, before := [] }

/-- The key point of call number i, made up: of just the size that the head's letters ask for, ending in
the lookup's point's last ls + lt coordinates. -/
def zkAt (i : Nat) : Point :=
  let _ := p.sizes
  Array.replicate (lJ p.floor (callList.getD i []) - Norm.ls) (E.mk3 2 0 0)
    ++ z4.last (Norm.ls + Norm.lt)

/-- The head's seat at a record that is the next token's seat alone. -/
def L : Seat (Option E) :=
  { reply := id, setReply := fun _ x => some x
    request := fun _ => ⟨fun _ => 0, 0, 2⟩, ledger := fun _ => {}
    lookup := fun _ => some (z4, zkAt), reads := fun _ => none, heard := fun _ => none
    setLedger := fun s _ => .ok s, setHeard := fun s _ => .ok s, setWeightClaim := fun s _ => s
    setKeyForms := fun s _ => s }

theorem given_returns : (given p L (some (E.mk3 7 0 0))).toOption.isSome = true := by decide

end K07Toy

open K07Toy in
theorem k07Member : K07Member := by
  have hg := given_returns
  cases hq : given p L (some (E.mk3 7 0 0)) with
  | error e => rw [hq] at hg; cases hg
  | ok g =>
    exact ⟨Option E, L, p, 2, 0, 2, 7, none, some (E.mk3 7 0 0), [Reply.quiet [.e (7, 0, 0)]],
      some (E.mk3 7 0 0), some (E.mk3 7 0 0), g, fun _ _ => rfl, by decide, rfl, rfl, hq,
      by decide⟩

/-- THE MEMBER's CLAUSES ARE THE LAW's PREMISES: the law is applied to a member with nothing else in hand,
both halves, and gives its conclusions there. (Were a premise of the law lacking among the clauses, this
would not type.) -/
theorem k07Member_spends (m : K07Member) :
    ∃ (V asked y n : Nat), y = asked ∧ asked < V ∧ n < V := by
  obtain ⟨S, L, p, T, r, e, asked, s, s', rs, sHead, sEnd, g, h1, h2, _, h3, h4, h5⟩ := m
  obtain ⟨a, b⟩ := k07Law S L h1 p T r e asked
  obtain ⟨_, n, hn, _⟩ := a s s' rs h2
  obtain ⟨c1, c2, _⟩ := b sHead sEnd g h3 h4 h5
  exact ⟨p.sizes.V, asked, g.token.y, n, c1, c2, hn⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07Member
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07Member_spends
