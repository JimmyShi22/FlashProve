-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeardStays.lean: what the output head's own block laid as "what the head
heard" stays in the carried record, from behind that block onward: the relation, who is shown to
keep it, and what follows at a later record.

Law/PlanesStay.lean's SamePlanes asks also the tables and the record of the smallness test: the step
that makes the tables (piece 5 of the head's link) turns both, so SamePlanes does not hold across
piece 5. The claim on the weights reads neither. Here is the shorter relation, which does hold
across it.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  SameHeard s s': the request's words and the heard reply are the same; and where s stands in the
      head's link, so does s', with the same: opened; what the head heard (x); what the lookup left
      (lookHeard). Nothing is asked of the ledger, of the tables or of the smallness test's record.
  SameHeard.refl, SameHeard.trans; sameHeard_of_planes, sameHeard_of_alike: SamePlanes gives it, and
      so does Law/RunsFixed.lean's Alike (which asks besides: the tables, squaresP, a later ledger
      and the arrays' widths; and nothing of the smallness test's record). Neither of these two
      gives the other; both fail across piece 5, on the tables.
  readsQuiet_sameHeard: a yes of the step that makes the head's tables keeps it.
  five_sameHeard: A YES OF PIECE 5's BLOCK (the reads' sending with that step behind it) KEEPS IT.
  heard_at: behind a yes of the head's block at s', and SameHeard s' sQ: sQ stands in the head's
      link with x = heardOf gk H (Law/WeightTwinAt.lean's x_behind's letters), and its request's
      words are those of the record in front of the head's block.

Every letter under "there is", and the clause that pins it. heard_at: g by given at s; H, F1 by the
hearing's return; a by s.here; gk by a.lookHeard; o' by sQ.here.
WHO OWES SameHeard, from behind piece 5 on: as in Law/PlanesStay.lean's head: the digits' lookup and
the step behind it, the merge and the step behind it, the batching's own rounds.
What it does not say. That a later block keeps it. Nothing on the ledger: that a hidden value stays
is another law. Nothing on chance. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.PlanesStay
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8

/-- **The second record holds what the head heard, as the first.** -/
structure SameHeard (s s' : S) : Prop where
  req : s'.req = s.req
  reply : s'.out.reply = s.out.reply
  head : ∀ o, s.here = .head o → ∃ o', s'.here = .head o' ∧ o'.opened = o.opened ∧ o'.x = o.x ∧
    o'.lookHeard = o.lookHeard

theorem SameHeard.refl (s : S) : SameHeard s s :=
  ⟨rfl, rfl, fun o h => ⟨o, h, rfl, rfl, rfl⟩⟩

theorem SameHeard.trans {s s' s'' : S} (a : SameHeard s s') (b : SameHeard s' s'') :
    SameHeard s s'' := by
  refine ⟨b.req.trans a.req, b.reply.trans a.reply, fun o h => ?_⟩
  obtain ⟨o1, h1, a1, a2, a3⟩ := a.head o h
  obtain ⟨o2, h2, b1, b2, b3⟩ := b.head o1 h1
  exact ⟨o2, h2, b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem sameHeard_of_planes {s s' : S} (a : SamePlanes s s') : SameHeard s s' := by
  refine ⟨a.req, a.reply, fun o h => ?_⟩
  obtain ⟨o', h', a1, a2, _, a4, _⟩ := a.head o h
  exact ⟨o', h', a1, a2, a4⟩

/-- Law/RunsFixed.lean's Alike gives it too. -/
theorem sameHeard_of_alike {s s' : S} (a : Alike s s') : SameHeard s s' := by
  obtain ⟨o, o', ho, ho', e1, _, _, e4, e5, e6, e7, _, _⟩ := a
  refine ⟨e7, e6, fun o2 h => ?_⟩
  have e : First.Here.head o = .head o2 := ho.symm.trans h
  cases e
  exact ⟨o', ho', e4, e1, e5⟩

/-- **A yes of the step that makes the head's tables keeps it.** -/
theorem readsQuiet_sameHeard {P : ReadsQuiet.PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    SameHeard s s' := by
  obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := ReadsQuiet.head_ok hd
  refine ⟨rfl, rfl, fun o h => ?_⟩
  have e : First.Here.head a = .head o := ha.symm.trans h
  cases e
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- **A yes of piece 5's block keeps it.** -/
theorem five_sameHeard {q : Params.First} {gp : _root_.Desc.Plain.GPar} {l moment : Nat}
    {arrays : Option (List Nat)} {name : String} {P : ReadsQuiet.PH} {s1 s3 : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name (ReadsQuiet.head P)).decide s1 rs gs =
      .ok s3) : SameHeard s1 s3 := by
  obtain ⟨s2, a1, a2⟩ := andThen_ok h5
  exact (sameHeard_of_planes (commit_same a1)).trans (readsQuiet_sameHeard a2)

/-- **What the head heard, at a later record.** -/
theorem heard_at (h : Model.Head.Shape) (iU3 work l : Nat) {s s' sQ : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') (hst : SameHeard s' sQ) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : Forest.Heard) (o' : HeadOwn),
      given (parOf h work) (seatAt h iU3) s = .ok g ∧
      hear ((seatAt h iU3).ledger s) rs = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      sQ.here = .head o' ∧ o'.x = some (heardOf gk H) ∧ o'.lookHeard = some gk ∧
      o'.opened = a.opened ∧ sQ.req = s.req ∧ sQ.out.reply = s.out.reply := by
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, rfl⟩ := Came.x_behind h iU3 work l hd
  obtain ⟨o', ho', e1, e2, e3⟩ := hst.head _ rfl
  exact ⟨g, H, F1, a, gk, o', hg, hh, ha, hgk, ho', e2, e3.trans hgk, e1, hst.req, hst.reply⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sameHeard_of_planes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sameHeard_of_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readsQuiet_sameHeard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.five_sameHeard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_at
