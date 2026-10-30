-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/EqLedger.lean (for the keeping of the index masks' ledger along the
chain; the first of a link's three closing sub-protocols: kind K9's "the one equation"): THE ONE
EQUATION TURNS THE ENTRY OF ONE ORACLE MESSAGE ALONE: ONE OF THE PRESENT LINK's OWN MESSAGES; EVERY
OTHER MESSAGE's ENTRY STAYS TO THE SIGN; NO GROUP's MEMBERS TURN; WHAT WAS PUT OUT STAYS. Statements
and proofs.

Why. The one equation's row takes its mask entries out of a ledger (`asRow`,
Johnson/Desc/First/Batch/Text.lean: `takeN o ..` at o := `messageNow f f.link m`). Other files
keep, along the chain, the ledger of the index masks' message, which is a member of no group. So
they want: the message that is taken from is another one.
  `takeMaskP_other`, `takeN_other`: taking mask entries of the message o leaves every other
    message's entry. (After the proofs of `takeMaskP_bits`, `takeN_bits`,
    Johnson/Desc/First/Batch/Law/Back.lean.)
  `asRow_other`, `door_other`: so do `asRow` and `door`, at every number o' that `messageNow f
    f.link m` gives at no m.
  `now_own`: `messageNow f f.link m = some o` gives that o is among f.own.
  `door_members`: the door leaves the number of the groups and, at every number, the group's
    members.
  `oneEquation_other`: a yes of the decision of `oneEquation atS p` at s: there is the link's
    context L with s.link? = some L, and: what was put out stays; every group of the statement
    behind has the members of a group in front; and every message that is not among
    L.check.frame.own has its entry as it was.
  `oneEquation_ledger`: SO, where the index masks' message is a member of no group (ho) and every
    one of the link's own messages is a member of some group (hown): its ledger stays; it is still a
    member of no group; what was put out stays.
Limits. hown IS A PREMISE: a fact at a reached state: a walk in another file ends, in front of the
one equation, in "the link's group's members are the switch's main message, the kept copies and
L.check.frame.own" (read in that file; not imported). Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.DoorTests
import Johnson.Desc.First.Batch.Law.Hout
import Johnson.Desc.First.Batch.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Ans Equation asRow St door takeN messageNow oneEquation atS Where)
open VerifiableInference.Desc.K9L (ok_bind there_ok door_addRowP asRow_groups)

theorem takeMaskP_other {X : Type} (d d' : St X) (o n : ℕ)
    (h : Ground.takeMaskP d o = some (n, d')) (o' : ℕ) (hne : o' ≠ o) :
    d'.st.oracles[o']? = d.st.oracles[o']? := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
    show (d.st.oracles.modify o _)[o']? = _
    rw [Array.getElem?_modify, if_neg fun c => hne c.symm]
  · simp at h

theorem takeN_other {X : Type} (o : ℕ) : ∀ (n : ℕ) (d : St X) (acc : List ℕ)
    (x : List ℕ × St X), takeN o n d acc = .ok x → ∀ o', o' ≠ o →
    x.2.st.oracles[o']? = d.st.oracles[o']?
  | 0, d, acc, x, h, _, _ => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
  | n + 1, d, acc, x, h, o', hne => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    rw [takeN_other o n y.2 _ x h o' hne, takeMaskP_other d y.2 o y.1 (there_ok hy) o' hne]

theorem asRow_other {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) (o' : ℕ)
    (hne : ∀ m, messageNow f f.link m ≠ some o') : d'.st.oracles[o']? = d.st.oracles[o']? := by
  unfold asRow at h
  obtain ⟨row0, _, h⟩ := ok_bind h
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : d = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : x.2 = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact takeN_other o _ d [] x hx o' fun c => hne m (by rw [there_ok ho, c])

theorem door_other {X : Type} (owed laid : Option ℕ) (L : LinkCtx) (F : Fork) (d : St X)
    (out : VerifiableInference.Desc.K9.Out X) (h : door owed laid L F d = .ok out) (o' : ℕ)
    (hne : ∀ m, messageNow L.check.frame L.check.frame.link m ≠ some o') :
    out.d.st.oracles[o']? = d.st.oracles[o']? := by
  obtain ⟨q, G, row, d1, _, hr, ha⟩ := door_addRowP owed laid L F d out h
  unfold Ground.addRowP at ha
  split at ha
  · rw [← Option.some.inj ha]
    exact asRow_other _ _ _ _ _ _ hr o' hne
  · simp at ha

/-- At the present link the message is one of the link's own. -/
theorem now_own {f : ReqFrame} {m o : ℕ} (h : messageNow f f.link m = some o) : o ∈ f.own := by
  unfold messageNow at h
  split at h
  · cases h
  · rw [if_pos (beq_self_eq_true _)] at h
    exact Array.mem_of_getElem? h

/-- The door leaves the number of the groups and each group's members. -/
theorem door_members {X : Type} (owed laid : Option ℕ) (L : LinkCtx) (F : Fork) (d : St X)
    (out : VerifiableInference.Desc.K9.Out X) (h : door owed laid L F d = .ok out) (i : ℕ) :
    (out.d.st.groups[i]?).map (fun G : Group => G.members) =
      (d.st.groups[i]?).map fun G : Group => G.members := by
  obtain ⟨q, G, row, d1, _, hr, ha⟩ := door_addRowP owed laid L F d out h
  unfold Ground.addRowP at ha
  split at ha
  · rw [← Option.some.inj ha, ← asRow_groups _ _ _ _ _ _ hr]
    show ((d1.st.groups.modify _ _)[i]?).map _ = _
    rw [Array.getElem?_modify]
    split
    · cases d1.st.groups[i]? <;> rfl
    · rfl
  · simp at ha

/-- **THE ONE EQUATION.** -/
theorem oneEquation_other {Cl : Type} (p : Where) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok s') :
    ∃ L, s.link? = some L ∧ s'.out = s.out ∧
      (∀ i : ℕ, (s'.st.groups[i]?).map (fun G : Group => G.members) =
        (s.st.groups[i]?).map fun G : Group => G.members) ∧
      ∀ o', o' ∉ L.check.frame.own → s'.st.oracles[o']? = s.st.oracles[o']? := by
  have hout := VerifiableInference.Desc.K9.oneEquation_keeps
    VerifiableInference.Desc.K9.beside_out p h
  simp only [oneEquation] at h
  obtain ⟨a, ha, h⟩ := ok_bind h
  obtain ⟨o, ho, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have hg := there_ok ha
  simp only [atS, bind, Option.bind] at hg
  cases hL : s.link? with
  | none => rw [hL] at hg; cases hg
  | some L =>
    rw [hL] at hg
    cases hF : s.fork? with
    | none => rw [hF] at hg; cases hg
    | some F =>
      rw [hF] at hg
      cases hT : s.tl? with
      | none => rw [hT] at hg; cases hg
      | some tl =>
        rw [hT] at hg
        cases hU : VerifiableInference.Desc.K9.usedOf s with
        | none => rw [hU] at hg; cases hg
        | some u =>
          rw [hU] at hg
          obtain rfl := Option.some.inj hg
          exact ⟨L, rfl, hout, fun i => door_members _ _ _ _ _ _ ho i,
            fun o' hn => door_other _ _ _ _ _ _ ho o' fun m c => hn (now_own c)⟩

/-- **So the ledger of a message outside the groups stays**, where the link's own messages are
members. -/
theorem oneEquation_ledger {Cl : Type} (p : Where) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok s')
    (ho : ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members)
    (hown : ∀ L, s.link? = some L → ∀ o ∈ L.check.frame.own, ∃ G ∈ s.st.groups, o ∈ G.members) :
    (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) =
        (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) ∧
      (∀ G ∈ s'.st.groups, s'.out.indexMasks ∉ G.members) ∧ s'.out = s.out := by
  obtain ⟨L, hL, e1, e2, e3⟩ := oneEquation_other p s s' rs gs h
  have hn : s.out.indexMasks ∉ L.check.frame.own := fun c => by
    obtain ⟨G, hG, hm⟩ := hown L hL _ c
    exact ho G hG hm
  rw [e1]
  refine ⟨by rw [e3 _ hn], fun G' hG' => ?_, rfl⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hG'
  have k := e2 i
  rw [Array.getElem?_eq_getElem hi, Option.map_some] at k
  cases hs : s.st.groups[i]? with
  | none => rw [hs] at k; cases k
  | some G₀ =>
    rw [hs, Option.map_some] at k
    rw [Option.some.inj k]
    exact ho G₀ (Array.mem_of_getElem? hs)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.door_other
#print axioms VerifiableInference.Desc.First.Close.door_members
#print axioms VerifiableInference.Desc.First.Close.oneEquation_other
#print axioms VerifiableInference.Desc.First.Close.oneEquation_ledger
