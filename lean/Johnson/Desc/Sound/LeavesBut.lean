-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LeavesBut.lean: "ONE READING h OF THE CARRIED RECORD IS TURNED BY NO BLOCK OF A CHAIN's FLAT LIST BUT AT THE PLACES TOLD
APART": what a chain's parts owe for it, and that it is enough.

Why. The description's decision folds over Chain.blocksInOrder (Johnson/Desc/Block.lean). "No block but the one that hears the reply turns the reply"
is wanted at EVERY block of that list. Block.Leaves h (Johnson/Desc/Sound/FoldHeard.lean) is the shape of the fact at one block, and
leavesLink | leavesChain (FoldHeardProofs.lean) carry it from a chain's parts to the flat list where ALL blocks leave h, with the batching's
block asked outright at the link's own claims. Here: the same with places told apart, and with the batching's debt paid down to the kinds'
single runs of claims.

  leavesClaimsInBy: where every run of claims of every block leaves h, claimsInBy leaves h, whatever the test behind each run (the like of leavesAfterIn).
  leavesRunBehind: the like for the frame's step behind the batching (the tests behind the adding cannot write, by type).
  Link.LeavesBut, Chain.LeavesBut: THE DEBT OF THE PARTS: seven clauses a link, five a chain. but: the test that tells places apart.
  Link.LeavesBut.flat, Chain.LeavesBut.flat: THE CLOSURE: every block of the flat list stands at a place that but names, or leaves h.

Silly members. but := fun _ => true: both records are met where the runs, lay and clear leave h, and the closure says nothing of any block. A
constant h: all is met, and the closure says nothing. So what the closure is worth lies in h and but.
Every "there is", walked: no statement has one.
Nearest kin. In the build on which this file was written: Block.Leaves, leavesAfterIn, leavesLink, leavesChain (used or mirrored here). In files of this project
that are not in this library: Block.Keeps | ClaimsKeep | AfterKeeps (Johnson/Desc/Plain/SeatKept.lean): Block.Keeps b π unfolds to Block.Leaves π b, to
the letter; claimsIn_back, general in a relation.
Limits. A rule: shown of no chain of the protocol here. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α : Type}

/-! ## 1 claimsIn -/

/-- **Where every run of claims of every block leaves h, so does claimsInBy**, at every order and every test behind a run. -/
theorem leavesClaimsInBy (h : S → α) (each : Nat × String → List Cl → S → Except String Unit)
    (bs : List (Block S Cl)) (order : List (Nat × String))
    (hb : ∀ b ∈ bs, ∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → h y.2 = h s) (s : S) :
    ∀ y, claimsInBy each bs order s = .ok y → h y.2 = h s := by
  suffices G : ∀ (o : List (Nat × String)) (acc : Except String (List Cl × S)),
      (∀ x, acc = .ok x → h x.2 = h s) → ∀ y,
      o.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) acc = .ok y →
        h y.2 = h s from
    fun y H => G order (.ok ([], s)) (fun x e => by obtain rfl := Except.ok.inj e; rfl) y H
  intro o
  induction o with
  | nil => intro acc ha y H; exact ha y H
  | cons o l ih =>
    intro acc ha y H
    refine ih _ ?_ y H
    intro w hw
    obtain ⟨x, hx, hw⟩ := bindOk hw
    unfold claimsInStep at hw
    obtain ⟨run, hrun, hw⟩ := bindOk hw
    have hmem : ∃ b ∈ bs, (o.2, run) ∈ b.claims := by
      cases hb' : bs[o.1]? with
      | none => rw [hb'] at hrun; exact nomatch hrun
      | some b =>
        rw [hb'] at hrun
        cases hl : b.claims.lookup o.2 with
        | none =>
          have : named (o.2 ++ ": no such run") (b.claims.lookup o.2) = .ok run := hrun
          rw [hl] at this; exact nomatch this
        | some r =>
          have : named (o.2 ++ ": no such run") (b.claims.lookup o.2) = .ok run := hrun
          rw [hl] at this
          have e : r = run := Except.ok.inj this
          exact ⟨b, List.mem_of_getElem? hb', e ▸ memOfLookup _ _ _ hl⟩
    obtain ⟨b, hbm, hc⟩ := hmem
    cases hr : run x.1.length x.2 with
    | error e => rw [hr] at hw; exact nomatch hw
    | ok z =>
      rw [hr] at hw
      cases he : each o z.1 z.2 with
      | error e =>
        have hw' : (match each o z.1 z.2 with
          | .ok _ => Except.ok (x.1 ++ z.1, z.2)
          | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)) = Except.ok w := hw
        rw [he] at hw'; exact nomatch hw'
      | ok u =>
        have hw' : (match each o z.1 z.2 with
          | .ok _ => Except.ok (x.1 ++ z.1, z.2)
          | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)) = Except.ok w := hw
        rw [he] at hw'
        have e : (x.1 ++ z.1, z.2) = w := Except.ok.inj hw'
        rw [← e]
        show h z.2 = h s
        rw [hb b hbm _ hc _ _ z hr]
        exact ha x hx

/-- The frame's step behind the batching leaves h where the runs behind the batching do. -/
theorem leavesRunBehind (h : S → α) (L : Link S Cl)
    (ha : ∀ b ∈ L.hear, ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → h s' = h s) :
    ∀ s s', L.runBehind s = .ok s' → h s' = h s := by
  intro s s' H
  unfold Link.runBehind at H
  split at H
  · exact leavesAfterIn S Cl α h L.hear L.orderAfter ha _ _ H
  · exact nomatch H

/-! ## 2 The debt of the parts, and the closure -/

/-- **What a link's parts owe**, so that every block of its flat list leaves h or stands at a place that but names. THE RUNS ARE OWED AT EVERY
BLOCK OF hear, also at a place that but names: they run inside the batching's decision and in the block behind it. -/
structure Link.LeavesBut (h : S → α) (but : Place → Bool) (L : Link S Cl) : Prop where
  lay : ∀ s s', L.lay s = .ok s' → h s' = h s
  hear : ∀ b ∈ L.hear, but b.place = true ∨ b.Leaves h
  claims : ∀ b ∈ L.hear, ∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → h y.2 = h s
  after : ∀ b ∈ L.hear, ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → h s' = h s
  batch : ∀ f : S → Except String (List Cl × S), (∀ s y, f s = .ok y → h y.2 = h s) →
    but (L.batch f).place = true ∨ (L.batch f).Leaves h
  close : ∀ b ∈ L.close, but b.place = true ∨ b.Leaves h
  clear : ∀ s s', L.clear s = .ok s' → h s' = h s

/-- What a chain's parts owe. -/
structure Chain.LeavesBut (h : S → α) (but : Place → Bool) (c : Chain S Cl) : Prop where
  first : but c.first.place = true ∨ c.first.Leaves h
  front : ∀ b ∈ c.front, but b.place = true ∨ b.Leaves h
  links : ∀ L ∈ c.links, L.LeavesBut h but
  back : ∀ b ∈ c.back, but b.place = true ∨ b.Leaves h
  last : but c.last.place = true ∨ c.last.Leaves h

/-- **The closure at a link.** -/
theorem Link.LeavesBut.flat {h : S → α} {but : Place → Bool} {L : Link S Cl}
    (H : L.LeavesBut h but) : ∀ b ∈ L.blocksInOrder, but b.place = true ∨ b.Leaves h := by
  intro b hb
  unfold Link.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.cons_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · exact Or.inr fun s rs gs s' K => H.lay _ _ K
  · exact H.hear b hb
  · exact H.batch _ fun s y K => leavesClaimsInBy h L.each L.hear L.order H.claims s y K
  · exact Or.inr fun s rs gs s' K => leavesRunBehind h L H.after _ _ K
  · exact H.close b hb
  · exact Or.inr fun s rs gs s' K => H.clear _ _ K

/-- **The closure at a chain: every block of the flat list stands at a place that but names, or leaves h.** -/
theorem Chain.LeavesBut.flat {h : S → α} {but : Place → Bool} {c : Chain S Cl}
    (H : c.LeavesBut h but) : ∀ b ∈ c.blocksInOrder, but b.place = true ∨ b.Leaves h := by
  intro b hb
  unfold Chain.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap, List.cons_append,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | (((⟨p, hp, rfl⟩ | ⟨L, hL, hb⟩) | ⟨p, hp, rfl⟩) | rfl)
  · exact H.first.imp id fun K s rs gs s' D => K s rs gs s' D
  · exact (H.front p hp).imp id fun K s rs gs s' D => K s rs gs s' D
  · exact (H.links L hL).flat b hb
  · exact (H.back p hp).imp id fun K s rs gs s' D => K s rs gs s' D
  · exact H.last.imp id fun K s rs gs s' D => K s rs gs s' D

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.leavesClaimsInBy
#print axioms VerifiableInference.Desc.leavesRunBehind
#print axioms VerifiableInference.Desc.Link.LeavesBut.flat
#print axioms VerifiableInference.Desc.Chain.LeavesBut.flat
