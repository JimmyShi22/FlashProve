-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsReads.lean: the kind K1's member at a segment's reads: a
commitment with a step without a round joined behind it (IM.k1Reads, IM.k1Quiet,
Johnson/IMR/K1Seat.lean): what the WHOLE member leaves of the verifier's state as it was; the flag
that it lays in the head's link; and that facts on the state which other members have laid stay past
K1's four sorts of member. Definitions of propositions, and theorems. Over
Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean. It imports files of the sealed library alone beside
that.

  K1QuietKeeps, k1_quiet_keeps: the joined step: every field but the chain's place is as it was; of
    that place the smallness test's own part (tl) has turned, and at an attention link and at the
    head's the tables are laid (t). At the head's link it was open in front.
  K1ReadsKeeps, k1_reads_keeps: the whole member: there is a state between: K1CommitKeeps to it,
    K1QuietKeeps from it.
  k1_reads_lays_t: BEHIND THE MEMBER IN THE HEAD's LINK THE TABLES ARE LAID.
  head_stays_commit, head_stays_reads: a fact on the head's own part of the state that does not read
    what turns stays. Four examples: opened, x, claim, t.
  sized_stays_commit, sized_stays_reads, sizedR_stays_commit, sizedR_stays_reads: "the ledger has
    its sizes", in both of the library's forms.
  head_commit, head_stays_quiet, sized_of_slots, sizedR_of_slots: tools.
  head_idle_send, head_idle_first: at the sending behind the links and at the opening the chain does
    not stand in the head's link.
  rest_reads, out_reads, out_stays_reads: K1Rest and K1Out of the whole member; the mark, the reply
    with the pile, the request.
  rest_reads, out_reads are what the next three are called with at the reads' member.
  ledgerAt_stays, room_stays, outOfGroups_stays: three sentences on the index masks' message stay:
    "its ledger is that of k takes" (K13.Law.LedgerAt, Johnson/Desc/K13/Law/LedgerWithin.lean) and
    "its ledger is not shut, and what is left with the rows on the pile is room enough" where K1Rest
    holds; "it is a member of no group" (P1L20.outOfGroupsB, Johnson/P1L20R/RoomFold.lean) where
    K1Out holds too. The last two are written out: no name is given to them here.

Not shown here. ONE WAY, FROM A RETURN or from a clause. Nothing on the member as a chain seats it.
Where no step can be made for the place the joined step rejects every file: nothing is said there.
K1ReadsKeeps has a state between that no border names. Who lays the two sentences on the ledger, and
that a taking returns, is not said. The definitions are premises' forms: nothing is claimed of them.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.Keeps
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Desc.K13.Law.LedgerWithin
import Johnson.P1L20R.RoomFold
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K13.Law (LedgerAt LedStay)
open OnBytes.Model.Stages (LinkH)

/-- **What the step without a round behind the reads' commitment leaves of the state as it was.** A
definition: a premise's form. -/
def K1QuietKeeps (s s' : S) : Prop :=
  s'.st = s.st ∧ s'.book = s.book ∧ s'.roots = s.roots ∧ s'.rowsOwed = s.rowsOwed ∧
    s'.failed = s.failed ∧ s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req ∧
    ((∃ a tl, s.here = .lay a ∧ s'.here = .lay { a with tl := tl }) ∨
      (∃ a t tl, s.here = .att a ∧ s'.here = .att { a with t := some t, tl := tl }) ∨
      ∃ a t tl, s.here = .head a ∧ a.opened = true ∧
        s'.here = .head { a with t := some t, tl := tl })

/-- **A return of that step leaves that.** -/
theorem k1_quiet_keeps {G : ProofFile.Ground} {l : Nat} {X : LinkH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k1Quiet G l X).decide s rs gs = .ok s') :
    K1QuietKeeps s s' := by
  refine VerifiableInference.Desc.K1.k1Quiet_decides K1QuietKeeps (fun P s rs gs s' h => ?_)
    (fun P s rs gs s' h => ?_) (fun A s s' h => ?_) G l X s rs gs s' h
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_ok h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inl ⟨a, tl', ha, rfl⟩⟩
  · obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ :=
      VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inr (.inr ⟨a, t, tl', ha, ho, rfl⟩)⟩
  · obtain ⟨a, t, tl, ha, rfl⟩ := _root_.Meaning.K2.readsAtSO_eq h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .inr (.inl ⟨a, t, tl, ha, rfl⟩)⟩

/-- **What the whole member at a segment's reads leaves.** A definition: a premise's form. -/
def K1ReadsKeeps (s s' : S) : Prop := ∃ m, K1CommitKeeps s m ∧ K1QuietKeeps m s'

/-- **A return of the whole member leaves that.** -/
theorem k1_reads_keeps {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {X : LinkH} {pr : Nat}
    {reads : Option (List Nat)} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') : K1ReadsKeeps s s' := by
  obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (show (((VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
      reads : VerifiableInference.Desc.Block S Unit).decide s _ _).bind fun s₁ =>
        (IM.k1Quiet G l X).decide s₁ _ _) = .ok s' from h)
  exact ⟨m, k1_commit_keeps h1, k1_quiet_keeps h2⟩

/-- Behind a commitment in the head's link: the link was open, and of the head's own part the
context and the ledger alone have turned; the ledger in front is the one that the clause names. -/
theorem head_commit {s s' : S} (k : K1CommitKeeps s s') {a : HeadOwn} (ha : s.here = .head a) :
    a.opened = true ∧ ∃ L' F', s'.here = .head { a with L := L', F := F' } ∧
      PscRun.SlotsSame a.F F' := by
  obtain ⟨-, -, -, L, F, tl, L', F', hL, hF, -, hh, hs, -⟩ := k
  have ho : a.opened = true := by
    unfold S.link? at hL
    rw [ha] at hL
    by_cases ho : a.opened = true
    · exact ho
    · simp [ho] at hL
  have eF : F = a.F := by
    unfold S.fork? at hF
    rw [ha] at hF
    simpa [ho] using hF.symm
  refine ⟨ho, L', F', ?_, eF ▸ hs⟩
  rw [hh]
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  obtain rfl : here = .head a := ha
  simp [S.putLink, S.putFork, ho]

/-- **BEHIND THE MEMBER IN THE HEAD's LINK THE TABLES ARE LAID.** -/
theorem k1_reads_lays_t {s s' : S} (k : K1ReadsKeeps s s') (h : ∃ a, s.here = .head a) :
    ∃ a', s'.here = .head a' ∧ a'.t.isSome = true := by
  obtain ⟨m, kc, kq⟩ := k
  obtain ⟨a, ha⟩ := h
  obtain ⟨-, L', F', hm, -⟩ := head_commit kc ha
  obtain ⟨-, -, -, -, -, -, -, -, q⟩ := kq
  rcases q with ⟨b, _, hb, _⟩ | ⟨b, _, _, hb, _⟩ | ⟨b, t, tl, _, _, hs⟩
  · rw [hm] at hb; cases hb
  · rw [hm] at hb; cases hb
  · exact ⟨_, hs, rfl⟩

/-- **A fact on the head's own part that reads neither the context nor the ledger stays past a
commitment.** -/
theorem head_stays_commit (P : HeadOwn → Prop) (hP : ∀ a L F, P a → P { a with L := L, F := F })
    {s s' : S} (k : K1CommitKeeps s s') (h : ∃ a, s.here = .head a ∧ P a) :
    ∃ a', s'.here = .head a' ∧ P a' := by
  obtain ⟨a, ha, pa⟩ := h
  obtain ⟨-, L', F', hs, -⟩ := head_commit k ha
  exact ⟨_, hs, hP a L' F' pa⟩

/-- **A fact that reads none of the four that turn stays past the whole member at the reads.** -/
theorem head_stays_reads (P : HeadOwn → Prop)
    (hP : ∀ a L F t tl, P a → P { a with L := L, F := F, t := some t, tl := tl }) {s s' : S}
    (k : K1ReadsKeeps s s') (h : ∃ a, s.here = .head a ∧ P a) :
    ∃ a', s'.here = .head a' ∧ P a' := by
  obtain ⟨m, kc, kq⟩ := k
  obtain ⟨a, ha, pa⟩ := h
  obtain ⟨-, L', F', hm, -⟩ := head_commit kc ha
  obtain ⟨-, -, -, -, -, -, -, -, q⟩ := kq
  rcases q with ⟨b, _, hb, _⟩ | ⟨b, _, _, hb, _⟩ | ⟨b, t, tl, hb, _, hs⟩
  · rw [hm] at hb; cases hb
  · rw [hm] at hb; cases hb
  · rw [hm] at hb
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj hb
    exact ⟨_, hs, hP a L' F' t tl pa⟩

example : ∀ (a : HeadOwn) L F t tl, a.opened = true →
    ({ a with L := L, F := F, t := some t, tl := tl } : HeadOwn).opened = true :=
  fun _ _ _ _ _ h => h
example : ∀ (a : HeadOwn) L F t tl, a.x.isSome = true →
    ({ a with L := L, F := F, t := some t, tl := tl } : HeadOwn).x.isSome = true :=
  fun _ _ _ _ _ h => h
example : ∀ (a : HeadOwn) L F t tl, a.claim.isSome = true →
    ({ a with L := L, F := F, t := some t, tl := tl } : HeadOwn).claim.isSome = true :=
  fun _ _ _ _ _ h => h
example : ∀ (a : HeadOwn) L F, a.t.isSome = true →
    ({ a with L := L, F := F } : HeadOwn).t.isSome = true := fun _ _ _ h => h

/-- The three lengths pass where the slots are the same. -/
theorem sized_of_slots {F F' : Fork} (h : PscRun.SlotsSame F F') (z : PscRun.Sized F) :
    PscRun.Sized F' := by
  obtain ⟨a, b, c⟩ := z
  exact ⟨by rw [h.vp, h.ns]; exact a, by rw [h.mf, h.ns]; exact b, by rw [h.gotF, h.ns]; exact c⟩

/-- The same in the library's other form. -/
theorem sizedR_of_slots {F F' : Fork} (h : PscRun.SlotsSame F F') (z : Road.Sized F) :
    Road.Sized F' :=
  ⟨by rw [h.vp, h.ns]; exact z.vp, by rw [h.mf, h.ns]; exact z.mf,
    by rw [h.gotF, h.ns]; exact z.got⟩

/-- **"The ledger has its sizes" stays past a commitment.** -/
theorem sized_stays_commit {s s' : S} (k : K1CommitKeeps s s')
    (h : ∃ a, s.here = .head a ∧ PscRun.Sized a.F) :
    ∃ a', s'.here = .head a' ∧ PscRun.Sized a'.F := by
  obtain ⟨a, ha, z⟩ := h
  obtain ⟨-, L', F', hs, sl⟩ := head_commit k ha
  exact ⟨_, hs, sized_of_slots sl z⟩

theorem sizedR_stays_commit {s s' : S} (k : K1CommitKeeps s s')
    (h : ∃ a, s.here = .head a ∧ Road.Sized a.F) :
    ∃ a', s'.here = .head a' ∧ Road.Sized a'.F := by
  obtain ⟨a, ha, z⟩ := h
  obtain ⟨-, L', F', hs, sl⟩ := head_commit k ha
  exact ⟨_, hs, sizedR_of_slots sl z⟩

/-- The joined step leaves a fact on the head's own part that reads neither t nor tl. -/
theorem head_stays_quiet (P : HeadOwn → Prop)
    (hP : ∀ a t tl, P a → P { a with t := some t, tl := tl }) {s s' : S}
    (k : K1QuietKeeps s s') (h : ∃ a, s.here = .head a ∧ P a) :
    ∃ a', s'.here = .head a' ∧ P a' := by
  obtain ⟨a, ha, pa⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, q⟩ := k
  rcases q with ⟨b, _, hb, _⟩ | ⟨b, _, _, hb, _⟩ | ⟨b, t, tl, hb, _, hs⟩
  · rw [ha] at hb; cases hb
  · rw [ha] at hb; cases hb
  · rw [ha] at hb
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj hb
    exact ⟨_, hs, hP a t tl pa⟩

/-- **"The ledger has its sizes" stays past the whole member at the reads.** -/
theorem sized_stays_reads {s s' : S} (k : K1ReadsKeeps s s')
    (h : ∃ a, s.here = .head a ∧ PscRun.Sized a.F) :
    ∃ a', s'.here = .head a' ∧ PscRun.Sized a'.F := by
  obtain ⟨m, kc, kq⟩ := k
  exact head_stays_quiet (fun a => PscRun.Sized a.F) (fun _ _ _ z => z) kq
    (sized_stays_commit kc h)

theorem sizedR_stays_reads {s s' : S} (k : K1ReadsKeeps s s')
    (h : ∃ a, s.here = .head a ∧ Road.Sized a.F) :
    ∃ a', s'.here = .head a' ∧ Road.Sized a'.F := by
  obtain ⟨m, kc, kq⟩ := k
  exact head_stays_quiet (fun a => Road.Sized a.F) (fun _ _ _ z => z) kq (sizedR_stays_commit kc h)

/-- At the sending behind the links the chain does not stand in the head's link. -/
theorem head_idle_send {s s' : S} (k : K1SendKeeps s s') : ¬ ∃ a, s.here = .head a := by
  obtain ⟨-, -, -, -, -, b, _, hb, -⟩ := k
  rintro ⟨a, ha⟩
  rw [ha] at hb
  cases hb

/-- Nor at the first segment's opening. -/
theorem head_idle_first {s s' : S} (k : K1FirstKeeps s s') : ¬ ∃ a, s.here = .head a := by
  obtain ⟨-, hb, -⟩ := k
  rintro ⟨a, ha⟩
  rw [ha] at hb
  cases hb

/-- **K1Rest of the whole member at the reads.** -/
theorem rest_reads {s s' : S} (k : K1ReadsKeeps s s') : K1Rest s s' := by
  obtain ⟨m, ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, -⟩, b1, b2, b3, b4, b5, -, b7, b8, -⟩ := k
  exact ⟨b5.trans a1, b7.trans a2, b8.trans a3, b4.trans a4, b1 ▸ a5, b1 ▸ a6, b1 ▸ a7, b3 ▸ a8,
    b2 ▸ a9⟩

/-- The mark, the reply with the pile of rows, the request: as they were. So the number of rows on
the pile is what it was; at the kind's three other sorts K1Rest says the same. -/
theorem out_stays_reads {s s' : S} (k : K1ReadsKeeps s s') :
    s'.out = s.out ∧ s'.failed = s.failed ∧ s'.req = s.req :=
  ⟨(rest_reads k).2.1, (rest_reads k).1, (rest_reads k).2.2.1⟩

/-- **"The ledger of the index masks' message is that of k takes" stays where K1Rest holds.** -/
theorem ledgerAt_stays {s s' : S} (k : K1Rest s s') {n : Nat}
    (h : LedgerAt s.st s.out.indexMasks n) : LedgerAt s'.st s'.out.indexMasks n := by
  rw [k.2.1]
  exact k.2.2.2.2.2.1.at h

/-- **K1Out of the whole member at the reads.** -/
theorem out_reads {s s' : S} (k : K1ReadsKeeps s s') : K1Out s s' := by
  obtain ⟨m, ⟨-, o, -⟩, b1, -⟩ := k
  exact fun i hi hO => b1 ▸ o i hi hO

/-- **"The ledger of the index masks' message is not shut, and what is left in it, with the rows
that lie on the pile, is room enough" stays where K1Rest holds.** The sentence is written out, by
the library's reader of that ledger (Johnson/Top/H0/Walk/FrameLaw.lean). -/
theorem room_stays {s s' : S} (k : K1Rest s s') {room : Nat}
    (h : ∃ l, Johnson.Desc.First.Walk.Law.ledgerAt s = some l ∧ l.closed = false ∧
      room ≤ l.left + s.out.pending.length) :
    ∃ l, Johnson.Desc.First.Walk.Law.ledgerAt s' = some l ∧ l.closed = false ∧
      room ≤ l.left + s'.out.pending.length := by
  obtain ⟨l, hl, hc, hr⟩ := h
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨x', hx', -, e⟩ := k.2.2.2.2.2.2.1.msg _ x hx
  refine ⟨l, ?_, hc, by rw [k.2.1]; exact hr⟩
  show (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) = some l
  rw [k.2.1, hx']
  exact e.trans hxl

/-- **"The index masks' message is a member of no group" stays where K1Rest and K1Out hold**, if
that message has a ledger in front: in the library's test with code
(Johnson/P1L20R/RoomFold.lean). -/
theorem outOfGroups_stays {s s' : S} (k : K1Rest s s') (o : K1Out s s')
    (hl : (Johnson.Desc.First.Walk.Law.ledgerAt s).isSome = true)
    (h : P1L20.outOfGroupsB s = true) : P1L20.outOfGroupsB s' = true := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hl
  obtain ⟨x, hx, -⟩ := Option.bind_eq_some_iff.1 hl
  have hi : s.out.indexMasks < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  refine P1L20.outOfGroupsB_iff.2 ?_
  rw [k.2.1]
  exact o _ hi (P1L20.outOfGroupsB_iff.1 h)

end ProofFile.Honest.K1
