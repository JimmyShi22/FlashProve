-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawNamed.lean: THE SMALLNESS TEST: THE ARRAYS THAT THE DRAWN MATRIX MULTIPLIES
LIE IN MESSAGES WHOSE TREES THE PLACE NAMES: FROM ONE TEST WITH CODE; AND HALF OF THAT TEST FROM THE
YES OF THE STEP THAT CLOSES THE LIST OF TABLES.

Johnson/Desc/First/K8/LawSeats.lean pays "every tree off which a member's word is read is sent in
front of the block's stretch" from the file's one test on the plan, UNDER ONE PREMISE: every such
tree is named by the block. The list of members and their seats were letters there. At the values
of Johnson/Desc/First/K8/Named.lean:
  `namedNow_own`: at a message born at the link under way `Order.namedNow` is `ownNow`.
  `seatFn`: the seats as a function on the list's numbers.
  `named_of_test`: **`namedB` = true gives that premise**: every seat's tree is among
    `p.matsIn ++ p.readsIn`.
  `arrays_in_named`: under `namedB`: every array that the matrix multiplies lies, now, in a message
    that is a member of the list. Not one to one: two arrays in one message share a member.
  `nums_eq_msgs`, `arr_of_test`: under `namedB` no message falls out of the list; and at every
    member's seat the book's own list of the tree's parts (`arrOf`) gives the member's number.
  `seats_nodup`: under `namedB` no two members sit at one seat.
  `msgNow_of_front`: **a yes of `Order.front`**, which the step that closes the list asks: every
    such array has a message now; the statement has it; its sample is answered. So of the test's
    five clauses two are paid by the running text: by `front_ok`, `orderOk_fixed`, `fixed_sampled`
    (Johnson/Desc/K8/ReadsQuietLaws.lean).
  `namedB_of_order`, `BookNames p s`: what is left of the test behind that yes: the book has each
    message, in a tree that the place names, and lists it there. `namedAt_behind_layers`,
    `namedAt_behind_head`: so the test at the carried record (`namedAt`) says yes right behind that
    step, if the book names.
  `namedCallerAt`, `named_seats_below`: `frameCallerAt` and `seats_below` at these values.
Definitions, statements and proofs.
Limits. Those of Named.lean. `namedB` is shown true at no value here. MESSAGE-WISE: where inside its
message an array's entries lie is not said. rad, cs, Θ and rdm stay letters.

-/
import Johnson.Desc.First.K8.Named
import Johnson.Desc.First.K8.LawSeats
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.First.Att.ReadsO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Named
open OnBytes OnBytes.Model

theorem length_seats (rad : OracleShape → Nat) (S : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) : (seatsOf S book tl L).length = (listOf rad S book tl L).length := by
  simp [seatsOf, listOf]

/-- The seats as a function on the list's numbers. -/
def seatFn (rad : OracleShape → Nat) (S : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) (i : Fin (listOf rad S book tl L).length) : ℕ × ℕ :=
  (seatsOf S book tl L).get (i.cast (length_seats rad S book tl L).symm)

/-- At a message born at the link under way `Order.namedNow` is `ownNow`. -/
theorem namedNow_own (L : LinkCtx) (w : Order.Lies) (h : w.born = L.check.frame.link) :
    Order.namedNow L.check.frame w = ownNow L w.message := by
  unfold Order.namedNow ownNow
  cases L.check.frame.next <;> simp [h]

/-- What the test says of one array. -/
theorem namedB_at {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) {t : Nat} (ht : t ∈ arrays tl) :
    ∃ o m, msgNow L t = some o ∧ memberAt S book o = some m ∧ m.2.1 ∈ p.matsIn ++ p.readsIn ∧
      partAt book m.2.1 m.2.2 = some o := by
  have h1 := List.all_eq_true.1 h t ht
  cases ho : msgNow L t with
  | none => simp [ho] at h1
  | some o =>
    simp only [ho] at h1
    cases hm : memberAt S book o with
    | none => simp [hm] at h1
    | some m =>
      simp only [hm, Bool.and_eq_true, beq_iff_eq] at h1
      exact ⟨o, m, rfl, hm, by simpa using h1.1, h1.2⟩

/-- A number of the list of messages is some array's. -/
theorem mem_msgs {tl : HTailF2} {L : LinkCtx} {o : Nat} :
    o ∈ msgs tl L ↔ ∃ t ∈ arrays tl, msgNow L t = some o := by
  unfold msgs
  rw [List.mem_eraseDups, List.mem_filterMap]

/-- What the test says of one member: the statement and the book have it so; its tree is named; the
book's list of the tree's parts has its number at its tenant. -/
theorem member_ok {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) {m : Nat × OracleShape × (Nat × Nat)}
    (hm : m ∈ (msgs tl L).filterMap fun o => (memberAt S book o).map fun x => (o, x)) :
    memberAt S book m.1 = some m.2 ∧ m.2.2.1 ∈ p.matsIn ++ p.readsIn ∧
      partAt book m.2.2.1 m.2.2.2 = some m.1 := by
  obtain ⟨o, ho, hom⟩ := List.mem_filterMap.1 hm
  obtain ⟨t, ht, hto⟩ := mem_msgs.1 ho
  obtain ⟨o', m', h1, h2, h3, h4⟩ := namedB_at h ht
  obtain rfl : o = o' := Option.some.inj (hto.symm.trans h1)
  rw [h2] at hom
  obtain rfl : (o, m') = m := Option.some.inj hom
  exact ⟨h2, h3, h4⟩

/-- **The test gives the premise on the seats.** -/
theorem named_of_test {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) (rad : OracleShape → Nat)
    (i : Fin (listOf rad S book tl L).length) :
    (seatFn rad S book tl L i).1 ∈ p.matsIn ++ p.readsIn := by
  have hx : seatFn rad S book tl L i ∈ seatsOf S book tl L := List.get_mem _ _
  unfold seatsOf members at hx
  obtain ⟨m, hm, e⟩ := List.mem_map.1 hx
  rw [← e]
  exact (member_ok h hm).2.1

/-- **Every array that the matrix multiplies lies, now, in a message that is a member.** -/
theorem arrays_in_named {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) {t : Nat} (ht : t ∈ arrays tl) :
    ∃ o m, msgNow L t = some o ∧ o ∈ msgs tl L ∧ memberAt S book o = some m ∧
      (o, m) ∈ members S book tl L ∧ m.2.1 ∈ p.matsIn ++ p.readsIn := by
  obtain ⟨o, m, h1, h2, h3, _⟩ := namedB_at h ht
  have ho : o ∈ msgs tl L := mem_msgs.2 ⟨t, ht, h1⟩
  exact ⟨o, m, h1, ho, h2, List.mem_filterMap.2 ⟨o, ho, by rw [h2]; rfl⟩, h3⟩

/-- **Under the test no message falls out**: the members' numbers are the list of messages. -/
theorem nums_eq_msgs {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) : numsOf S book tl L = msgs tl L := by
  unfold numsOf members
  have key : ∀ l : List Nat, (∀ o ∈ l, (memberAt S book o).isSome = true) →
      (l.filterMap fun o => (memberAt S book o).map fun m => (o, m)).map (·.1) = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons o l ih =>
      intro hl
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hl o List.mem_cons_self)
      rw [List.filterMap_cons, hm]
      simp only [Option.map_some, List.map_cons]
      rw [ih fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')]
  refine key _ fun o ho => ?_
  obtain ⟨t, ht, hto⟩ := mem_msgs.1 ho
  obtain ⟨o', m', h1, h2, _, _⟩ := namedB_at h ht
  obtain rfl : o = o' := Option.some.inj (hto.symm.trans h1)
  rw [h2]
  rfl

/-- **The book's own inverse**: at every member's seat `arrOf` gives the member's number. -/
theorem arr_of_test {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) {m : Nat × OracleShape × (Nat × Nat)}
    (hm : m ∈ members S book tl L) : arrOf book m.2.2.1 m.2.2.2 = m.1 := by
  unfold arrOf
  rw [(member_ok h hm).2.2]
  rfl

/-- A list with its repeats erased has none. -/
theorem nodup_erased : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_erased n _ ?_⟩
    · have := (List.mem_filter.1 (List.mem_eraseDups.1 hm)).2
      simp at this
    · exact le_trans (List.length_filter_le _ _) (by simpa using h)

/-- **Under the test no two members sit at one seat.** -/
theorem seats_nodup {p : Par} {S : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : namedB p S book tl L = true) : (seatsOf S book tl L).Nodup := by
  have hn : (numsOf S book tl L).Nodup := by
    rw [nums_eq_msgs h]
    exact nodup_erased _ _ le_rfl
  unfold numsOf at hn
  unfold seatsOf
  refine List.Nodup.map_on (fun m hm m' hm' e => ?_) (List.Nodup.of_map _ hn)
  have a := (member_ok h hm).2.2
  have a' := (member_ok h hm').2.2
  rw [e] at a
  have e1 : m.1 = m'.1 := Option.some.inj (a.symm.trans a')
  exact List.inj_on_of_nodup_map hn hm hm' e1

/-- **A yes of the guard in front of the draw**: every such array has a message now; the statement
has it; its sample is answered. -/
theorem msgNow_of_order {tl : HTailF2} {L : LinkCtx} {S : Statement}
    (hO : Order.orderOk tl L S = true) {t : Nat} (ht : t ∈ arrays tl) :
    ∃ o x, msgNow L t = some o ∧ S.oracles[o]? = some x ∧ x.sampled = true := by
  obtain ⟨_, h1, h2⟩ := VerifiableInference.Desc.K8.ReadsQuiet.orderOk_fixed hO
  have hf : Order.fixed L S t = true := by
    unfold arrays at ht
    rcases List.mem_append.1 ht with ht | ht
    · exact h1 t (by simpa using ht)
    · obtain ⟨n, hn, e⟩ := List.mem_filterMap.1 ht
      exact h2 n (List.mem_range.1 hn) t e
  obtain ⟨w, o, x, a1, _, a3, a4, a5⟩ := VerifiableInference.Desc.K8.ReadsQuiet.fixed_sampled hf
  refine ⟨o, x, ?_, a4, a5⟩
  unfold msgNow
  rw [a1]
  exact a3

theorem msgNow_of_front {tl : HTailF2} {L : LinkCtx} {S : Statement}
    (h : Order.front tl L S = .ok ()) {t : Nat} (ht : t ∈ arrays tl) :
    ∃ o x, msgNow L t = some o ∧ S.oracles[o]? = some x ∧ x.sampled = true :=
  msgNow_of_order (VerifiableInference.Desc.K8.ReadsQuiet.front_ok h).2.2 ht

/-- What is left of the test behind that yes: the book has each message, in a named tree. -/
theorem namedB_of_order {p : Par} {tl : HTailF2} {L : LinkCtx} {S : Statement} {book : TreeBook}
    (h : Order.orderOk tl L S = true)
    (hb : ∀ o ∈ msgs tl L, ∃ jt, book.place[o]? = some jt ∧ jt.1 ∈ p.matsIn ++ p.readsIn ∧
      partAt book jt.1 jt.2 = some o) :
    namedB p S book tl L = true := by
  refine List.all_eq_true.2 fun t ht => ?_
  obtain ⟨o, x, h1, h2, _⟩ := msgNow_of_order h ht
  obtain ⟨jt, h3, h4, h5⟩ := hb o (mem_msgs.2 ⟨t, ht, h1⟩)
  simp only [h1, memberAt, h2, h3, Bool.and_eq_true, beq_iff_eq]
  exact ⟨by simpa using h4, h5⟩

/-- What is left of the test, of the book at a carried record. -/
def BookNames (p : Par) (s : S) : Prop :=
  ∀ tl L, s.tl? = some tl → s.link? = some L → ∀ o ∈ msgs tl L,
    ∃ jt, s.book.place[o]? = some jt ∧ jt.1 ∈ p.matsIn ++ p.readsIn ∧
      partAt s.book jt.1 jt.2 = some o

/-- **Behind the step that closes the list at a layers' link** the test at the carried record says
yes, if the book names. -/
theorem namedAt_behind_layers (p : Par) (P : VerifiableInference.Desc.K8.ReadsQuiet.PG) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K8.ReadsQuiet.layers P).decide s rs gs = .ok s')
    (hb : BookNames p s') : namedAt p s' = true := by
  obtain ⟨a, own, tl', _, _, hc, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_ok h
  obtain ⟨_, _, _, hO⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  subst e
  exact namedB_of_order hO (hb tl' a.L rfl rfl)

/-- The like at the head's link. -/
theorem namedAt_behind_head (p : Par) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K8.ReadsQuiet.head P).decide s rs gs = .ok s')
    (hb : BookNames p s') : namedAt p s' = true := by
  obtain ⟨a, cov, x, t, tl', _, ho, _, _, _, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨_, _, _, hO⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  subst e
  have h1 : (S.tl? { s with here := .head { a with t := some t, tl := tl' } }) = some tl' := by
    simp [S.tl?, ho]
  have h2 : (S.link? { s with here := .head { a with t := some t, tl := tl' } }) = some a.L := by
    simp [S.link?, ho]
  unfold namedAt
  rw [h1, h2]
  exact namedB_of_order hO (hb tl' a.L h1 h2)

/-- The like at an attention link: behind every block `readsAtO W l g`. -/
theorem namedAt_behind_att (p : Par) (A : Attention.Plan) {s s' : S}
    (h : Att.readsAtSO A s = .ok s') (hb : BookNames p s') : namedAt p s' = true := by
  unfold Att.readsAtSO at h
  cases hh : s.here with
  | att a =>
    simp only [hh] at h
    obtain ⟨h5, _, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨g, _, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain ⟨r, hr, h⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok h
    obtain rfl : { s with here := .att { a with t := some r.1, tl := r.2.1 } } = s' := by
      simpa [pure, Except.pure] using h
    unfold Att.readsStepO at hr
    obtain ⟨_, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
    obtain ⟨_, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
    obtain ⟨t, _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
    obtain ⟨tl', _, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
    obtain ⟨_, hf, hr⟩ := VerifiableInference.Desc.K8.ReadsQuiet.bind_ok hr
    obtain rfl : (Att.tabsBack t, tl', a.F.next) = r := by simpa [pure, Except.pure] using hr
    exact namedB_of_order (VerifiableInference.Desc.K8.ReadsQuiet.front_ok hf).2.2
      (hb tl' a.L rfl rfl)
  | _ => simp [hh] at h

section
open Cb Cb.Pv.Tail KObj Johnson.Pack VerifiableInference.Desc.Sound

variable (cs : OnBytes.Codes) (rad : OracleShape → Nat) (S : Statement) (book : TreeBook)
  (tl : HTailF2) (L : LinkCtx) (tl0 : HTailF2)
  (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0))
  (rdm : (sigOf cs (listOf rad S book tl L)).Msg → Θ.M) (p : Par)

/-- `frameCallerAt` at these values: no premise on seats is left but the test. -/
def namedCallerAt (h : namedB p S book tl L = true) :
    CallerAt p (tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl0) Θ
      (sigOf cs (listOf rad S book tl L)) rdm) :=
  frameCallerAt cs (listOf rad S book tl L) (seatFn rad S book tl L) tl0 Θ rdm p
    (named_of_test h rad)

/-- `seats_below` at these values. -/
theorem named_seats_below {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {b : Block F.S₁ F.Cl}
    (hl : Like seat p b) (pre post : List (Block F.S₁ F.Cl))
    (hflat : F.first.blocksInOrder = pre ++ b :: post) (hF : F.planOk = true)
    (h : namedB p S book tl L = true) (i : Fin (listOf rad S book tl L).length) :
    (seatFn rad S book tl L i).1 < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) :=
  seats_below (listOf rad S book tl L) (seatFn rad S book tl L) p F hl pre post hflat hF
    (named_of_test h rad) i

end

end VerifiableInference.Desc.First.K8.Named

#print axioms VerifiableInference.Desc.First.K8.Named.namedNow_own
#print axioms VerifiableInference.Desc.First.K8.Named.named_of_test
#print axioms VerifiableInference.Desc.First.K8.Named.arrays_in_named
#print axioms VerifiableInference.Desc.First.K8.Named.nums_eq_msgs
#print axioms VerifiableInference.Desc.First.K8.Named.arr_of_test
#print axioms VerifiableInference.Desc.First.K8.Named.msgNow_of_front
#print axioms VerifiableInference.Desc.First.K8.Named.namedB_of_order
#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_behind_layers
#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_behind_head
#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_behind_att
#print axioms VerifiableInference.Desc.First.K8.Named.seats_nodup
#print axioms VerifiableInference.Desc.First.K8.Named.namedCallerAt
#print axioms VerifiableInference.Desc.First.K8.Named.named_seats_below
