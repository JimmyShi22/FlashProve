-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Shape/Claims.lean: A MARK BESIDE THE SHAPE FOR WHAT A PROXIMITY TEST's FRONT
ASKS OF ALL CONSTRAINTS THAT LIE OPEN ON A GROUP; the law on what the adding's five clauses read of
a statement's shape; and: each of the ground's thirteen plain functions keeps the mark, TWO OF THEM
(the admitting; the copying of a sample) UNDER A PREMISE THAT NO LAW OF THIS FILE MEETS. No
statement here names a kind of sub-protocol, a chain or a frame for an honest side. A word: a
constraint here is what the files beside this one, and the library's clauses' names, call a row
(`OnBytes.Row`): a constraint that lies open: an open row; a sample constraint: a sample row.

What is asked. The front of a proximity test asks once more, of every constraint that lies open on
its group, all eight clauses of the adding, at the statement as it then is (`openClaimsE`,
Johnson/Desc/Ground/Ask.lean; `rowL`, Johnson/Desc/First/Base/Ground.lean). The first two clauses
(the group is there; no test of it has begun) the front tests itself; the third (no sample
constraint) it tests a second time by a clause of its own. The mark is the last six: the constraint
is no sample constraint, and it passes the five clauses that read its summands (`rowRestB`,
Johnson/Desc/Ground/Shape/Ground.lean).

Why one mark serves. Of these six clauses some parts read the constraint alone: its kind; all four
clauses of `tensorInOrder`, on a term's tensor and on each tensor of a whole coefficient vector;
`coeffsInside`, the size and the step of a run. A CONSTRAINT THAT LIES DOES NOT CHANGE, so these
hold for ever once they held. The other parts read of the statement, through its shape
(`rowRestS_eq`, More.lean): the codes; the shapes of the messages that the summands name; the
group's members; the members' pads. These change in few ways: messages come; members join; a pad is
laid. `Grown` says which changes do no harm.

Main names.
  `Grown`, `Grown.refl`, `Grown.trans`: the shape a' is the shape a, grown, as far as the five
      clauses at the group g read it: the codes stay; every message that was there is there, with
      its shape; if the group was there it is there, with all members that it had; at a member that
      it had the list of pad places, AS THE CLAUSES READ IT (no message: no place), is as it was. Of
      a new member nothing is asked.
  `tableBitsS_grown`, `placeFitsS_grown`: a table's index bits stay; a summand that fits its place
      still fits it.
  `foldl_stays`, `coefficient_none`: no summand of the constraint names the message o: then its
      coefficient on every entry of o's tables is the element 0 itself. So a member that was none
      when a constraint passed brings no coefficient on a pad: the constraint's summands name
      members.
  `rowRestS_grown`: THE LAW ON WHAT `rowRestS` READS: a constraint that passes the five clauses at a
      shape passes them at the shape grown.
  `modAt_at`, `orc_grown`, `grp_grown`, `more_orcs`, `more_groups`, `mem_insAt`, `fresh_pad`,
      `shut_grown`: the sorts of change.
  `X_grown`: for X one of join, addRow, addRows, newGroup, recv, adopt, takeMask, takeMasks,
      closeLedger, spend, beginRun (eleven of the thirteen), and for the two inner loops addRowsFrom
      and takeMasksInto: where XS returns, the statement's shape behind is `Grown` AT EVERY g, with
      no further premise.
  `admit_grown`, `elsewhere_grown`: these two functions lay a pad on a message. Premise: that
      message is no member of the group g.
  `membersSampledS`, `notMember_of_sampled`: a test with code on the shape: every member of g is
      sampled (a member whose message is not there counts as not sampled). Where it passes, a
      message that is not sampled, or is not there, is no member of g.
  `claimsAtB`, `claimsAt_iff`, `claims_start`: THE MARK AT A GROUP, a function of a statement; true
      where the group is not there; true at a statement without a group.
  `claims_keep`, `old_rows`, `old_rows_modify`: the mark is kept where the shape grows and each
      constraint behind lay in front or passes by itself.
  `X_claims`: for the same X, and admit and elsewhere under the premise above: the function keeps
      the mark at every group. `addRow_claims`: the new constraint has just passed the clauses,
      which do not read the group's constraints (`rowRestB_withRow`, More.lean).
  `refuse_ok`, `forM_ok`, `open_of_claims`, `claims_of_open`: the mark and the front's test: where
      the group is there and no test of it has begun, the mark gives `openClaimsE S g = .ok ()`; and
      that .ok gives the mark.
  `rowsPass_of_claims`, `claims_of_rowsPass`: the same with the front's test written as one Bool: at
      the group, every constraint that lies passes all clauses of `rowL`.

How the mark is meant. As Marks.lean means its two: a mark that the functions CARRY: a run on shapes
asks it and hands it on, and never computes it from constraints. The reader `claimsAtB` is for the
laws alone. THREE OF ITS FIVE CLAUSES READ VALUES: the terms' and the whole vectors' (a written-out
variable's pair against (1, 1), in `tensorInOrder`), and the pads' (the coefficients on them).

Imports. More.lean; and, beside this folder's files, Johnson/Desc/Ground/Ask.lean, for `openClaimsE`
and `refuse`: the library's; it names no kind of sub-protocol.

Names that a reader may meet elsewhere. `refuse_ok`, `forM_ok`: the library has lemmas of these
names and this content, in other forms, in Johnson/Desc/K12/SeatLaws.lean (with `openClaimsE_ok`): a
file of one kind of sub-protocol, so it is not imported here; where both namespaces are opened the
names are ambiguous. `addRowsFrom_claims`: OnBytes.Means has a lemma of this name on another notion
(Johnson/Desc/Means/ClaimsP.lean). `Grown`, `claims_keep`, `mem_insAt` have namesakes in other
namespaces. `coefficient_none` has three kin: coefficient_off (Johnson/Desc/Means/Lays.lean;
Johnson/Desc/K14/Law/Carry.lean) and coefficient_off_names (Johnson/Desc/Third/Law/Renamed.lean):
each says that the coefficient's VALUE under a reading is 0; this one says that the element is
`zeroE`, which `allZero`, a test on words, needs.

Limits. WHO MEETS THE PREMISE OF `admit_claims` AND `elsewhere_claims` IS NOT IN THIS FILE: no law
here says that any of the thirteen keeps `membersSampledS`, that `stTidyB` gives it, or that the
accept of the admitting (of the copying: at its message `mine`) gives "not sampled". It can be met:
Tidy holds "every member is sampled", the joining asks "sampled", the admitting and the copying ask
"not sampled": so at a tidy statement these two reject at a member.
Johnson/Desc/Ground/Shape/ClaimsMarks.lean, which stands over this file, has that as laws, at a tidy
statement. THE MEMBERS' SAMPLE CONSTRAINTS ARE NOT UNDER THE MARK: what the batching's guard asks of
them (`combOk`, Johnson/Desc/K12/JoinGuarded.lean) is not given here. `beginRun_claims` says nothing at
the group under test: its constraints have left the statement. That a whole proximity test keeps the
mark at the other groups is not shown: some texts of the library write a statement by themselves,
not through the thirteen (among them Johnson/Desc/K12/JoinGuarded.lean and
Johnson/Desc/First/Base/Meanwhile.lean, where a message is marked as spent by hand). No maker of
constraints is named: that a sub-protocol's constraints pass the adding is the adding's own accept.
`Grown` is sufficient, not necessary. No evaluation and no negative test of the mark lies in this
file; such lines stand in a file that is not part of this library. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.Ground.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## 1 What the five clauses read of a statement's shape, and how that may grow -/

/-- **The shape a' is the shape a, grown, as far as the five clauses at the group g read it**: the
codes stay; every message that was there is there, with its shape; if the group was there it is
there, with all members that it had; at a member that it had the list of pad places, as the clauses
read it (no message: no place), is as it was. Of a new member nothing is asked. -/
structure Grown (a a' : StSh) (g : Nat) : Prop where
  codes : a'.codes = a.codes
  shapes : ∀ (o : Nat) (x : OrcSh), a.oracles[o]? = some x →
    ∃ x' : OrcSh, a'.oracles[o]? = some x' ∧ x'.shape = x.shape
  group : ∀ G : GrpSh, a.groups[g]? = some G → ∃ G' : GrpSh, a'.groups[g]? = some G' ∧
    (∀ o, o ∈ G.members → o ∈ G'.members) ∧
    ∀ o, o ∈ G.members →
      ((a'.oracles[o]?).map (·.pad)).getD [] = ((a.oracles[o]?).map (·.pad)).getD []

/-- A shape is itself, grown. -/
theorem Grown.refl (a : StSh) (g : Nat) : Grown a a g :=
  ⟨rfl, fun _ x h => ⟨x, h, rfl⟩, fun G h => ⟨G, h, fun _ c => c, fun _ _ => rfl⟩⟩

/-- Grown, and grown again. -/
theorem Grown.trans {a b c : StSh} {g : Nat} (h : Grown a b g) (k : Grown b c g) : Grown a c g := by
  refine ⟨k.codes.trans h.codes, fun o x hx => ?_, fun G hG => ?_⟩
  · obtain ⟨y, hy, e⟩ := h.shapes o x hx
    obtain ⟨z, hz, e'⟩ := k.shapes o y hy
    exact ⟨z, hz, e'.trans e⟩
  · obtain ⟨G', hG', m, p⟩ := h.group G hG
    obtain ⟨G'', hG'', m', p'⟩ := k.group G' hG'
    exact ⟨G'', hG'', fun o ho => m' o (m o ho), fun o ho => (p' o (m o ho)).trans (p o ho)⟩

/-- A table's index bits stay, where the message was there. -/
theorem tableBitsS_grown {a a' : StSh} {g : Nat} (h : Grown a a' g) {o : Nat} {x : OrcSh}
    (hx : a.oracles[o]? = some x) (part : Part) : tableBitsS a' o part = tableBitsS a o part := by
  obtain ⟨x', hx', e⟩ := h.shapes o x hx
  unfold tableBitsS
  rw [hx, hx', h.codes]
  dsimp only
  rw [e]

/-- A summand that fits its place still fits it, where the group behind has lost no member (hm).
Beside: its message was a member, and its table's index bits stay. -/
theorem placeFitsS_grown {a a' : StSh} {g : Nat} (h : Grown a a' g) {G G' : GrpSh}
    (hm : ∀ o, o ∈ G.members → o ∈ G'.members) {o : Nat} {part : Part} {vars index : Nat}
    (hp : placeFitsS a G o part vars index = true) :
    placeFitsS a' G' o part vars index = true ∧ o ∈ G.members ∧
      tableBitsS a' o part = tableBitsS a o part := by
  unfold placeFitsS at hp ⊢
  simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, decide_eq_true_eq] at hp ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  cases hx : a.oracles[o]? with
  | none =>
    rw [hx] at h2
    cases h2
  | some x =>
    obtain ⟨x', hx', e⟩ := h.shapes o x hx
    have hb := tableBitsS_grown h hx part
    rw [hx] at h2
    rw [hx', hb]
    refine ⟨⟨⟨⟨hm o h1, ?_⟩, h3⟩, h4⟩, h1, rfl⟩
    show decide (0 < x'.shape.rows part) = true
    rw [e]
    exact h2

/-! ## 2 A constraint that does not name a message has the coefficient 0 on it -/

/-- A fold that never turns its value. -/
theorem foldl_stays {α β : Type} (f : β → α → β) : ∀ (l : List α) (z : β),
    (∀ x ∈ l, ∀ s, f s x = s) → l.foldl f z = z
  | [], _, _ => rfl
  | x :: l, z, h => by
    rw [List.foldl_cons, h x List.mem_cons_self,
      foldl_stays f l z fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **No term, single entry, run or whole vector of the constraint names the message o: then its
coefficient on every entry of o's tables is the element 0 itself.** -/
theorem coefficient_none (r : OnBytes.Row) (o : Nat) (part : Part) (i : Nat)
    (h1 : ∀ t ∈ r.terms.toList, t.oracle ≠ o) (h2 : ∀ u ∈ r.units.toList, u.oracle ≠ o)
    (h3 : ∀ w ∈ r.runs.toList, w.oracle ≠ o) (h4 : ∀ f ∈ r.forms.toList, f.oracle ≠ o) :
    r.coefficient o part i = zeroE := by
  unfold OnBytes.Row.coefficient
  simp only [← Array.foldl_toList]
  rw [foldl_stays _ r.forms.toList _ fun f hf s => by
      have e : (f.oracle == o) = false := beq_eq_false_iff_ne.2 (h4 f hf)
      simp [e],
    foldl_stays _ r.runs.toList _ fun w hw s => by
      have e : (w.oracle == o) = false := beq_eq_false_iff_ne.2 (h3 w hw)
      simp [e],
    foldl_stays _ r.units.toList _ fun u hu s => by
      have e : (u.oracle == o) = false := beq_eq_false_iff_ne.2 (h2 u hu)
      simp [e],
    foldl_stays _ r.terms.toList _ fun t ht s => by
      have e : (t.oracle == o) = false := beq_eq_false_iff_ne.2 (h1 t ht)
      simp [e]]

/-! ## 3 The law -/

/-- **A constraint that passes the five clauses at a shape passes them at the shape grown.** -/
theorem rowRestS_grown {a a' : StSh} {g : Nat} (h : Grown a a' g) (r : OnBytes.Row)
    (hr : rowRestS a g r = true) : rowRestS a' g r = true := by
  unfold rowRestS at hr ⊢
  cases hG : a.groups[g]? with
  | none =>
    rw [hG] at hr
    cases hr
  | some G =>
    obtain ⟨G', hG', hm, hp⟩ := h.group G hG
    rw [hG] at hr
    rw [hG']
    simp only [has, Option.map_some, Option.getD_some, Bool.and_eq_true,
      Array.all_eq_true_iff_forall_mem, List.all_eq_true, decide_eq_true_eq] at hr ⊢
    obtain ⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩ := hr
    refine ⟨⟨⟨⟨fun t ht => ⟨(t1 t ht).1, (placeFitsS_grown h hm (t1 t ht).2).1⟩, fun u hu => ?_⟩,
      fun w hw => ?_⟩, fun f hf => ?_⟩, fun o ho q hq => ?_⟩
    · obtain ⟨p1, _, p3⟩ := placeFitsS_grown h hm (t2 u hu)
      rw [p3]
      exact p1
    · obtain ⟨p1, _, p3⟩ := placeFitsS_grown h hm (t3 w hw).2
      rw [p3]
      exact ⟨(t3 w hw).1, p1⟩
    · obtain ⟨p1, _, p3⟩ := placeFitsS_grown h hm (t4 f hf).1
      rw [p3]
      exact ⟨p1, (t4 f hf).2⟩
    · by_cases hold : o ∈ G.members
      · rw [hp o hold] at hq
        exact t5 o hold q hq
      · rw [coefficient_none r o q.1 q.2
          (fun t ht c => hold (c ▸
            (placeFitsS_grown h hm (t1 t (Array.mem_toList_iff.1 ht)).2).2.1))
          (fun u hu c => hold (c ▸
            (placeFitsS_grown h hm (t2 u (Array.mem_toList_iff.1 hu))).2.1))
          (fun w hw c => hold (c ▸
            (placeFitsS_grown h hm (t3 w (Array.mem_toList_iff.1 hw)).2).2.1))
          (fun f hf c => hold (c ▸
            (placeFitsS_grown h hm (t4 f (Array.mem_toList_iff.1 hf)).1).2.1))]
        rfl

/-! ## 4 The thirteen plain functions on shapes: each leaves a shape that is the shape in front,
grown; the admitting and the copying under a premise -/

/-- A changed list at any number. The library's modAt_get (Core.lean) is the case j = i. -/
theorem modAt_at {α : Type} (l : List α) (i j : Nat) (f : α → α) :
    (modAt l i f)[j]? = (l[j]?).map fun x => if j = i then f x else x := by
  unfold modAt
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases l[j]? with
  | none => rfl
  | some x => simp

/-- A change of one message that leaves its shape; it leaves its pad too, or the message is no
member of the group. -/
theorem orc_grown (a : StSh) (g o : Nat) (f : OrcSh → OrcSh) (hs : ∀ x, (f x).shape = x.shape)
    (hp : (∀ x, (f x).pad = x.pad) ∨ ∀ G : GrpSh, a.groups[g]? = some G → o ∉ G.members) :
    Grown a { a with oracles := modAt a.oracles o f } g := by
  refine ⟨rfl, fun j x hx => ?_, fun G hG => ⟨G, hG, fun _ c => c, fun j hj => ?_⟩⟩
  · refine ⟨if j = o then f x else x, ?_, ?_⟩
    · show (modAt a.oracles o f)[j]? = _
      rw [modAt_at, hx]
      rfl
    · split
      · exact hs x
      · rfl
  · show (((modAt a.oracles o f)[j]?).map (·.pad)).getD [] = _
    rw [modAt_at]
    cases a.oracles[j]? with
    | none => rfl
    | some x =>
      show (if j = o then f x else x).pad = x.pad
      split
      · rename_i e
        rcases hp with hp | hp
        · exact hp x
        · exact absurd (e ▸ hj) (hp G hG)
      · rfl

/-- A change of one group that loses no member. -/
theorem grp_grown (a : StSh) (g g' : Nat) (f : GrpSh → GrpSh)
    (hm : ∀ (G : GrpSh) (o : Nat), o ∈ G.members → o ∈ (f G).members) :
    Grown a { a with groups := modAt a.groups g' f } g := by
  refine ⟨rfl, fun _ x hx => ⟨x, hx, rfl⟩, fun G hG => ⟨if g = g' then f G else G, ?_, ?_,
    fun _ _ => rfl⟩⟩
  · show (modAt a.groups g' f)[g]? = _
    rw [modAt_at, hG]
    rfl
  · intro o ho
    split
    · exact hm G o ho
    · exact ho

/-- Messages without a pad come behind those that are there. -/
theorem more_orcs (a : StSh) (g : Nat) (l : List OrcSh) (hl : ∀ x ∈ l, x.pad = []) :
    Grown a { a with oracles := a.oracles ++ l } g := by
  have key : ∀ (j : Nat) (x : OrcSh), a.oracles[j]? = some x → (a.oracles ++ l)[j]? = some x :=
    fun j x hx => by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]
      exact hx
  refine ⟨rfl, fun j x hx => ⟨x, key j x hx, rfl⟩, fun G hG => ⟨G, hG, fun _ c => c, fun j _ => ?_⟩⟩
  show (((a.oracles ++ l)[j]?).map (·.pad)).getD [] = _
  cases hx : a.oracles[j]? with
  | some x => rw [key j x hx]
  | none =>
    cases hy : (a.oracles ++ l)[j]? with
    | none => rfl
    | some y =>
      have hmem : y ∈ a.oracles ++ l := List.mem_of_getElem? hy
      rcases List.mem_append.1 hmem with c | c
      · rw [List.getElem?_append_right (List.getElem?_eq_none_iff.1 hx)] at hy
        exact hl y (List.mem_of_getElem? hy)
      · exact hl y c

/-- Groups come behind those that are there: a list of them. -/
theorem more_groups (a : StSh) (g : Nat) (l : List GrpSh) :
    Grown a { a with groups := a.groups ++ l } g :=
  ⟨rfl, fun _ x hx => ⟨x, hx, rfl⟩, fun G hG => ⟨G, by
    show (a.groups ++ l)[g]? = _
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hG).1]
    exact hG, fun _ c => c, fun _ _ => rfl⟩⟩

/-- A member laid into a list loses none. -/
theorem mem_insAt {α : Type} (l : List α) (i : Nat) (x y : α) (h : y ∈ l) : y ∈ insAt l i x := by
  unfold insAt
  split
  · rename_i hi
    exact (List.mem_insertIdx hi).2 (Or.inr h)
  · exact h

/-- The joining: the group loses no member; of a message the list of its groups alone changes. -/
theorem join_grown {a a' : CoreSh} {g' o : Nat} {kept : Bool} (h : joinS a g' o kept = some a')
    (g : Nat) : Grown a.st a'.st g := by
  unfold joinS at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (grp_grown a.st g g' (fun G' => { G' with
        members := insAt G'.members (G.members.filter (· < o)).length o
        kept := insAt G'.kept (G.members.filter (· < o)).length kept })
      fun G' o' ho' => mem_insAt _ _ _ _ ho').trans
      (orc_grown _ g o (fun x => { x with groups := x.groups ++ [g'] }) (fun _ => rfl)
        (Or.inl fun _ => rfl))
  · cases h

/-- The adding of a constraint: of a group the kinds alone change. -/
theorem addRow_grown {a a' : CoreSh} {g' : Nat} {kind : RowKind} (h : addRowS a g' kind = some a')
    (g : Nat) : Grown a.st a'.st g := by
  unfold addRowS at h
  split at h
  · obtain rfl := Option.some.inj h
    exact grp_grown a.st g g' _ fun _ _ c => c
  · cases h

/-- Constraints added one behind the other. -/
theorem addRowsFrom_grown (g' g : Nat) : ∀ (kinds : List RowKind) (a a' : CoreSh),
    addRowsFromS g' kinds a = some a' → Grown a.st a'.st g
  | [], a, a', h => by
    obtain rfl := Option.some.inj h
    exact Grown.refl _ _
  | k :: l, a, a', h => by
    obtain ⟨b, hb, h'⟩ := Option.bind_eq_some_iff.1 h
    exact (addRow_grown hb g).trans (addRowsFrom_grown g' g l b a' h')

/-- The adding of constraints. -/
theorem addRows_grown {a a' : CoreSh} {g' : Nat} {kinds : List RowKind}
    (h : addRowsS a g' kinds = some a') (g : Nat) : Grown a.st a'.st g := by
  unfold addRowsS at h
  split at h
  · exact addRowsFrom_grown g' g kinds a a' h
  · cases h

/-- A new group comes behind those that are there. -/
theorem newGroup_grown {a : CoreSh} {code maskCode : Nat} {y : Nat × CoreSh}
    (h : newGroupS a code maskCode = some y) (g : Nat) : Grown a.st y.2.st g := by
  unfold newGroupS at h
  split at h
  · obtain rfl := Option.some.inj h
    exact more_groups a.st g _
  · cases h

/-- A message as it comes in has no pad. -/
theorem fresh_pad (sent : Array OracleNotice) : ∀ x ∈ sent.toList.map freshOrc, x.pad = [] := by
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx
  rfl

/-- The receiving: messages without a pad come behind those that are there. -/
theorem recv_grown {first : Nat} {a : CoreSh} {sent : Array OracleNotice}
    {y : Array Nat × CoreSh} (h : recvS first a sent = some y) (g : Nat) :
    Grown a.st y.2.st g := by
  unfold recvS at h
  split at h
  · obtain ⟨lay, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact more_orcs a.st g _ (fresh_pad sent)
  · cases h

/-- The taking over: the like. -/
theorem adopt_grown {a : CoreSh} {sent : Array OracleNotice} {given : List (Nat × SrcSh)}
    {y : Array Nat × CoreSh} (h : adoptS a sent given = some y) (g : Nat) :
    Grown a.st y.2.st g := by
  unfold adoptS at h
  split at h
  · obtain ⟨lay, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact more_orcs a.st g _ (fresh_pad sent)
  · cases h

/-- The taking of a mask entry: a ledger alone changes. -/
theorem takeMask_grown {a : CoreSh} {o : Nat} {y : Nat × CoreSh} (h : takeMaskS a o = some y)
    (g : Nat) : Grown a.st y.2.st g := by
  unfold takeMaskS at h
  split at h
  · obtain ⟨l, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact orc_grown a.st g o _ (fun _ => rfl) (Or.inl fun _ => rfl)
  · cases h

/-- Mask entries taken one behind the other. -/
theorem takeMasksInto_grown (o g : Nat) : ∀ (n : Nat) (a : CoreSh) (acc : Array Nat)
    (y : List Nat × CoreSh), takeMasksIntoS o n a acc = some y → Grown a.st y.2.st g
  | 0, a, acc, y, h => by
    obtain rfl := Option.some.inj h
    exact Grown.refl _ _
  | n + 1, a, acc, y, h => by
    rw [takeMasksIntoS] at h
    split at h
    · cases h
    · rename_i i b hb
      exact (takeMask_grown hb g).trans (takeMasksInto_grown o g n b _ y h)

/-- The taking of mask entries. -/
theorem takeMasks_grown {a : CoreSh} {o count : Nat} {y : List Nat × CoreSh}
    (h : takeMasksS a o count = some y) (g : Nat) : Grown a.st y.2.st g :=
  takeMasksInto_grown o g count a #[] y h

/-- A ledger is shut. -/
theorem closeLedger_grown {a a' : CoreSh} {o : Nat} (h : closeLedgerS a o = some a') (g : Nat) :
    Grown a.st a'.st g := by
  unfold closeLedgerS at h
  split at h
  · obtain rfl := Option.some.inj h
    exact orc_grown a.st g o _ (fun _ => rfl) (Or.inl fun _ => rfl)
  · cases h

/-- A message is spent as a mask: its field spent alone changes. -/
theorem spend_grown {a a' : CoreSh} {o : Nat} (h : spendS a o = some a') (g : Nat) :
    Grown a.st a'.st g := by
  unfold spendS at h
  split at h
  · obtain rfl := Option.some.inj h
    exact orc_grown a.st g o _ (fun _ => rfl) (Or.inl fun _ => rfl)
  · cases h

/-- **The admitting**, which lays a pad on its message. Premise: the message is no member of the
group. -/
theorem admit_grown {a a' : CoreSh} {o n : Nat} (h : admitS a o n = some a') (g : Nat)
    (hm : ∀ G : GrpSh, a.st.groups[g]? = some G → o ∉ G.members) : Grown a.st a'.st g := by
  unfold admitS at h
  split at h
  · obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact orc_grown a.st g o _ (fun _ => rfl) (Or.inr hm)
  · cases h

/-- **The copying of a sample**, which lays a pad on the message mine. Premise: that message is no
member of the group. -/
theorem elsewhere_grown {a a' : CoreSh} {mine theirs : Nat} {b : StSh}
    (h : elsewhereS a mine b theirs = some a') (g : Nat)
    (hm : ∀ G : GrpSh, a.st.groups[g]? = some G → mine ∉ G.members) : Grown a.st a'.st g := by
  unfold elsewhereS at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact orc_grown a.st g mine _ (fun _ => rfl) (Or.inr hm)
  · cases h

/-- Ledgers are shut, one behind the other. -/
theorem shut_grown (g : Nat) : ∀ (l : List Nat) (a : StSh),
    Grown a { a with oracles := l.foldl (fun os o => modAt os o shutS) a.oracles } g
  | [], a => Grown.refl a g
  | o :: l, a =>
    (orc_grown a g o shutS (fun _ => rfl) (Or.inl fun _ => rfl)).trans
      (shut_grown g l { a with oracles := modAt a.oracles o shutS })

/-- The beginning of a test: ledgers are shut; of the group the fields inRun and kinds change. -/
theorem beginRun_grown {a : CoreSh} {g' : Nat} {y : (GroupLayout × Nat) × CoreSh}
    (h : beginRunS a g' = some y) (g : Nat) : Grown a.st y.2.st g := by
  unfold beginRunS at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (shut_grown g G.members a.st).trans (grp_grown _ g g' _ fun _ _ c => c)
  · cases h

/-- Every member of the group is sampled: with code, on the shape. True where the group is not
there. A member whose message is not there counts as not sampled: the test fails. -/
def membersSampledS (a : StSh) (g : Nat) : Bool :=
  (a.groups[g]?).all fun G => G.members.all fun o => (a.oracles[o]?).any (·.sampled)

/-- **Where every member is sampled, a message that is not sampled is no member.** «Not sampled» is
the test's own form: it takes in a message that is not there. -/
theorem notMember_of_sampled {a : StSh} {g o : Nat} (h : membersSampledS a g = true)
    (ho : (a.oracles[o]?).any (·.sampled) = false) :
    ∀ G : GrpSh, a.groups[g]? = some G → o ∉ G.members := by
  intro G hG hmem
  unfold membersSampledS at h
  rw [hG] at h
  have := List.all_eq_true.1 h o hmem
  rw [ho] at this
  cases this

/-! ## 5 The mark, a function of a statement -/

/-- **THE MARK AT THE GROUP g**: every constraint that lies open on the group is no sample
constraint and passes, AT THE STATEMENT AS IT IS, the five clauses of the adding that read its
summands. True where the group is not there. -/
def claimsAtB (S : Statement) (g : Nat) : Bool :=
  (S.groups[g]?).all fun G => G.rows.all fun r => r.kind != .sample && rowRestB S g r

/-- What the mark says. -/
theorem claimsAt_iff {S : Statement} {g : Nat} : claimsAtB S g = true ↔
    ∀ G : Group, S.groups[g]? = some G → ∀ r ∈ G.rows.toList,
      (r.kind != .sample) = true ∧ rowRestB S g r = true := by
  unfold claimsAtB
  cases S.groups[g]? with
  | none => simp
  | some G =>
    simp only [Option.all_some, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
      Option.some.injEq, forall_eq', Array.mem_toList_iff]

/-- At a statement without a group the mark is true. -/
theorem claims_start (codes : Codes) (oracles : Array Oracle) (g : Nat) :
    claimsAtB { codes := codes, oracles := oracles, groups := #[] } g = true :=
  claimsAt_iff.2 fun G h => by simp at h

/-- **The mark is kept** where the shape behind is the shape in front, grown, and each constraint
that lies behind lay in front, or passes by itself. -/
theorem claims_keep {S S' : Statement} {g : Nat} (hG : Grown (stSh S) (stSh S') g)
    (hr : ∀ G' : Group, S'.groups[g]? = some G' → ∀ r ∈ G'.rows.toList,
      (∃ G : Group, S.groups[g]? = some G ∧ r ∈ G.rows.toList) ∨
        ((r.kind != .sample) = true ∧ rowRestB S' g r = true))
    (h : claimsAtB S g = true) : claimsAtB S' g = true := by
  refine claimsAt_iff.2 fun G' hG' r hrm => ?_
  rcases hr G' hG' r hrm with ⟨G, hG0, hm⟩ | hn
  · obtain ⟨k, p⟩ := claimsAt_iff.1 h G hG0 r hm
    refine ⟨k, ?_⟩
    rw [← rowRestS_eq] at p ⊢
    exact rowRestS_grown hG r p
  · exact hn

/-- Where the groups stay, each constraint that lies behind lay in front. -/
theorem old_rows {S S' : Statement} {g : Nat} (e : S'.groups = S.groups) :
    ∀ G' : Group, S'.groups[g]? = some G' → ∀ r ∈ G'.rows.toList,
      (∃ G : Group, S.groups[g]? = some G ∧ r ∈ G.rows.toList) ∨
        ((r.kind != .sample) = true ∧ rowRestB S' g r = true) :=
  fun G' hG' _ hr => Or.inl ⟨G', e ▸ hG', hr⟩

/-- A change of one group that adds no constraint to it (it may take some away). -/
theorem old_rows_modify {S S' : Statement} {g g' : Nat} {f : Group → Group}
    (e : S'.groups = S.groups.modify g' f) (hf : ∀ G, ∀ r ∈ (f G).rows.toList, r ∈ G.rows.toList) :
    ∀ G' : Group, S'.groups[g]? = some G' → ∀ r ∈ G'.rows.toList,
      (∃ G : Group, S.groups[g]? = some G ∧ r ∈ G.rows.toList) ∨
        ((r.kind != .sample) = true ∧ rowRestB S' g r = true) := by
  intro G' hG' r hr
  rw [e, Array.getElem?_modify] at hG'
  split at hG'
  · obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hG'
    exact Or.inl ⟨G, hG, hf G r hr⟩
  · exact Or.inl ⟨G', hG', hr⟩

/-! ## 6 Each of the thirteen plain functions keeps the mark, at every group; the admitting and the
copying under a premise -/

/-- The joining keeps the mark: also at the group that the message joins. -/
theorem join_claims (d d' : DState L) (g' o : Nat) (kept : Bool)
    (h : joinP d g' o kept = some d') (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  refine claims_keep (join_grown (join_carries d d' g' o kept h) g) ?_ hc
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact old_rows_modify (f := fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }) rfl
      fun _ _ c => c
  · cases h

/-- **The adding lays the mark on what it adds**: the new constraint has just passed the clauses,
and they do not read the group's constraints. -/
theorem addRow_claims (d d' : DState L) (g' : Nat) (row : OnBytes.Row)
    (h : addRowP d g' row = some d') (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  refine claims_keep (addRow_grown (addRow_carries d d' g' row h) g) ?_ hc
  unfold addRowP at h
  split at h
  · rename_i hok
    obtain rfl := Option.some.inj h
    rw [addRowG_eq, Bool.and_eq_true] at hok
    intro G' hG' r hr
    have hG'' : (d.st.groups.modify g' fun G => { G with rows := G.rows.push row })[g]? =
      some G' := hG'
    rw [Array.getElem?_modify] at hG''
    split at hG''
    · rename_i e
      obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hG''
      have hr' : r ∈ (G.rows.push row).toList := hr
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr'
      rcases hr' with c | rfl
      · exact Or.inl ⟨G, hG, c⟩
      · refine Or.inr ⟨?_, ?_⟩
        · have := hok.1
          unfold addRowG at this
          rw [Bool.and_eq_true] at this
          exact this.2
        · subst e
          show rowRestB (withRow d.st g' r) g' r = true
          rw [rowRestB_withRow]
          exact hok.2
    · exact Or.inl ⟨G', hG'', hr⟩
  · cases h

/-- Constraints added one behind the other. -/
theorem addRowsFrom_claims (g' g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g' rows d = some d' → claimsAtB d.st g = true → claimsAtB d'.st g = true
  | [], d, d', h, hc => by
    obtain rfl := Option.some.inj h
    exact hc
  | r :: l, d, d', h, hc => by
    obtain ⟨e, he, h'⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_claims g' g l e d' h' (addRow_claims d e g' r he g hc)

/-- The adding of constraints keeps and lays the mark. -/
theorem addRows_claims (d d' : DState L) (g' : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g' rows = some d') (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_claims g' g rows d d' h hc
  · cases h

/-- A new group: no constraint lies on it. -/
theorem newGroup_claims (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  refine claims_keep (newGroup_grown (newGroup_carries d d' code maskCode n h) g) ?_ hc
  unfold newGroupP at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    intro G' hG' r hr
    have hG'' : (d.st.groups.push { code := code, maskCode := maskCode })[g]? = some G' := hG'
    rw [Array.getElem?_push] at hG''
    split at hG''
    · obtain rfl := Option.some.inj hG''
      cases hr
    · exact Or.inl ⟨G', hG'', hr⟩
  · cases h

/-- The receiving keeps the mark. -/
theorem recv_claims (first : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP first d sent = some (ids, d')) (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  refine claims_keep (recv_grown (recv_carries first d d' sent ids h) g) (old_rows ?_) hc
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    rfl
  · cases h

/-- The taking over keeps the mark. -/
theorem adopt_claims (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat) (h : adoptP d sent given = some (ids, d'))
    (g : Nat) (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (adopt_grown (adopt_carries d d' sent given ids h) g) (old_rows ?_) hc
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    rfl
  · cases h

/-- The taking of a mask entry keeps the mark. -/
theorem takeMask_claims (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d'))
    (g : Nat) (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (takeMask_grown (takeMask_carries d d' o n h) g) (old_rows ?_) hc
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    rfl
  · cases h

/-- Mask entries taken one behind the other. -/
theorem takeMasksInto_claims (o g : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') → claimsAtB d.st g = true →
    claimsAtB d'.st g = true
  | 0, d, d', acc, l, h, hc => by
    cases h
    exact hc
  | n + 1, d, d', acc, l, h, hc => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      exact takeMasksInto_claims o g n e d' _ l h (takeMask_claims d e o i he g hc)

/-- The taking of mask entries keeps the mark. -/
theorem takeMasks_claims (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true :=
  takeMasksInto_claims o g count d d' #[] l h hc

/-- The shutting of a ledger keeps the mark. -/
theorem closeLedger_claims (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d') (g : Nat)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (closeLedger_grown (closeLedger_carries d d' o h) g) (old_rows ?_) hc
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- The spending of a mask keeps the mark. -/
theorem spend_claims (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d') (g : Nat)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (spend_grown (spend_carries d d' o h) g) (old_rows ?_) hc
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- **The admitting**, where the message is no member of the group. -/
theorem admit_claims (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') (g : Nat)
    (hm : ∀ G : GrpSh, (stSh d.st).groups[g]? = some G → o ∉ G.members)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (admit_grown (admit_carries d d' o rows h) g hm) (old_rows ?_) hc
  unfold admitP at h
  split at h
  · obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- **The copying of a sample**, where the message is no member of the group. -/
theorem elsewhere_claims (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (g : Nat)
    (hm : ∀ G : GrpSh, (stSh d.st).groups[g]? = some G → mine ∉ G.members)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true := by
  refine claims_keep (elsewhere_grown (elsewhere_carries d d' mine other theirs h) g hm)
    (old_rows ?_) hc
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

/-- **The beginning of a test.** At the group under test the constraints have left the statement:
the mark is true there for nothing. -/
theorem beginRun_claims (d d' : DState L) (g' : Nat) (run : RunInput)
    (h : beginRunP d g' = some (run, d')) (g : Nat) (hc : claimsAtB d.st g = true) :
    claimsAtB d'.st g = true := by
  refine claims_keep (beginRun_grown (beginRun_carries d d' g' run h) g) ?_ hc
  unfold beginRunP at h
  split at h
  · obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact old_rows_modify (f := fun G => { G with inRun := true, rows := #[] })
      (by
        show (begun d.st g' G).groups = _
        unfold begun
        dsimp only
        rw [ProxRun.closeLedgers_groups]
        rfl)
      fun _ _ c => by cases c
  · cases h

/-! ## 7 The mark and the front's own test -/

/-- refuse returns .ok exactly where all clauses hold. -/
theorem refuse_ok (l : Clauses) : refuse l = .ok () ↔ ok l = true := by
  unfold refuse ok
  cases hf : l.find? (!·.2) with
  | none =>
    simp only [true_iff, List.all_eq_true]
    intro c hc
    have := List.find?_eq_none.1 hf c hc
    simpa using this
  | some c =>
    simp only [reduceCtorEq, false_iff]
    intro hall
    have h1 := List.find?_some hf
    have h2 := List.all_eq_true.1 hall c (List.mem_of_find?_eq_some hf)
    simp [h2] at h1

/-- A list of tests, one behind the other, returns .ok exactly where each does. -/
theorem forM_ok {α : Type} (f : α → Except String Unit) : ∀ l : List α,
    l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok ()
  | [] => by simp [pure, Except.pure]
  | x :: l => by
    rw [show (x :: l).forM f = (f x >>= fun _ => l.forM f) from rfl]
    cases hx : f x with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, List.mem_cons, forall_eq_or_imp, hx, false_and]
    | ok u =>
      simp only [bind, Except.bind, List.mem_cons, forall_eq_or_imp, hx, true_and]
      exact forM_ok f l

/-- **From the mark to the front's test**: where the group is there and no test of it has begun,
every constraint that lies open on it could be laid on it now. -/
theorem open_of_claims {S : Statement} {g : Nat} {G : Group} (hG : S.groups[g]? = some G)
    (hrun : G.inRun = false) (h : claimsAtB S g = true) : openClaimsE S g = .ok () := by
  unfold openClaimsE
  rw [hG]
  refine (forM_ok _ _).2 fun r hr => (refuse_ok _).2 ?_
  obtain ⟨k, p⟩ := claimsAt_iff.1 h G hG r hr
  rw [addRowG_eq, Bool.and_eq_true]
  refine ⟨?_, p⟩
  unfold addRowG
  rw [grp_get, hG, Bool.and_eq_true]
  exact ⟨by simp [grpSh, hrun], k⟩

/-- **From the front's test to the mark.** -/
theorem claims_of_open {S : Statement} {g : Nat} (h : openClaimsE S g = .ok ()) :
    claimsAtB S g = true := by
  refine claimsAt_iff.2 fun G hG r hr => ?_
  unfold openClaimsE at h
  rw [hG] at h
  have hk := (refuse_ok _).1 ((forM_ok _ _).1 h r hr)
  rw [addRowG_eq, Bool.and_eq_true] at hk
  refine ⟨?_, hk.2⟩
  have := hk.1
  unfold addRowG at this
  rw [Bool.and_eq_true] at this
  exact this.2

/-- **From the mark to the front's test as one Bool**: at the group, every constraint that lies open
passes all clauses of the adding. -/
theorem rowsPass_of_claims {S : Statement} {g : Nat} {G : Group} (hG : S.groups[g]? = some G)
    (hrun : G.inRun = false) (h : claimsAtB S g = true) :
    ((S.groups[g]?).any fun G => G.rows.toList.all fun row => ok (rowL S g row)) = true := by
  have ho := open_of_claims hG hrun h
  unfold openClaimsE at ho
  rw [hG] at ho
  rw [hG]
  exact List.all_eq_true.2 fun r hr => (refuse_ok _).1 ((forM_ok _ _).1 ho r hr)

/-- **From that Bool to the mark.** -/
theorem claims_of_rowsPass {S : Statement} {g : Nat}
    (h : ((S.groups[g]?).any fun G => G.rows.toList.all fun row => ok (rowL S g row)) = true) :
    claimsAtB S g = true := by
  refine claims_of_open ?_
  unfold openClaimsE
  cases hG : S.groups[g]? with
  | none =>
    rw [hG] at h
    cases h
  | some G =>
    rw [hG] at h
    exact (forM_ok _ _).2 fun r hr => (refuse_ok _).2 (List.all_eq_true.1 h r hr)

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.Grown.refl
#print axioms VerifiableInference.Desc.Ground.Sh.Grown.trans
#print axioms VerifiableInference.Desc.Ground.Sh.tableBitsS_grown
#print axioms VerifiableInference.Desc.Ground.Sh.placeFitsS_grown
#print axioms VerifiableInference.Desc.Ground.Sh.foldl_stays
#print axioms VerifiableInference.Desc.Ground.Sh.coefficient_none
#print axioms VerifiableInference.Desc.Ground.Sh.rowRestS_grown
#print axioms VerifiableInference.Desc.Ground.Sh.modAt_at
#print axioms VerifiableInference.Desc.Ground.Sh.orc_grown
#print axioms VerifiableInference.Desc.Ground.Sh.grp_grown
#print axioms VerifiableInference.Desc.Ground.Sh.more_orcs
#print axioms VerifiableInference.Desc.Ground.Sh.more_groups
#print axioms VerifiableInference.Desc.Ground.Sh.mem_insAt
#print axioms VerifiableInference.Desc.Ground.Sh.join_grown
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_grown
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_grown
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_grown
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_grown
#print axioms VerifiableInference.Desc.Ground.Sh.fresh_pad
#print axioms VerifiableInference.Desc.Ground.Sh.recv_grown
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_grown
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_grown
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_grown
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_grown
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_grown
#print axioms VerifiableInference.Desc.Ground.Sh.spend_grown
#print axioms VerifiableInference.Desc.Ground.Sh.admit_grown
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_grown
#print axioms VerifiableInference.Desc.Ground.Sh.shut_grown
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_grown
#print axioms VerifiableInference.Desc.Ground.Sh.notMember_of_sampled
#print axioms VerifiableInference.Desc.Ground.Sh.claimsAt_iff
#print axioms VerifiableInference.Desc.Ground.Sh.claims_start
#print axioms VerifiableInference.Desc.Ground.Sh.claims_keep
#print axioms VerifiableInference.Desc.Ground.Sh.old_rows
#print axioms VerifiableInference.Desc.Ground.Sh.old_rows_modify
#print axioms VerifiableInference.Desc.Ground.Sh.join_claims
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_claims
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_claims
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_claims
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_claims
#print axioms VerifiableInference.Desc.Ground.Sh.recv_claims
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_claims
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_claims
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_claims
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_claims
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_claims
#print axioms VerifiableInference.Desc.Ground.Sh.spend_claims
#print axioms VerifiableInference.Desc.Ground.Sh.admit_claims
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_claims
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_claims
#print axioms VerifiableInference.Desc.Ground.Sh.refuse_ok
#print axioms VerifiableInference.Desc.Ground.Sh.forM_ok
#print axioms VerifiableInference.Desc.Ground.Sh.open_of_claims
#print axioms VerifiableInference.Desc.Ground.Sh.claims_of_open
#print axioms VerifiableInference.Desc.Ground.Sh.rowsPass_of_claims
#print axioms VerifiableInference.Desc.Ground.Sh.claims_of_rowsPass
