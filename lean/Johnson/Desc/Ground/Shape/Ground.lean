-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/Ground.lean: THE GROUND's ELEVEN PLAIN FUNCTIONS ON SHAPES. For each of
the ten plain functions of the ground and the beginning of a proximity test
(Johnson/Desc/First/Base/Ground.lean): a function with code on `CoreSh`
(Johnson/Desc/Ground/Shape/Core.lean): its guards as one Bool on the shape, and one update; and two
laws that hold it against the library's text. It stands over the library's ground alone: no kind,
no chain, no frame for an honest side.

The two laws, for a function X (`shD d`: the shape of a carried state's three).
  `X_carries`   where X accepts at d, XS at the shape in front returns what X returns (numbers, a
      layout) and THE SHAPE BEHIND. The accept is the one premise.
  `X_returns`   where XS returns at the shape in front, X accepts.
What an argument that holds values owes beside it, and what of it stands on the shape:
  `addRow`   on the shape: the new row's kind. returns asks `rowRestB d.st g row`: the five clauses
      of the adding that read the row's summands, as ONE Bool. Three of these five read values: the
      terms' and the forms' (a written-out variable's pair) and the pads' (the coefficients on
      them); the two others read no value.
  `admit`   on the shape: the number of the rows.
  `elsewhere`   on the shape: the other statement's shape.
  `adopt`   on the shape: each tree's number, and whether its root is the chain's own or given
      (`givenSh`).

Main names. `joinS`, `addRowS`, `adoptS`, `elsewhereS`, `newGroupS`, `takeMaskS`, `closeLedgerS`,
`spendS`, `admitS`, `recvS`, `beginRunS`, each with the two laws. `joinG_eq` and the like: the
guards on the shape are the library's own list of clauses, evaluated. `layoutS`, `layoutS_eq`: a
group's layout off the shape. `runCountS`, `runCountS_eq`: the number of rows that a test takes in.

Limits. `_returns` gives that X accepts, not what it returns: that is `_carries`. Nothing is said
of a maker of rows: that the rows which a sub-protocol makes pass `rowRestB` is owed where they are
made. Nothing is evaluated here. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.Ground.Shape.Core
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## 0 Helpers -/

/-- The shape of a carried state's three. -/
abbrev shD (d : DState L) : CoreSh := coreSh (coreOf d)

theorem stSh_eq {S : Statement} {c : Codes} {o : List OrcSh} {g : List GrpSh} (h1 : S.codes = c)
    (h2 : S.oracles.toList.map orcSh = o) (h3 : S.groups.toList.map grpSh = g) :
    stSh S = ⟨c, o, g⟩ := by
  unfold stSh
  rw [h1, h2, h3]

/-- A member laid into a list at a place, if the place is there. -/
def insAt {α : Type} (l : List α) (i : Nat) (x : α) : List α :=
  if i ≤ l.length then l.insertIdx i x else l

theorem insAt_toList {α : Type} (a : Array α) (i : Nat) (x : α) :
    (a.insertIdxIfInBounds i x).toList = insAt a.toList i x := by
  unfold insAt Array.insertIdxIfInBounds
  rw [Array.length_toList]
  split
  · rw [Array.toList_insertIdx]
  · rfl

/-! ## 1 A message joins a group -/

/-- The guards of the joining, on the shape. -/
def joinG (a : StSh) (g o : Nat) (kept : Bool) : Bool :=
  match a.groups[g]?, a.oracles[o]? with
  | some G, some x =>
    x.sampled && !G.inRun && (x.shape.mainRows == 0 || x.shape.code == G.code) &&
      (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode) && !G.members.contains o &&
      (!kept || decide (0 < x.shape.mainRows))
  | _, _ => false

theorem joinG_eq (S : Statement) (g o : Nat) (kept : Bool) :
    joinG (stSh S) g o kept = ok (joinL S g o kept) := by
  unfold joinG ok joinL
  rw [grp_get, orc_get]
  cases S.groups[g]? <;> cases S.oracles[o]? <;>
    simp [has, grpSh, orcSh, Bool.and_assoc]

/-- **The joining on shapes.** -/
def joinS (a : CoreSh) (g o : Nat) (kept : Bool) : Option CoreSh :=
  if joinG a.st g o kept then
    (a.st.groups[g]?).map fun G => { a with st := { a.st with
      groups := modAt a.st.groups g fun G' => { G' with
        members := insAt G'.members (G.members.filter (· < o)).length o
        kept := insAt G'.kept (G.members.filter (· < o)).length kept }
      oracles := modAt a.st.oracles o fun x => { x with groups := x.groups ++ [g] } } }
  else none

theorem join_carries (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') :
    joinS (shD d) g o kept = some (shD d') := by
  unfold joinP at h
  split at h
  · rename_i hok
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold joinS
    have hg : joinG (shD d).st g o kept = true := (joinG_eq d.st g o kept).trans hok
    rw [if_pos hg]
    show ((stSh d.st).groups[g]?).map _ = _
    rw [grp_get, hG, Option.map_some, Option.map_some]
    congr 1
    have efs : (G.members.filter (· < o)).size = (G.members.toList.filter (· < o)).length := by
      rw [← Array.length_toList, Array.toList_filter]
    show _ = CoreSh.mk (stSh (withMessageInGroup d.st g o kept G)) (bookSh d.book) d.roots
    rw [stSh_eq (S := withMessageInGroup d.st g o kept G) rfl
      (map_modify _ _ _ orcSh (fun x => { x with groups := x.groups ++ [g] }) fun _ => rfl)
      (map_modify _ _ _ grpSh (fun G' => { G' with
        members := insAt G'.members ((grpSh G).members.filter (· < o)).length o
        kept := insAt G'.kept ((grpSh G).members.filter (· < o)).length kept }) fun G' => by
          show grpSh _ = _
          unfold grpSh
          simp only [insAt_toList]
          rw [efs])]
    rfl
  · cases h

theorem join_returns (d : DState L) (g o : Nat) (kept : Bool) (y : CoreSh)
    (h : joinS (shD d) g o kept = some y) : ∃ d', joinP d g o kept = some d' := by
  unfold joinS at h
  split at h
  · rename_i hg
    have hok : ok (joinL d.st g o kept) = true := (joinG_eq d.st g o kept).symm.trans hg
    obtain ⟨G', hG', _⟩ := Option.map_eq_some_iff.1 h
    have hG'' : ((d.st.groups[g]?).map grpSh) = some G' := (grp_get d.st g).symm.trans hG'
    obtain ⟨G, hG, _⟩ := Option.map_eq_some_iff.1 hG''
    unfold joinP
    rw [if_pos hok, hG]
    exact ⟨_, rfl⟩
  · cases h

/-! ## 2 A new open row -/

/-- The five clauses of the adding that read the row's summands, as one test with code. Three of
them read values: the terms' and the forms' (a written-out variable's pair) and the pads' (the
coefficients on them). -/
def rowRestB (S : Statement) (g : Nat) (row : OnBytes.Row) : Bool := ok ((rowL S g row).drop 3)

/-- The guards of the adding, on the shape. kind: the new row's. -/
def addRowG (a : StSh) (g : Nat) (kind : RowKind) : Bool :=
  (a.groups[g]?).any (fun G => !G.inRun) && kind != .sample

theorem addRowG_eq (S : Statement) (g : Nat) (row : OnBytes.Row) :
    ok (rowL S g row) = (addRowG (stSh S) g row.kind && rowRestB S g row) := by
  unfold addRowG rowRestB ok rowL
  rw [grp_get]
  cases S.groups[g]? <;> simp [has, grpSh, Bool.and_assoc]

/-- **The adding of an open row on shapes.** -/
def addRowS (a : CoreSh) (g : Nat) (kind : RowKind) : Option CoreSh :=
  if addRowG a.st g kind then
    some { a with st := { a.st with
      groups := modAt a.st.groups g fun G => { G with kinds := G.kinds ++ [kind] } } }
  else none

theorem addRow_carries (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') :
    addRowS (shD d) g row.kind = some (shD d') := by
  unfold addRowP at h
  split at h
  · rename_i hok
    cases h
    rw [addRowG_eq, Bool.and_eq_true] at hok
    unfold addRowS
    have hg : addRowG (shD d).st g row.kind = true := hok.1
    rw [if_pos hg]
    congr 1
    show _ = CoreSh.mk (stSh (withRow d.st g row)) (bookSh d.book) d.roots
    rw [stSh_eq (S := withRow d.st g row) rfl rfl
      (map_modify _ _ _ grpSh (fun G => { G with kinds := G.kinds ++ [row.kind] }) fun G => by
        show grpSh _ = _
        unfold grpSh
        simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil])]
    rfl
  · cases h

theorem addRow_returns (d : DState L) (g : Nat) (row : OnBytes.Row) (y : CoreSh)
    (h : addRowS (shD d) g row.kind = some y) (hv : rowRestB d.st g row = true) :
    ∃ d', addRowP d g row = some d' := by
  unfold addRowS at h
  split at h
  · rename_i hg
    unfold addRowP
    rw [if_pos (by rw [addRowG_eq, Bool.and_eq_true]; exact ⟨hg, hv⟩)]
    exact ⟨_, rfl⟩
  · cases h

/-! ## 3 Messages come in: received, or taken over from another chain -/

theorem foldl_push_sh {α β ι : Type} (sh : α → β) (mk : ι → α) : ∀ (l : List ι) (A : Array α),
    (l.foldl (fun t i => t.push (mk i)) A).toList.map sh =
      l.foldl (fun t i => t ++ [sh (mk i)]) (A.toList.map sh)
  | [], _ => rfl
  | i :: l, A => by
    rw [List.foldl_cons, List.foldl_cons, foldl_push_sh sh mk l, Array.toList_push,
      List.map_append]
    rfl

theorem foldl_modify_sh {α β ι : Type} (sh : α → β) (k : ι → Nat) (f : ι → α → α)
    (g : ι → β → β) (h : ∀ i x, sh (f i x) = g i (sh x)) : ∀ (l : List ι) (A : Array α),
    (l.foldl (fun t i => t.modify (k i) (f i)) A).toList.map sh =
      l.foldl (fun t i => modAt t (k i) (g i)) (A.toList.map sh)
  | [], _ => rfl
  | i :: l, A => by
    rw [List.foldl_cons, List.foldl_cons, foldl_modify_sh sh k f g h l,
      map_modify _ _ _ sh (g i) (h i)]

/-- A message as it comes in: not sampled, no sample row, no pad, in no group. -/
def freshOrc (n : OracleNotice) : OrcSh := ⟨n.shape, false, 0, [], [], none, false⟩

theorem sent_oracles (S : Statement) (sent : Array OracleNotice) :
    (stSent S sent).oracles.toList.map orcSh =
      S.oracles.toList.map orcSh ++ sent.toList.map freshOrc := by
  show (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle)).toList.map orcSh = _
  rw [Array.toList_append, Array.toList_map, List.map_append, List.map_map]
  rfl

theorem place_sent (B : Array (Nat × Nat)) (n : Nat) (f : Nat → Nat × Nat) :
    (B ++ (Array.range n).map f).toList = B.toList ++ (List.range n).map f := by
  rw [Array.toList_append, Array.toList_map, Array.toList_range]

/-- The new messages' places. -/
def placesS (a : CoreSh) (n : Nat) (lay : TreeLay) : List (Nat × Nat) :=
  a.book.place ++ (List.range n).map fun i =>
    (a.book.trees.length + lay.tree.getD i 0, lay.part.getD i 0)

/-- The guards of the taking over, on the shape. given: the number of trees that are handed in. -/
def adoptG (a : CoreSh) (sent : Array OracleNotice) (given : Nat) : Bool :=
  sent.all (fun n => Own.sentShapeFits a.st.codes n.shape) &&
    sent.all (fun n => n.shape.answers != 0) &&
    a.st.oracles.length == a.book.place.length && Own.treesCan a.st.codes sent &&
    has (Own.treesMade a.st.codes sent) fun lay => lay.shapes.size == given

theorem adoptG_eq (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src)) :
    adoptG (shD d) sent given.size = ok (adoptL d.st d.book sent given) := by
  unfold adoptG ok adoptL
  show (_ && _ && (stSh d.st).oracles.length == (bookSh d.book).place.length && _ && _) = _
  rw [orc_size, place_size]
  simp [Bool.and_assoc]
  rfl

/-- **The taking over on shapes.** given: for each tree its number and where its root is taken from,
without the two values. -/
def adoptS (a : CoreSh) (sent : Array OracleNotice) (given : List (Nat × SrcSh)) :
    Option (Array Nat × CoreSh) :=
  if adoptG a sent given.length then
    (Own.treesMade a.st.codes sent).map fun lay =>
      ((Array.range sent.size).map (· + a.st.oracles.length),
        { st := { a.st with oracles := a.st.oracles ++ sent.toList.map freshOrc }
          book :=
            { trees := (List.range sent.size).foldl (fun t i =>
                modAt t (a.book.trees.length + lay.tree.getD i 0) fun x =>
                  { x with parts := x.parts ++ [a.st.oracles.length + i] })
                ((List.range given.length).foldl (fun t i =>
                  t ++ [⟨lay.shapes.getD i {}, (given.getD i (0, .own 0)).1,
                    (given.getD i (0, .own 0)).2, [], false, 0⟩]) a.book.trees)
              place := placesS a sent.size lay }
          roots := a.roots })
  else none

/-- What is handed in, without the two values. -/
def givenSh (given : Array (Nat × Fmt.Src)) : List (Nat × SrcSh) :=
  given.toList.map fun x => (x.1, srcSh x.2)

theorem givenSh_get (given : Array (Nat × Fmt.Src)) (i : Nat) :
    (givenSh given).getD i (0, .own 0) =
      ((given.getD i (0, .own 0)).1, srcSh (given.getD i (0, .own 0)).2) := by
  unfold givenSh
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases given[i]? <;> rfl

/-- The book behind a taking over, read. -/
theorem adopt_book (B : TreeBook) (n0 n : Nat) (lay : TreeLay) (given : Array (Nat × Fmt.Src)) :
    bookSh
      { trees := (List.range n).foldl (fun trees i =>
          trees.modify (B.trees.size + lay.tree.getD i 0) fun x =>
            { x with parts := x.parts.push (n0 + i) })
          ((List.range given.size).foldl (fun trees i =>
            trees.push { shape := lay.shapes.getD i {}, number := (given.getD i (0, .own 0)).1,
                         src := (given.getD i (0, .own 0)).2 }) B.trees)
        place := B.place ++ (Array.range n).map fun i =>
          (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0) } =
    { trees := (List.range n).foldl (fun t i =>
        modAt t ((bookSh B).trees.length + lay.tree.getD i 0) fun x =>
          { x with parts := x.parts ++ [n0 + i] })
        ((List.range (givenSh given).length).foldl (fun t i =>
          t ++ [⟨lay.shapes.getD i {}, ((givenSh given).getD i (0, .own 0)).1,
            ((givenSh given).getD i (0, .own 0)).2, [], false, 0⟩]) (bookSh B).trees)
      place := (bookSh B).place ++ (List.range n).map fun i =>
        ((bookSh B).trees.length + lay.tree.getD i 0, lay.part.getD i 0) } := by
  have hlen : (givenSh given).length = given.size := by
    unfold givenSh
    rw [List.length_map, Array.length_toList]
  rw [tree_size, hlen]
  simp only [givenSh_get]
  unfold bookSh
  dsimp only
  rw [place_sent, foldl_modify_sh treeSh (fun i => B.trees.size + lay.tree.getD i 0)
    (fun i x => { x with parts := x.parts.push (n0 + i) })
    (fun i x => { x with parts := x.parts ++ [n0 + i] })
    (fun i x => by
      show treeSh _ = _
      unfold treeSh
      simp only [Array.toList_push]),
    foldl_push_sh treeSh]
  rfl

theorem adopt_carries (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat) (h : adoptP d sent given = some (ids, d')) :
    adoptS (shD d) sent (givenSh given) = some (ids, shD d') := by
  have hlen : (givenSh given).length = given.size := by
    unfold givenSh
    rw [List.length_map, Array.length_toList]
  unfold adoptP at h
  split at h
  · rename_i hok
    obtain ⟨lay, hlay, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    unfold adoptS
    have hg : adoptG (shD d) sent (givenSh given).length = true := by
      rw [hlen]
      exact (adoptG_eq d sent given).trans hok
    rw [if_pos hg]
    show (Own.treesMade d.st.codes sent).map _ = _
    rw [hlay, Option.map_some]
    congr 1
    refine Prod.ext ?_ ?_
    · show (Array.range sent.size).map (· + (stSh d.st).oracles.length) = _
      rw [orc_size]
    · show CoreSh.mk _ _ _ = CoreSh.mk (stSh (stSent d.st sent)) (bookSh _) d.roots
      rw [stSh_eq (S := stSent d.st sent) rfl (sent_oracles d.st sent) rfl]
      congr 1
      show BookSh.mk _ (placesS (shD d) sent.size lay) = _
      unfold placesS
      have e3 : (shD d).st.oracles.length = d.st.oracles.size := orc_size d.st
      rw [e3]
      exact (adopt_book d.book d.st.oracles.size sent.size lay given).symm
  · cases h

theorem adopt_returns (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (y : Array Nat × CoreSh) (h : adoptS (shD d) sent (givenSh given) = some y) :
    ∃ x, adoptP d sent given = some x := by
  have hlen : (givenSh given).length = given.size := by
    unfold givenSh
    rw [List.length_map, Array.length_toList]
  unfold adoptS at h
  split at h
  · rename_i hg
    rw [hlen] at hg
    obtain ⟨lay, hlay, _⟩ := Option.map_eq_some_iff.1 h
    have hlay' : Own.treesMade d.st.codes sent = some lay := hlay
    unfold adoptP
    rw [if_pos ((adoptG_eq d sent given).symm.trans hg), hlay']
    exact ⟨_, rfl⟩
  · cases h

/-! ## 4 A message is sampled in another statement -/

/-- The guards of the copying, on the two shapes. -/
def elsewhereG (a : StSh) (mine : Nat) (b : StSh) (theirs : Nat) : Bool :=
  match a.oracles[mine]?, b.oracles[theirs]? with
  | some x, some y =>
    y.sampled && !x.sampled &&
      (x.shape.mainRows == y.shape.mainRows && x.shape.mainDeg == y.shape.mainDeg &&
        x.shape.maskRows == y.shape.maskRows && x.shape.answers == y.shape.answers) &&
      (x.shape.mainRows == 0 ||
        has a.codes.base[x.shape.code]? fun c => b.codes.base[y.shape.code]? == some c) &&
      (x.shape.maskRows == 0 ||
        has a.codes.mask[x.shape.maskCode]? fun z => b.codes.mask[y.shape.maskCode]? == some z)
  | _, _ => false

theorem elsewhereG_eq (S : Statement) (mine : Nat) (other : Statement) (theirs : Nat) :
    elsewhereG (stSh S) mine (stSh other) theirs = ok (elsewhereL S mine other theirs) := by
  unfold elsewhereG ok elsewhereL
  rw [orc_get, orc_get]
  cases S.oracles[mine]? <;> cases other.oracles[theirs]? <;>
    simp [has, stSh, orcSh, Bool.and_assoc]

/-- **The copying of a sample from another statement, on shapes.** b: the other statement's shape.
-/
def elsewhereS (a : CoreSh) (mine : Nat) (b : StSh) (theirs : Nat) : Option CoreSh :=
  if elsewhereG a.st mine b theirs then
    (b.oracles[theirs]?).map fun y => { a with st := { a.st with
      oracles := modAt a.st.oracles mine fun x =>
        { x with sampled := true, rows := y.rows, pad := y.pad } } }
  else none

theorem elsewhere_carries (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') :
    elsewhereS (shD d) mine (stSh other) theirs = some (shD d') := by
  unfold elsewhereP at h
  split at h
  · rename_i hok
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold elsewhereS
    have hg : elsewhereG (shD d).st mine (stSh other) theirs = true :=
      (elsewhereG_eq d.st mine other theirs).trans hok
    rw [if_pos hg, orc_get, hy, Option.map_some, Option.map_some]
    congr 1
    show _ = CoreSh.mk (stSh { d.st with oracles := d.st.oracles.modify mine fun x =>
      { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad } })
      (bookSh d.book) d.roots
    rw [stSh_eq (S := { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad } }) rfl
      (map_modify _ _ _ orcSh
        (fun x => { x with sampled := true, rows := (orcSh y).rows, pad := (orcSh y).pad })
        fun x => by
          show orcSh _ = _
          unfold orcSh
          simp only [Array.size_map]) rfl]
    rfl
  · cases h

theorem elsewhere_returns (d : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (y : CoreSh) (h : elsewhereS (shD d) mine (stSh other) theirs = some y) :
    ∃ d', elsewhereP d mine other theirs = some d' := by
  unfold elsewhereS at h
  split at h
  · rename_i hg
    obtain ⟨y', hy', _⟩ := Option.map_eq_some_iff.1 h
    rw [orc_get] at hy'
    obtain ⟨y0, hy0, _⟩ := Option.map_eq_some_iff.1 hy'
    unfold elsewhereP
    rw [if_pos ((elsewhereG_eq d.st mine other theirs).symm.trans hg), hy0]
    exact ⟨_, rfl⟩
  · cases h

/-! ## 5 A new group -/

/-- **A new group on shapes.** -/
def newGroupS (a : CoreSh) (code maskCode : Nat) : Option (Nat × CoreSh) :=
  if ok (groupL a.st.codes code maskCode) then
    some (a.st.groups.length, { a with st := { a.st with
      groups := a.st.groups ++ [⟨code, maskCode, [], [], [], false⟩] } })
  else none

theorem newGroup_carries (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) :
    newGroupS (shD d) code maskCode = some (n, shD d') := by
  unfold newGroupP at h
  split at h
  · rename_i hok
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    unfold newGroupS
    have hg : ok (groupL (shD d).st.codes code maskCode) = true := hok
    rw [if_pos hg]
    congr 1
    refine Prod.ext (grp_size d.st) ?_
    show _ = CoreSh.mk (stSh (Ground.withGroup d.st code maskCode)) (bookSh d.book) d.roots
    rw [stSh_eq (S := Ground.withGroup d.st code maskCode) rfl rfl
      (g := (stSh d.st).groups ++ [⟨code, maskCode, [], [], [], false⟩]) (by
        show (d.st.groups.push _).toList.map grpSh = _
        rw [Array.toList_push, List.map_append]
        rfl)]
    rfl
  · cases h

theorem newGroup_returns (d : DState L) (code maskCode : Nat) (y : Nat × CoreSh)
    (h : newGroupS (shD d) code maskCode = some y) : ∃ x, newGroupP d code maskCode = some x := by
  unfold newGroupS at h
  split at h
  · rename_i hg
    have hok : ok (newGroupL d.st code maskCode) = true := hg
    unfold newGroupP
    rw [if_pos hok]
    exact ⟨_, rfl⟩
  · cases h

/-! ## 6 Changes of one oracle message: a mask entry is taken; a ledger is shut; a mask is spent -/

/-- A change of one oracle message, seen through the reader. -/
theorem orc_change (d : DState L) (o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (fS : OrcSh → OrcSh) (hf : ∀ x, orcSh (f x) = fS (orcSh x)) :
    ({ shD d with st := { (shD d).st with oracles := modAt (shD d).st.oracles o fS } } : CoreSh) =
      CoreSh.mk (stSh { d.st with oracles := d.st.oracles.modify o f }) (bookSh d.book)
        d.roots := by
  rw [stSh_eq (S := { d.st with oracles := d.st.oracles.modify o f }) rfl
    (map_modify _ _ _ orcSh fS hf) rfl]
  rfl

/-- The guards of the taking of a mask entry, on the shape. -/
def takeMaskG (a : StSh) (o : Nat) : Bool :=
  match (a.oracles[o]?).bind (·.ledger) with
  | some l => !l.closed && decide (0 < l.left)
  | none => false

theorem takeMaskG_eq (S : Statement) (o : Nat) : takeMaskG (stSh S) o = ok (takeMaskL S o) := by
  unfold takeMaskG ok takeMaskL
  rw [orc_get]
  cases hx : S.oracles[o]? with
  | none => simp [has]
  | some x => cases hl : x.ledger <;> simp [has, orcSh, hl]

/-- **The taking of the next free mask entry, on shapes.** -/
def takeMaskS (a : CoreSh) (o : Nat) : Option (Nat × CoreSh) :=
  if takeMaskG a.st o then
    ((a.st.oracles[o]?).bind (·.ledger)).map fun l =>
      (Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next,
        { a with st := { a.st with oracles := modAt a.st.oracles o fun x => { x with
          ledger := some { l with
            next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1
            left := l.left - 1 } } } })
  else none

theorem ledger_get (S : Statement) (o : Nat) :
    ((stSh S).oracles[o]?).bind (·.ledger) = (S.oracles[o]?).bind (·.ledger) := by
  rw [orc_get]
  cases S.oracles[o]? <;> rfl

theorem takeMask_carries (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    takeMaskS (shD d) o = some (n, shD d') := by
  unfold takeMaskP at h
  split at h
  · rename_i hok
    obtain ⟨l, hl, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    unfold takeMaskS
    have hg : takeMaskG (shD d).st o = true := (takeMaskG_eq d.st o).trans hok
    rw [if_pos hg]
    show (((stSh d.st).oracles[o]?).bind (·.ledger)).map _ = _
    rw [ledger_get, hl, Option.map_some]
    congr 1
    refine Prod.ext rfl ?_
    exact orc_change d o _ _ fun _ => rfl
  · cases h

theorem takeMask_returns (d : DState L) (o : Nat) (y : Nat × CoreSh)
    (h : takeMaskS (shD d) o = some y) : ∃ x, takeMaskP d o = some x := by
  unfold takeMaskS at h
  split at h
  · rename_i hg
    obtain ⟨l, hl, _⟩ := Option.map_eq_some_iff.1 h
    have hl' : ((stSh d.st).oracles[o]?).bind (·.ledger) = some l := hl
    rw [ledger_get] at hl'
    unfold takeMaskP
    rw [if_pos ((takeMaskG_eq d.st o).symm.trans hg), hl']
    exact ⟨_, rfl⟩
  · cases h

/-- A ledger shut, on the shape. -/
def shutS (x : OrcSh) : OrcSh :=
  { x with ledger := x.ledger.map fun l => { l with closed := true } }

/-- **The shutting of a ledger, on shapes.** -/
def closeLedgerS (a : CoreSh) (o : Nat) : Option CoreSh :=
  if o < a.st.oracles.length then
    some { a with st := { a.st with oracles := modAt a.st.oracles o shutS } }
  else none

theorem closeLedger_carries (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d') :
    closeLedgerS (shD d) o = some (shD d') := by
  unfold closeLedgerP at h
  split at h
  · rename_i hok
    cases h
    have hlt : o < d.st.oracles.size := by
      simpa [ok, closeLedgerL] using hok
    unfold closeLedgerS
    have hg : o < (shD d).st.oracles.length := by
      show o < (stSh d.st).oracles.length
      rw [orc_size]
      exact hlt
    rw [if_pos hg]
    congr 1
    exact orc_change d o _ shutS fun _ => rfl
  · cases h

theorem closeLedger_returns (d : DState L) (o : Nat) (y : CoreSh)
    (h : closeLedgerS (shD d) o = some y) : ∃ d', closeLedgerP d o = some d' := by
  unfold closeLedgerS at h
  split at h
  · rename_i hg
    have hlt : o < (stSh d.st).oracles.length := hg
    rw [orc_size] at hlt
    unfold closeLedgerP
    rw [if_pos (by simpa [ok, closeLedgerL] using hlt)]
    exact ⟨_, rfl⟩
  · cases h

/-- The guards of the spending of a mask, on the shape. -/
def spendG (a : StSh) (o : Nat) : Bool :=
  (a.oracles[o]?).any fun x => !x.sampled && x.shape.answers == 0 && !x.spent

theorem spendG_eq (S : Statement) (o : Nat) : spendG (stSh S) o = ok (spendAsMaskL S o) := by
  unfold spendG ok spendAsMaskL
  rw [orc_get]
  cases S.oracles[o]? <;> simp [has, orcSh, Bool.and_assoc]

/-- **The spending of a message as a mask, on shapes.** -/
def spendS (a : CoreSh) (o : Nat) : Option CoreSh :=
  if spendG a.st o then
    some { a with st := { a.st with
      oracles := modAt a.st.oracles o fun x => { x with spent := true } } }
  else none

theorem spend_carries (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d') :
    spendS (shD d) o = some (shD d') := by
  unfold spendAsMaskP at h
  split at h
  · rename_i hok
    cases h
    unfold spendS
    have hg : spendG (shD d).st o = true := (spendG_eq d.st o).trans hok
    rw [if_pos hg]
    congr 1
    exact orc_change d o _ _ fun _ => rfl
  · cases h

theorem spend_returns (d : DState L) (o : Nat) (y : CoreSh) (h : spendS (shD d) o = some y) :
    ∃ d', spendAsMaskP d o = some d' := by
  unfold spendS at h
  split at h
  · rename_i hg
    unfold spendAsMaskP
    rw [if_pos ((spendG_eq d.st o).symm.trans hg)]
    exact ⟨_, rfl⟩
  · cases h

/-! ## 7 A sample's answers are in -/

/-- The guards of the admitting, on the shape. n: the number of rows handed in. -/
def admitG (a : StSh) (o n : Nat) : Bool :=
  (a.oracles[o]?).any fun x => (Own.padMade a.codes x.shape).isSome && !x.sampled &&
    n == x.shape.answers && decide (1 ≤ x.shape.answers)

theorem admitG_eq (S : Statement) (o : Nat) (rows : Array OnBytes.Row) :
    admitG (stSh S) o rows.size = ok (admitL S o rows) := by
  unfold admitG ok admitL
  rw [orc_get]
  cases S.oracles[o]? <;> simp [has, stSh, orcSh, Bool.and_assoc]

/-- **The admitting of a sample's rows, on shapes.** n: their number. -/
def admitS (a : CoreSh) (o n : Nat) : Option CoreSh :=
  if admitG a.st o n then
    (a.st.oracles[o]?).bind fun x => (Own.padMade a.st.codes x.shape).map fun places =>
      { a with st := { a.st with oracles := modAt a.st.oracles o fun y => { y with
          sampled := true, rows := n, pad := places.map fun p => (p.part, p.index)
          ledger := freshLedger a.st.codes x.shape } } }
  else none

theorem admit_carries (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') : admitS (shD d) o rows.size = some (shD d') := by
  unfold admitP at h
  split at h
  · rename_i hok
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, hpl, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    unfold admitS
    have hg : admitG (shD d).st o rows.size = true := (admitG_eq d.st o rows).trans hok
    rw [if_pos hg]
    show ((stSh d.st).oracles[o]?).bind _ = _
    rw [orc_get, hx, Option.map_some, Option.bind_some]
    show (Own.padMade d.st.codes x.shape).map _ = _
    rw [hpl, Option.map_some]
    congr 1
    show _ = CoreSh.mk (stSh (admitted d.st o x.shape places rows)) (bookSh d.book) d.roots
    rw [stSh_eq (S := admitted d.st o x.shape places rows) rfl
      (map_modify _ _ _ orcSh (fun y => { y with
          sampled := true, rows := rows.size, pad := places.map fun p => (p.part, p.index)
          ledger := freshLedger d.st.codes x.shape }) fun _ => rfl) rfl]
    rfl
  · cases h

theorem admit_returns (d : DState L) (o : Nat) (rows : Array OnBytes.Row) (y : CoreSh)
    (h : admitS (shD d) o rows.size = some y) : ∃ d', admitP d o rows = some d' := by
  unfold admitS at h
  split at h
  · rename_i hg
    obtain ⟨x', hx', h⟩ := Option.bind_eq_some_iff.1 h
    have hx'' : (stSh d.st).oracles[o]? = some x' := hx'
    rw [orc_get] at hx''
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hx''
    obtain ⟨places, hpl, _⟩ := Option.map_eq_some_iff.1 h
    have hpl' : Own.padMade d.st.codes x.shape = some places := hpl
    unfold admitP
    rw [if_pos ((admitG_eq d.st o rows).symm.trans hg), hx]
    refine ⟨{ d with st := admitted d.st o x.shape places rows }, ?_⟩
    show ((Own.padMade d.st.codes x.shape).bind fun places =>
      some { d with st := admitted d.st o x.shape places rows }) = _
    rw [hpl']
    rfl
  · cases h

/-! ## 8 The oracle messages of one prover's message -/

/-- The trees of a prover's message, laid behind those that the book has. -/
def treesSentS (first : Nat) : List TreeShape → Nat → List TreeSh → List TreeSh
  | [], _, trees => trees
  | s :: l, roots, trees =>
    treesSentS first l (roots + 1) (trees ++ [⟨s, first + roots, .own roots, [], false, 0⟩])

theorem treesSent_sh (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (A : Array Tree),
    (treesSent first l roots A).toList.map treeSh = treesSentS first l roots (A.toList.map treeSh)
  | [], _, _ => rfl
  | s :: l, roots, A => by
    show (treesSent first l (roots + 1) (A.push _)).toList.map treeSh = _
    rw [treesSent_sh first l, Array.toList_push, List.map_append]
    rfl

/-- The guards of the receiving, on the shape. -/
def recvG (a : CoreSh) (sent : Array OracleNotice) : Bool :=
  ok (sentL a.st.codes sent) && a.st.oracles.length == a.book.place.length

theorem recvG_eq (d : DState L) (sent : Array OracleNotice) :
    recvG (shD d) sent = ok (recvL d.st d.book sent) := by
  unfold recvG recvL ok
  show (_ && (stSh d.st).oracles.length == (bookSh d.book).place.length) = _
  rw [orc_size, place_size, List.all_append]
  simp
  rfl

/-- **The receiving on shapes.** first: the number of the chain's first tree. -/
def recvS (first : Nat) (a : CoreSh) (sent : Array OracleNotice) : Option (Array Nat × CoreSh) :=
  if recvG a sent then
    (Own.treesMade a.st.codes sent).map fun lay =>
      ((Array.range sent.size).map (· + a.st.oracles.length),
        { st := { a.st with oracles := a.st.oracles ++ sent.toList.map freshOrc }
          book :=
            { trees := (List.range sent.size).foldl (fun t i =>
                modAt t (a.book.trees.length + lay.tree.getD i 0) fun x => { x with
                  parts := x.parts ++ [a.st.oracles.length + i]
                  oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
                (treesSentS first lay.shapes.toList a.roots a.book.trees)
              place := placesS a sent.size lay }
          roots := a.roots + lay.shapes.size })
  else none

/-- The book behind a receiving, read. -/
theorem recv_book (first : Nat) (B : TreeBook) (n0 roots : Nat) (sent : Array OracleNotice)
    (lay : TreeLay) :
    bookSh
      { trees := partsLaid sent lay n0 B.trees.size
          (treesSent first lay.shapes.toList roots B.trees)
        place := B.place ++ (Array.range sent.size).map fun i =>
          (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0) } =
    { trees := (List.range sent.size).foldl (fun t i =>
        modAt t ((bookSh B).trees.length + lay.tree.getD i 0) fun x => { x with
          parts := x.parts ++ [n0 + i]
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
        (treesSentS first lay.shapes.toList roots (bookSh B).trees)
      place := (bookSh B).place ++ (List.range sent.size).map fun i =>
        ((bookSh B).trees.length + lay.tree.getD i 0, lay.part.getD i 0) } := by
  rw [tree_size]
  unfold bookSh partsLaid
  dsimp only
  rw [place_sent, foldl_modify_sh treeSh (fun i => B.trees.size + lay.tree.getD i 0)
    (fun i x => { x with
      parts := x.parts.push (n0 + i)
      oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
    (fun i x => { x with
      parts := x.parts ++ [n0 + i]
      oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
    (fun i x => by
      show treeSh _ = _
      unfold treeSh
      simp only [Array.toList_push]),
    treesSent_sh]

theorem recv_carries (first : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP first d sent = some (ids, d')) :
    recvS first (shD d) sent = some (ids, shD d') := by
  unfold recvP at h
  split at h
  · rename_i hok
    obtain ⟨lay, hlay, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    unfold recvS
    rw [if_pos ((recvG_eq d sent).trans hok)]
    show (Own.treesMade d.st.codes sent).map _ = _
    rw [hlay, Option.map_some]
    congr 1
    refine Prod.ext ?_ ?_
    · show (Array.range sent.size).map (· + (stSh d.st).oracles.length) = _
      rw [orc_size]
    · show CoreSh.mk _ _ _ = CoreSh.mk (stSh (stSent d.st sent)) (bookSh _)
        (d.roots + lay.shapes.size)
      rw [stSh_eq (S := stSent d.st sent) rfl (sent_oracles d.st sent) rfl]
      congr 1
      show BookSh.mk _ (placesS (shD d) sent.size lay) = _
      unfold placesS
      have e3 : (shD d).st.oracles.length = d.st.oracles.size := orc_size d.st
      rw [e3]
      exact (recv_book first d.book d.st.oracles.size d.roots sent lay).symm
  · cases h

theorem recv_returns (first : Nat) (d : DState L) (sent : Array OracleNotice)
    (y : Array Nat × CoreSh) (h : recvS first (shD d) sent = some y) :
    ∃ x, recvP first d sent = some x := by
  unfold recvS at h
  split at h
  · rename_i hg
    obtain ⟨lay, hlay, _⟩ := Option.map_eq_some_iff.1 h
    have hlay' : Own.treesMade d.st.codes sent = some lay := hlay
    unfold recvP
    rw [if_pos ((recvG_eq d sent).symm.trans hg), hlay']
    exact ⟨_, rfl⟩
  · cases h

/-! ## 9 A proximity test begins -/

theorem getD_toList {α : Type} (a : Array α) (i : Nat) (x : α) :
    a.toList.getD i x = a.getD i x := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- For each member: the bits that index its rows in the table, if it has a block there. -/
def blockBitsS (a : StSh) (G : GrpSh) (part : Part) : Array (Option Nat) :=
  (Array.range G.members.length).map fun i =>
    if (a.oracles[G.members.getD i noId]?).any (fun x => decide (0 < x.shape.rows part)) &&
        !(part == .main && G.kept.getD i false) then
      some (match a.oracles[G.members.getD i noId]? with
        | some x => ceilLog2 (x.shape.rows part)
        | none => 0)
    else none

theorem blockBitsS_eq (S : Statement) (G : Group) (part : Part) :
    blockBitsS (stSh S) (grpSh G) part = Own.blockBits S G part := by
  unfold blockBitsS Own.blockBits Own.tableThere Statement.rowBits
  show (Array.range G.members.toList.length).map _ = _
  rw [Array.length_toList]
  congr 1
  funext i
  have e1 : (grpSh G).members.getD i noId = G.members.getD i noId := getD_toList _ _ _
  have e2 : (grpSh G).kept.getD i false = G.kept.getD i false := getD_toList _ _ _
  dsimp only
  rw [e1, e2, orc_get]
  cases S.oracles[G.members.getD i noId]? <;> rfl

/-- **The layout of a group, off the shape.** -/
def layoutS (a : StSh) (G : GrpSh) : GroupLayout :=
  let mask := layBlocks (blockBitsS a G .mask)
  let main := layBlocks (blockBitsS a G .main)
  let h := ceilLog2 mask.2
  { k := max (max (ceilLog2 main.2) h) 1, h := h,
    logEll := (a.codes.base.getD G.code default).logEll,
    logEllZk := (a.codes.mask.getD G.maskCode default).logEll,
    members := G.members.toArray, kept := G.kept.toArray, mainFirst := main.1, maskFirst := mask.1 }

theorem layoutS_eq (S : Statement) (G : Group) :
    layoutS (stSh S) (grpSh G) = Own.layoutOf S G := by
  unfold layoutS Own.layoutOf
  rw [blockBitsS_eq, blockBitsS_eq]
  rfl

/-- The number of rows that a proximity test takes in. -/
def runCountS (a : StSh) (G : GrpSh) : Nat :=
  (G.kinds.filter (· == .plain)).length +
    (G.members.map fun o => ((a.oracles[o]?).map (·.rows)).getD 0).sum +
    (G.kinds.filter (· == .generator)).length

theorem size_kind (rows : Array OnBytes.Row) (k : RowKind) :
    (rows.filter (·.kind == k)).size = ((rows.toList.map (·.kind)).filter (· == k)).length := by
  rw [← Array.length_toList, Array.toList_filter, List.filter_map, List.length_map]
  rfl

theorem size_samples (S : Statement) : ∀ (l : List Nat) (A : Array OnBytes.Row),
    (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) A).size =
      A.size + (l.map fun o => (((stSh S).oracles[o]?).map (·.rows)).getD 0).sum
  | [], _ => rfl
  | o :: l, A => by
    rw [List.foldl_cons, size_samples S l, Array.size_append, List.map_cons, List.sum_cons,
      orc_get, Nat.add_assoc]
    cases S.oracles[o]? <;> rfl

theorem runCountS_eq (S : Statement) (G : Group) :
    runCountS (stSh S) (grpSh G) = (runRows S G).size := by
  unfold runCountS runRows
  rw [Array.size_append, Array.size_append, size_kind, size_kind, ← Array.foldl_toList,
    size_samples]
  show _ = _ + (0 + _) + _
  rw [Nat.zero_add]
  rfl

/-- The guards of the beginning, on the shape. -/
def beginRunG (a : StSh) (g : Nat) : Bool :=
  (a.groups[g]?).any fun G => !G.inRun && !G.members.isEmpty &&
    G.members.all fun o => decide (o < a.oracles.length)

theorem beginRunG_eq (S : Statement) (g : Nat) : beginRunG (stSh S) g = ok (beginRunL S g) := by
  unfold beginRunG ok beginRunL
  rw [grp_get, orc_size]
  cases S.groups[g]? <;> simp [has, grpSh, Bool.and_assoc]

/-- The statement's shape behind the beginning. -/
def begunS (a : StSh) (g : Nat) (G : GrpSh) : StSh :=
  { a with
    oracles := G.members.foldl (fun os o => modAt os o shutS) a.oracles
    groups := modAt a.groups g fun G => { G with inRun := true, kinds := [] } }

/-- **The beginning of a proximity test, on shapes.** It returns the layout and the number of rows.
-/
def beginRunS (a : CoreSh) (g : Nat) : Option ((GroupLayout × Nat) × CoreSh) :=
  if beginRunG a.st g then
    (a.st.groups[g]?).map fun G =>
      ((layoutS a.st G, runCountS a.st G), { a with st := begunS a.st g G })
  else none

theorem closeLedgers_sh : ∀ (l : List Nat) (S : Statement),
    (closeLedgers S l).oracles.toList.map orcSh =
      l.foldl (fun os o => modAt os o shutS) (S.oracles.toList.map orcSh)
  | [], _ => rfl
  | o :: l, S => by
    show (closeLedgers _ l).oracles.toList.map orcSh = _
    rw [closeLedgers_sh l, List.foldl_cons]
    congr 1
    exact map_modify _ _ _ orcSh shutS fun _ => rfl

theorem beginRun_carries (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) :
    beginRunS (shD d) g = some ((run.layout, run.rows.size), shD d') := by
  unfold beginRunP at h
  split at h
  · rename_i hok
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    unfold beginRunS
    have hg : beginRunG (shD d).st g = true := (beginRunG_eq d.st g).trans hok
    rw [if_pos hg]
    show ((stSh d.st).groups[g]?).map _ = _
    rw [grp_get, hG, Option.map_some, Option.map_some]
    congr 1
    refine Prod.ext (Prod.ext (layoutS_eq d.st G) (runCountS_eq d.st G)) ?_
    show _ = CoreSh.mk (stSh (begun d.st g G)) (bookSh d.book) d.roots
    rw [stSh_eq (S := begun d.st g G) (closeLedgers_codes _ _) (closeLedgers_sh _ _)
      (g := modAt (stSh d.st).groups g fun G => { G with inRun := true, kinds := [] }) (by
        show ((closeLedgers d.st G.members.toList).groups.modify g _).toList.map grpSh = _
        rw [ProxRun.closeLedgers_groups]
        exact map_modify _ _ _ grpSh _ fun _ => rfl)]
    rfl
  · cases h

theorem beginRun_returns (d : DState L) (g : Nat) (y : (GroupLayout × Nat) × CoreSh)
    (h : beginRunS (shD d) g = some y) : ∃ x, beginRunP d g = some x := by
  unfold beginRunS at h
  split at h
  · rename_i hg
    obtain ⟨G', hG', _⟩ := Option.map_eq_some_iff.1 h
    have hG'' : (stSh d.st).groups[g]? = some G' := hG'
    rw [grp_get] at hG''
    obtain ⟨G, hG, _⟩ := Option.map_eq_some_iff.1 hG''
    unfold beginRunP
    rw [if_pos ((beginRunG_eq d.st g).symm.trans hg), hG]
    exact ⟨_, rfl⟩
  · cases h

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.stSh_eq
#print axioms VerifiableInference.Desc.Ground.Sh.insAt_toList
#print axioms VerifiableInference.Desc.Ground.Sh.joinG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.join_carries
#print axioms VerifiableInference.Desc.Ground.Sh.join_returns
#print axioms VerifiableInference.Desc.Ground.Sh.addRowG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_carries
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_returns
#print axioms VerifiableInference.Desc.Ground.Sh.foldl_push_sh
#print axioms VerifiableInference.Desc.Ground.Sh.foldl_modify_sh
#print axioms VerifiableInference.Desc.Ground.Sh.sent_oracles
#print axioms VerifiableInference.Desc.Ground.Sh.place_sent
#print axioms VerifiableInference.Desc.Ground.Sh.adoptG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.givenSh_get
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_book
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_carries
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_returns
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhereG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_carries
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_returns
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_carries
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_returns
#print axioms VerifiableInference.Desc.Ground.Sh.orc_change
#print axioms VerifiableInference.Desc.Ground.Sh.takeMaskG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.ledger_get
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_carries
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_returns
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_carries
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_returns
#print axioms VerifiableInference.Desc.Ground.Sh.spendG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.spend_carries
#print axioms VerifiableInference.Desc.Ground.Sh.spend_returns
#print axioms VerifiableInference.Desc.Ground.Sh.admitG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.admit_carries
#print axioms VerifiableInference.Desc.Ground.Sh.admit_returns
#print axioms VerifiableInference.Desc.Ground.Sh.treesSent_sh
#print axioms VerifiableInference.Desc.Ground.Sh.recvG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.recv_book
#print axioms VerifiableInference.Desc.Ground.Sh.recv_carries
#print axioms VerifiableInference.Desc.Ground.Sh.recv_returns
#print axioms VerifiableInference.Desc.Ground.Sh.getD_toList
#print axioms VerifiableInference.Desc.Ground.Sh.blockBitsS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.layoutS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.size_kind
#print axioms VerifiableInference.Desc.Ground.Sh.size_samples
#print axioms VerifiableInference.Desc.Ground.Sh.runCountS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.beginRunG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedgers_sh
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_carries
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_returns
