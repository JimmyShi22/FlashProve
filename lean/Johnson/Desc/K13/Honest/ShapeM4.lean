-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ShapeM4.lean: kind K13's sub-protocol behind W's commitment (`rowsB`,
Johnson/Desc/K13/Kind.lean): a shape of the verifier's state, and the shape's own update there.
Definitions with code, and statements with their proofs. No shape for all kinds is defined here.

The shape is a projection of the first chain's state onto flags, counts, lengths, numbers of oracle
messages and of groups, places of tables, shapes of oracle messages and codes: no element of a
field, by type. Johnson/Desc/K13/Honest/Shape.lean has the like for the members' batching; its shape
holds what that sub-protocol reads (the pile's rows' shapes, the ledgers). This one holds all that
`rowsB` reads but field elements: the numbers handed on, what is laid for the last chain, the
claim's shape, the messages' marks `sampled`, lists of groups and pads, and the groups. (Of field
elements `rowsB` reads the claim's point and its masks' coefficients, in one test:
Johnson/Desc/K13/Honest/ShapeM4Ready.lean.) It also holds what `rowsB` writes and no test of this
chain reads: a group's `kept` and number of rows; the split's and the first fold's mask's numbers.
Both shapes hold the codes and the messages' shapes; Johnson/Desc/K13/Honest/ShapeSim.lean has a
shape of what stands at the chain's end (`EndSh`), which holds the numbers handed on, the four
numbers laid and the claim's row's shape, as `Sh4` does. Johnson/Desc/K13/Honest/ShapeTie.lean ties
the two at what is laid, where the claim is made of a row; no lemma ties the other fields.
The types and the projections onto them lie in ShapeDefs.lean of this folder, which imports the
library alone; the update and the laws lie here.
Main names:
  `GrpSh`, `Msg4`, `StSh`, `stSh` (ShapeDefs.lean): a group's, a message's and the statement's
    shape.
  `ClaimSh`, `LaidSh`, `Sh4`, `sh4` (ShapeDefs.lean): the claim's shape (how many coordinates its
    point has; the places of its masks: message, table, index; no coefficient, no coordinate, no
    target, no weight); what is laid for the last chain; the state's shape.
  `StSh.push`, `StSh.join`, `StSh.row`, `joinsSh`: one more group; a message joins a group; one more
    row in a group; joinings in a row: on the shape.
  `stSh_withGroup`, `stSh_joined`, `stSh_withRow`: these are what the library's three functions on
    the statement do to its shape.
  `step4`: **the update**: a function with code of the plan's shape and the state's shape; it reads
    no round.
  `shape_step4`: **wherever the decision of `rowsB` accepts, from s to s', the shape of s' is the
    update of the shape of s.**

What is not claimed. When the decision accepts. Nothing on W's commitment, which stands in front of
`rowsB` in one joined sub-protocol, at one place (`atM4`, Johnson/Desc/K13/AtS.lean). IN THE PROOF
FILE's IOP THE SUB-PROTOCOL DOES NOT STAND BARE: every lot's sub-protocol is laid behind a guard
that rejects where the state behind bears a mark of failure (`guardMark`,
Johnson/Desc/ProofFile/Frames1.lean) and behind a guard on the reply (`sameReply`). `Sh4` has no
field for the mark, and no law here says that the mark behind is the mark in front: so for the
guarded sub-protocol this shape lacks one flag. That the shape at a state of a run hangs on no sent
value and on no coin: the type shuts out field elements; that a number is not made of one along a
run is a statement on every sub-protocol in front. "Accepts" is `Block.decide`'s answer `.ok` and no
more. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeDefs
import Johnson.Desc.K13.Honest.OwnLaid
import Johnson.Desc.K13.Law.M4Proof
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-! ## The shape -/

theorem msgs_at (St : Statement) (o : ℕ) : (stSh St).msgs[o]? = (St.oracles[o]?).map msg4 :=
  Array.getElem?_map ..

theorem grps_at (St : Statement) (g : ℕ) : (stSh St).groups[g]? = (St.groups[g]?).map grpSh :=
  Array.getElem?_map ..

/-! ## The three functions on the statement, on the shape -/

/-- One more group, which has no member and no row. -/
def StSh.push (h : StSh) (c z : Nat) : StSh :=
  { h with groups := h.groups.push ⟨c, z, #[], #[], 0, false⟩ }

/-- The message o joins the group g. -/
def StSh.join (h : StSh) (g o : Nat) (k : Bool) : StSh :=
  let pos := ((((h.groups[g]?).map (·.members)).getD #[]).filter (· < o)).size
  { h with
    groups := h.groups.modify g fun G => { G with
      members := G.members.insertIdxIfInBounds pos o
      kept := G.kept.insertIdxIfInBounds pos k }
    msgs := h.msgs.modify o fun x => { x with groups := x.groups ++ [g] } }

/-- One more row in the group g. -/
def StSh.row (h : StSh) (g : Nat) : StSh :=
  { h with groups := h.groups.modify g fun G => { G with rows := G.rows + 1 } }

/-- Joinings in a row. -/
def joinsSh (g : Nat) : List Nat → StSh → StSh
  | [], h => h
  | o :: l, h => joinsSh g l (h.join g o false)

/-- A map goes through `Array.modify`. -/
theorem map_modify_comm {α β : Type} (f : α → β) (a : Array α) (i : Nat) (u : α → α) (v : β → β)
    (h : ∀ x, f (u x) = v (f x)) : (a.modify i u).map f = (a.map f).modify i v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_map]
  split
  · rw [Option.map_map, Option.map_map]
    exact congrArg (fun q => Option.map q a[j]?) (funext h)
  · rfl

theorem stSh_withGroup (St : Statement) (c z : Nat) :
    stSh (Ground.withGroup St c z) = (stSh St).push c z := by
  simp [stSh, Ground.withGroup, StSh.push, grpSh]

theorem stSh_joined (St : Statement) (g o : Nat) (k : Bool) (G : Group)
    (hG : St.groups[g]? = some G) : stSh (withMessageInGroup St g o k G) = (stSh St).join g o k := by
  have hpos : ((((stSh St).groups[g]?).map (·.members)).getD #[]) = G.members := by
    show (((St.groups.map grpSh)[g]?).map (·.members)).getD #[] = _
    rw [Array.getElem?_map, hG]
    rfl
  have e1 := map_modify_comm msg4 St.oracles o (fun x => { x with groups := x.groups ++ [g] })
    (fun x => { x with groups := x.groups ++ [g] }) (fun _ => rfl)
  have e2 := map_modify_comm grpSh St.groups g
    (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k })
    (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k }) (fun _ => rfl)
  unfold StSh.join
  rw [hpos]
  unfold stSh withMessageInGroup
  dsimp only
  rw [e1, e2]

theorem stSh_withRow (St : Statement) (g : Nat) (r : OnBytes.Row) :
    stSh (withRow St g r) = (stSh St).row g := by
  have e := map_modify_comm grpSh St.groups g (fun G' => { G' with rows := G'.rows.push r })
    (fun G' => { G' with rows := G'.rows + 1 }) (fun G' => by simp [grpSh])
  unfold StSh.row stSh withRow
  dsimp only
  rw [e]

/-- One joining that returns, on the shape. -/
theorem join_sh {d d' : St} {g o : ℕ} {k : Bool} (h : Ground.joinP d g o k = some d') :
    stSh d'.st = (stSh d.st).join g o k := by
  obtain ⟨G, hG, _, e⟩ := joinP_inv h
  rw [e]
  exact stSh_joined d.st g o k G hG

/-- Joinings in a row that return, on the shape. -/
theorem joinAll_sh {g : ℕ} : ∀ (l : List ℕ) (d d' : St), K13.joinAll g l d = .ok d' →
    stSh d'.st = joinsSh g l (stSh d.st)
  | [], d, d', hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    rfl
  | o :: l, d, d', hj => by
    simp only [K13.joinAll, Law.bind_ok, Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    rw [joinAll_sh l d₁ d' h2, join_sh h1]
    rfl

/-! ## The update -/

/-- What the lens hands on of the count that is owed: nothing where none waits. -/
def owedSh : Option Nat → Option Nat
  | none => none
  | some r => if r == 0 then none else some r

/-- **The update**: the own group is made; the messages of the claim's masks, W and, where the plan
asks for a split, the split's message join it; one row is added; four numbers are laid beside the
claim, which stays. -/
def step4 (Sh : LinShape) (h : Sh4) : Sh4 :=
  match h.laid with
  | none => h
  | some l =>
    let w := (h.ids[0]?).getD noId
    let g := h.st.groups.size
    let a := (joinsSh g (listOfT (l.claim.slots.map (·.1)))
      (h.st.push Sh.w.code Sh.ownMaskCode)).join g w false
    let split := if Sh.ownSplitNeeded then (h.ids[1]?).getD noId else noId
    let b := if Sh.ownSplitNeeded then a.join g split false else a
    { h with
      laid := some ⟨w, split, g, if Sh.masksAhead then h.ids.back? else none, l.claim⟩
      owed := owedSh h.owed
      st := b.row g }

/-- The text behind W's commitment, on the shape. -/
theorem rows_sh {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St} {o : LinFirst × St}
    (h : rows Sh claim ids d = .ok o) :
    laidSh o.1 = ⟨(ids[0]?).getD noId, if Sh.ownSplitNeeded then (ids[1]?).getD noId else noId,
        (stSh d.st).groups.size, if Sh.masksAhead then ids.back? else none, claimSh4 claim⟩ ∧
      stSh o.2.st =
        (if Sh.ownSplitNeeded then
          ((joinsSh (stSh d.st).groups.size (listOfT ((claimSh4 claim).slots.map (·.1)))
            ((stSh d.st).push Sh.w.code Sh.ownMaskCode)).join (stSh d.st).groups.size
              ((ids[0]?).getD noId) false).join (stSh d.st).groups.size
                (if Sh.ownSplitNeeded then (ids[1]?).getD noId else noId) false
        else
          (joinsSh (stSh d.st).groups.size (listOfT ((claimSh4 claim).slots.map (·.1)))
            ((stSh d.st).push Sh.w.code Sh.ownMaskCode)).join (stSh d.st).groups.size
              ((ids[0]?).getD noId) false).row (stSh d.st).groups.size := by
  simp only [rows_is, Law.bind_ok, Law.there_ok, Law.pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, hsp, d₃, h3, mask, hmask, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := newGroupP_inv hb
  obtain ⟨_, _, _, e4⟩ := addRows_one h4
  have hsz : (stSh d.st).groups.size = d.st.groups.size := Array.size_map ..
  have hslots : (claimSh4 claim).slots.map (·.1) = claim.masks.toList.map (·.oracle) := by
    show (claim.masks.toList.map fun u => (u.oracle, u.part, u.index)).map (·.1) = _
    rw [List.map_map]
    rfl
  have s1 : stSh d₁.st = joinsSh b.1 (listOfT (claim.masks.toList.map (·.oracle)))
      ((stSh d.st).push Sh.w.code Sh.ownMaskCode) := by
    rw [joinAll_sh _ _ _ h1, e2, stSh_withGroup]
  have s2 : stSh d₂.st = (stSh d₁.st).join b.1 w false := join_sh h2
  have hw' : (ids[0]?).getD noId = w := by rw [hw]; rfl
  have hm : mask = if Sh.masksAhead then ids.back? else none := by
    by_cases ha : Sh.masksAhead = true
    · rw [if_pos ha] at hmask ⊢
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hmask
      exact hv.symm
    · rw [if_neg ha] at hmask ⊢
      exact (Option.some.inj hmask).symm
  rw [hsz, hslots, hw', ← e1]
  by_cases hs : Sh.ownSplitNeeded = true
  · rw [if_pos hs] at hsp h3
    have hsp' : (ids[1]?).getD noId = split := by rw [hsp]; rfl
    simp only [if_pos hs, hsp']
    refine ⟨by rw [← hm]; rfl, ?_⟩
    show stSh d₄.st = _
    rw [e4, stSh_withRow, join_sh h3, s2, s1]
  · rw [if_neg hs] at hsp h3
    obtain rfl := Option.some.inj hsp
    obtain rfl := Option.some.inj h3
    simp only [if_neg hs]
    refine ⟨by rw [← hm]; rfl, ?_⟩
    show stSh d₄.st = _
    rw [e4, stSh_withRow, s2, s1]

variable {Cl : Type}

/-- **Wherever the decision of `rowsB` accepts, the shape behind is the update of the shape in
front.** -/
theorem shape_step4 {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') : sh4 s' = step4 P.lin (sh4 s) := by
  obtain ⟨p, l, o, hp, hl, hrows, rfl⟩ := rowsB_ok atS P h
  cases hs : s.here with
  | mem a =>
    simp only [atS, hs] at hp
    obtain rfl := Option.some.inj hp
    have hl' : a.lin = some l := hl
    obtain ⟨e1, e2⟩ := rows_sh hrows
    have hfront : sh4 s = ⟨true, a.ids, some (laidSh l), s.rowsOwed, stSh s.st⟩ := by
      unfold sh4
      rw [hs]
      show Sh4.mk true a.ids (a.lin.map laidSh) s.rowsOwed (stSh s.st) = _
      rw [hl']
      rfl
    have howed : (if s.noneWaits = true then none else s.rowsOwed) = owedSh s.rowsOwed := by
      unfold S.noneWaits owedSh
      cases s.rowsOwed with
      | none => rfl
      | some r => rfl
    rw [hfront]
    unfold sh4
    simp only [atS, hs]
    show Sh4.mk true a.ids (some (laidSh o.1)) (if s.noneWaits = true then none else s.rowsOwed)
      (stSh o.2.st) = _
    rw [e1, e2, howed]
    unfold step4
    by_cases hn : P.lin.ownSplitNeeded = true
    · simp only [if_pos hn]
      rfl
    · simp only [if_neg hn]
      rfl
  | between => simp [atS, hs] at hp
  | lay a => simp [atS, hs] at hp
  | att a => simp [atS, hs] at hp
  | head a => simp [atS, hs] at hp
  | fin a => simp [atS, hs] at hp

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.msgs_at
#print axioms VerifiableInference.Desc.K13.Honest.grps_at
#print axioms VerifiableInference.Desc.K13.Honest.map_modify_comm
#print axioms VerifiableInference.Desc.K13.Honest.stSh_withGroup
#print axioms VerifiableInference.Desc.K13.Honest.stSh_joined
#print axioms VerifiableInference.Desc.K13.Honest.stSh_withRow
#print axioms VerifiableInference.Desc.K13.Honest.join_sh
#print axioms VerifiableInference.Desc.K13.Honest.joinAll_sh
#print axioms VerifiableInference.Desc.K13.Honest.rows_sh
#print axioms VerifiableInference.Desc.K13.Honest.shape_step4
