-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadNew.lean: THE FORM's HALF AT A SWITCH: WHAT RIDES FOR THE READING (ReadSeat,
Johnson/Prover/Link/ReadSeat.lean) HOLDS AT THE TREE THAT A SWITCH SENDS, behind the joining of the
switch's message to its group, whatever the switch takes; and it rides from there to the front of
the next fold. The new tree is a term (newTree): its two parts are the switch's message g and its
rider g + 1; it has been opened at no list.

Main names (namespace Johnson.Prover.Link).
  size_sentOf, sentOf_zero, sentOf_one   the sending's two notices: the target's, then the rider's.
  newTree, bookSentP_new, bookSentP_place   the tree that a switch sends, written out; the new
    messages' places.
  key_joined_at, key_ledgerShut, key_admitted   what each turn behind the sending makes of what
    the guard G9 reads.
  key_stJ_g, key_stJ_rider, size_stJ   the two new messages behind the joining: g counts its
    target's answers and is in the one group; the rider is in none.
  sharesOk_two   the guard G9 at a tree of two parts.
  readSeat_new   ReadSeat AT THE NEW TREE behind the joining.
  readSeat_behind   THE WHOLE RIDE: behind the claims, the beginning of the test and the reading of
    the old tree.

Asked: one rider · the sending's lay has one tree, with part i at place i (the premises of
seatP_of_sent, Johnson/Desc/K12/Law/SwTies.lean) · statement and book in step in front of the switch
· the target counts an answer · the rider counts none.

By: treesSent_at, partsLaid_one (Johnson/Prover/Link/BookLaid.lean) · stSent_new, joined_other
(OnBytes/Slice/BlkStLaws.lean) · closeLedgers_size (OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean) ·
ReadSeat.withRows, .begun, .bookRead (Johnson/Prover/Link/ReadRide.lean).

Limits. The five things asked are premises. Nothing on the tree's shape beyond the letter sh. "mask"
is the library's name: nothing is said of what a mask does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadRide
import Johnson.Prover.Link.BookLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc
open H2K.Sw (Taken bookSentP)

/-- The tree that a switch sends: the switch's message g and its rider are its two parts; opened at
no list. -/
def newTree (ft roots : Nat) (sh : TreeShape) (g : Nat) : Tree :=
  { shape := sh, number := ft + roots, src := .own roots, parts := #[g, g + 1], oneList := true
    lists := 0 }

theorem size_sentOf (T : SwitchTarget) (others : Array OracleNotice) (h1 : others.size = 1) :
    (Slice.sentOf T others).size = 2 := by
  unfold Slice.sentOf
  rw [Array.size_append, h1]
  rfl

theorem sentOf_one (T : SwitchTarget) (others : Array OracleNotice) (h1 : others.size = 1) :
    (Slice.sentOf T others).getD 1 default = others.getD 0 default := by
  unfold Slice.sentOf
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append, h1]

theorem sentOf_zero (T : SwitchTarget) (others : Array OracleNotice)
    (h : 0 < (Slice.sentOf T others).size) : (Slice.sentOf T others)[0].shape = T.shape := by
  simp [Slice.sentOf]

/-- **The new tree, written out.** -/
theorem bookSentP_new (ft roots : Nat) (S : Statement) (Bk : TreeBook) (T : SwitchTarget)
    (others : Array OracleNotice) (lay : TreeLay) (sh : TreeShape) (h1 : others.size = 1)
    (hs : lay.shapes = #[sh]) (ht : ∀ i, i < 2 → lay.tree.getD i 0 = 0)
    (hr : (others.getD 0 default).shape.answers = 0) :
    (bookSentP ft roots S Bk (Slice.sentOf T others) lay).trees[Bk.trees.size]? =
      some (newTree ft roots sh S.oracles.size) := by
  have hx : (treesSent ft lay.shapes.toList roots Bk.trees)[Bk.trees.size]? =
      some { shape := sh, number := ft + roots, src := .own roots } := by
    have h := treesSent_at ft lay.shapes.toList roots Bk.trees 0
    rw [hs] at h ⊢
    exact h
  show (partsLaid (Slice.sentOf T others) lay S.oracles.size Bk.trees.size
    (treesSent ft lay.shapes.toList roots Bk.trees))[Bk.trees.size]? = _
  rw [partsLaid_one _ lay _ _ _ _ (by rw [size_sentOf T others h1]; exact ht) hx,
    size_sentOf T others h1]
  have e : ((List.range 2).any fun i =>
      ((Slice.sentOf T others).getD i default).shape.answers == 0) = true := by
    refine List.any_eq_true.2 ⟨1, by simp, ?_⟩
    rw [sentOf_one T others h1, hr]
    rfl
  simp only [e, Bool.or_true]
  rfl

/-! ## The keys of the two new messages -/

/-- A joining lays the group behind the message's groups. -/
theorem key_joined_at (S : Statement) (gp g : Nat) (k : Bool) (G : Group) :
    ((withMessageInGroup S gp g k G).oracles[g]?).map shareKey =
      (S.oracles[g]?).map fun x => (x.shape.answers, x.groups ++ [gp]) := by
  show ((S.oracles.modify g _)[g]?).map shareKey = _
  rw [Array.getElem?_modify, if_pos rfl]
  cases S.oracles[g]? <;> rfl

theorem key_ledgerShut (S : Statement) (T : SwitchTarget) (g o : Nat) :
    ((ledgerShut S T g).oracles[o]?).map shareKey = (S.oracles[o]?).map shareKey := by
  unfold ledgerShut
  split
  · exact key_closeLedgers [g] S o
  · rfl

theorem key_admitted (S : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) (o' : Nat) :
    ((admitted S o s p rows).oracles[o']?).map shareKey = (S.oracles[o']?).map shareKey := by
  show ((S.oracles.modify o _)[o']?).map shareKey = _
  refine key_modify _ _ _ ?_ _
  intro _
  rfl

variable (D : Taken) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice) (S : Statement)

/-- The switch's message behind its joining: its target's count of answers; in the one group. -/
theorem key_stJ_g (h1 : others.size = 1) :
    ((D.stJ T gp others S).oracles[S.oracles.size]?).map shareKey =
      some (T.shape.answers, [gp]) := by
  unfold Taken.stJ
  rw [key_joined_at]
  have e : ((ledgerShut (D.stA T others S) T S.oracles.size).oracles[S.oracles.size]?).map
      shareKey = some (T.shape.answers, []) := by
    rw [key_ledgerShut]
    unfold Taken.stA
    rw [key_admitted]
    have h0 : 0 < (Slice.sentOf T others).size := by rw [size_sentOf T others h1]; omega
    have := stSent_new S (Slice.sentOf T others) 0
    rw [Nat.add_zero, Array.getElem?_eq_getElem h0] at this
    rw [this]
    show some (((Slice.sentOf T others)[0]'h0).shape.answers, []) = _
    rw [sentOf_zero T others h0]
  cases hx : (ledgerShut (D.stA T others S) T S.oracles.size).oracles[S.oracles.size]? with
  | none => rw [hx] at e; cases e
  | some x =>
    rw [hx] at e
    have e' := Option.some.inj e
    have ea : x.shape.answers = T.shape.answers := congrArg Prod.fst e'
    have eg : x.groups = [] := congrArg Prod.snd e'
    show some (x.shape.answers, x.groups ++ [gp]) = _
    rw [ea, eg]
    rfl

/-- The rider behind the joining: its notice's count of answers. -/
theorem key_stJ_rider (h1 : others.size = 1) :
    ((D.stJ T gp others S).oracles[S.oracles.size + 1]?).map shareKey =
      some ((others.getD 0 default).shape.answers, []) := by
  unfold Taken.stJ
  rw [joined_other _ _ _ _ _ _ (by omega), key_ledgerShut]
  unfold Taken.stA
  rw [key_admitted, stSent_new S (Slice.sentOf T others) 1,
    Array.getElem?_eq_getElem (show 1 < (Slice.sentOf T others).size by
      rw [size_sentOf T others h1]; omega)]
  have e : (Slice.sentOf T others)[1]'(by rw [size_sentOf T others h1]; omega) =
      others.getD 0 default := by
    rw [← sentOf_one T others h1, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [size_sentOf T others h1]; omega)]
    rfl
  rw [e]
  rfl

theorem size_stJ (h1 : others.size = 1) :
    (D.stJ T gp others S).oracles.size = S.oracles.size + 2 := by
  unfold Taken.stJ withMessageInGroup ledgerShut
  show (Array.modify _ _ _).size = _
  rw [Array.size_modify]
  have e : (D.stA T others S).oracles.size = S.oracles.size + 2 := by
    unfold Taken.stA admitted
    show (Array.modify _ _ _).size = _
    rw [Array.size_modify, stSent_size, size_sentOf T others h1]
  split
  · rw [closeLedgers_size, e]
  · exact e

/-- The guard G9 at a tree of two parts: one sampled message in one group; one without a sample. -/
theorem sharesOk_two (S' : Statement) (tr : Tree) (g g' a gp' : Nat) (l : List Nat)
    (hp : tr.parts = #[g, g']) (k0 : (S'.oracles[g]?).map shareKey = some (a, [gp']))
    (ha : a ≠ 0) (k1 : (S'.oracles[g']?).map shareKey = some (0, l)) : sharesOk S' tr = true := by
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.1 k0
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 k1
  have xa : x.shape.answers = a := congrArg Prod.fst ex
  have xg : x.groups = [gp'] := congrArg Prod.snd ex
  have ya : y.shape.answers = 0 := congrArg Prod.fst ey
  unfold sharesOk
  rw [hp]
  simp [hx, hy, xa, xg, ya, ha]

/-- The place of a message that was just sent. -/
theorem bookSentP_place (ft roots : Nat) (S' : Statement) (Bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (i : Nat) (h : i < sent.size) :
    (bookSentP ft roots S' Bk sent lay).place[Bk.place.size + i]? =
      some (Bk.trees.size + lay.tree.getD i 0, lay.part.getD i 0) := by
  show (Bk.place ++ _)[Bk.place.size + i]? = _
  rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Array.getElem?_map, Array.getElem?_eq_getElem (by rw [Array.size_range]; exact h),
    Array.getElem_range]
  rfl

/-! ## What rides, at the new tree -/

/-- **What rides holds at the new tree behind the joining**, whatever the switch takes. -/
theorem readSeat_new (ft roots : Nat) (Bk : TreeBook) (sh : TreeShape) (h1 : others.size = 1)
    (hs : D.lay.shapes = #[sh])
    (ht : ∀ i, i < 2 → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (step : S.oracles.size = Bk.place.size) (ha : T.shape.answers ≠ 0)
    (hr : (others.getD 0 default).shape.answers = 0) :
    ReadSeat (D.stJ T gp others S) (bookSentP ft roots S Bk (Slice.sentOf T others) D.lay)
      [S.oracles.size] (S.oracles.size + 1) Bk.trees.size
      (newTree ft roots sh S.oracles.size) where
  inBook := bookSentP_new ft roots S Bk T others D.lay sh h1 hs (fun i hi => (ht i hi).1) hr
  place := fun p h => by
    have h2 : p < 2 := h
    have hp := bookSentP_place ft roots S Bk (Slice.sentOf T others) D.lay p
      (by rw [size_sentOf T others h1]; exact h2)
    rw [(ht p h2).1, (ht p h2).2, ← step] at hp
    match p, h2, hp with
    | 0, _, hp => exact hp
    | 1, _, hp => exact hp
  parts := rfl
  once := rfl
  shares := sharesOk_two _ _ S.oracles.size (S.oracles.size + 1) T.shape.answers gp [] rfl
    (key_stJ_g D T gp others S h1) ha (by rw [key_stJ_rider D T gp others S h1, hr])
  there := fun o ho => by
    rw [size_stJ D T gp others S h1]
    rcases List.mem_append.1 ho with h | h <;> rw [List.mem_singleton.1 h] <;> omega

/-- **The whole ride to the next fold's front**: behind the claims, the beginning of the test
and the reading of the old tree. -/
theorem readSeat_behind (ft roots : Nat) (Bk : TreeBook) (sh : TreeShape) (h1 : others.size = 1)
    (hs : D.lay.shapes = #[sh])
    (ht : ∀ i, i < 2 → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (step : S.oracles.size = Bk.place.size) (ha : T.shape.answers ≠ 0)
    (hr : (others.getD 0 default).shape.answers = 0) (tOld : Nat) (hO : tOld < Bk.trees.size) :
    ReadSeat (begun (D.stR T gp others S) gp (D.grown S))
      (bookRead (bookSentP ft roots S Bk (Slice.sentOf T others) D.lay) tOld)
      [S.oracles.size] (S.oracles.size + 1) Bk.trees.size
      (newTree ft roots sh S.oracles.size) :=
  (((readSeat_new D T gp others S ft roots Bk sh h1 hs ht step ha hr).withRows gp D.rows).begun gp
    (D.grown S)).bookRead tOld (Nat.ne_of_lt hO)

end Johnson.Prover.Link
