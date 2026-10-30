-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SymbolsMade.lean: THE SMALLNESS TEST: WHERE addTreesF
(OnBytes/Model/Tail.lean), the routine by which the planners lay a sub-proof's arrays, RETURNS, THE
ARRAY UNDER EACH MATRIX's NUMBER (gtTree[mu]) IS A SYMBOL ARRAY WITH ONE VIRTUAL ROW AND THE ROWS
AND COLUMNS OF THAT MATRIX's SHAPE (shp[mu]), where the shape has a row of cells; AND THE LIST HAS
A MEMBER FOR EACH ARRAY. General: no planner, no scope, no premise but the return and that row.
Lemmas; none of the library's goals.

  `addN_both`, `addP_both`   what the two routines that add an array do to the ledger AND to the
                   list: a push on each; in front the two were of one length
  `ListLooks F T`   where entry i of the list bears a shape q, array i of the ledger is of symbols,
                   has q.Rr rows, q.Kc columns and one virtual row
  `listLooks_push`, `listLooks_addN`, `listLooks_addP`   it goes over a push on both; so the two
                   routines keep it, and behind each the two are of one length
  **`addTreesF_syms`**   behind addTreesF: at every mu below NM whose shape has a row of cells: the
                   look of the array gtTree[mu] is (symbols, shp[mu].Rr, shp[mu].Kc, 1) · the list
                   is as long as the ledger: the planner's form of what `allHeld_at_link`
                   (Johnson/Desc/K8/Honest/LeftAtLink.lean) asks of the link's list at a state
The walk is that of the library's `addTreesF_mS` (Johnson/Road/K4/Plan/ShapeRows.lean), cut for cut,
with this invariant in the place of that one. KIN: `addTreesF_looks`
(Johnson/Desc/Kinds/Law/AddTreesLooks.lean) has of a symbol array the kind and the virtual row, at
the numbers that the map's lists PK, TX, FT hold, and by its own limits not its rows and columns ·
`addTreesF_sym` (Johnson/IMR/OwnLaid.lean) has rows and columns, in the matrix's numbers, at PK and
TX alone · `addP_spec`, `addN_spec` (AddTreesLooks.lean) say the push on the ledger alone. None
speaks by gtTree and shp, in which the verifier's tests on the ties read.
Limits. That the routine returns anywhere is not said. Where a shape has no row of cells nothing is
said (the routine's last test holds the shape's rows of cells against the matrix's). THE PLANNED
LEDGER AT THE ROUTINE's RETURN ALONE: nothing on a plan, a built segment or a state. Nothing on
which matrix an array bears beyond the shape.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Road.K4.Plan.ShapeRows
import Johnson.Desc.First.Batch.Law.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- What t2AddN does to the ledger and to the list. -/
theorem addN_both {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    F.trees.size = T.nt.size ∧
      F'.trees = F.trees.push
        { name := name, kind := .table, R := R, K := K, owner := !foreign,
          rows := Array.replicate nv ({} : HRow) } ∧
      T'.nt = T.nt.push { ec := ec, a := a, foreign := foreign } := by
  unfold t2AddN at h
  split at h
  · cases h
  · rename_i hc
    have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨e3, e4⟩ := Prod.mk.inj e2
    have ho : t2Open F T = true := by simpa using hc
    unfold t2Open at ho
    simp only [Bool.and_eq_true, beq_iff_eq] at ho
    exact ⟨ho.2, by rw [← e3], by rw [← e4]⟩

/-- What t2AddP does to the ledger and to the list. -/
theorem addP_both {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) :
    F.trees.size = T.nt.size ∧
      F'.trees = F.trees.push
        { name := name, kind := .symbols, R := (ShP.of m k a).Rr, K := (ShP.of m k a).Kc,
          owner := !foreign, rows := Array.replicate 1 ({} : HRow) } ∧
      T'.nt = T.nt.push { ec := 1, a := a, foreign := foreign, p := some (ShP.of m k a) } := by
  unfold t2AddP at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, e4⟩ := Prod.mk.inj e2
      have ho : t2Open F T = true := by simpa using hc
      unfold t2Open at ho
      simp only [Bool.and_eq_true, beq_iff_eq] at ho
      exact ⟨ho.2, by rw [← e3], by rw [← e4]⟩

/-- Where an entry of the list bears a shape, the array of its number has that shape's look. -/
def ListLooks (F : Fork) (T : Tail2) : Prop :=
  ∀ (i : Nat) (q : ShP), (T.nt.getD i {}).p = some q →
    LinkJoin.look (F.trees.getD i {}) = (HKind.symbols, q.Rr, q.Kc, 1)

/-- It goes over a push on both. -/
theorem listLooks_push {F F' : Fork} {T T' : Tail2} {X : HTree} {n : N2}
    (hs : F.trees.size = T.nt.size) (hF : F'.trees = F.trees.push X) (hT : T'.nt = T.nt.push n)
    (g : ListLooks F T)
    (hX : ∀ q : ShP, n.p = some q → LinkJoin.look X = (HKind.symbols, q.Rr, q.Kc, 1)) :
    ListLooks F' T' := by
  intro i q hq
  rw [hT, Array.getD_eq_getD_getElem?, Array.getElem?_push] at hq
  rw [hF, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
  split at hq
  · rename_i e
    rw [if_pos e]
    exact hX q hq
  · rename_i e
    rw [if_neg e]
    have k := g i q (by rw [Array.getD_eq_getD_getElem?]; exact hq)
    rw [Array.getD_eq_getD_getElem?] at k
    exact k

/-- t2AddN keeps it. -/
theorem listLooks_addN {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : ListLooks F T) :
    ListLooks F' T' ∧ F'.trees.size = T'.nt.size := by
  obtain ⟨hs, hF, hT⟩ := addN_both h
  refine ⟨listLooks_push hs hF hT g (fun q hq => by cases hq), ?_⟩
  rw [hF, hT, Array.size_push, Array.size_push, hs]

/-- t2AddP keeps it. -/
theorem listLooks_addP {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : ListLooks F T) :
    ListLooks F' T' ∧ F'.trees.size = T'.nt.size := by
  obtain ⟨hs, hF, hT⟩ := addP_both h
  refine ⟨listLooks_push hs hF hT g (fun q hq => ?_), ?_⟩
  · obtain rfl := Option.some.inj hq
    simp [LinkJoin.look]
  · rw [hF, hT, Array.size_push, Array.size_push, hs]

/-- **Behind addTreesF the array under each matrix's number has that matrix's shape's look, and
the list has a member for each array.** -/
theorem addTreesF_syms {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (∀ mu, mu < tl'.NM → 0 < (tl'.shp.getD mu {}).m →
      LinkJoin.look (G.trees.getD (tl'.gtTree.getD mu 0) {}) =
        (HKind.symbols, (tl'.shp.getD mu {}).Rr, (tl'.shp.getD mu {}).Kc, 1)) ∧
      G.trees.size = T'.nt.size := by
  unfold addTreesF at h
  obtain ⟨h0, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨e3, e4⟩ := Prod.mk.inj e2
  -- the list that is handed in is empty
  have G0 : ListLooks F { T with link := true } := by
    intro i q hq
    have hE : T.nt.isEmpty = true := by simpa using h0
    have hz : T.nt.size = 0 := Array.isEmpty_iff_size_eq_zero.1 hE
    have hn : T.nt[i]? = none := Array.getElem?_eq_none (by omega)
    have hq' : (T.nt.getD i {}).p = some q := hq
    rw [Array.getD_eq_getD_getElem?, hn] at hq'
    cases hq'
  have K1 : ListLooks F1 T1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => ListLooks s.1 s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨_, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, (listLooks_addN hP hI).1⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl G0 h1
  have K2 : ListLooks F2 T2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => ListLooks s.1 s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, (listLooks_addP hP hI).1⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : ListLooks F3 T3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => ListLooks s.1 s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, (listLooks_addP hP hI).1⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : ListLooks FB TB ∧ FB.trees.size = TB.nt.size :=
    listLooks_addN hB (listLooks_addN hZ K3).1
  have K4 : ListLooks F4 T4 ∧ F4.trees.size = T4.nt.size :=
    forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => ListLooks s.1 s.2 ∧ s.1.trees.size = s.2.nt.size)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, listLooks_addP hP hI.1⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  refine ⟨fun mu hmu hpos => ?_, by rw [← e3, ← e4]; exact K4.2⟩
  have hNM : tl'.NM = tl.NM := by rw [← e1]
  have hgt : tl'.gtTree = tl.gtTree := by rw [← e1]
  have hm : mu < tl.NM := by rw [← hNM]; exact hmu
  have hs : tl'.shp.getD mu {} = (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {} := by
    rw [← e1]
    show ((Array.range tl.NM).map fun mu =>
      (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {}).getD mu {} = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hm]
    rfl
  cases hp : (T4.nt.getD (tl.gtTree.getD mu 0) {}).p with
  | none =>
    rw [hs, hp] at hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  | some q =>
    rw [hs, hp, hgt, ← e3]
    exact K4.1 _ q hp

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.addN_both
#print axioms VerifiableInference.Desc.First.K8.Honest.addP_both
#print axioms VerifiableInference.Desc.First.K8.Honest.listLooks_push
#print axioms VerifiableInference.Desc.First.K8.Honest.listLooks_addN
#print axioms VerifiableInference.Desc.First.K8.Honest.listLooks_addP
#print axioms VerifiableInference.Desc.First.K8.Honest.addTreesF_syms
