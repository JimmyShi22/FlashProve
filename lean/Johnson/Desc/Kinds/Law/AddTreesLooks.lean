-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AddTreesLooks.lean: WHERE addTreesF (OnBytes/Model/Tail.lean), the routine by
which all three planners lay a sub-proof's arrays, RETURNS FROM AN EMPTY LEDGER AND AN EMPTY LIST,
EVERY ARRAY OF THE LEDGER THAT IT HANDS BACK IS OF JUST ONE OF FOUR SORTS, AND ITS NUMBER STANDS IN
THE RECORD'S MAP ix WHERE THAT SORT STANDS. General: no planner, no scope, no premise but the
return. The statement serves a list of conditions in front of the
batching. Definitions, statements and proofs; nothing is evaluated.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Plan).
  LooksU tl nU t X: a vector: for some n below 3 the map names t as U(n+1): a table of one row,
      nU[n] columns, one virtual row.
  LooksM tl t X: a matrix's symbol array: the map names t among PK, TX or FT: symbols, one virtual
      row.
  LooksZ tl t X, LooksB tl t X: the arrays ZZ and BZ: t is the map's number; a table of tau rows, 2
      mz columns, 2 zzBlocks + 2 virtual rows; a table of 32 rows, bzColumns columns, 3 virtual
      rows.
  Looks: one of the four. looks_apart: no two of the four hold of one array: by the arrays' own
      looks (symbols or table; 1, an even number, 3 virtual rows): no word on the order of the
      numbers is needed.
  addN_spec, addP_spec: what the two routines that add an array return. allLook_push: the invariant
      goes over a push.
  TreesStay F F': every array of F stands in F' at its number. treesStay_push.
  addTreesF_walk: the one walk: all that follows, together.
  addTreesF_looks: THE STATEMENT. addTrees_looks: under the name by which the plans call the
      routine.

How. Each array gets the ledger's length as its number when it is laid, and the routine holds that
number against the map at once and refuses if they part. The cuts of the routine's text are those of
addTreesF_mS (Johnson/Road/K4/Plan/ShapeRows.lean), with this invariant in the place
of that one.
KIN, AND WHAT THIS ADDS. The library's OnBytes.Tie.Pv.Tail.addTreesF_frame
(OnBytes/Tie/Pv/Tail/EndAdd.lean) goes FROM THE MAP TO THE LOOK, at any ledger: the array under each
number that the map holds for a vector, for ZZ and for BZ has these very sizes; by its own limits it
says nothing on the symbol arrays. Here the way is FROM THE ARRAY TO THE MAP: every array is one of
the four: there is no fifth. KIN OF THE TWO SMALL LAWS ON ONE ADD: that file's t2AddN_ok (the
number; the elder arrays stay; kind and three sizes of the new one) · the lookups' Fo.t2AddN_ok (the
number; the list is one longer and begins with the old one; rows and virtual rows) ·
t2AddN_tree (the new array whole, read by getD) · t2AddP_at (the number; one longer;
rows and columns) · t2AddP_ok in two files (EndAdd.lean, FoAddTrees.lean: the elder arrays stay).
OF A SYMBOL ARRAY NONE SAYS THE KIND OR THE VIRTUAL ROWS. addN_spec and addP_spec say the add as
ONE EQUATION ON THE LIST (a push), by which the invariants here are carried.
What it does not say. That the routine returns anywhere. THE CONVERSE: that every entry of the map's
lists PK, TX, FT is the number of an array that was laid: the routine walks pkMat, pxMat and ft, and
tests the map at their indices alone. Which matrix an array bears, and a symbol array's rows and
columns. Nothing at a ledger or list that is not empty at the start. Nothing on soundness.

-/
import Johnson.Goal.Meaning.PlanPort
import OnBytes.Tie.Pv.Tail.EndAdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Plan

open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- A vector U(n+1). -/
def LooksU (tl : HTailF2) (nU : Array Nat) (t : Nat) (X : HTree) : Prop :=
  ∃ n, n < 3 ∧ tl.ix.U.getD n none = some t ∧ X.kind = .table ∧ X.R = 1 ∧ X.K = nU.getD n 0 ∧
    X.rows.size = 1

/-- A matrix's symbol array. -/
def LooksM (tl : HTailF2) (t : Nat) (X : HTree) : Prop :=
  (∃ i : Nat, tl.ix.PK[i]? = some t ∨ tl.ix.TX[i]? = some t ∨ tl.ix.FT[i]? = some t) ∧
    X.kind = .symbols ∧ X.rows.size = 1

/-- The array ZZ. -/
def LooksZ (tl : HTailF2) (t : Nat) (X : HTree) : Prop :=
  t = tl.ix.ZZ ∧ X.kind = .table ∧ X.R = tl.tau ∧ X.K = 2 * tl.mz ∧
    X.rows.size = 2 * tl.zzBlocks + 2

/-- The array BZ. -/
def LooksB (tl : HTailF2) (t : Nat) (X : HTree) : Prop :=
  t = tl.ix.BZ ∧ X.kind = .table ∧ X.R = 32 ∧ X.K = tl.bzColumns ∧ X.rows.size = 3

/-- One of the four. -/
def Looks (tl : HTailF2) (nU : Array Nat) (t : Nat) (X : HTree) : Prop :=
  LooksU tl nU t X ∨ LooksM tl t X ∨ LooksZ tl t X ∨ LooksB tl t X

/-- Every array of the ledger is of one of the four sorts. -/
def AllLook (tl : HTailF2) (nU : Array Nat) (F : Fork) : Prop :=
  ∀ t X, F.trees[t]? = some X → Looks tl nU t X

/-- **No two of the four hold of one array.** -/
theorem looks_apart (tl : HTailF2) (nU : Array Nat) (t : Nat) (X : HTree) :
    ¬ (LooksU tl nU t X ∧ LooksM tl t X) ∧ ¬ (LooksU tl nU t X ∧ LooksZ tl t X) ∧
      ¬ (LooksU tl nU t X ∧ LooksB tl t X) ∧ ¬ (LooksM tl t X ∧ LooksZ tl t X) ∧
      ¬ (LooksM tl t X ∧ LooksB tl t X) ∧ ¬ (LooksZ tl t X ∧ LooksB tl t X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_, _, _, k, _⟩, _, k', _⟩
    rw [k] at k'
    cases k'
  · rintro ⟨⟨_, _, _, _, _, _, r⟩, _, _, _, _, r'⟩
    omega
  · rintro ⟨⟨_, _, _, _, _, _, r⟩, _, _, _, _, r'⟩
    omega
  · rintro ⟨⟨_, k, _⟩, _, k', _⟩
    rw [k] at k'
    cases k'
  · rintro ⟨⟨_, k, _⟩, _, k', _⟩
    rw [k] at k'
    cases k'
  · rintro ⟨⟨_, _, _, _, r⟩, _, _, _, _, r'⟩
    omega

/-- What t2AddN returns. -/
theorem addN_spec {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    got = F.trees.size ∧ F'.trees = F.trees.push
      { name := name, kind := .table, R := R, K := K, owner := !foreign,
        rows := Array.replicate nv ({} : HRow) } := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e3, _⟩ := Prod.mk.inj e2
    exact ⟨e1.symm, by rw [← e3]⟩

/-- What t2AddP returns. -/
theorem addP_spec {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) :
    got = F.trees.size ∧ ∃ X : HTree, F'.trees = F.trees.push X ∧ X.kind = .symbols ∧
      X.rows.size = 1 := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, _⟩ := Prod.mk.inj e2
      exact ⟨e1.symm, _, by rw [← e3], rfl, by simp⟩

/-- The invariant goes over a push. -/
theorem allLook_push {tl : HTailF2} {nU : Array Nat} {F F' : Fork} {X : HTree}
    (g : AllLook tl nU F) (hF : F'.trees = F.trees.push X) (hX : Looks tl nU F.trees.size X) :
    AllLook tl nU F' := by
  intro t Y hY
  rw [hF, Array.getElem?_push] at hY
  split at hY
  · rename_i e
    obtain rfl := Option.some.inj hY
    rw [e]
    exact hX
  · exact g t Y hY

/-- A symbol array whose number the map bears. -/
theorem allLook_addP {tl : HTailF2} {nU : Array Nat} {F : Fork} {T : Tail2} {name : String}
    {m k w a : Nat} {foreign : Bool} {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : AllLook tl nU F)
    (hi : ∃ i : Nat, tl.ix.PK[i]? = some got ∨ tl.ix.TX[i]? = some got ∨
      tl.ix.FT[i]? = some got) :
    AllLook tl nU F' := by
  obtain ⟨e, X, hF, hk, hr⟩ := addP_spec h
  exact allLook_push g hF (Or.inr (Or.inl ⟨e ▸ hi, hk, hr⟩))

/-- Every array of F stands in F' at its number. -/
def TreesStay (F F' : Fork) : Prop :=
  ∀ (t : Nat) (X : HTree), F.trees[t]? = some X → F'.trees[t]? = some X

theorem TreesStay.refl (F : Fork) : TreesStay F F := fun _ _ h => h

theorem TreesStay.trans {F G H : Fork} (h : TreesStay F G) (k : TreesStay G H) : TreesStay F H :=
  fun t X x => k t X (h t X x)

theorem treesStay_push {F F' : Fork} {Y : HTree} (hF : F'.trees = F.trees.push Y) : TreesStay F F'
    := by
  intro t X hX
  have ht : t < F.trees.size := by
    by_contra c
    rw [Array.getElem?_eq_none (by omega)] at hX
    cases hX
  rw [hF, Array.getElem?_push, if_neg (by omega)]
  exact hX

/-- At each index of the list l the map's list A holds a number, and the array at it is there and
is of symbols. -/
def SymMarks (A : Array Nat) (l : List Nat) (F : Fork) : Prop :=
  ∀ i ∈ l, ∃ (t : Nat) (X : HTree), A[i]? = some t ∧ F.trees[t]? = some X ∧ X.kind = .symbols

theorem SymMarks.keep {A : Array Nat} {l : List Nat} {F F' : Fork} (m : SymMarks A l F)
    (k : TreesStay F F') : SymMarks A l F' := fun i hi => by
  obtain ⟨t, X, p1, p2, p3⟩ := m i hi
  exact ⟨t, X, p1, k t X p2, p3⟩

/-- One turn of a loop that adds a symbol array and holds its number against the list A. -/
theorem symMarks_addP {A : Array Nat} {pre : List Nat} {a : Nat} {F : Fork} {T : Tail2}
    {name : String} {m k w b : Nat} {foreign : Bool} {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w b foreign = .ok (got, F', T')) (eg : A[a]? = some got)
    (g : SymMarks A pre F) : TreesStay F F' ∧ SymMarks A (pre ++ [a]) F' := by
  obtain ⟨es, X, hF, hk, -⟩ := addP_spec h
  refine ⟨treesStay_push hF, fun i hi => ?_⟩
  rcases List.mem_append.1 hi with hi | hi
  · exact (g.keep (treesStay_push hF)) i hi
  · obtain rfl := List.mem_singleton.1 hi
    exact ⟨got, X, eg, by rw [hF, es]; simp, hk⟩

/-- **The one walk.** -/
theorem addTreesF_walk {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    AllLook tl nU G ∧ SymMarks tl.ix.PK (List.range tl.pkMat.size) G ∧
      SymMarks tl.ix.TX (List.range tl.pxMat.size) G ∧ SymMarks tl.ix.FT (List.range tl.ft.size) G
          := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨nZ, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨nB, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨-, e2⟩ := Prod.mk.inj e
  obtain ⟨e3, -⟩ := Prod.mk.inj e2
  have G0 : AllLook tl nU ({} : Fork) := by
    intro t X hX
    have h0 : (({} : Fork).trees : Array HTree) = #[] := rfl
    rw [h0] at hX
    simp at hX
  have K1 : AllLook tl nU F1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => AllLook tl nU s.1)
    (fun pre a rest hl s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      have ha : a < 3 := List.mem_range.1 (by rw [hl]; simp)
      dsimp only at hs
      split at hs
      · rename_i want hw
        obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨ne, hs⟩ := ok_of_jp hs
        have eg : got = want := by simpa using ne
        obtain ⟨es, hF⟩ := addN_spec hP
        refine ⟨_, (Except.ok.inj hs).symm,
          allLook_push hI hF (Or.inl ⟨a, ha, ?_, rfl, rfl, rfl, ?_⟩)⟩
        · rw [hw, ← eg, es]
        · simp
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl G0 h1
  have K2 : AllLook tl nU F2 ∧ SymMarks tl.ix.PK (List.range tl.pkMat.size) F2 :=
    forIn_keeps _ (List.range tl.pkMat.size)
    (fun pre (s : MProd Fork Tail2) => AllLook tl nU s.1 ∧ SymMarks tl.ix.PK pre s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      have eg : some got = tl.ix.PK[a]? := by simpa using ne
      exact ⟨_, (Except.ok.inj hs).symm, allLook_addP hP hI.1 ⟨a, Or.inl eg.symm⟩,
        (symMarks_addP hP eg.symm hI.2).2⟩)
    (List.range tl.pkMat.size) [] _ _ rfl ⟨K1, fun _ hi => by cases hi⟩ h2
  have K3 : (AllLook tl nU F3 ∧ TreesStay F2 F3) ∧ SymMarks tl.ix.TX (List.range tl.pxMat.size) F3
      :=
    forIn_keeps _ (List.range tl.pxMat.size)
    (fun pre (s : MProd Fork Tail2) =>
      (AllLook tl nU s.1 ∧ TreesStay F2 s.1) ∧ SymMarks tl.ix.TX pre s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      have eg : some got = tl.ix.TX[a]? := by simpa using ne
      obtain ⟨k, m⟩ := symMarks_addP hP eg.symm hI.2
      exact ⟨_, (Except.ok.inj hs).symm,
        ⟨allLook_addP hP hI.1.1 ⟨a, Or.inr (Or.inl eg.symm)⟩, hI.1.2.trans k⟩, m⟩)
    (List.range tl.pxMat.size) [] _ _ rfl ⟨⟨K2.1, TreesStay.refl F2⟩, fun _ hi => by cases hi⟩ h3
  obtain ⟨esZ, hFZ⟩ := addN_spec hZ
  obtain ⟨esB, hFB⟩ := addN_spec hB
  have KZ : AllLook tl nU FZ := by
    have eg : gotZ = tl.ix.ZZ := by simpa using nZ
    exact allLook_push K3.1.1 hFZ
      (Or.inr (Or.inr (Or.inl ⟨by rw [← eg, esZ], rfl, rfl, rfl, by simp⟩)))
  have KB : AllLook tl nU FB := by
    have eg : gotB = tl.ix.BZ := by simpa using nB
    exact allLook_push KZ hFB (Or.inr (Or.inr (Or.inr ⟨by rw [← eg, esB], rfl, rfl, rfl, by simp⟩)))
  have K4 : (AllLook tl nU F4 ∧ TreesStay FB F4) ∧ SymMarks tl.ix.FT (List.range tl.ft.size) F4 :=
    forIn_keeps _ (List.range tl.ft.size)
    (fun pre (s : MProd Fork Tail2) =>
      (AllLook tl nU s.1 ∧ TreesStay FB s.1) ∧ SymMarks tl.ix.FT pre s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      have eg : some got = tl.ix.FT[a]? := by simpa using ne
      obtain ⟨k, m⟩ := symMarks_addP hP eg.symm hI.2
      exact ⟨_, (Except.ok.inj hs).symm,
        ⟨allLook_addP hP hI.1.1 ⟨a, Or.inr (Or.inr eg.symm)⟩, hI.1.2.trans k⟩, m⟩)
    (List.range tl.ft.size) [] _ _ rfl ⟨⟨KB, TreesStay.refl FB⟩, fun _ hi => by cases hi⟩ h4
  have k34 : TreesStay F3 F4 := ((treesStay_push hFZ).trans (treesStay_push hFB)).trans K4.1.2
  rw [← e3]
  exact ⟨K4.1.1, K2.2.keep (K3.1.2.trans k34), K3.2.keep k34, K4.2⟩

/-- **THE STATEMENT**: behind addTreesF, from an empty ledger and an empty list. -/
theorem addTreesF_looks {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ t X, G.trees[t]? = some X → Looks tl nU t X :=
  (addTreesF_walk h).1

/-- The same at every number below the ledger's length, read as the library's shapeAt reads. -/
theorem addTreesF_looksAt {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ t, t < G.trees.size → Looks tl nU t (G.trees.getD t {}) := by
  intro t ht
  refine addTreesF_looks h t _ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rfl

/-- The same under the name by which the sub-proofs' plans call the routine. -/
theorem addTrees_looks {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTrees {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ t X, G.trees[t]? = some X → Looks tl nU t X :=
  addTreesF_looks h

/-! ## The way back, at each named number -/

/-- The library's "the state has array t, of this kind and these sizes", in this file's letters. -/
theorem of_has {G : Fork} {t : Nat} {k : HKind} {R K n : Nat}
    (h : OnBytes.Tie.Pv.Tail.Has G t (k, R, K, n)) :
    ∃ X, G.trees[t]? = some X ∧ X.kind = k ∧ X.R = R ∧ X.K = K ∧ X.rows.size = n := by
  obtain ⟨ht, hs⟩ := h
  unfold OnBytes.Tie.Pv.Tail.Port.shapeAt at hs
  obtain ⟨s1, s2⟩ := Prod.mk.inj hs
  obtain ⟨s2, s3⟩ := Prod.mk.inj s2
  obtain ⟨s3, s4⟩ := Prod.mk.inj s3
  refine ⟨G.trees.getD t {}, ?_, s1, s2, s3, s4⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rfl

/-- **The array at the map's ZZ.** At any ledger and list. -/
theorem addTreesF_atZ {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∃ X, G.trees[tl.ix.ZZ]? = some X ∧ LooksZ tl tl.ix.ZZ X := by
  obtain ⟨X, x0, x1, x2, x3, x4⟩ :=
    of_has (OnBytes.Tie.Pv.Tail.addTreesF_frame tl tl' F G T T' nU aTX hb hbLine h).2.1
  exact ⟨X, x0, rfl, x1, x2, x3, x4⟩

/-- **The array at the map's BZ.** -/
theorem addTreesF_atB {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∃ X, G.trees[tl.ix.BZ]? = some X ∧ LooksB tl tl.ix.BZ X := by
  obtain ⟨X, x0, x1, x2, x3, x4⟩ :=
    of_has (OnBytes.Tie.Pv.Tail.addTreesF_frame tl tl' F G T T' nU aTX hb hbLine h).2.2.1
  exact ⟨X, x0, rfl, x1, x2, x3, x4⟩

/-- **The array at each number that the map holds for a vector.** -/
theorem addTreesF_atU {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ n, n < 3 → ∀ t, tl.ix.U.getD n none = some t → ∃ X, G.trees[t]? = some X ∧
      X.kind = .table ∧ X.R = 1 ∧ X.K = nU.getD n 0 ∧ X.rows.size = 1 := by
  intro n hn t ht
  have u := (OnBytes.Tie.Pv.Tail.addTreesF_frame tl tl' F G T T' nU aTX hb hbLine h).1 n hn t ht
  exact of_has ⟨u.inside, u.shape⟩

/-- **The symbol arrays of the matrices that no other sub-proof reads.** -/
theorem addTreesF_atPK {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ i, i < tl.pkMat.size → ∃ t X, tl.ix.PK[i]? = some t ∧ G.trees[t]? = some X ∧
      X.kind = .symbols :=
  fun i hi => (addTreesF_walk h).2.1 i (List.mem_range.2 hi)

/-- **Those of the matrices that other sub-proofs read.** -/
theorem addTreesF_atTX {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ i, i < tl.pxMat.size → ∃ t X, tl.ix.TX[i]? = some t ∧ G.trees[t]? = some X ∧
      X.kind = .symbols :=
  fun i hi => (addTreesF_walk h).2.2.1 i (List.mem_range.2 hi)

/-- **Those of an earlier sub-proof's matrices.** -/
theorem addTreesF_atFT {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) :
    ∀ i, i < tl.ft.size → ∃ t X, tl.ix.FT[i]? = some t ∧ G.trees[t]? = some X ∧
      X.kind = .symbols :=
  fun i hi => (addTreesF_walk h).2.2.2 i (List.mem_range.2 hi)

end VerifiableInference.Desc.Kinds.Head.Law.Plan

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.looks_apart
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addN_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addP_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.allLook_push
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.allLook_addP
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.treesStay_push
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.symMarks_addP
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_walk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_looks
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.of_has
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atB
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atU
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atPK
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atTX
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_atFT
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTreesF_looksAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Plan.addTrees_looks
