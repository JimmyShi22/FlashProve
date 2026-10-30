-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyDoorForm.lean: at the first border of the key file's last chain the thread's clause on the state, at the form
`fillAt`, from the two earlier chains' last shapes and one closed test. So hForm of a door is a law and one line that
Lean's kernel evaluates, and that line can say no.

Why. `fillAt` (Johnson/Desc/Last/ShapeAt.lean) was written for the proof file, and has been evaluated at no state of
a key file. By `shapeAt_zero_iff` its test at border 0 is the start's yes, `firstDoorB` and `sharedDoorB`. Every clause
of these two but the marks reads the shape alone, and the marks ride in the shape.

Main names.
  `bookFitsS`, `bookFitsS_eq`: the library's `bookFitsB` on a book's shape.
  `firstDoorS`, `firstDoor_of_S`: the six tests that `firstDoorB_of_six` asks, and the mask, on the first chain's shape.
  `sharedDoorS`, `sharedDoor_of_S`: `sharedDoorB` on what the start reads of the shared chain.
  `doorFormS`: the two at one pair of shapes.
  `door_form_full`: the test says yes at the two written terms. By Lean's kernel. IT CAN SAY NO: then the form is wrong
    for the key file.
  `form_start_key`: where the two states have these shapes and the start says yes, the form's test says yes and the
    statement is in order.

What stays open. That any state has these shapes: `shape19_of_thr`, `shape12_of_thr` give it where the two threads
stand. Nothing here says that they stand. The shapes are the written terms of the full size: in scope alone.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastThread
import E2E.KeyShapeThirdStart
import Johnson.Desc.Last.ShapeDoorLess

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Sound (bookFitsB tenantB)
open VerifiableInference.Desc.Last (Handed firstSixB firstSixClauses firstDoorB firstDoorB_of_six
  sharedDoorB sharedDoorClauses fillAt fill_of_shapeAt shapeAt_zero_iff start_parts)
open VerifiableInference.Desc.Third (S₃ SharedOut sharedOfEnd)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces Xi descriptionFromSource thirdPar firstOf rowOfLinClaim)
open AtPublicFiles.AtFiles (Sh₁B sh₁B LinSh linSh SharedSh sharedSh sharedOf sharedOf_eq sh₂ KeySourced weights_ok
  weightsB door_of_back pubOf CF SF)
open AtPublicFiles.AtFiles.Full (T19 V12 six_sourced first_of_sourced)
open AtPublicFiles.KeyLastThread (handOf handKey endKey)

/-! ## 1 The book on its shape -/

/-- `bookFitsB` on a book's shape. -/
def bookFitsS (B : BookSh) : Bool :=
  (List.range B.place.length).all fun i =>
    match B.place[i]? with
    | some q =>
      (match B.trees[q.1]? with
       | some t => decide (t.parts[q.2]? = some i)
       | none => false)
    | none => true

theorem bookFitsS_eq (B : TreeBook) : bookFitsS (bookSh B) = bookFitsB B := by
  unfold bookFitsS bookFitsB
  rw [place_size]
  refine List.all_congr rfl fun i => ?_
  rw [place_get]
  cases B.place[i]? with
  | none => rfl
  | some q =>
    show (match (bookSh B).trees[q.1]? with
      | some t => decide (t.parts[q.2]? = some i)
      | none => false) =
      (match B.trees[q.1]? with
      | some t => decide (t.parts[q.2]? = some i)
      | none => false)
    rw [tree_get]
    cases B.trees[q.1]? with
    | none => rfl
    | some t =>
      show decide ((t.parts.toList)[q.2]? = some i) = decide (t.parts[q.2]? = some i)
      rw [Array.getElem?_toList]

/-! ## 2 The first chain's end -/

/-- **The first chain's part of the door, on the shape.** a: the shape; l: what the start reads of its claim. -/
def firstDoorS (a : Sh₁B) (l : LinSh) : Bool :=
  a.2.tidy && bookFitsS a.1.book && l.weights && l.mask.isSome &&
    (match a.1.st.groups[l.own]? with
     | some G =>
       (G.members.length == 2) &&
         (G.members.all fun i =>
           match a.1.st.oracles[i]? with
           | some x => x.rows == 1
           | none => false) &&
         !G.kinds.isEmpty
     | none => false)

/-- The value that is handed, where the state names its claim. -/
theorem handOf_eq (s : FirstState) (l : LinFirst) (hl : s.lin = some l) :
    handOf s l = ⟨s.d.st, s.d.book, s.d.roots, l.w, l.own, l.mask, [rowOfLinClaim l.claim]⟩ := by
  unfold handOf firstOf
  rw [hl]

theorem firstDoor_of_S (Q : AtPublicFiles.KeyShape.Pub1) (cs : Codes) (s : FirstState) (l : LinFirst)
    (hl : s.lin = some l)
    (h : firstDoorS (sh₁B Q cs s) (linSh Q.one.lin cs l) = true) :
    firstDoorB (handOf s l) = true := by
  rw [handOf_eq s l hl]
  have h' : (stTidyB s.d.st && bookFitsS (bookSh s.d.book) &&
      weightsB Q.one.lin (linLayOmega cs Q.one.lin) (rowOfLinClaim l.claim).g && l.mask.isSome &&
      (match (stSh s.d.st).groups[l.own]? with
       | some G =>
         (G.members.length == 2) &&
           (G.members.all fun i =>
             match (stSh s.d.st).oracles[i]? with
             | some x => x.rows == 1
             | none => false) &&
           !G.kinds.isEmpty
       | none => false)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨t, b⟩, w⟩, m⟩, g⟩ := h'
  rw [bookFitsS_eq] at b
  rw [grp_get] at g
  refine firstDoorB_of_six ?_ m
  simp only [firstSixB, firstSixClauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  cases hG : s.d.st.groups[l.own]? with
  | none =>
    rw [hG] at g
    cases g
  | some G =>
    rw [hG] at g
    have g' : (((G.members.toList.length == 2) &&
        (G.members.toList.all fun i =>
          match (stSh s.d.st).oracles[i]? with
          | some x => x.rows == 1
          | none => false)) &&
        !(G.rows.toList.map (·.kind)).isEmpty) = true := g
    simp only [Bool.and_eq_true] at g'
    obtain ⟨⟨g1, g2⟩, g3⟩ := g'
    refine ⟨t, b, ?_, ?_, ?_, ?_⟩
    · show (rowOfLinClaim l.claim).g.all (·.ok) = true
      exact List.all_eq_true.2 (weights_ok w)
    · show (G.members.size == 2) = true
      rw [Array.length_toList] at g1
      exact g1
    · show (G.members.toList.all fun i =>
        match s.d.st.oracles[i]? with
        | some x => x.sampleRows.size == 1
        | none => false) = true
      refine List.all_eq_true.2 fun i hi => ?_
      show (match s.d.st.oracles[i]? with
        | some x => x.sampleRows.size == 1
        | none => false) = true
      have c : (match (stSh s.d.st).oracles[i]? with
        | some x => x.rows == 1
        | none => false) = true := List.all_eq_true.1 g2 i hi
      rw [orc_get] at c
      cases ho : s.d.st.oracles[i]? with
      | none =>
        rw [ho] at c
        cases c
      | some x =>
        rw [ho] at c
        exact c
    · show (!G.rows.isEmpty) = true
      cases hr : G.rows.toList with
      | nil =>
        rw [hr] at g3
        cases g3
      | cons r rs =>
        have : G.rows.isEmpty = false := by
          rw [← Array.isEmpty_toList, hr]
          rfl
        rw [this]
        rfl

/-! ## 3 The shared chain's end -/

/-- **The shared chain's part of the door, on what the start reads of it.** S: the plan's shape. -/
def sharedDoorS (S : LinShape) (b : SharedSh) : Bool :=
  b.tidy && bookFitsS b.book &&
    (match b.book.place[b.omega]? with
     | some q => q.2 == 0
     | none => true) &&
    (match b.st.oracles[b.omega]? with
     | some y => decide (y.shape = S.omega) && (y.rows == 1)
     | none => false)

theorem sharedDoor_of_S (p : VerifiableInference.Desc.Third.P₁₄) (d : _root_.Desc.K14.St)
    {e : _} (he : _root_.Desc.K14.ended d = some e)
    (h : sharedDoorS p.S (sharedSh d) = true) :
    sharedDoorB p (sharedOfEnd e) = true := by
  have hE : e.st = d.st ∧ e.book = d.book ∧ e.lin.omega = d.loc.oOmega := by
    unfold _root_.Desc.K14.ended at he
    split at he
    · obtain rfl := Option.some.inj he
      exact ⟨rfl, rfl, rfl⟩
    · cases he
  obtain ⟨e1, e2, e3⟩ := hE
  have h' : (stTidyB d.st && bookFitsS (bookSh d.book) &&
      (match (bookSh d.book).place[d.loc.oOmega]? with
       | some q => q.2 == 0
       | none => true) &&
      (match (stSh d.st).oracles[d.loc.oOmega]? with
       | some y => decide (y.shape = p.S.omega) && (y.rows == 1)
       | none => false)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨t, b⟩, q⟩, y⟩ := h'
  rw [bookFitsS_eq] at b
  rw [place_get] at q
  rw [orc_get] at y
  have hs : (sharedOfEnd e).st = d.st := e1
  have hb : (sharedOfEnd e).book = d.book := e2
  have ho : (sharedOfEnd e).omega = d.loc.oOmega := e3
  simp only [sharedDoorB, sharedDoorClauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact OnBytes.Means.inOrderB_iff.2 (OnBytes.Means.tidy4B_iff.1 t).inOrder
  · rw [hb]
    exact b
  · show (match (sharedOfEnd e).book.place[(sharedOfEnd e).omega]? with
      | some q => q.2 == 0
      | none => true) = true
    rw [hb, ho]
    exact q
  · show (match (sharedOfEnd e).st.oracles[(sharedOfEnd e).omega]? with
      | some y => decide (y.shape = p.S.omega)
      | none => false) = true
    rw [hs, ho]
    cases hy : d.st.oracles[d.loc.oOmega]? with
    | none =>
      rw [hy] at y
      cases y
    | some x =>
      rw [hy] at y
      have y' : (decide (x.shape = p.S.omega) && (x.sampleRows.size == 1)) = true := y
      simp only [Bool.and_eq_true] at y'
      exact y'.1
  · show (match (sharedOfEnd e).st.oracles[(sharedOfEnd e).omega]? with
      | some y => y.sampleRows.size == 1
      | none => false) = true
    rw [hs, ho]
    cases hy : d.st.oracles[d.loc.oOmega]? with
    | none =>
      rw [hy] at y
      cases y
    | some x =>
      rw [hy] at y
      have y' : (decide (x.shape = p.S.omega) && (x.sampleRows.size == 1)) = true := y
      simp only [Bool.and_eq_true] at y'
      exact y'.2

/-! ## 4 The closed test -/

/-- **The door's test at a pair of shapes.** -/
def doorFormS (S : LinShape) (a : Sh₁B) (b : SharedSh) : Bool :=
  (match a.2.back.door with
   | some l => firstDoorS a l
   | none => false) && sharedDoorS S b

/-- **It says yes at the written terms.** By Lean's kernel. A NO HERE SAYS THAT THE FORM IS WRONG FOR THE KEY FILE. -/
theorem door_form_full :
    doorFormS SF T19 (sharedOf V12) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **The form's test at border 0, and the order of the statement**, in scope, at two states of the two written
shapes at which the start says yes. R: the own test's rounds; the test at border 0 does not read them. -/
theorem form_start_key (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (R : List Fmt.DeclaredRound) (x : Xi) (e₁ : FirstState) (e₂ : _root_.Desc.K14.St) (s₃ : S₃)
    (h1 : sh₁B (pubOf X) CF e₁ = T19) (h2 : sh₂ e₂ = V12)
    (hst : (descriptionFromSource X N P).start₃ x e₁ e₂ = .ok s₃) :
    (fillAt (thirdPar X.chains) R handKey endKey).shape 0 (x, e₁) e₂ s₃ = true ∧
      OnBytes.Means.InOrder s₃.st := by
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have h6 := six_sourced hs scope
  obtain ⟨h, o, hh, ho, h₀⟩ := (AtPublicFiles.KeyLastThread.start_key X N P x e₁ e₂ s₃).1 hst
  have hh' : e₁.lin.map (handOf e₁) = some h := hh
  have ho' : (_root_.Desc.K14.ended e₂).map sharedOfEnd = some o := ho
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hh'
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 ho'
  have hc := door_form_full
  rw [← h1, ← h2, sharedOf_eq] at hc
  have hd : (sh₁B (pubOf X) CF e₁).2.back.door =
      some (linSh (pubOf X).one.lin CF l) := by
    have e' := door_of_back (pubOf X).one.lin CF e₁
    rw [hl] at e'
    exact e'
  unfold doorFormS at hc
  rw [hd, Bool.and_eq_true] at hc
  have hS : (thirdPar X.chains).S = SF := by
    show X.chains.made.sized.key.once.shape = _
    rw [← hlin]
    exact h6.lin
  have f₁ := firstDoor_of_S (pubOf X) CF e₁ l hl hc.1
  have f₂ := sharedDoor_of_S (thirdPar X.chains) e₂ he (by rw [hS]; exact hc.2)
  refine ⟨fill_of_shapeAt (thirdPar X.chains) R handKey endKey hh ho
    (shapeAt_zero_iff.2 ⟨h₀, f₁, f₂⟩), ?_⟩
  obtain ⟨a, -, -⟩ := start_parts h₀
  rw [a]
  have t : OnBytes.Means.tidy4B (handOf e₁ l).st = true := by
    simp only [firstDoorB, VerifiableInference.Desc.Last.firstDoorClauses, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true] at f₁
    exact f₁.1
  exact (OnBytes.Means.tidy4B_iff.1 t).inOrder

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.bookFitsS_eq
#print axioms AtPublicFiles.KeyLastChain.handOf_eq
#print axioms AtPublicFiles.KeyLastChain.firstDoor_of_S
#print axioms AtPublicFiles.KeyLastChain.sharedDoor_of_S
#print axioms AtPublicFiles.KeyLastChain.door_form_full
#print axioms AtPublicFiles.KeyLastChain.form_start_key
