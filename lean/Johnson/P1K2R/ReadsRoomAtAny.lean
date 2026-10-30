-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/ReadsRoomAtAny.lean: WHAT AN ACCEPT OF THE PUBLIC TESTS ON THE LINKS'
STRUCTURES
(OnBytes/Model/StagesLinks.lean: buildLinksH) SAYS OF THE VECTOR OF READS OF EVERY LINK WHOSE RECORD
NAMES ONE: under which name it stands in the link's list of arrays, and that the request's layout
has an array of that name with the plan's rows and columns. Johnson/Desc/Kinds/Law/
ReadsRoomOfBuilt.lean has this sentence AT THE LAST LINK ALONE, «an earlier segment's declaration is
turned by later readers». HERE: WHAT A LATER READER TURNS (keptUpTo) IS THE FIELD life ALONE: SO «an
array of that name, rows and columns is declared» IS KEPT AT EVERY LINK.
  DeclLike     an array of a's name, rows and columns is declared at some moment
  keptUpTo_like · foreign_like   the two steps keep it, at every earlier link
  declareLinks_atAny   that file's invariant, said at every index of the list walked so far
  reads_named_at       MAIN: its reads_named_of_built, at every link
CALLED AS THEY STAND, OUT OF THAT FILE: Decl · declareOwn_reads · foreign_keeps · heldAgainst_at ·
linkHeld_at; OnBytes/TieK/LinksEnd.lean's forIn_keeps · ok_of_bind · ok_of_jp. foreign_like's walk
through foreign's text is that of foreign_keeps.
WHAT IT IS NOT. An implication from an accept of buildLinksH; general in the links' structures: no
scope, no public part. No routine is evaluated. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.ReadsRoomOfBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model.Stages
open OnBytes.TieK (ok_of_bind ok_of_jp forIn_keeps)
open VerifiableInference.Desc.Kinds.Head.Law.Built (Decl declareOwn_reads foreign_keeps
  heldAgainst_at linkHeld_at)

/-- An array of a's name, rows and columns is declared at some moment. -/
def DeclLike (mo : Array (Array FrameArray)) (a : FrameArray) : Prop :=
  ∃ a', Decl mo a' ∧ a'.name = a.name ∧ a'.rows = a.rows ∧ a'.columns = a.columns

theorem DeclLike.of {mo : Array (Array FrameArray)} {a : FrameArray} (h : Decl mo a) :
    DeclLike mo a := ⟨a, h, rfl, rfl, rfl⟩

/-- keptUpTo turns the field life alone. -/
theorem keptUpTo_like {D D' : FrameLink} {name : String} {life : Nat}
    (h : keptUpTo D name life = .ok D') {a : FrameArray} (k : DeclLike D.moment a) :
    DeclLike D'.moment a := by
  unfold keptUpTo at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    obtain ⟨a', ⟨j, M, hj, ha⟩, e1, e2, e3⟩ := k
    have hlt : j < D.moment.size := by
      by_contra c
      rw [Array.getElem?_eq_none (by omega)] at hj
      cases hj
    by_cases h0 : j = 0
    · subst h0
      have hM : D.moment.getD 0 #[] = M := by
        rw [Array.getD_eq_getD_getElem?, hj]
        rfl
      refine ⟨if a'.name == name then { a' with life := max a'.life life } else a',
        ⟨0, M.map fun a => if a.name == name then { a with life := max a.life life } else a, ?_,
          ?_⟩, ?_, ?_, ?_⟩
      · show (D.moment.set! 0 _)[0]? = _
        rw [hM]
        simp [hlt]
      · rw [Array.toList_map]
        exact List.mem_map.2 ⟨a', ha, rfl⟩
      · split <;> exact e1
      · split <;> exact e2
      · split <;> exact e3
    · refine ⟨a', ⟨j, M, ?_, ha⟩, e1, e2, e3⟩
      show (D.moment.set! 0 _)[j]? = _
      rw [← hj]
      simp [Ne.symm h0]
  · cases h

/-- A later reader keeps, at every earlier link, «an array of that name, rows and columns is
declared». -/
theorem foreign_like {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : OnBytes.Model.PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    ∀ (j : Nat) (D : FrameLink), s.2[j]? = some D →
      ∃ D', s'.2[j]? = some D' ∧ ∀ a, DeclLike D.moment a → DeclLike D'.moment a := by
  unfold foreign at h
  cases e1 : pl.owner with
  | none =>
    simp only [e1] at h
    cases h
  | some owner =>
    simp only [e1] at h
    obtain ⟨-, h⟩ := ok_of_jp h
    cases e2 : links[layersLink p4 owner]? with
    | none =>
      simp only [e2] at h
      cases h
    | some Y =>
      simp only [e2] at h
      cases e3 : pl.rootIndex with
      | none =>
        simp only [e3] at h
        cases h
      | some ri =>
        simp only [e3] at h
        obtain ⟨-, h⟩ := ok_of_jp h
        cases e4 : Y.tl.pxMat[ri - Y.tl.pkMat.size]? with
        | none =>
          simp only [e4] at h
          cases h
        | some mu =>
          simp only [e4] at h
          cases e5 : X.Fp.trees[tree]? with
          | none =>
            simp only [e5] at h
            cases h
          | some mine =>
            simp only [e5] at h
            cases e6 : (Y.tl.gtTree[mu]?).bind (fun t => Y.Fp.trees[t]?) with
            | none =>
              simp only [e6] at h
              cases h
            | some theirs =>
              simp only [e6] at h
              obtain ⟨-, h⟩ := ok_of_jp h
              obtain ⟨ar, h1, h⟩ := ok_of_bind h
              cases e7 : s.2[layersLink p4 owner]? with
              | none =>
                simp only [e7] at h
                cases h
              | some D0 =>
                simp only [e7] at h
                obtain ⟨D1, hk, h⟩ := ok_of_bind h
                obtain rfl := Except.ok.inj h
                intro j D hj
                have hlt : layersLink p4 owner < s.2.size := by
                  by_contra c
                  rw [Array.getElem?_eq_none (by omega)] at e7
                  cases e7
                by_cases hb : j = layersLink p4 owner
                · subst hb
                  obtain rfl : D0 = D := Option.some.inj (e7.symm.trans hj)
                  refine ⟨D1, ?_, fun a k => keptUpTo_like hk k⟩
                  show (s.2.set! _ D1)[_]? = _
                  simp [hlt]
                · refine ⟨D, ?_, fun a k => k⟩
                  show (s.2.set! _ D1)[j]? = _
                  rw [← hj]
                  simp [Ne.symm hb]

/-- **EVERY LINK IN THE DECLARATIONS OF ALL**: its list of arrays keeps every name that its own
declaration gave, and what it declared stays declared, by name, rows and columns. -/
theorem declareLinks_atAny {links : Array LinkH} {NGr : Nat} {p4 : Bool}
    {r : Array LinkH × Array FrameLink} (h : declareLinks links NGr p4 = .ok r) {n : Nat}
    {Y : LinkH} (hY : links[n]? = some Y) :
    ∃ (d : Declaring) (s1 : Array (Nat × String)) (Dn : FrameLink), declareOwn Y n = .ok d ∧
      (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
        s1[u]? = some c) ∧
      r.1[n]? = some { Y with arrayOf := s1 } ∧ r.2[n]? = some Dn ∧
      ∀ a, Decl d.moment a → DeclLike Dn.moment a := by
  unfold declareLinks at h
  obtain ⟨st, hr, h⟩ := ok_of_bind h
  obtain ⟨declared, named⟩ := st
  obtain rfl : (named, declared) = r := Except.ok.inj h
  have K := forIn_keeps _ links.toList.zipIdx
    (fun pr (s : MProd (Array FrameLink) (Array LinkH)) =>
      s.fst.size = pr.length ∧ s.snd.size = pr.length ∧
      ∀ (j : Nat) (X : LinkH) (l : Nat), pr[j]? = some (X, l) →
        ∃ (d : Declaring) (s1 : Array (Nat × String)) (Dn : FrameLink), declareOwn X l = .ok d ∧
          (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
            s1[u]? = some c) ∧
          s.snd[j]? = some { X with arrayOf := s1 } ∧ s.fst[j]? = some Dn ∧
          ∀ a, Decl d.moment a → DeclLike Dn.moment a) ?_
    links.toList.zipIdx [] _ _ rfl ⟨rfl, rfl, fun j X l c => by
      have c' : ([] : List (LinkH × Nat))[j]? = some (X, l) := c
      rw [List.getElem?_nil] at c'
      cases c'⟩ hr
  · obtain ⟨-, -, k3⟩ := K
    exact k3 n Y n (by simp [List.getElem?_zipIdx, hY])
  · intro pr a rest e s s' hI hs
    obtain ⟨i1, i2, i3⟩ := hI
    obtain ⟨X, l⟩ := a
    obtain ⟨d, hd, hs⟩ := ok_of_bind hs
    obtain ⟨s2, h2, hs⟩ := ok_of_bind hs
    obtain ⟨-, hs⟩ := ok_of_jp hs
    have J := forIn_keeps _ (zipT X.tl.ix.FT.toList X.tl.plFor.toList)
      (fun _ (x : Array (Nat × String) × Array FrameLink) =>
        (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
          x.1[u]? = some c) ∧ x.2.size = s.fst.size ∧
        ∀ (j : Nat) (D : FrameLink), s.fst[j]? = some D →
          ∃ D', x.2[j]? = some D' ∧ ∀ a, DeclLike D.moment a → DeclLike D'.moment a) ?_
      (zipT X.tl.ix.FT.toList X.tl.plFor.toList) [] _ _ rfl
      ⟨fun _ _ hu _ => hu, rfl, fun j D hj => ⟨D, hj, fun _ k => k⟩⟩ h2
    · obtain ⟨j1, j2, j3⟩ := J
      refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_, ?_⟩
      · show (s2.2.push _).size = _
        simp [j2, i1]
      · show (s.snd.push _).size = _
        simp [i2]
      · intro j X' l' hl
        by_cases hj : j < pr.length
        · rw [List.getElem?_append_left hj] at hl
          obtain ⟨d', s1, Dn, b1, b2, b3, b4, b5⟩ := i3 j X' l' hl
          obtain ⟨D', c1, c2⟩ := j3 j Dn b4
          refine ⟨d', s1, D', b1, b2, ?_, ?_, fun a k => c2 a (b5 a k)⟩
          · show (s.snd.push _)[j]? = _
            rw [Array.getElem?_push_lt (by omega)]
            rw [← b3, Array.getElem?_eq_getElem (by omega)]
          · show (s2.2.push _)[j]? = _
            rw [Array.getElem?_push_lt (by omega)]
            rw [← c1, Array.getElem?_eq_getElem (by omega)]
        · have hj' : j = pr.length := by
            by_contra c
            rw [List.getElem?_eq_none (by simp; omega)] at hl
            cases hl
          subst hj'
          obtain ⟨rfl, rfl⟩ : X = X' ∧ l = l' := by simpa using hl
          refine ⟨d, s2.1, { name := X.name, moment := d.moment }, hd, j1, ?_, ?_,
            fun a k => DeclLike.of k⟩
          · show (s.snd.push _)[pr.length]? = _
            rw [← i2]
            simp
          · show (s2.2.push _)[pr.length]? = _
            rw [← i1, ← j2]
            simp
    · intro pr2 a2 rest2 e2 x x' hJ hx
      obtain ⟨tree, pl⟩ := a2
      obtain ⟨y, hy, hx⟩ := ok_of_bind hx
      obtain ⟨f1, f2⟩ := foreign_keeps hy
      refine ⟨y, (Except.ok.inj hx).symm, fun u c hu hc => f1 u c (hJ.1 u c hu hc) hc,
        f2.trans hJ.2.1, fun j D hj => ?_⟩
      obtain ⟨D', c1, c2⟩ := hJ.2.2 j D hj
      obtain ⟨D'', c3, c4⟩ := foreign_like hy j D' c1
      exact ⟨D'', c3, fun a k => c4 a (c2 a k)⟩

/-- **BEHIND AN ACCEPT OF THE PUBLIC TESTS ON THE LINKS' STRUCTURES, AT EVERY LINK WHOSE RECORD
NAMES A THIRD VECTOR**: it stands in the link's list of arrays under the name "U3" of that link, and
the given layout has an array of that name there, with the rows and columns of the plan's array. -/
theorem reads_named_at {l₀ : Array LinkH} {NGr : Nat} {p4 : Bool} {ws : OnBytes.Model.WsLay}
    {first : Params.First} {B : LinksH} (hB : buildLinksH l₀ NGr p4 ws first = .ok B) {n t : Nat}
    {Y : LinkH} (hY : l₀[n]? = some Y) (hU : Y.tl.ix.U.getD 2 none = some t) :
    (∃ b, B.links[n]? = some b ∧ b.arrayOf[t]? = some (n, "U3")) ∧
      ∃ tr A, Y.Fp.trees[t]? = some tr ∧ reqArray first.layout n "U3" = some A ∧
        A.sizeI = tr.R ∧ A.sizeC = tr.K := by
  unfold buildLinksH at hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨⟨links', declared⟩, hd, hB⟩ := ok_of_bind hB
  obtain ⟨u, hh, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, hB⟩ := ok_of_jp hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  cases hB
  cases u
  obtain ⟨d, s1, Dn, a1, a2, a3, a4, a5⟩ := declareLinks_atAny hd hY
  obtain ⟨g1, tr, m, g2, g3⟩ := declareOwn_reads a1 hU
  obtain ⟨a', k1, n1, n2, n3⟩ := a5 _ g3
  obtain ⟨L, arrays, _, b2, b3⟩ := heldAgainst_at hh a4
  obtain ⟨A, c1, c2, c3⟩ := linkHeld_at b3 k1
  refine ⟨⟨_, a3, a2 t _ g1 rfl⟩, tr, A, g2, ?_, c2.trans n2, c3.trans n3⟩
  unfold reqArray
  rw [b2]
  rw [n1] at c1
  exact c1

end P1K2

#print axioms P1K2.DeclLike.of
#print axioms P1K2.keptUpTo_like
#print axioms P1K2.foreign_like
#print axioms P1K2.declareLinks_atAny
#print axioms P1K2.reads_named_at
