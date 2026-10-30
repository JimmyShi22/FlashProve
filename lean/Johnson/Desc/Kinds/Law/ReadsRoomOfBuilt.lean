-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsRoomOfBuilt.lean: WHAT AN ACCEPT OF THE PUBLIC TESTS ON THE SEGMENTS'
STRUCTURES (OnBytes/Model/StagesLinks.lean: buildLinksH) SAYS OF THE LAST SEGMENT's VECTOR OF READS:
under which name it stands in the segment's list of arrays, and that the request's layout has an
array of that name with the plan's rows and columns. Statements and proofs.

How. No routine is evaluated. ONE INVARIANT carries it: namesH refuses to name an array twice, so an
entry of a list of arrays, once named, never turns; and a declared array, once pushed, stays in its
moment. The sizes come by heldAgainst (linkHeld, arrayHeld: the given layout against the
declarations), not by linksFit, which asks only that an array is laid.

  namesH_sets, namesH_keeps     the invariant at its root.
  Decl                          "an array is declared at some moment"; kept by push and modify.
  own_sets, own_keeps           one declaration.
  ReadsGood, declareOwn_reads   a segment's own declaration names its third vector "U3", with the
                                rows and columns of the plan's array.
  foreign_keeps                 naming an array that an earlier segment sent keeps the names given.
  declareLinks_atLast           the last segment in the declarations of all: nothing runs behind
                                it.
  heldAgainst_at, linkHeld_at   the given layout against the declarations, at one segment and array.
  reads_named_of_built          MAIN.

WHAT IT IS NOT. An implication from an accept of buildLinksH; general in the segments' structures:
no scope, no public part. AT THE LAST SEGMENT ALONE (an earlier segment's declaration is turned by
later readers). Of the eleven arrays of the head's list it names ONE. Nothing on soundness.
LETTERS. Under "there is": tr, A (MAIN): pinned by equations; d, s1 (declareLinks_atLast): d by an
equation, s1 by the list's entry n; L, arrays, A (heldAgainst_at, linkHeld_at): by equations.

-/
import OnBytes.TieK.LinksEnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Built

open OnBytes OnBytes.Model.Stages
open OnBytes.TieK (ok_of_bind ok_of_jp forIn_keeps)

/-- **A name, once given, is there.** -/
theorem namesH_sets {ar ar' : Array (Nat × String)} {t born : Nat} {name : String}
    (h : namesH ar t born name = .ok ar') : ar'[t]? = some (born, name) := by
  unfold namesH at h
  cases e : ar[t]? with
  | none =>
    rw [e] at h
    cases h
  | some a =>
    rw [e] at h
    dsimp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      have ht : t < ar.size := by
        by_contra c
        rw [Array.getElem?_eq_none (by omega)] at e
        cases e
      simp [ht]
    · cases h

/-- **A name, once given, stays**: the routine refuses to name an array twice. -/
theorem namesH_keeps {ar ar' : Array (Nat × String)} {t born : Nat} {name : String}
    (h : namesH ar t born name = .ok ar') {u : Nat} {c : Nat × String} (hu : ar[u]? = some c)
    (hc : c.2.isEmpty = false) : ar'[u]? = some c := by
  unfold namesH at h
  cases e : ar[t]? with
  | none =>
    rw [e] at h
    cases h
  | some a =>
    rw [e] at h
    dsimp only at h
    split at h
    · rename_i ha
      obtain rfl := Except.ok.inj h
      have hne : t ≠ u := by
        rintro rfl
        rw [e] at hu
        obtain rfl := Option.some.inj hu
        rw [hc] at ha
        cases ha
      simp [hne, hu]
    · cases h

/-- An array is declared at some moment. -/
def Decl (mo : Array (Array FrameArray)) (a : FrameArray) : Prop :=
  ∃ (j : Nat) (M : Array FrameArray), mo[j]? = some M ∧ a ∈ M.toList

theorem Decl.push {mo : Array (Array FrameArray)} {a : FrameArray} (h : Decl mo a)
    (M : Array FrameArray) : Decl (mo.push M) a := by
  obtain ⟨j, M0, hj, ha⟩ := h
  refine ⟨j, M0, ?_, ha⟩
  have hlt : j < mo.size := by
    by_contra c
    rw [Array.getElem?_eq_none (by omega)] at hj
    cases hj
  rw [Array.getElem?_push_lt hlt]
  rw [Array.getElem?_eq_getElem hlt] at hj
  exact hj

theorem Decl.modify {mo : Array (Array FrameArray)} {a : FrameArray} (h : Decl mo a) (i : Nat)
    (b : FrameArray) : Decl (mo.modify i (·.push b)) a := by
  obtain ⟨j, M0, hj, ha⟩ := h
  by_cases e : i = j
  · subst e
    refine ⟨i, M0.push b, ?_, ?_⟩
    · rw [Array.getElem?_modify, if_pos rfl, hj]
      rfl
    · simp [ha]
  · refine ⟨j, M0, ?_, ha⟩
    rw [Array.getElem?_modify, if_neg e, hj]

/-- **What one declaration sets.** -/
theorem own_sets {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') (h0 : 0 < d.moment.size) :
    d'.arrayOf[tree]? = some (l, name) ∧ ∃ t n, X.Fp.trees[tree]? = some t ∧
      Decl d'.moment { name := name, rows := t.R, columns := t.K, overE := n } := by
  unfold own at h
  obtain ⟨ar, h1, h⟩ := ok_of_bind h
  cases e1 : X.Fp.trees[tree]? with
  | none =>
    simp only [e1] at h
    cases h
  | some t =>
    cases e2 : X.Tp.nt[tree]? with
    | none =>
      simp only [e1, e2] at h
      cases h
    | some n =>
      simp only [e1, e2] at h
      obtain rfl := Except.ok.inj h
      refine ⟨namesH_sets h1, t, n.ec == 3, rfl, d.moment.size - 1, ?_⟩
      have hlt : d.moment.size - 1 < d.moment.size := by omega
      refine ⟨(d.moment[d.moment.size - 1]'hlt).push
        { name := name, rows := t.R, columns := t.K, overE := n.ec == 3 }, ?_, by simp⟩
      rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_eq_getElem hlt]
      rfl

/-- **What one declaration keeps.** -/
theorem own_keeps {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
      d'.arrayOf[u]? = some c) ∧
      (∀ a, Decl d.moment a → Decl d'.moment a) ∧ d'.moment.size = d.moment.size := by
  unfold own at h
  obtain ⟨ar, h1, h⟩ := ok_of_bind h
  cases e1 : X.Fp.trees[tree]? with
  | none =>
    simp only [e1] at h
    cases h
  | some t =>
    cases e2 : X.Tp.nt[tree]? with
    | none =>
      simp only [e1, e2] at h
      cases h
    | some n =>
      simp only [e1, e2] at h
      obtain rfl := Except.ok.inj h
      exact ⟨fun u c hu hc => namesH_keeps h1 hu hc, fun a ha => ha.modify _ _, by simp⟩

/-- What is wanted of a declaration in the making: array t bears the name "U3" of link l, and an
array of that name is declared with the rows and columns of the plan's array t. -/
def ReadsGood (X : LinkH) (l t : Nat) (d : Declaring) : Prop :=
  d.arrayOf[t]? = some (l, "U3") ∧ ∃ tr n, X.Fp.trees[t]? = some tr ∧
    Decl d.moment { name := "U3", rows := tr.R, columns := tr.K, overE := n }

theorem ReadsGood.own {X : LinkH} {l t : Nat} {d d' : Declaring} (G : ReadsGood X l t d)
    {tree : Nat} {name : String} (h : own X l d tree name = .ok d') : ReadsGood X l t d' := by
  obtain ⟨k1, k2, _⟩ := own_keeps h
  obtain ⟨g1, tr, n, g2, g3⟩ := G
  exact ⟨k1 _ _ g1 rfl, tr, n, g2, k2 _ g3⟩

theorem ReadsGood.next {X : LinkH} {l t : Nat} {d : Declaring} (G : ReadsGood X l t d) :
    ReadsGood X l t d.nextMoment := by
  obtain ⟨g1, tr, n, g2, g3⟩ := G
  exact ⟨g1, tr, n, g2, g3.push _⟩

/-- **The segment's own declaration names its third vector "U3".** -/
theorem declareOwn_reads {X : LinkH} {l t : Nat} {d : Declaring} (h : declareOwn X l = .ok d)
    (hU : X.tl.ix.U.getD 2 none = some t) : ReadsGood X l t d := by
  unfold declareOwn at h
  dsimp only at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨d1, -, h⟩ := ok_of_bind h
  obtain ⟨d2, -, h⟩ := ok_of_bind h
  obtain ⟨d3, h3, h⟩ := ok_of_bind h
  obtain ⟨d4, h4, h⟩ := ok_of_bind h
  obtain ⟨d5, h5, h⟩ := ok_of_bind h
  obtain rfl := Except.ok.inj h
  have hmem : ((some t : Option Nat), 2) ∈ (X.tl.ix.U.toList.take 4).zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_take_of_lt (by decide)]
    have e : X.tl.ix.U[2]? = some (some t) := by
      cases c : X.tl.ix.U[2]? with
      | none =>
        rw [Array.getD_eq_getD_getElem?, c] at hU
        cases hU
      | some v =>
        rw [Array.getD_eq_getD_getElem?, c] at hU
        exact congrArg some hU
    simpa using e
  have K : ((some t : Option Nat), 2) ∈ (X.tl.ix.U.toList.take 4).zipIdx → ReadsGood X l t d3 := by
    refine forIn_keeps _ (X.tl.ix.U.toList.take 4).zipIdx
      (fun pr (s : Declaring) => ((some t : Option Nat), 2) ∈ pr → ReadsGood X l t s) ?_
      (X.tl.ix.U.toList.take 4).zipIdx [] _ _ rfl (fun c => absurd c (by simp)) h3
    intro pr a rest e s s' hI hs
    obtain ⟨u, n⟩ := a
    cases u with
    | none =>
      refine ⟨s, (Except.ok.inj hs).symm, fun hm => hI ?_⟩
      rcases List.mem_append.1 hm with c | c
      · exact c
      · simp at c
    | some tree =>
      obtain ⟨d', ho, hs⟩ := ok_of_bind hs
      refine ⟨d', (Except.ok.inj hs).symm, fun hm => ?_⟩
      rcases List.mem_append.1 hm with c | c
      · exact (hI c).next.own ho
      · obtain ⟨rfl, rfl⟩ : t = tree ∧ 2 = n := by simpa using c
        obtain ⟨o1, tr, m, o2, o3⟩ := own_sets ho (by simp [Declaring.nextMoment])
        have e3 : ("U" ++ toString ((2 : Nat) + 1) : String) = "U3" := by decide
        rw [show ("U" ++ toString (((some t : Option Nat), 2).2 + 1) : String) = "U3" from e3]
          at o1 o3
        exact ⟨o1, tr, m, o2, o3⟩
  exact ((K hmem).next.own h4).own h5

/-- **Naming an array that an earlier segment sent keeps every name given**, and the number of the
declarations. -/
theorem foreign_keeps {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : OnBytes.Model.PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    (∀ (u : Nat) (c : Nat × String), s.1[u]? = some c → c.2.isEmpty = false →
      s'.1[u]? = some c) ∧ s'.2.size = s.2.size := by
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
              | some D =>
                simp only [e7] at h
                obtain ⟨D', -, h⟩ := ok_of_bind h
                obtain rfl := Except.ok.inj h
                exact ⟨fun u c hu hc => namesH_keeps h1 hu hc, by simp⟩

/-- **The last segment in the declarations of all**: its own declaration stands as it was made, and
its list of arrays keeps every name that its own declaration gave. -/
theorem declareLinks_atLast {links : Array LinkH} {NGr : Nat} {p4 : Bool}
    {r : Array LinkH × Array FrameLink} (h : declareLinks links NGr p4 = .ok r) {n : Nat}
    {Y : LinkH} (hn : links.size = n + 1) (hY : links[n]? = some Y) :
    ∃ (d : Declaring) (s1 : Array (Nat × String)), declareOwn Y n = .ok d ∧
      (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
        s1[u]? = some c) ∧
      r.1[n]? = some { Y with arrayOf := s1 } ∧
      r.2[n]? = some { name := Y.name, moment := d.moment } ∧ r.2.size = n + 1 := by
  unfold declareLinks at h
  obtain ⟨st, hr, h⟩ := ok_of_bind h
  obtain ⟨declared, named⟩ := st
  obtain rfl : (named, declared) = r := Except.ok.inj h
  have K := forIn_keeps _ links.toList.zipIdx
    (fun pr (s : MProd (Array FrameLink) (Array LinkH)) =>
      s.fst.size = pr.length ∧ s.snd.size = pr.length ∧ ∀ X l, pr.getLast? = some (X, l) →
        ∃ (d : Declaring) (s1 : Array (Nat × String)), declareOwn X l = .ok d ∧
          (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
            s1[u]? = some c) ∧
          s.snd.back? = some { X with arrayOf := s1 } ∧
          s.fst.back? = some { name := X.name, moment := d.moment }) ?_
    links.toList.zipIdx [] _ _ rfl ⟨rfl, rfl, fun X l c => by simp at c⟩ hr
  · obtain ⟨k1, k2, k3⟩ := K
    have hlen : links.toList.zipIdx.length = n + 1 := by simp [hn]
    have hlast : links.toList.zipIdx.getLast? = some (Y, n) := by
      rw [List.getLast?_eq_getElem?, hlen]
      simp [List.getElem?_zipIdx, hY]
    obtain ⟨d, s1, a1, a2, a3, a4⟩ := k3 Y n hlast
    refine ⟨d, s1, a1, a2, ?_, ?_, by rw [k1, hlen]⟩
    · rw [Array.back?_eq_getElem?, k2, hlen] at a3
      exact a3
    · rw [Array.back?_eq_getElem?, k1, hlen] at a4
      exact a4
  · intro pr a rest e s s' hI hs
    obtain ⟨i1, i2, -⟩ := hI
    obtain ⟨X, l⟩ := a
    obtain ⟨d, hd, hs⟩ := ok_of_bind hs
    obtain ⟨s2, h2, hs⟩ := ok_of_bind hs
    obtain ⟨-, hs⟩ := ok_of_jp hs
    have J := forIn_keeps _ (zipT X.tl.ix.FT.toList X.tl.plFor.toList)
      (fun _ (x : Array (Nat × String) × Array FrameLink) =>
        (∀ (u : Nat) (c : Nat × String), d.arrayOf[u]? = some c → c.2.isEmpty = false →
          x.1[u]? = some c) ∧ x.2.size = s.fst.size) ?_
      (zipT X.tl.ix.FT.toList X.tl.plFor.toList) [] _ _ rfl ⟨fun _ _ hu _ => hu, rfl⟩ h2
    · obtain ⟨j1, j2⟩ := J
      refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_, ?_⟩
      · show (s2.2.push _).size = _
        simp [j2, i1]
      · show (s.snd.push _).size = _
        simp [i2]
      · intro X' l' hl
        obtain ⟨rfl, rfl⟩ : X = X' ∧ l = l' := by simpa using hl
        exact ⟨d, s2.1, hd, j1, by simp, by simp⟩
    · intro pr2 a2 rest2 e2 x x' hJ hx
      obtain ⟨tree, pl⟩ := a2
      obtain ⟨y, hy, hx⟩ := ok_of_bind hx
      obtain ⟨f1, f2⟩ := foreign_keeps hy
      exact ⟨y, (Except.ok.inj hx).symm, fun u c hu hc => f1 u c (hJ.1 u c hu hc) hc,
        f2.trans hJ.2⟩

/-- **What the comparison of the given layout with the declarations says at one segment.** -/
theorem heldAgainst_at {declared : Array FrameLink} {p : Params.First}
    (h : heldAgainst declared p = .ok ()) {n : Nat} {D : FrameLink} (hD : declared[n]? = some D) :
    ∃ L arrays, p.shape.link[n]? = some L ∧ p.layout.link[n]? = some arrays ∧
      linkHeld D L arrays = true := by
  unfold heldAgainst at h
  split at h
  · rename_i c
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at c
    obtain ⟨⟨c1, c2⟩, c3⟩ := c
    have hlt : n < declared.size := by
      by_contra x
      rw [Array.getElem?_eq_none (by omega)] at hD
      cases hD
    have l1 : n < p.shape.link.length := by omega
    have l2 : n < p.layout.link.length := by omega
    refine ⟨p.shape.link[n], p.layout.link[n], List.getElem?_eq_getElem l1,
      List.getElem?_eq_getElem l2, ?_⟩
    refine c3 (D, p.shape.link[n], p.layout.link[n]) ?_
    rw [zipT_eq, zipT_eq]
    refine List.mem_iff_getElem?.2 ⟨n, ?_⟩
    simp [List.getElem?_zip_eq_some, hD, l1, l2]
  · cases h

/-- **A declared array is laid out as declared.** -/
theorem linkHeld_at {D : FrameLink} {L : Params.ReqLink} {arrays : List Params.ReqArray}
    (h : linkHeld D L arrays = true) {a : FrameArray} (ha : Decl D.moment a) :
    ∃ A, (arrays.find? fun A => A.name == a.name) = some A ∧ A.sizeI = a.rows ∧
      A.sizeC = a.columns := by
  obtain ⟨j, M, hj, hm⟩ := ha
  unfold linkHeld at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩ := h
  have hz : (M, j) ∈ D.moment.toList.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simpa using hj
  have hA := h3 (M, j) hz
  have hA' : arrayHeld L.messages arrays j a = true := by
    rw [Array.all_eq_true_iff_forall_mem] at hA
    exact hA a (Array.mem_toList_iff.1 hm)
  unfold arrayHeld at hA'
  cases e : arrays.find? fun A => A.name == a.name with
  | none =>
    simp only [e] at hA'
    cases hA'
  | some A =>
    simp only [e, Bool.and_eq_true, beq_iff_eq] at hA'
    exact ⟨A, rfl, hA'.1.1.1.1, hA'.1.1.1.2⟩

/-- **BEHIND AN ACCEPT OF THE PUBLIC TESTS ON THE SEGMENTS' STRUCTURES: the last segment's third
vector stands in its list of arrays under the name "U3" of that segment, and the given layout has an
array of that name there, with the rows and columns of the plan's array.** -/
theorem reads_named_of_built {l₀ : Array LinkH} {NGr : Nat} {p4 : Bool} {ws : OnBytes.Model.WsLay}
    {first : Params.First} {B : LinksH} (hB : buildLinksH l₀ NGr p4 ws first = .ok B) {n t : Nat}
    {Y : LinkH} (hn : l₀.size = n + 1) (hY : l₀[n]? = some Y)
    (hU : Y.tl.ix.U.getD 2 none = some t) :
    ((B.links.map (·.arrayOf)).getD n #[])[t]? = some (n, "U3") ∧
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
  obtain ⟨d, s1, a1, a2, a3, a4, _⟩ := declareLinks_atLast hd hn hY
  obtain ⟨g1, tr, m, g2, g3⟩ := declareOwn_reads a1 hU
  obtain ⟨L, arrays, _, b2, b3⟩ := heldAgainst_at hh a4
  obtain ⟨A, c1, c2, c3⟩ := linkHeld_at b3 g3
  have a3' : links'[n]? = some { Y with arrayOf := s1 } := a3
  refine ⟨?_, tr, A, g2, ?_, c2, c3⟩
  · show ((links'.map (·.arrayOf)).getD n #[])[t]? = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, a3']
    exact a2 t _ g1 rfl
  · unfold reqArray
    rw [b2]
    exact c1

end VerifiableInference.Desc.Kinds.Head.Law.Built

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Built.declareOwn_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Built.declareLinks_atLast
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Built.reads_named_of_built
