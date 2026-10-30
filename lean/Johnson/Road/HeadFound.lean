-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadFound.lean: in the output head's list of lookup calls no segment's name occurs
twice, so every segment is the one that its name finds.

The verifier's routines name a segment by a string: callNo (OnBytes/Model/HeadHeard.lean) takes the
first call that has a segment with the name, and CallD.seg? (OnBytes/Model/Calls.lean) the first
such segment of a call. Johnson/Road/HeadLaid.lean shows that each of the nine names has a call and
a segment. This file shows the converse for a layout that the verifier returns: each segment of each
call is found under its own name, at its own call.

How. The function that reads the lines of the calls (callsFrom, with lineSegs, in
OnBytes/Model/HeadLayout.lean) keeps the list of the names met so far and refuses a name that is in
it. So the names of one line are apart from each other and from all names met before.

Main theorems: place_names; lineSegs_names; segFind_of_nodup; callsFrom_found; callsOf_from;
found_of_layout (each segment is found under its name); callsFrom_nodup, names_nodup_of_layout (the
names of a call's segments are apart, so no segment stands twice in a call); member_of_layout,
names_of_layout (it has the name and the length of a member of the head's list); cols_of_layout (a
call has 2^lJ columns); calls_le_six.

What is not claimed. Nothing on the columns of two segments being apart, and nothing on what a
segment holds. That layout returns a value is a hypothesis. The program does not import this file.
-/
import Johnson.Road.HeadLaid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-- A function of the members alone, mapped over a list with numbers. -/
theorem zipIdx_map_fst {α β : Type} (f : α → β) : ∀ (l : List α) (k : ℕ),
    (l.zipIdx k).map (fun x => f x.1) = l.map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_fst f l (k + 1)]

/-- The names of a placed call's segments are the names that were to be placed, in their order. -/
theorem place_names (name kind : String) (asks : List Model.SegAsk) (fl : ℕ) :
    (Model.place name kind asks fl).segs.map (·.name) = asks.map (·.1) := by
  have e : (Model.place name kind asks fl).segs.map (·.name) =
      (asks.zipIdx 0).map (fun x => (fun a : Model.SegAsk => a.1) x.1) := by
    show (List.map _ (List.map _ asks.zipIdx)) = _
    rw [List.map_map]
    rfl
  rw [e]
  exact zipIdx_map_fst _ asks 0

/-- What one line of the calls takes, by name: the names of the line, which are apart from each
other and from the names met before; and the names met after it are these and those. -/
theorem lineSegs_names (sd : List (String × String × ℕ)) (kind : String) :
    ∀ (ns seen : List String) (r : List Model.SegAsk × List String),
      Model.Head.lineSegs sd kind ns seen = some r →
      r.1.map (·.1) = ns ∧ ns.Nodup ∧ (∀ n ∈ ns, n ∉ seen) ∧
        ∀ n, n ∈ r.2 ↔ n ∈ ns ∨ n ∈ seen
  | [], seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact ⟨rfl, List.nodup_nil, fun n hn => (by cases hn), fun n => (by simp)⟩
  | n0 :: ns, seen, r, h => by
    rw [Model.Head.lineSegs] at h
    split at h
    · cases h
    · rename_i x hf
      split at h
      · cases h
      · rename_i hc
        have hn0 : n0 ∉ seen := fun hm => hc (by simp [hm])
        cases hr : Model.Head.lineSegs sd kind ns (n0 :: seen) with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : ((n0, x.2.2, false) :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          obtain ⟨i1, i2, i3, i4⟩ := lineSegs_names sd kind ns (n0 :: seen) r' hr
          refine ⟨?_, ?_, ?_, ?_⟩
          · show n0 :: r'.1.map (·.1) = n0 :: ns
            rw [i1]
          · exact List.nodup_cons.mpr ⟨fun hm => i3 n0 hm List.mem_cons_self, i2⟩
          · intro n hn hm
            rcases List.mem_cons.mp hn with e | hn'
            · rw [e] at hm
              exact hn0 hm
            · exact i3 n hn' (List.mem_cons_of_mem _ hm)
          · intro n
            show n ∈ r'.2 ↔ _
            rw [i4 n]
            simp only [List.mem_cons]
            tauto

/-- In a list of segments whose names are apart, each segment is the first with its name. -/
theorem segFind_of_nodup : ∀ (l : List Model.Seg), (l.map (·.name)).Nodup → ∀ g ∈ l,
    l.find? (fun s => s.name == g.name) = some g
  | [], _, g, hg => by cases hg
  | s :: l, hn, g, hg => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hg with e | hg'
    · rw [e]
      simp
    · have hne : (s.name == g.name) = false := by
        have k : s.name ≠ g.name := by
          intro e
          apply hn.1
          rw [e]
          exact List.mem_map.mpr ⟨g, hg', rfl⟩
        simpa using k
      simp only [List.find?_cons, hne]
      exact segFind_of_nodup l hn.2 g hg'

/-- A call without a segment of the name finds none. -/
theorem seg_none {c : Model.CallD} {n : String} (h : ∀ g ∈ c.segs, g.name ≠ n) :
    c.seg? n = none :=
  List.find?_eq_none.mpr fun g hg => by simpa using h g hg

/-- What the lines of the calls give, by name: no segment has a name met before; and each segment of
each call is found under its name, at its call. There are as many calls as lines. -/
theorem callsFrom_found (sd : List (String × String × ℕ)) (fl : ℕ) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List Model.CallD × List String),
      Model.Head.callsFrom sd fl lines names seen = some r →
      r.1.length = lines.length ∧
      (∀ c ∈ r.1, ∀ g ∈ c.segs, g.name ∉ seen) ∧
      ∀ q c g, r.1[q]? = some c → g ∈ c.segs →
        r.1.findIdx? (fun c => (c.seg? g.name).isSome) = some q ∧ c.seg? g.name = some g
  | [], _, seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact ⟨rfl, fun c hc => (by cases hc), fun q c g hq => (by simp at hq)⟩
  | [] :: _, _, _, _, h => by cases h
  | [_] :: _, _, _, _, h => by cases h
  | [_, _] :: _, _, _, _, h => by cases h
  | (name :: kind :: s :: ss) :: rest, names, seen, r, h => by
    rw [Model.Head.callsFrom] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i asks seen' hl
        cases hr : Model.Head.callsFrom sd fl rest (name :: names) seen' with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : (Model.place name kind asks fl :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          obtain ⟨l1, l2, l3, l4⟩ := lineSegs_names sd kind (s :: ss) seen (asks, seen') hl
          obtain ⟨i0, i1, i2⟩ := callsFrom_found sd fl rest (name :: names) seen' r' hr
          have hP : (Model.place name kind asks fl).segs.map (·.name) = s :: ss :=
            (place_names name kind asks fl).trans l1
          have hPm : ∀ g ∈ (Model.place name kind asks fl).segs, g.name ∈ s :: ss := by
            intro g hg
            rw [← hP]
            exact List.mem_map.mpr ⟨g, hg, rfl⟩
          have hPf : ∀ g ∈ (Model.place name kind asks fl).segs,
              (Model.place name kind asks fl).seg? g.name = some g := by
            intro g hg
            exact segFind_of_nodup _ (by rw [hP]; exact l2) g hg
          refine ⟨?_, ?_, ?_⟩
          · show r'.1.length + 1 = rest.length + 1
            rw [i0]
          · intro c hc g hg
            rcases List.mem_cons.mp hc with e | hc'
            · rw [e] at hg
              exact l3 _ (hPm g hg)
            · exact fun hm => i1 c hc' g hg ((l4 _).2 (Or.inr hm))
          · intro q c g hq hg
            cases q with
            | zero =>
              have e : Model.place name kind asks fl = c := by simpa using hq
              subst e
              refine ⟨?_, hPf g hg⟩
              rw [List.findIdx?_cons, if_pos (by rw [hPf g hg]; rfl)]
            | succ q =>
              have hq' : r'.1[q]? = some c := by simpa using hq
              obtain ⟨f1, f2⟩ := i2 q c g hq' hg
              refine ⟨?_, f2⟩
              have hfresh : g.name ∉ seen' := i1 c (List.mem_of_getElem? hq') g hg
              have hno : (Model.place name kind asks fl).seg? g.name = none :=
                seg_none fun g' hg' e => hfresh ((l4 _).2 (Or.inl (e ▸ hPm g' hg')))
              rw [List.findIdx?_cons, if_neg (by rw [hno]; simp), f1]
              rfl

/-- The names of the segments of each call that the lines give are apart from each other. -/
theorem callsFrom_nodup (sd : List (String × String × ℕ)) (fl : ℕ) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List Model.CallD × List String),
      Model.Head.callsFrom sd fl lines names seen = some r →
      ∀ c ∈ r.1, (c.segs.map (·.name)).Nodup
  | [], _, seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact fun c hc => (by cases hc)
  | [] :: _, _, _, _, h => by cases h
  | [_] :: _, _, _, _, h => by cases h
  | [_, _] :: _, _, _, _, h => by cases h
  | (name :: kind :: s :: ss) :: rest, names, seen, r, h => by
    rw [Model.Head.callsFrom] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i asks seen' hl
        cases hr : Model.Head.callsFrom sd fl rest (name :: names) seen' with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : (Model.place name kind asks fl :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          obtain ⟨l1, l2, -, -⟩ := lineSegs_names sd kind (s :: ss) seen (asks, seen') hl
          intro c hc
          rcases List.mem_cons.mp hc with e | hc'
          · rw [e, place_names, l1]
            exact l2
          · exact callsFrom_nodup sd fl rest (name :: names) seen' r' hr c hc'

/-- The calls that callsOf returns are read by callsFrom from at most six lines, with nothing met
before. -/
theorem callsOf_from {h : Model.Head.Shape} {L : Model.Head.HL} {cs : List Model.CallD}
    (hc : Model.Head.callsOf h L = .ok cs) :
    ∃ fl lines seen, lines.length ≤ 6 ∧
      Model.Head.callsFrom (Model.Head.segments h L) fl lines [] [] = some (cs, seen) := by
  unfold Model.Head.callsOf at hc
  obtain ⟨e6, hc⟩ := ok_of_needed hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i calls seen hf
    obtain ⟨-, hc⟩ := ok_of_needed hc
    cases hc
    exact ⟨_, _, seen, of_decide_eq_true e6, hf⟩

section Layout
variable {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
  (hy : Model.Head.layout h tauFC = .ok L)
include hy

/-- **Each segment of each call is the one that its name finds.** -/
theorem found_of_layout {q : ℕ} (hq : q < L.calls.size) {g : Model.Seg}
    (hg : g ∈ (L.calls.getD q default).segs) :
    Model.Head.callNo L g.name = some q ∧ (L.calls.getD q default).seg? g.name = some g := by
  obtain ⟨cs, hc, -, hL⟩ := (admittedH_of_layout hy).calls
  obtain ⟨fl, lines, seen, -, hf⟩ := callsOf_from hc
  obtain ⟨-, -, F3⟩ := callsFrom_found _ _ _ [] [] (cs, seen) hf
  rw [hL] at hq hg ⊢
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e] at hg ⊢
  obtain ⟨f1, f2⟩ := F3 q cs[q] g (by simp [hq']) hg
  refine ⟨?_, f2⟩
  unfold Model.Head.callNo
  rw [hL]
  simpa using f1

/-- **The names of a call's segments are apart from each other**: no segment stands twice in a
call's list. -/
theorem names_nodup_of_layout {q : ℕ} (hq : q < L.calls.size) :
    ((L.calls.getD q default).segs.map (·.name)).Nodup := by
  obtain ⟨cs, hc, -, hL⟩ := (admittedH_of_layout hy).calls
  obtain ⟨fl, lines, seen, -, hf⟩ := callsOf_from hc
  rw [hL] at hq ⊢
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e]
  exact callsFrom_nodup _ _ _ [] [] (cs, seen) hf cs[q] (List.getElem_mem hq')

/-- **Each segment of each call has the name and the length of a member of the head's list of
segments.** -/
theorem member_of_layout {q : ℕ} (hq : q < L.calls.size) {g : Model.Seg}
    (hg : g ∈ (L.calls.getD q default).segs) :
    ∃ x ∈ Model.Head.segments h L, g.name = x.1 ∧ g.n = x.2.2 := by
  obtain ⟨cs, hc, -, hL⟩ := (admittedH_of_layout hy).calls
  obtain ⟨c1, -⟩ := callsOf_spec hc
  rw [hL] at hq hg
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e] at hg
  obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq')
  rw [e1] at hg
  obtain ⟨a, ha, a1, a2, -⟩ := place_segs name kind asks fl g hg
  obtain ⟨x, f1, f2⟩ := e2 a ha
  have hx1 : x.1 = a.1 := by simpa using List.find?_some f1
  exact ⟨x, List.mem_of_find?_eq_some f1, a1.trans hx1.symm, a2.trans f2⟩

/-- The name alone. -/
theorem names_of_layout {q : ℕ} (hq : q < L.calls.size) {g : Model.Seg}
    (hg : g ∈ (L.calls.getD q default).segs) : ∃ x ∈ Model.Head.segments h L, g.name = x.1 := by
  obtain ⟨x, hx, e, -⟩ := member_of_layout hy hq hg
  exact ⟨x, hx, e⟩

/-- **A call has 2^lJ columns.** -/
theorem cols_of_layout {q : ℕ} (hq : q < L.calls.size) :
    (L.calls.getD q default).J = 2 ^ (L.calls.getD q default).lJ := by
  obtain ⟨cs, hc, -, hL⟩ := (admittedH_of_layout hy).calls
  obtain ⟨c1, -⟩ := callsOf_spec hc
  rw [hL] at hq ⊢
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e]
  obtain ⟨name, kind, asks, fl, e1, -⟩ := c1 cs[q] (List.getElem_mem hq')
  rw [e1]
  rfl

/-- **There are at most six calls.** -/
theorem calls_le_six : L.calls.size ≤ 6 := by
  obtain ⟨cs, hc, -, hL⟩ := (admittedH_of_layout hy).calls
  obtain ⟨fl, lines, seen, h6, hf⟩ := callsOf_from hc
  obtain ⟨F1, -, -⟩ := callsFrom_found _ _ _ [] [] (cs, seen) hf
  rw [hL]
  have e : cs.toArray.size = cs.length := by simp
  rw [e]
  have F1' : cs.length = lines.length := F1
  omega

end Layout

#print axioms found_of_layout
#print axioms names_nodup_of_layout
#print axioms member_of_layout
#print axioms cols_of_layout
#print axioms calls_le_six

end OnBytes.Road.Hd
