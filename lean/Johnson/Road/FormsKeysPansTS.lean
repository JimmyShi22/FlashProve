-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPansTS.lean: the calls of the verifier's second walk over the panels are the
calls 0, 1, 2 and 5.

The theorems of Johnson/Road/FormsKeysPans.lean on the order of the verifier's panels take the list
TS of the calls of the second walk as a hypothesis: TS = [0, 1, 2, 5]. The check of a layer
sub-proof makes that list itself (callsTS in OnBytes/Model/Layer.lean): readsOf lists the names of
the calls that hold a segment with a term in the second token sumcheck, and callNo looks each name
up: it returns the number of the first call of that name. This file concludes the list.

What is compared with what: the verifier with itself, under the library's eight lines of calls
(LinesAre in FormsKeysPans.lean).

The way.
 1. No two calls of a layout that the verifier returns share a name: takeCalls, which reads the
    lines of the calls, refuses a name that it has seen (takeCalls_nodup), and the placing of a call
    keeps its name (callNames_nodup).
 2. In a list without a repeated name, the first member with the name of member i is member i
    (findIdx_nodup).
 3. The names that readsOf lists are those of the calls whose segments' names give a term
    (tscCalls_eq, filter_zip_map).
 4. With the library's lines and routed experts these are the calls 0, 1, 2 and 5, by evaluation on
    the families' names (ts_of_lines). So the hypothesis TS = [0, 1, 2, 5] holds of the list that
    the check makes (ts_eq).

What is asked, and what shows that it can be met: layout and readsOf return; there are routed
experts; the eight lines are the library's. Johnson/Road/FormsKeysPansRun.lean evaluates these, and
the conclusion, at a made-up shape. That is a run.

Main theorems: ts_of_lines, ts_eq; callNames_nodup, takeCalls_nodup, findIdx_nodup, tscCalls_eq.

What is not claimed: anything for other lines of calls, or without routed experts. The program does
not import this file.
-/
import Johnson.Road.FormsKeysPans
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysWorld

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (refuseIf CallD SegAsk place)
open OnBytes.Model.Layer (Lay Reads layout readsOf readsR takeSegments takeCalls)
open Inst.Model.FFSeg (fams)

/-! ## No two calls share a name -/

/-- The names of the calls that takeCalls returns are all different, and none is among the names
that it was given as seen. -/
theorem takeCalls_nodup (sd : List (String × String × ℕ × Bool)) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List (String × String × List SegAsk) × List String),
      takeCalls sd lines names seen = .ok r →
      (r.1.map (·.1)).Nodup ∧ ∀ n ∈ r.1.map (·.1), n ∉ names
  | [], _, _, _, h => by
    cases h
    exact ⟨List.nodup_nil, fun _ hn => absurd hn List.not_mem_nil⟩
  | ln :: rest, names, seen, r, h => by
    rcases ln with _ | ⟨name, _ | ⟨kind, _ | ⟨s, more⟩⟩⟩
    · cases h
    · cases h
    · cases h
    · have h : (do
          refuseIf (names.contains name) "policy-call-list"
          refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
          let a ← takeSegments sd kind (s :: more) seen
          let r ← takeCalls sd rest (name :: names) a.2
          pure ((name, kind, a.1) :: r.1, r.2)) = .ok r := h
      obtain ⟨h0, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨a', -, h⟩ := ok_of_bind h
      obtain ⟨r', h2, h⟩ := ok_of_bind h
      cases h
      obtain ⟨k1, k2⟩ := takeCalls_nodup sd rest (name :: names) a'.2 r' h2
      have hnot : name ∉ names := by
        intro hm
        have : names.contains name = true := List.contains_iff_mem.mpr hm
        rw [h0] at this
        cases this
      refine ⟨?_, ?_⟩
      · show (name :: r'.1.map (·.1)).Nodup
        exact List.nodup_cons.mpr ⟨fun hm => k2 name hm List.mem_cons_self, k1⟩
      · intro n hn
        have hn' : n ∈ name :: r'.1.map (·.1) := hn
        rcases List.mem_cons.mp hn' with e | hm
        · rw [e]
          exact hnot
        · exact fun hx => k2 n hm (List.mem_cons_of_mem _ hx)

/-- No two calls of a layout that the verifier returns, for a shape with routed experts, share a
name. -/
theorem callNames_nodup {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (h3 : h.p3 = true) : (y.calls.toList.map (·.name)).Nodup := by
  obtain ⟨cl, taken, ht, -, hc⟩ := (admitted_of_layout hy h3).calls
  have e : y.calls.toList.map (·.name) = taken.1.map (·.1) := by
    rw [hc, List.toList_toArray, List.map_map]
    exact List.map_congr_left fun _ _ => rfl
  rw [e]
  exact (takeCalls_nodup _ cl [] [] taken ht).1

/-! ## Looking a name up -/

/-- In a list whose members have different names, the first member with the name of member i is
member i. -/
theorem findIdx_nodup {α : Type} (f : α → String) : ∀ (l : List α), (l.map f).Nodup →
    ∀ (i : ℕ) (hi : i < l.length), l.findIdx? (fun c => f c == f l[i]) = some i
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: l, hn, 0, _ => by
    rw [List.findIdx?_cons]
    simp
  | a :: l, hn, i + 1, hi => by
    have hn' : f a ∉ l.map f ∧ (l.map f).Nodup := List.nodup_cons.mp hn
    have hi' : i < l.length := Nat.lt_of_succ_lt_succ hi
    have hne : (f a == f l[i]) = false := by
      cases hb : (f a == f l[i]) with
      | false => rfl
      | true =>
        exact absurd (List.mem_map.mpr ⟨l[i], List.getElem_mem hi', (beq_iff_eq.mp hb).symm⟩) hn'.1
    rw [List.findIdx?_cons]
    show (if (f a == f l[i]) = true then some 0
      else Option.map (fun i => i + 1) (l.findIdx? fun c => f c == f l[i])) = some (i + 1)
    rw [hne, if_neg Bool.false_ne_true, findIdx_nodup f l hn'.2 i hi']
    rfl

/-- The search in an array is the search in its list. -/
theorem findIdx_toList {α : Type} (p : α → Bool) (a : Array α) :
    a.findIdx? p = a.toList.findIdx? p := by
  cases a with
  | mk l => exact List.findIdx?_toArray p l

/-- callNo at the name of call number i of a layout without a repeated name. -/
theorem callNo_at {y : Lay} (hn : (y.calls.toList.map (·.name)).Nodup) {i : ℕ}
    (hi : i < y.calls.toList.length) : y.callNo (y.calls.toList[i]).name = some i := by
  unfold Lay.callNo
  rw [findIdx_toList]
  exact findIdx_nodup (·.name) y.calls.toList hn i hi

/-! ## The names that readsOf lists -/

/-- A list paired with its image, filtered by the image: the list filtered. -/
theorem filter_zip_map {α β γ : Type} (g : α → β) (P : β → Bool) (n : α → γ) : ∀ l : List α,
    ((l.zip (l.map g)).filter fun x => P x.2).map (fun x => n x.1) =
      (l.filter fun c => P (g c)).map n
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.zip_cons_cons, List.filter_cons, List.filter_cons]
    by_cases h : P (g a) = true
    · rw [if_pos h, if_pos h, List.map_cons, List.map_cons, filter_zip_map g P n l]
    · rw [if_neg h, if_neg h, filter_zip_map g P n l]

/-- The names that readsOf lists: those of the calls some segment of which has a term in the second
token sumcheck, by the segments' names. -/
theorem tscCalls_eq {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    rd.tscCalls = (y.calls.toList.filter fun c =>
      !((c.segs.map (·.name)).flatMap (readsR y.h.p3)).isEmpty).map (·.name) := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  show ((y.calls.toList.zip (y.calls.toList.map fun c =>
      c.segs.flatMap fun s => readsR y.h.p3 s.name)).filter fun x => !x.2.isEmpty).map
        (·.1.name) = _
  rw [filter_zip_map (fun c : CallD => c.segs.flatMap fun s => readsR y.h.p3 s.name)
    (fun x => !x.isEmpty) (·.name)]
  congr 1
  refine List.filter_congr fun c _ => ?_
  rw [flatMap_names]

/-! ## With the library's lines -/

/-- THE CALLS OF THE SECOND WALK. On a layout that the verifier returns for a shape with routed
experts, whose eight lines of calls are the library's: the list that the check of a layer sub-proof
makes, the names that readsOf lists, each looked up by callNo, is 0, 1, 2, 5. -/
theorem ts_of_lines {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (h3 : h.p3 = true) (hN : LinesAre y) {rd : Reads}
    (hr : readsOf y = .ok rd) :
    rd.tscCalls.mapM y.callNo = some [0, 1, 2, 5] := by
  have hn := callNames_nodup hy h3
  have hp : y.h.p3 = true := by
    rw [(admitted_of_layout hy h3).shape]
    exact h3
  have hlen : y.calls.toList.length = 8 := by
    have := congrArg List.length hN
    simpa using this
  have cn : ∀ i (hi : i < y.calls.toList.length),
      y.callNo (y.calls.toList[i]).name = some i := fun i hi => callNo_at hn hi
  rw [tscCalls_eq hr, hp]
  unfold LinesAre at hN
  generalize y.calls.toList = L at hN hlen cn
  rcases L with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, _ |
    ⟨c7, _ | ⟨c8, L⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hlen; done)
  have hN' : [c0.segs.map (·.name), c1.segs.map (·.name), c2.segs.map (·.name),
      c3.segs.map (·.name), c4.segs.map (·.name), c5.segs.map (·.name), c6.segs.map (·.name),
      c7.segs.map (·.name)] = [(fams 0).map segName, (fams 1).map segName, (fams 2).map segName,
      (fams 3).map segName, (fams 4).map segName, (fams 5).map segName, (fams 6).map segName,
      (fams 7).map segName] := hN
  simp only [List.cons.injEq, and_true] at hN'
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := hN'
  have f0 : (!((c0.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by rw [e0]; rfl
  have f1 : (!((c1.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by rw [e1]; rfl
  have f2 : (!((c2.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by rw [e2]; rfl
  have f3 : ¬ (!((c3.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by
    rw [e3]
    exact Bool.false_ne_true
  have f4 : ¬ (!((c4.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by
    rw [e4]
    exact Bool.false_ne_true
  have f5 : (!((c5.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by rw [e5]; rfl
  have f6 : ¬ (!((c6.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by
    rw [e6]
    exact Bool.false_ne_true
  have f7 : ¬ (!((c7.segs.map (·.name)).flatMap (readsR true)).isEmpty) = true := by
    rw [e7]
    exact Bool.false_ne_true
  rw [List.filter_cons, if_pos f0, List.filter_cons, if_pos f1, List.filter_cons, if_pos f2,
    List.filter_cons, if_neg f3, List.filter_cons, if_neg f4, List.filter_cons, if_pos f5,
    List.filter_cons, if_neg f6, List.filter_cons, if_neg f7, List.filter_nil]
  have a0 : y.callNo c0.name = some 0 := cn 0 (by simp)
  have a1 : y.callNo c1.name = some 1 := cn 1 (by simp)
  have a2 : y.callNo c2.name = some 2 := cn 2 (by simp)
  have a5 : y.callNo c5.name = some 5 := cn 5 (by simp)
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, a0, a1, a2, a5]
  rfl

/-- The hypothesis on the calls of the second walk in Johnson/Road/FormsKeysPans.lean and in the
files that stand on it. Under the hypotheses of ts_of_lines (layout and readsOf return; there are
routed experts; the eight lines are the library's): if TS is the list that the check of a layer
sub-proof makes, it is 0, 1, 2, 5. -/
theorem ts_eq {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (h3 : h.p3 = true) (hN : LinesAre y) {rd : Reads}
    (hr : readsOf y = .ok rd) {TS : List ℕ} (hT : rd.tscCalls.mapM y.callNo = some TS) :
    TS = [0, 1, 2, 5] :=
  Option.some.inj (hT.symm.trans (ts_of_lines hy h3 hN hr))

#print axioms takeCalls_nodup
#print axioms callNames_nodup
#print axioms findIdx_nodup
#print axioms tscCalls_eq
#print axioms ts_of_lines
#print axioms ts_eq

end OnBytes.Road
