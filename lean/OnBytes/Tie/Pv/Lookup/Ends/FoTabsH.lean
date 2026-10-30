-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTabsH.lean.
The tables of reads that a list of asks makes (Head.addFun), found again by name.

Head.tablesOf makes the head's tables from a list of asks: a matrix's first part, the number of its
parts, the length of a block of rows, the weights, a name. This file says where the table of an ask
lies and which records it leaves, whatever stands before and behind it in the list.

Defines:
  partStart: the first entry of part p of a table that begins at entry p0.
  askStep: Head.addFun at an ask.
States:
  addFun_ok: what one ask adds: one line to the list of names; one record for each part.
  asks_mono: later asks keep the lines and the records.
  asks_find: the ask a in a list pre ++ a :: post that makes tables (the fold of askStep returns),
    whose name no line of the tables at the start and no ask of pre bears: the table is found under
    its name, with some first entry p0 and the length of its parts from p0 on, and each part has
    its record, counted from p0. The statement does not say which entry p0 is; in the proof it is
    the length of the vector behind pre.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStillH

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

/-- An ask: the first part's number, the parts, the length of a block, the weights, the name. -/
abbrev Ask : Type := ℕ × ℕ × ℕ × Array E × String

/-- The entries of part number M of a table with blocks of Lf rows. -/
def partLen (mats : Array TMat) (Lf M : ℕ) : ℕ := (mats.getD M {}).k * ((mats.getD M {}).m / Lf)

/-- The first entry of part p of a table that begins at entry p0. -/
def partStart (mats : Array TMat) (M0 Lf p0 : ℕ) : ℕ → ℕ
  | 0 => p0
  | p + 1 => partStart mats M0 Lf p0 p + partLen mats Lf (M0 + p)

/-- The record of part p. -/
def partRec (mats : Array TMat) (M0 Lf p0 : ℕ) (phi : Array E) (p : ℕ) : HFun :=
  { mat := M0 + p, len := Lf, phi := phi, tree := 2, start := partStart mats M0 Lf p0 p }

/-- Head.addFun at an ask. -/
def askStep (mats : Array TMat) (t : Head.Tables) (a : Ask) : Option Head.Tables :=
  Head.addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

theorem addFun_fold (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (fs : Array HFun) (p0 : ℕ) :
    ∀ parts, (List.range parts).foldl
      (fun (s : Array HFun × ℕ) q =>
        let M := mats.getD (M0 + q) {}
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + M.k * (M.m / Lf))) (fs, p0) =
      (fs ++ ((List.range parts).map (partRec mats M0 Lf p0 phi)).toArray,
        partStart mats M0 Lf p0 parts)
  | 0 => by simp [partStart]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, addFun_fold mats M0 Lf phi fs p0 n]
    simp only [List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil]
    refine Prod.ext ?_ rfl
    apply Array.toList_inj.mp
    simp [partRec]

/-- What one ask adds. -/
theorem addFun_ok {mats : Array TMat} {t t' : Head.Tables} {a : Ask}
    (h : askStep mats t a = some t') :
    t'.tab = t.tab ++ [(a.2.2.2.2, t.p, t'.p - t.p)] ∧
      t'.funs = t.funs ++
        ((List.range a.2.1).map (partRec mats a.1 a.2.2.1 t.p a.2.2.2.1)).toArray ∧
      t'.p = partStart mats a.1 a.2.2.1 t.p a.2.1 := by
  unfold askStep Head.addFun at h
  rw [addFun_fold] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · have e := Option.some.inj h
    rw [← e]
    exact ⟨rfl, rfl, rfl⟩

/-- Later asks keep the lines and the records. -/
theorem asks_mono (mats : Array TMat) : ∀ (l : List Ask) (t t' : Head.Tables),
    l.foldlM (askStep mats) t = some t' →
      (∃ more, t'.tab = t.tab ++ more ∧ more.map (·.1) = l.map (·.2.2.2.2)) ∧
        ∀ f ∈ t.funs.toList, f ∈ t'.funs.toList
  | [], t, t', h => by
    have e : t = t' := Option.some.inj h
    subst e
    exact ⟨⟨[], by simp, rfl⟩, fun _ hf => hf⟩
  | a :: l, t, t', h => by
    rw [List.foldlM_cons] at h
    cases h1 : askStep mats t a with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some t1 =>
      rw [h1] at h
      have h' : l.foldlM (askStep mats) t1 = some t' := h
      obtain ⟨⟨more, m1, m2⟩, m3⟩ := asks_mono mats l t1 t' h'
      obtain ⟨a1, a2, _⟩ := addFun_ok h1
      refine ⟨⟨(a.2.2.2.2, t.p, t1.p - t.p) :: more, ?_, ?_⟩, fun f hf => m3 f ?_⟩
      · rw [m1, a1, List.append_assoc]
        rfl
      · rw [List.map_cons, List.map_cons, m2]
      · rw [a2, Array.toList_append]
        exact List.mem_append_left _ hf

/-- **A table is found again under its name.** -/
theorem asks_find (mats : Array TMat) (pre post : List Ask) (a : Ask) (t0 t : Head.Tables)
    (h : (pre ++ a :: post).foldlM (askStep mats) t0 = some t)
    (h0 : ∀ e ∈ t0.tab, e.1 ≠ a.2.2.2.2) (hp : ∀ b ∈ pre, b.2.2.2.2 ≠ a.2.2.2.2) :
    ∃ p0 len, (t.tab.find? fun e => e.1 == a.2.2.2.2) = some (a.2.2.2.2, p0, len) ∧
      len = partStart mats a.1 a.2.2.1 p0 a.2.1 - p0 ∧
      ∀ p < a.2.1, partRec mats a.1 a.2.2.1 p0 a.2.2.2.1 p ∈ t.funs.toList := by
  rw [List.foldlM_append] at h
  cases h1 : pre.foldlM (askStep mats) t0 with
  | none => rw [h1] at h; exact absurd h (by simp)
  | some tp =>
    rw [h1] at h
    have h' : (a :: post).foldlM (askStep mats) tp = some t := h
    rw [List.foldlM_cons] at h'
    cases h2 : askStep mats tp a with
    | none => rw [h2] at h'; exact absurd h' (by simp)
    | some ta =>
      rw [h2] at h'
      have h'' : post.foldlM (askStep mats) ta = some t := h'
      obtain ⟨⟨m1, e1, n1⟩, _⟩ := asks_mono mats pre t0 tp h1
      obtain ⟨a1, a2, a3⟩ := addFun_ok h2
      obtain ⟨⟨m2, e2, _⟩, k2⟩ := asks_mono mats post ta t h''
      refine ⟨tp.p, ta.p - tp.p, ?_, by rw [a3], fun p hp' => k2 _ ?_⟩
      · rw [e2, a1, e1, List.append_assoc, List.append_assoc, List.find?_append,
          List.find?_append]
        have z0 : (t0.tab.find? fun e => e.1 == a.2.2.2.2) = none := by
          rw [List.find?_eq_none]
          intro e he
          simpa using h0 e he
        have z1 : (m1.find? fun e => e.1 == a.2.2.2.2) = none := by
          rw [List.find?_eq_none]
          intro e he
          have : e.1 ∈ m1.map (·.1) := List.mem_map_of_mem he
          rw [n1] at this
          obtain ⟨b, hb, eb⟩ := List.mem_map.mp this
          have := hp b hb
          rw [eb] at this
          simpa using this
        rw [z0, z1]
        simp
      · rw [a2, Array.toList_append]
        refine List.mem_append_right _ ?_
        simp only [List.mem_map, List.mem_range]
        exact ⟨p, hp', rfl⟩

end Fo
