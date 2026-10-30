-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Part.lean: the masked sumcheck's short text (Johnson/Desc/Part/MaskedSum4.lean):
where its functions return, what they leave; and the other way round. Theorems on roundOf,
varRounds, readAll, hear, row, shownEnds, whole: each as an equation or a pair of implications. No
arithmetic.

`row_some` goes as row_spec does in Johnson/Desc/Part/MaskedSumTie.lean, a file on the same text
under a reading.

Limits. Sentences on one text alone: nothing here ties it to another. It has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork Psc)

/-! ## A round -/

theorem roundOf_some {n k : Nat} {r : Fmt.RoundView} {s d : List E} (h : roundOf n k r = some (s, d)) :
    scalars r.vals = some s ∧ s.length = n ∧ r.drawn.elems.length = k ∧ d =
      r.drawn.elems.map E.ofTriple := by
  unfold roundOf at h
  cases hs : scalars r.vals with
  | none =>
    rw [hs] at h
    have h' : (none : Option (List E × List E)) = some (s, d) := h
    cases h'
  | some s' =>
    rw [hs] at h
    have h' : (if s'.length == n && r.drawn.elems.length == k then some
      (s', r.drawn.elems.map E.ofTriple) else none) =
        some (s, d) := h
    split at h'
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have e := Option.some.inj h'
      cases e
      exact ⟨rfl, hc.1, hc.2, rfl⟩
    · cases h'

theorem roundOf_mk {n k : Nat} {r : Fmt.RoundView} {s : List E} (h1 : scalars r.vals = some s)
    (h2 : s.length = n)
    (h3 : r.drawn.elems.length = k) : roundOf n k r = some (s, r.drawn.elems.map E.ofTriple) := by
  unfold roundOf
  rw [h1]
  simp [h2, h3]

/-! ## The variables' rounds -/

theorem varRounds_cons_some {v : Var} {vs : List Var} {r0 : Fmt.RoundView} {rs rest : List Fmt.RoundView}
    {l : List (List E × E)}
    (h : varRounds (v :: vs) (r0 :: rs) = some (l, rest)) :
    ∃ s g l', roundOf (v.d - 1) 1 r0 = some (s, [g]) ∧ varRounds vs rs = some (l', rest) ∧ l =
      (s, g) :: l' := by
  cases h1 : roundOf (v.d - 1) 1 r0 with
  | none => simp [varRounds, h1] at h
  | some sd =>
    obtain ⟨s, d⟩ := sd
    match d, h1 with
    | [], h1 => simp [varRounds, h1] at h
    | _ :: _ :: _, h1 => simp [varRounds, h1] at h
    | [g], h1 =>
      cases h2 : varRounds vs rs with
      | none => simp [varRounds, h1, h2] at h
      | some y =>
        obtain ⟨l', rest'⟩ := y
        simp only [varRounds, h1, h2, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨e1, e2⟩ := h
        subst e1 e2
        exact ⟨s, g, l', rfl, rfl, rfl⟩

theorem varRounds_cons_mk {v : Var} {vs : List Var} {r0 : Fmt.RoundView} {rs rest : List Fmt.RoundView}
    {l' : List (List E × E)}
    {s : List E} {g : E} (h1 : roundOf (v.d - 1) 1 r0 = some (s, [g]))
      (h2 : varRounds vs rs = some (l', rest)) :
    varRounds (v :: vs) (r0 :: rs) = some ((s, g) :: l', rest) := by
  simp only [varRounds, h1, h2]

theorem varRounds_nil (rs : List Fmt.RoundView) : varRounds [] rs = some ([], rs) := by
  cases rs <;> rfl

theorem varRounds_none (v : Var) (vs : List Var) : varRounds (v :: vs) [] = none := rfl

/-- Variables after variables: the rounds are read one list after the other. -/
theorem varRounds_append_some : ∀ (a b : List Var) (rs rest : List Fmt.RoundView) (l : List (List E × E)),
    varRounds (a ++ b) rs = some (l, rest) →
    ∃ l1 mid l2, varRounds a rs = some (l1, mid) ∧ varRounds b mid = some (l2, rest) ∧ l = l1 ++
      l2 ∧
      l1.length = a.length
  | [], b, rs, rest, l, h => ⟨[], rs, l, varRounds_nil rs, h, rfl, rfl⟩
  | v :: a, b, [], rest, l, h => by
    have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l, rest) := h
    cases h'
  | v :: a, b, r0 :: rs, rest, l, h => by
    obtain ⟨s, g, l', h1, h2, e⟩ := varRounds_cons_some (vs := a ++ b) h
    obtain ⟨l1, mid, l2, k1, k2, k3, k4⟩ := varRounds_append_some a b rs rest l' h2
    refine ⟨(s, g) :: l1, mid, l2, varRounds_cons_mk h1 k1, k2, ?_, ?_⟩
    · rw [e, k3]
      rfl
    · simp [k4]

theorem varRounds_append_mk : ∀ (a b : List Var) (rs mid rest : List Fmt.RoundView)
    (l1 l2 : List (List E × E)),
    varRounds a rs = some (l1, mid) → varRounds b mid = some (l2, rest) →
    varRounds (a ++ b) rs = some (l1 ++ l2, rest)
  | [], b, rs, mid, rest, l1, l2, h1, h2 => by
    rw [varRounds_nil] at h1
    have e := Option.some.inj h1
    cases e
    exact h2
  | v :: a, b, [], mid, rest, l1, l2, h1, h2 => by
    have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l1, mid) := h1
    cases h'
  | v :: a, b, r0 :: rs, mid, rest, l1, l2, h1, h2 => by
    obtain ⟨s, g, l', k1, k2, e⟩ := varRounds_cons_some h1
    subst e
    exact varRounds_cons_mk (vs := a ++ b) k1 (varRounds_append_mk a b rs mid rest l' l2 k2 h2)

/-- The fold over variables after variables. -/
theorem after_append : ∀ (a b : List Var) (l1 l2 : List (List E × E)) (c : E), l1.length =
    a.length →
    after (a ++ b) (l1 ++ l2) c = after b l2 (after a l1 c)
  | [], b, [], l2, c, _ => by
    cases b <;> cases l2 <;> rfl
  | v :: a, b, (s, g) :: l1, l2, c, h => by
    show after (a ++ b) (l1 ++ l2) (valueAt (complete v s c) g) =
      after b l2 (after a l1 (valueAt (complete v s c) g))
    exact after_append a b l1 l2 _ (Nat.succ.inj h)
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h

/-! ## hear -/

/-- What `hear` hands back, of what was read. -/
def P1Tie.heardOf (C : Aff) (k : Call) (F : Fork) (T : E) (x : Read) : Heard :=
  { start := C, target := T, eps := x.eps, claim := after k.all x.rounds (addE x.mu (mulE x.eps T)),
    first := F.next,
    vars := k.all, r := x.rounds.map (·.2), sEnd := F.next + ownSlots k.all }

/-- The ledger behind `hear`: the slots are counted; the end values are laid under theirs. -/
def ledgerOf (k : Call) (F : Fork) (x : Read) : Option Fork :=
  ({ F with next := F.next + ownSlots k.all + x.values.length } : Fork).hideRun
    (F.next + ownSlots k.all)
    x.values.toArray ((x.rounds.map (·.2)).getLastD zeroE)

theorem hear_eq (C : Aff) (k : Call) (F : Fork) (rs : List Fmt.RoundView) :
    hear C k F rs = if shapeOk k = true then
      (F.publicPart C).bind fun T => (readAll k rs).bind fun x => (ledgerOf k F x).bind fun G =>
        some (P1Tie.heardOf C k F T x, G) else none := by
  unfold hear
  cases shapeOk k <;> rfl

theorem hear_some {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) :
    shapeOk k = true ∧ ∃ (T : E) (x : Read), F.publicPart C = some T ∧ readAll k rs = some x ∧
      ledgerOf k F x = some G ∧ h = P1Tie.heardOf C k F T x := by
  rw [hear_eq] at hh
  cases hs : shapeOk k with
  | false =>
    rw [hs] at hh
    have h' : (none : Option (Heard × Fork)) = some (h, G) := hh
    cases h'
  | true =>
    refine ⟨rfl, ?_⟩
    rw [hs] at hh
    cases hT : F.publicPart C with
    | none =>
      rw [hT] at hh
      have h' : (none : Option (Heard × Fork)) = some (h, G) := hh
      cases h'
    | some T =>
      cases hR : readAll k rs with
      | none =>
        rw [hT, hR] at hh
        have h' : (none : Option (Heard × Fork)) = some (h, G) := hh
        cases h'
      | some x =>
        cases hG : ledgerOf k F x with
        | none =>
          rw [hT, hR] at hh
          have h1 : ((ledgerOf k F x).bind fun G => some (P1Tie.heardOf C k F T x, G)) =
            some (h, G) := hh
          rw [hG] at h1
          have h' : (none : Option (Heard × Fork)) = some (h, G) := h1
          cases h'
        | some G' =>
          rw [hT, hR] at hh
          have h1 : ((ledgerOf k F x).bind fun G => some (P1Tie.heardOf C k F T x, G)) =
            some (h, G) := hh
          rw [hG] at h1
          have h' : some (P1Tie.heardOf C k F T x, G') = some (h, G) := h1
          cases h'
          exact ⟨T, x, rfl, rfl, hG, rfl⟩

theorem hear_mk {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {T : E} {x : Read}
    (hs : shapeOk k = true)
    (hT : F.publicPart C = some T) (hR : readAll k rs = some x) (hG : ledgerOf k F x = some G) :
    hear C k F rs = some (P1Tie.heardOf C k F T x, G) := by
  rw [hear_eq, if_pos hs, hT, hR]
  show ((ledgerOf k F x).bind fun G => some (P1Tie.heardOf C k F T x, G)) = _
  rw [hG]
  rfl

/-! ## row, the shown end values, whole -/

theorem row_some {h : Heard} {S0 : E} {kept : Aff} {F G : Fork} {f : Aff}
    (hr : row h S0 kept F = some (f, G)) :
    f = rowAff h S0 kept ∧
      F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
        (subE zeroE oneE) = some G := by
  unfold row at hr
  cases ho : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
    (subE zeroE oneE) with
  | none => simp [ho] at hr
  | some G' =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hr
    exact ⟨hr.1.symm, by rw [hr.2]⟩

theorem row_mk {h : Heard} {S0 : E} {kept : Aff} {F G : Fork}
    (ho : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
      (subE zeroE oneE) = some G) :
    row h S0 kept F = some (rowAff h S0 kept, G) := by
  unfold row
  simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

theorem P1Tie.mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys →
    l.map f = ys.map some
  | [], ys, h => by
    rw [List.mapM_nil] at h
    have h' : some ([] : List β) = some ys := h
    cases h'
    rfl
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none =>
      rw [ha] at h
      have h' : (none : Option (List β)) = some ys := h
      cases h'
    | some b =>
      cases hl : l.mapM f with
      | none =>
        rw [ha, hl] at h
        have h' : (none : Option (List β)) = some ys := h
        cases h'
      | some bs =>
        rw [ha, hl] at h
        have h' : some (b :: bs) = some ys := h
        cases h'
        rw [List.map_cons, List.map_cons, ha, P1Tie.mapM_some f l bs hl]

theorem mapM_mk {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = some (g a)) →
    l.mapM f = some (l.map g)
  | [], _ => by
    rw [List.mapM_nil]
    rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_mk f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

theorem whole_some {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : Heard}
    {f : Aff} (hw : whole C k endTerm F rs = some (h, f, G)) :
    ∃ (e : Ends) (G0 : Fork) (sh : List E), k.ends = some e ∧ hear C k F rs = some (h, G0) ∧
      shownEnds h e.n G0 = some sh ∧ row h (endTerm h.r sh) {} G0 = some (f, G) := by
  unfold whole at hw
  cases he : k.ends with
  | none =>
    rw [he] at hw
    have h' : (none : Option (Heard × Aff × Fork)) = some (h, f, G) := hw
    cases h'
  | some e =>
    cases hh : hear C k F rs with
    | none =>
      rw [he, hh] at hw
      have h' : (none : Option (Heard × Aff × Fork)) = some (h, f, G) := hw
      cases h'
    | some y =>
      obtain ⟨h0, G0⟩ := y
      cases hs : shownEnds h0 e.n G0 with
      | none =>
        rw [he, hh] at hw
        have h1 : ((shownEnds h0 e.n G0).bind fun sh =>
          (row h0 (endTerm h0.r sh) {} G0).bind fun z =>
            some (h0, z.1, z.2)) = some (h, f, G) := hw
        rw [hs] at h1
        have h' : (none : Option (Heard × Aff × Fork)) = some (h, f, G) := h1
        cases h'
      | some sh =>
        rw [he, hh] at hw
        have h1 : ((shownEnds h0 e.n G0).bind fun sh =>
          (row h0 (endTerm h0.r sh) {} G0).bind fun z =>
            some (h0, z.1, z.2)) = some (h, f, G) := hw
        rw [hs] at h1
        cases hr : row h0 (endTerm h0.r sh) {} G0 with
        | none =>
          have h2 : ((row h0 (endTerm h0.r sh) {} G0).bind fun z => some (h0, z.1, z.2)) =
            some (h, f, G) := h1
          rw [hr] at h2
          have h' : (none : Option (Heard × Aff × Fork)) = some (h, f, G) := h2
          cases h'
        | some z =>
          have h2 : ((row h0 (endTerm h0.r sh) {} G0).bind fun z => some (h0, z.1, z.2)) =
            some (h, f, G) := h1
          rw [hr] at h2
          have h' : some (h0, z.1, z.2) = some (h, f, G) := h2
          cases h'
          exact ⟨e, G0, sh, rfl, rfl, hs, hr⟩

theorem whole_mk {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G0 G : Fork}
    {rs : List Fmt.RoundView} {h : Heard}
    {f : Aff} {e : Ends} {sh : List E} (he : k.ends = some e) (hh : hear C k F rs = some (h, G0))
    (hs : shownEnds h e.n G0 = some sh) (hr : row h (endTerm h.r sh) {} G0 = some (f, G)) :
    whole C k endTerm F rs = some (h, f, G) := by
  unfold whole
  rw [he, hh]
  show ((shownEnds h e.n G0).bind fun sh => (row h (endTerm h.r sh) {} G0).bind fun z =>
    some (h, z.1, z.2)) = _
  rw [hs]
  show ((row h (endTerm h.r sh) {} G0).bind fun z => some (h, z.1, z.2)) = _
  rw [hr]
  rfl

end VerifiableInference.Desc.Part.MaskedSum
