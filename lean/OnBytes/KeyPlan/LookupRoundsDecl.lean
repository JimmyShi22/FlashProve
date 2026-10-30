-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyPlan/LookupRoundsDecl.lean: each round of a lookup, as the program lists them, is what
the declared structure makes of the round's entry.

A plan holds entries: a name and eleven words. A round as a reader needs it (`Fmt.Round`,
Fmt/Rules8.lean) has besides a kind, the cut of the prover's message into items, and the trees that
it opens. In the declared structure (Decl/Declared.lean) kind and cut are no fields: the kind
follows from the entry's name (`Fmt.kindOf`, the format page's R14.11), the cut from three of the
entry's words (`Fmt.Entry.cut`). The program's blocks state kind and items in their own text, and
`Lkp.roundsOf`, `Psc.roundsOf` (OnBytes/Iop/Lkp.lean, OnBytes/Iop/Psc.lean) list the rounds of a
lookup and of a sumcheck whole. This file proves that the two tellings agree on these rounds.

What it states. `FromEntry r`: r's kind is that of its entry's name, its items are its entry's cut,
and it opens no tree. `psc_fromEntry`, `tree_fromEntry`, `lookup_fromEntry`: every round of
`Psc.roundsOf work x`, `Lkp.treeRounds work levels more`, `Lkp.roundsOf work S` is such a round, for
all sizes, with or without a shift. The use: two such rounds with one entry are one round
(`FromEntry.same`, `FromEntry.ext`); two lists of such rounds with the same entries are one list
(`eq_of_entries`); and an entry, a kind and items that are told as the declared structure tells them
are those of such a round with that entry (`FromEntry.fields`). So an equation of entries is enough.
Limits. Nothing on what a dry run of the program's blocks notes: `Lkp.roundsOf` is a list that the
program's tests use. Nothing on rounds that send a root or an answer or open a tree. Not that any
chain's entries are those of these rounds (OnBytes/KeyPlan/ has that for a key's first chain). No
soundness, no hiding. For proofs only; no module of the program imports this file.

Terms: lean/GLOSSARY.md.
-/
import Decl.Declared
import OnBytes.Iop.Lkp

set_option autoImplicit false

namespace OnBytes.KeyPlan

/-- The round is what the declared structure makes of its entry, and opens no tree. -/
def FromEntry (r : Fmt.Round) : Prop :=
  Fmt.kindOf r.entry.name = some r.kind ∧ r.entry.cut = r.items ∧ r.opens = []

/-! ## The names -/

theorem kind_lkp : Fmt.kindOf "LKP" = some .elems := by decide
theorem kind_shift : Fmt.kindOf "LKP shift" = some .elems := by decide
theorem kind_join : Fmt.kindOf "JOIN" = some .elems := by decide
theorem kind_zero : Fmt.kindOf "ZERO" = some .elems := by decide
theorem kind_line : Fmt.kindOf "LINE" = some .elems := by decide
theorem kind_eps : Fmt.kindOf "PSC epsilon" = some .join := by decide
theorem kind_round : Fmt.kindOf "PSC round" = some .elems := by decide
theorem kind_y : Fmt.kindOf "PSC Y" = some .elems := by decide
theorem kind_values : Fmt.kindOf "PSC values" = some .nothing := by decide

/-! ## The makers of a round -/

/-- The cut of a message of n elements, without a root and without an answer. -/
theorem cut_plain (name : String) (work n dE nz : Nat) :
    ({ name := name, work := work, msg := 24 * n, drawE := dE, drawNZ := nz } : Fmt.Entry).cut =
      List.replicate n .e := by
  show List.replicate 0 Fmt.Item.answer ++ List.replicate 0 Fmt.Item.root ++
    List.replicate ((24 * n - 24 * 0 - 32 * 0) / 24) Fmt.Item.e = List.replicate n Fmt.Item.e
  rw [Nat.sub_zero, Nat.sub_zero, Nat.mul_div_cancel_left n (by decide : 0 < 24)]
  rfl

/-- A round in which the prover sends nothing and elements are drawn. -/
theorem rDraw_fromEntry (name : String) (work n : Nat) (h : Fmt.kindOf name = some .elems) :
    FromEntry (rDraw name work n) :=
  ⟨h, by
    show List.replicate 0 Fmt.Item.answer ++ List.replicate 0 Fmt.Item.root ++
      List.replicate ((0 - 24 * 0 - 32 * 0) / 24) Fmt.Item.e = []
    rfl, rfl⟩

/-- A round in which the prover sends n elements and one element is drawn. -/
theorem rOne_fromEntry (name : String) (kind : Fmt.Kind) (work n nz : Nat)
    (h : Fmt.kindOf name = some kind) : FromEntry (Psc.rOne name kind work n nz) :=
  ⟨h, cut_plain name work n 1 nz, rfl⟩

/-- The round of the shown values. -/
theorem rValues_fromEntry (n : Nat) : FromEntry (Psc.rValues n) :=
  ⟨kind_values, cut_plain "PSC values" 0 n 0 0, rfl⟩

/-! ## A sumcheck, a product tree, a lookup -/

theorem psc_fromEntry (work : Nat) (x : Psc.Size) : ∀ r ∈ Psc.roundsOf work x, FromEntry r := by
  intro r hr
  unfold Psc.roundsOf at hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · rw [List.mem_singleton.1 hr]
      exact rOne_fromEntry _ _ _ _ _ kind_eps
    · obtain ⟨d, _, e⟩ := List.mem_map.1 hr
      rw [← e]
      exact rOne_fromEntry _ _ _ _ _ kind_round
  · by_cases hy : x.withY = true
    · rw [if_pos hy] at hr
      rcases List.mem_cons.1 hr with e | hr
      · rw [e]
        exact rOne_fromEntry _ _ _ _ _ kind_y
      · rw [List.mem_singleton.1 hr]
        exact rValues_fromEntry _
    · rw [if_neg hy] at hr
      cases hr

theorem tree_fromEntry (work levels more : Nat) :
    ∀ r ∈ Lkp.treeRounds work levels more, FromEntry r := by
  intro r hr
  unfold Lkp.treeRounds at hr
  obtain ⟨l, _, hr⟩ := List.mem_flatMap.1 hr
  rcases List.mem_append.1 hr with hr | hr
  · exact psc_fromEntry _ _ r hr
  · rw [List.mem_singleton.1 hr]
    exact rDraw_fromEntry _ _ _ kind_line

/-- **Every round of a lookup is what the declared structure makes of its entry.** -/
theorem lookup_fromEntry (work : Nat) (S : Lkp.Public) :
    ∀ r ∈ Lkp.roundsOf work S, FromEntry r := by
  intro r hr
  unfold Lkp.roundsOf at hr
  simp only [List.mem_append] at hr
  rcases hr with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
  · by_cases hs : S.shifted = true
    · rw [if_pos hs] at h
      rw [List.mem_singleton.1 h]
      exact rDraw_fromEntry _ _ _ kind_shift
    · rw [if_neg hs] at h
      cases h
  · rw [List.mem_singleton.1 h]
    exact rDraw_fromEntry _ _ _ kind_lkp
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 h
    exact psc_fromEntry _ _ r h
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 h
    exact psc_fromEntry _ _ r h
  · rw [List.mem_singleton.1 h]
    exact rDraw_fromEntry _ _ _ kind_join
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 h
    exact tree_fromEntry _ _ _ r h
  · exact tree_fromEntry _ _ _ r h
  · exact psc_fromEntry _ _ r h
  · rw [List.mem_singleton.1 h]
    exact rDraw_fromEntry _ _ _ kind_zero
  · exact psc_fromEntry _ _ r h

/-! ## The use: from an equation of entries to whole rounds -/

/-- Two such rounds with one entry have one kind, one list of items and no opening. -/
theorem FromEntry.same {r r' : Fmt.Round} (h : FromEntry r) (h' : FromEntry r')
    (e : r.entry = r'.entry) : r.kind = r'.kind ∧ r.items = r'.items ∧ r.opens = r'.opens := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  rw [e] at a1 a2
  exact ⟨Option.some.inj (a1.symm.trans b1), a2.symm.trans b2, a3.trans b3.symm⟩

/-- They are one round. -/
theorem FromEntry.ext {r r' : Fmt.Round} (h : FromEntry r) (h' : FromEntry r')
    (e : r.entry = r'.entry) : r = r' := by
  obtain ⟨k, i, o⟩ := h.same h' e
  cases r
  cases r'
  rw [Fmt.Round.mk.injEq]
  exact ⟨e, k, i, o⟩

/-- **An entry, a kind and items that are told as the declared structure tells them are those of
such a round with that entry**: the three equations that a written round is asked for. -/
theorem FromEntry.fields {r : Fmt.Round} (h : FromEntry r) {e : Fmt.Entry} {k : Fmt.Kind}
    {items : List Fmt.Item} (he : e = r.entry) (hk : Fmt.kindOf e.name = some k)
    (hi : items = e.cut) : e = r.entry ∧ k = r.kind ∧ items = r.items := by
  rw [he] at hk hi
  exact ⟨he, Option.some.inj (hk.symm.trans h.1), hi.trans h.2.1⟩

/-- **Two lists of such rounds with the same entries are one list.** -/
theorem eq_of_entries : ∀ {l l' : List Fmt.Round}, (∀ r ∈ l, FromEntry r) →
    (∀ r ∈ l', FromEntry r) → l.map (·.entry) = l'.map (·.entry) → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, e => by simp at e
  | _ :: _, [], _, _, e => by simp at e
  | a :: l, b :: l', h, h', e => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at e
    rw [FromEntry.ext (h a (List.mem_cons_self ..)) (h' b (List.mem_cons_self ..)) e.1,
      eq_of_entries (fun r hr => h r (List.mem_cons_of_mem _ hr))
        (fun r hr => h' r (List.mem_cons_of_mem _ hr)) e.2]

end OnBytes.KeyPlan

#print axioms OnBytes.KeyPlan.psc_fromEntry
#print axioms OnBytes.KeyPlan.lookup_fromEntry
#print axioms OnBytes.KeyPlan.FromEntry.ext
#print axioms OnBytes.KeyPlan.FromEntry.fields
#print axioms OnBytes.KeyPlan.eq_of_entries
