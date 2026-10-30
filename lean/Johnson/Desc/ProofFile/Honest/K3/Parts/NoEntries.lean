-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/NoEntries.lean: conditional: from the hearing's return, on
any rounds, at any face: no form of the lookup's runs of claims names an entry of a virtual row: the
forms read slots and constants alone. (The statements speak of the heard rows, the key trees' last
forms, the form that the leaves' sumcheck was given and the leads of the claims on the planes; that
these are the forms of the runs, `formsOf`, Honest/K3/GoodDrawsLaw.lean, is not stated here.) The
counterpart of Honest/K3/Parts/NamesOwn.lean, which says which slots they name. Theorems; three
definitions.

Terms. Honest/K3/GLOSSARY.md: see there hearing, form, slot, row, run (of claims), sumcheck, key
tree, tie, leaves and planes.

What is shown.
  `NoEnt a`: the form a names no entry of a virtual row.
  `ne_ofConst` to `ne_onSlots`, `ne_rowAff`, `ne_stepDown`, `ne_joinForm`: the makers of forms.
  `row_ne`, `whole_ne`, `sumV_ne`, `level_ne`, `run_ne`, `tieV_ne`, `partsV_ne`, `keysV_ne`: the
    hearing's pieces.
  `heard_ne`, `hearV_ne`: what was heard: every row, every key tree's last form, the form that the
    leaves' sumcheck was given.
  `planesV_ne`: the leads of the three claims on the planes.
Helpers: `AllNe`, `CarriedNe`, `allNe_push`, `turn_ne`, `fold_ne`, `ne_foldl`, `ne_onFold`.

Hypotheses that remain. The hearing's return alone (`h`, `hh`; and, in `planesV_ne`, `hp`: that of
`planesV`): no course, no coin, and no hypothesis on the ledger. In the pieces: `h`, `hr`, `hw`,
`e`: the routine returns (`h` in `allNe_push`: `AllNe rows`); `hC`, `hs`, `hk`, `hf`, `ha`, `hb`,
`hy`: `NoEnt` (or `AllNe`, `CarriedNe`) of what goes in; `hg`: (in `ne_foldl`) the step g keeps
`NoEnt`. `ne_onFold`, `ne_foldl`, `fold_ne`, `partsV_ne` and `keysV_ne` have hypotheses without a
name besides, of the two sorts told.

Users. Honest/K3/Parts/KeyLeft.lean, Honest/K3/Law/Thread/CEndBelow.lean and
Honest/K3/Law/Thread/PadNamesOf.lean [not in this library] import this file.

Limits. All statements are implications. An instance: Honest/K3/Parts/PacksGuards.lean
[not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV messagesV planesV Hr sumV openV tieV
  partsV keysV)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried stepDown level_spec)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Forward (joinForm)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

/-! ## 1 The forms' makers -/

/-- **The form names no entry of a virtual row.** -/
def NoEnt (a : Aff) : Prop := a.ents.isEmpty = true

theorem ne_ofConst (v : E) : NoEnt (Aff.ofConst v) := rfl

theorem ne_empty : NoEnt {} := rfl

theorem ne_slot (j : Nat) : NoEnt (Aff.slot j) := rfl

/-- Conditional on both forms naming none. -/
theorem ne_addMul {a b : Aff} (ha : NoEnt a) (hb : NoEnt b) (k : E) : NoEnt (Aff.addMul a b k) := by
  have hb' : b.ents = #[] := by
    unfold NoEnt at hb
    simpa using hb
  show (b.ents.foldl (fun l x => l.push { x with coef := mulE x.coef k }) a.ents).isEmpty = true
  rw [hb']
  exact ha

theorem ne_scale {a : Aff} (ha : NoEnt a) (k : E) : NoEnt (Aff.scale a k) := ne_addMul ne_empty ha k

theorem ne_add {a b : Aff} (ha : NoEnt a) (hb : NoEnt b) : NoEnt (a + b) := ne_addMul ha hb oneE

theorem ne_sub {a b : Aff} (ha : NoEnt a) (hb : NoEnt b) : NoEnt (a - b) :=
  ne_addMul ha hb (subE zeroE oneE)

theorem ne_onFold : ∀ (u : List E) (first : Nat) (f : Aff), NoEnt f →
    NoEnt (u.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x))
      (first, f)).2
  | [], _, _, hf => hf
  | x :: u, first, f, hf => by
    rw [List.foldl_cons]
    exact ne_onFold u (first + 1) _ (ne_addMul hf (ne_slot first) x)

theorem ne_onSlots {first : Nat} {f : Aff} {u : List E} (hf : NoEnt f) :
    NoEnt (MaskedSum.onSlots f first u) := ne_onFold u first f hf

/-- Conditional on the form that the sumcheck was given and the kept term naming none. -/
theorem ne_rowAff (h : MaskedSum.Heard) (S0 : E) {kept : Aff} (hs : NoEnt h.start)
    (hk : NoEnt kept) :
    NoEnt (MaskedSum.rowAff h S0 kept) := by
  unfold MaskedSum.rowAff
  exact ne_addMul (ne_addMul (ne_onSlots (ne_ofConst _)) (ne_sub (ne_ofConst _) hs) _) hk _

theorem ne_stepDown (o : LevelOut) : NoEnt (stepDown o).2 :=
  ne_add (ne_scale (ne_slot _) _) (ne_scale (ne_slot _) _)

theorem ne_foldl (g : Aff → Nat → Aff) (hg : ∀ c j, NoEnt c → NoEnt (g c j)) :
    ∀ (l : List Nat) (c : Aff), NoEnt c → NoEnt (l.foldl g c)
  | [], _, hc => hc
  | j :: l, c, hc => ne_foldl g hg l _ (hg c j hc)

theorem ne_joinForm (f : LFace) (sG : Array Nat) (rho : Array E) : NoEnt (joinForm f sG rho) := by
  unfold joinForm
  refine ne_foldl _ (fun c j hc => ?_) _ _ (ne_ofConst _)
  by_cases hj : j < f.planes
  · simp only [if_pos hj]
    exact ne_addMul hc (ne_slot _) _
  · simp only [if_neg hj]
    exact ne_add hc (ne_ofConst _)

/-! ## 2 The masked sumcheck -/

/-- Conditional on the row's return, and on the form that the sumcheck was given and the kept term
naming none. -/
theorem row_ne {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) (hs : NoEnt h.start) (hk : NoEnt kept) :
    NoEnt f := by
  rw [MaskedSum.row_spec hr]
  exact ne_rowAff h S0 hs hk

/-- Conditional on the return, and on the form that is passed naming none. -/
theorem whole_ne {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) (hC : NoEnt C) : NoEnt f := by
  obtain ⟨_, G1, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact row_ne hr (by rw [(hear_names hh).1]; exact hC) ne_empty

/-- Conditional on the same. -/
theorem sumV_ne {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView} {x : MaskedSum.Heard × Aff}
    (e : sumV C k endTerm F rs = some (x, G, rest)) (hC : NoEnt C) : NoEnt x.2 :=
  whole_ne (sumV_whole e) hC

/-! ## 3 The hearing's pieces -/

/-- All rows of an array. -/
def AllNe (rows : Array Aff) : Prop := ∀ y ∈ rows.toList, NoEnt y

theorem allNe_push {rows : Array Aff} {y : Aff} (h : AllNe rows) (hy : NoEnt y) :
    AllNe (rows.push y) := by
  intro z hz
  rw [Array.toList_push] at hz
  rcases List.mem_append.1 hz with h1 | h1
  · exact h z h1
  · obtain rfl : z = y := by simpa using h1
    exact hy

/-- Conditional on the level's return, and on the form that is passed naming none. -/
theorem level_ne {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest))
    (hC : NoEnt C) : NoEnt o.row := by
  obtain ⟨hd, line, s, hw, _, _, _, _, _⟩ := level_spec h
  exact whole_ne hw hC

/-- What a run of levels carries. -/
def CarriedNe (c : Carried) : Prop := AllNe c.rows ∧ NoEnt c.form

theorem turn_ne {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) (hs : CarriedNe s) :
    CarriedNe s' := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, _, _⟩ := e
  subst e1
  exact ⟨allNe_push hs.1 (level_ne hx hs.2), ne_stepDown o⟩

theorem fold_ne (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → CarriedNe x.1 → CarriedNe y.1
  | [], x, y, h, hx => by
    obtain rfl : x = y := Option.some.inj h
    exact hx
  | i :: l, x, y, h, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact fold_ne m0 orders l _ y h (turn_ne hz hx)

/-- Conditional on the run's return, and on what it is given naming none. -/
theorem run_ne {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : vRun m0 n orders s F rs = some (s', G, rest)) (hs : CarriedNe s) :
    CarriedNe s' :=
  fold_ne m0 orders _ (s, F, rs) (s', G, rest) h hs

/-- Conditional on the return. -/
theorem tieV_ne {w : Nat} {a : E} {F G : Fork} {rs rest : List Fmt.RoundView} {rows : Array Aff} {sZ : Nat}
    {sG : Array Nat} (h : tieV w a F rs = some ((rows, sZ, sG), G, rest)) : AllNe rows := by
  unfold tieV at h
  obtain ⟨x, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  have a1 := sumV_ne e1 (ne_ofConst _)
  have P0 : AllNe (#[x.2] : Array Aff) := by
    intro y hy
    obtain rfl : y = x.2 := by simpa using hy
    exact a1
  have step := foldlM_keeps
    (fun (s : Array Aff × Nat × Array Nat) (_ : Fork) => AllNe s.1)
    (by
      intro s _ F' rs' s' G' rest' hs hp
      obtain ⟨y, F3, r3, e3, hs⟩ := bindHr_some hs
      obtain ⟨q1, _, _⟩ := pure_spec hs
      rw [q1]
      exact allNe_push hp (sumV_ne e3 (ne_slot _)))
    _ _ _ _ _ _ _ e2 P0
  simp only [Prod.mk.injEq] at hg
  obtain ⟨g1, _, _⟩ := hg
  subst g1
  exact step

/-- Conditional on the return, and on what is passed naming none. -/
theorem partsV_ne : ∀ (n : Nat) (rows : Array Aff) (C : Aff) (F : Fork) (rs : List Fmt.RoundView)
    (rows' : Array Aff) (roots : List Aff) (G : Fork) (rest : List Fmt.RoundView),
    partsV n rows C F rs = some ((rows', roots), G, rest) → AllNe rows → NoEnt C →
    AllNe rows' ∧ ∀ y ∈ roots, NoEnt y
  | 0, rows, C, F, rs, rows', roots, G, rest, h, hr, hC => by
    unfold partsV at h
    obtain ⟨a, _, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    refine ⟨hr, fun y hy => ?_⟩
    obtain rfl : y = C := by simpa using hy
    exact hC
  | n + 1, rows, C, F, rs, rows', roots, G, rest, h, hr, hC => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨x, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, _, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    obtain ⟨c1, c2⟩ := partsV_ne n _ _ F1 r1 x.1 x.2 F2 r2 e2 (allNe_push hr (sumV_ne e1 hC))
      (ne_slot _)
    refine ⟨c1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with h1 | h1
    · rw [h1]
      exact ne_slot _
    · exact c2 y h1

/-- Conditional on the return, and on what is passed naming none. -/
theorem keysV_ne (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff)
    (F : Fork)
    (rs : List Fmt.RoundView) (rows' : Array Aff) (keys : List (Array E × Aff)) (G : Fork)
    (rest : List Fmt.RoundView),
    keysV f xs Cs rows F rs = some ((rows', keys), G, rest) → AllNe rows → (∀ C ∈ Cs, NoEnt C) →
    AllNe rows' ∧ ∀ y ∈ keys, NoEnt y.2
  | [], _, rows, F, rs, rows', keys, G, rest, h, hr, _ => by
    unfold keysV at h
    obtain ⟨a, _, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    exact ⟨hr, fun y hy => by simp at hy⟩
  | _ :: _, [], rows, F, rs, rows', keys, G, rest, h, hr, _ => by
    unfold keysV at h
    obtain ⟨a, _, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    exact ⟨hr, fun y hy => by simp at hy⟩
  | x :: xs, C :: Cs, rows, F, rs, rows', keys, G, rest, h, hr, hC => by
    unfold keysV at h
    obtain ⟨k, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, _, _⟩ := pure_spec h
    simp only [Prod.mk.injEq] at a
    obtain ⟨a1, a2⟩ := a
    subst a1 a2
    have e1' : vRun 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C } F rs =
        some (k, F1, r1) := e1
    obtain ⟨k1, k2⟩ := run_ne e1' ⟨hr, hC C (by simp)⟩
    obtain ⟨c1, c2⟩ := keysV_ne f xs Cs k.rows F1 r1 y.1 y.2 F2 r2 e2 k1
      (fun D hD => hC D (List.mem_cons_of_mem _ hD))
    refine ⟨c1, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with h1 | h1
    · rw [h1]
      exact k2
    · exact c2 z h1

/-! ## 4 What was heard -/

/-- **Of what was heard**, from the return alone: no row, no key tree's last form, and not the form
that the leaves' sumcheck was given names an entry of a virtual row. Conditional on the return of
`messagesV`. -/
theorem heard_ne {f : LFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV}
    (h : messagesV f F rs = some (g, G, rest)) :
    AllNe g.rows ∧ (∀ y ∈ g.keys, NoEnt y.2) ∧ NoEnt g.leaves.start := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  have t1 := tieV_ne e7
  obtain ⟨p1, p2⟩ := partsV_ne _ _ _ _ _ _ _ _ _ e8 t1 (ne_slot _)
  obtain ⟨k1, k2⟩ := keysV_ne f _ _ _ _ _ _ _ _ _ e10 p1 p2
  have e12' : vRun f.mu f.d orderDefault
      { rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse } F11 r11 =
      some (table, F12, r12) := e12
  obtain ⟨q1, q2⟩ := run_ne e12' ⟨k1, ne_joinForm f sG _⟩
  have l1 := (hear_names (openV_hear e14)).1
  have b1 := sumV_ne e16 (ne_ofConst _)
  subst hg
  refine ⟨allNe_push q1 b1, k2, ?_⟩
  show NoEnt leaves.start
  rw [l1]
  exact q2

/-- **Behind `hearV`.** Conditional on the return of `hearV`. An instance:
Honest/K3/Parts/PacksGuards.lean [not in this library] (by evaluation). -/
theorem hearV_ne {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV f F rs = some (g, G)) :
    AllNe g.rows ∧ (∀ y ∈ g.keys, NoEnt y.2) ∧ NoEnt g.leaves.start :=
  heard_ne (hearV_messages hh).2

/-- **The leads of the three claims on the planes name no entry of a virtual row.** Conditional on
the return of `hearV` and that of `planesV`. -/
theorem planesV_ne {f : LFace} {F G F' G' : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {cl : List PlaneClaim} (hh : hearV f F rs = some (g, G))
    (hp : planesV f g F' = some (cl, G')) : ∀ c ∈ cl, NoEnt c.lead := by
  obtain ⟨_, _, c3⟩ := hearV_ne hh
  unfold planesV at hp
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hp
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, _⟩ := e
  subst e1
  have hy' : MaskedSum.row g.leaves oneE {} F' = some (y.1, y.2) := hy
  have r1 := row_ne hy' c3 ne_empty
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact r1
  · exact ne_slot _
  · exact ne_ofConst _

#print axioms ProofFile.Honest.K3.Parts.ne_ofConst
#print axioms ProofFile.Honest.K3.Parts.ne_empty
#print axioms ProofFile.Honest.K3.Parts.ne_slot
#print axioms ProofFile.Honest.K3.Parts.ne_addMul
#print axioms ProofFile.Honest.K3.Parts.ne_scale
#print axioms ProofFile.Honest.K3.Parts.ne_add
#print axioms ProofFile.Honest.K3.Parts.ne_sub
#print axioms ProofFile.Honest.K3.Parts.ne_onFold
#print axioms ProofFile.Honest.K3.Parts.ne_onSlots
#print axioms ProofFile.Honest.K3.Parts.ne_rowAff
#print axioms ProofFile.Honest.K3.Parts.ne_stepDown
#print axioms ProofFile.Honest.K3.Parts.ne_foldl
#print axioms ProofFile.Honest.K3.Parts.ne_joinForm
#print axioms ProofFile.Honest.K3.Parts.row_ne
#print axioms ProofFile.Honest.K3.Parts.whole_ne
#print axioms ProofFile.Honest.K3.Parts.sumV_ne
#print axioms ProofFile.Honest.K3.Parts.allNe_push
#print axioms ProofFile.Honest.K3.Parts.level_ne
#print axioms ProofFile.Honest.K3.Parts.turn_ne
#print axioms ProofFile.Honest.K3.Parts.fold_ne
#print axioms ProofFile.Honest.K3.Parts.run_ne
#print axioms ProofFile.Honest.K3.Parts.tieV_ne
#print axioms ProofFile.Honest.K3.Parts.partsV_ne
#print axioms ProofFile.Honest.K3.Parts.keysV_ne
#print axioms ProofFile.Honest.K3.Parts.heard_ne
#print axioms ProofFile.Honest.K3.Parts.hearV_ne
#print axioms ProofFile.Honest.K3.Parts.planesV_ne

end ProofFile.Honest.K3.Parts
