-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBaseWhole.lean.
The whole list of the claims that a run of `Attention.claims` adds: fixed before the state, reading
one array alone, naming slots below the number of slots.

`AttBaseUS` (OnBytes/Tie/Pv/Lookup/Ends/FoBaseUS.lean) says of the two lists A and B that their
members read the array of reads alone and name slots below the number of slots. The list that a run
of `Attention.claims` adds holds more: the rows of the lookup's record before A, the form of the
lookup's join between A and B, and the three claims on the lookup's planes behind B. Here all of
them are covered, on the same A and B. What the sub-proof's check adds behind `Attention.claims`
(the smallness test's claims) is not covered.

 * `lins_below`: where a run of `Fork.lins` returns, from a state with a coefficient for each slot,
   every slot of each of its forms is below the number of slots.
 * `wholeA P h A B cols`: the list that `AttBase` names: the rows, `A cols`, the join's form, `B
   cols`.
 * `AttBaseW P h A B C`: `AttBaseUS P h A B`; every member of `C cols`, at all cols, reads the array
   of reads alone; and for every run of `Attention.claims P h` that returns, from a state F with a
   coefficient for each slot and its arrays at their sizes, to G: there are ONE state Fp and one
   context cp of which all this holds: `wholeA` has been added from F to Fp; Fp has F's numbers of
   columns, is later than F and has its arrays at their sizes (the clauses of `AttBase` on its own
   state); `Forest.planeLins` has run from (Fp, cp) to the run's own end; `C (colsOf F)` has been
   added from Fp to G; and every member of `wholeA … ++ C …` reads the array of reads alone and
   names slots below `F.ns`. Fp and cp stand under an ∃: these clauses bind them and do not name
   them; cp has no clause but the run of `Forest.planeLins`. `AttBase`, inside `AttBaseUS`, has an
   ∃ of its own on a state and a context: that the two pairs are the same is not said; the pair here
   has all the clauses of the other.
 * `attBaseW_ex`: for a record h that is good there are such A, B, C.

That the rows and the join's form read one array alone stands under the quantifier on runs: of the
join's form it is had on a run alone (from the clause of `FixedUS` on values). Of A, B and C it
stands outright, at all numbers of columns. The lists themselves are fixed before the state.

Not said: how many members C has, and which they are. (`planeLins_added`,
OnBytes/Tie/Pv/Lookup/Ends/FoAddsLook.lean, says that the routine adds the three forms that
`Forest.planeClaims` returned inside it; two lists added between the same two states are equally
long, `Added.length_eq`, OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttAll.lean; that C is that list is not
shown.) "Has been added" is `Added` (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean): an equation of the
two totals at every reading and every world, with the claims' number.

The proof follows that of `claims_addedL` (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean) once more, as
in OnBytes/Tie/Pv/Lookup/Ends/FoBaseUS.lean, by the same cases.

Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns, or
which the claims are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBaseUS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention Cb.Fo

theorem lins_below : ∀ (l : List Aff) (F G : Fork), F.LS.size = F.ns → F.lins l = some G →
    ∀ f ∈ l, ∀ y ∈ f.slots.toList, y.1 < F.ns
  | [], _, _, _, _ => fun _ hf => absurd hf List.not_mem_nil
  | a :: l, X, Y, hs, h => by
    unfold Fork.lins at h
    rw [List.foldlM_cons] at h
    obtain ⟨X1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have a1 := added_lin hs h1
    intro f hf y hy
    rcases List.mem_cons.1 hf with rfl | hf
    · exact lin_below h1 y hy
    · rw [← a1.ns]
      exact lins_below l X1 Y a1.sized h2 f hf y hy

/-- The list that `AttBase` names. -/
def wholeA (P : Plan) (h : Attention.Heard) (A B : (ℕ → ℕ) → List Cl) (cols : ℕ → ℕ) : List Cl :=
  (h.g.rows.toList.map fun f => (f, #[])) ++ A cols ++
    [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B cols

/-- All the claims that a run of `Attention.claims` adds. -/
def AttBaseW (P : Plan) (h : Attention.Heard) (A B C : (ℕ → ℕ) → List Cl) : Prop :=
  AttBaseUS P h A B ∧
  (∀ cols, ∀ cl ∈ C cols, GoodCl h.iU3 cl) ∧
  ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
    F.LS.size = F.ns → Sized F →
    ∃ (Fp : Fork) (cp : Ctx), Added F Fp (wholeA P h A B (colsOf F)) ∧
      colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
      Forest.planeLins h.g h.S.cf.lmb
        (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
        (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c') ∧
      Added Fp G (C (colsOf F)) ∧
      ∀ cl ∈ wholeA P h A B (colsOf F) ++ C (colsOf F),
        GoodCl h.iU3 cl ∧ ∀ y ∈ cl.1.slots.toList, y.1 < F.ns

theorem attBaseW_of {P : Plan} {h : Attention.Heard} {A B C : (ℕ → ℕ) → List Cl}
    (hg : ∀ cols, ∀ cl ∈ A cols ++ B cols, GoodCl h.iU3 cl)
    (hc : ∀ cols, ∀ cl ∈ C cols, GoodCl h.iU3 cl)
    (hr : ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
      F.LS.size = F.ns → Sized F →
      (
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∃ (Fp : Fork) (cp : Ctx),
          Added F Fp ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
            [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F)) ∧
          colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
          Forest.planeLins h.g h.S.cf.lmb
            (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
            (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c')) ∧
      (∀ cl ∈ A (colsOf F) ++ B (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) ∧
      ∃ (Fp : Fork) (cp : Ctx), Added F Fp (wholeA P h A B (colsOf F)) ∧
        colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
        Forest.planeLins h.g h.S.cf.lmb
          (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
          (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c') ∧
        Added Fp G (C (colsOf F)) ∧
        ∀ cl ∈ wholeA P h A B (colsOf F) ++ C (colsOf F),
          GoodCl h.iU3 cl ∧ ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) :
    AttBaseW P h A B C :=
  ⟨attBaseUS_of hg fun F G c c' r hs hF =>
      ⟨(hr F G c c' r hs hF).1, (hr F G c c' r hs hF).2.1⟩, hc,
    fun F G c c' r hs hF => (hr F G c c' r hs hF).2.2⟩

theorem attBaseW_ex (P : Plan) (h : Attention.Heard) [Good h.iU3 h] :
    ∃ A B C, AttBaseW P h A B C := by
  obtain ⟨v3, L3, H3, V3, Q3⟩ := fixedUS_claim3 h (Joins.empty P.NC)
  by_cases g3 : Good h.iU3 (joins3 h (Joins.empty P.NC))
  swap
  · refine ⟨fun _ => [], fun _ => [], fun _ => [], attBaseW_of (fun _ _ hc => absurd hc (by simp))
      (fun _ _ hc => absurd hc (by simp)) fun F G c c' hr hs hF => ?_⟩
    exfalso
    unfold Attention.claims at hr
    obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
    have a0 := objects_added r0 hs
    obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
    obtain rfl := claim3_gives h _ _ _ _ _ _ r1
    exact g3 ⟨V3 _ _ (H3 _ _ _ _ _ r1 a0.sized).1⟩
  obtain ⟨v4, L4, H4, V4, Q4⟩ := fixedUS_claim4 h (joins3 h (Joins.empty P.NC))
  by_cases g4 : Good h.iU3 (joins4 h (joins3 h (Joins.empty P.NC)))
  swap
  · refine ⟨fun _ => [], fun _ => [], fun _ => [], attBaseW_of (fun _ _ hc => absurd hc (by simp))
      (fun _ _ hc => absurd hc (by simp)) fun F G c c' hr hs hF => ?_⟩
    exfalso
    unfold Attention.claims at hr
    obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
    have a0 := objects_added r0 hs
    obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
    obtain rfl := claim3_gives h _ _ _ _ _ _ r1
    obtain ⟨_, a1, _⟩ := H3 _ _ _ _ _ r1 a0.sized
    obtain ⟨j4, F2, c2, r2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
    obtain rfl := claim4_gives h _ _ _ _ _ _ r2
    exact g4 ⟨V4 _ _ (H4 _ _ _ _ _ r2 a1.sized).1⟩
  suffices hx : ∃ A B C : (ℕ → ℕ) → List Cl,
      (∀ cols, ∀ cl ∈ A cols ++ B cols, GoodCl h.iU3 cl) ∧
      (∀ cols, ∀ cl ∈ C cols, GoodCl h.iU3 cl) ∧
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
      F.LS.size = F.ns → Sized F →
      (
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∃ (Fp : Fork) (cp : Ctx),
          Added F Fp ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
            [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F)) ∧
          colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
          Forest.planeLins h.g h.S.cf.lmb
            (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
            (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c')) ∧
      (∀ cl ∈ A (colsOf F) ++ B (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) ∧
      ∃ (Fp : Fork) (cp : Ctx), Added F Fp (wholeA P h A B (colsOf F)) ∧
        colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
        Forest.planeLins h.g h.S.cf.lmb
          (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
          (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c') ∧
        Added Fp G (C (colsOf F)) ∧
        ∀ cl ∈ wholeA P h A B (colsOf F) ++ C (colsOf F),
          GoodCl h.iU3 cl ∧ ∀ y ∈ cl.1.slots.toList, y.1 < F.ns by
    obtain ⟨A, B, C, x1, x2, x3⟩ := hx
    exact ⟨A, B, C, attBaseW_of x1 x2 x3⟩
  obtain ⟨_, _, Ho⟩ := fixed_objects h.g
  obtain ⟨v5, L5, H5, V5, Q5⟩ := fixedUS_claim5 h (joins4 h (joins3 h (Joins.empty P.NC)))
  obtain ⟨_, _, Ha⟩ := fixed_allJoined (joinsA h P.NC)
  obtain ⟨_, _, Hl⟩ := fixed_paddingLaidA h.S h.g
  obtain ⟨_, _, Hj⟩ := fixed_join h.g (joinsA h P.NC).kf
  obtain ⟨_, _, Hn⟩ := Fixed.lin (joinForm h.g (joinsA h P.NC).kf)
  obtain ⟨_, L6, H6, _, Q6⟩ := fixedUS_claim6 h
  obtain ⟨_, L7, H7, _, Q7⟩ := fixedUS_claim7 h
  obtain ⟨_, L8, H8, _, Q8⟩ := fixedUS_claim8 h
  obtain ⟨_, Lq, Hq, _, Qq⟩ := fixedUS_planeLins (t0 := h.iU3) h.g h.S.cf.lmb
    (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
    (fun col => u3at h h.t.tPin col) (fun _ _ => fixedUS_u3at _ _ _) (fun _ => fixedUS_u3at _ _ _)
  have QA : ∀ k, ∀ cl ∈ (L3 k ++ L4 k ++ L5 k) ++ (L6 k ++ L7 k ++ L8 k), GoodCl h.iU3 cl := by
    intro k cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with ((q | q) | q) | ((q | q) | q)
    · exact Q3 k cl q
    · exact Q4 k cl q
    · exact Q5 k cl q
    · exact Q6 k cl q
    · exact Q7 k cl q
    · exact Q8 k cl q
  refine ⟨fun k => L3 k ++ L4 k ++ L5 k, fun k => L6 k ++ L7 k ++ L8 k, Lq, QA, Qq,
    fun F G c c' hr hs hF => ?_⟩
  unfold Attention.claims at hr
  obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have a0 := objects_added r0 hs
  have k0 := (Ho _ _ _ _ _ r0 hs).2.2
  obtain ⟨m0, z0⟩ := Keeps.objects _ _ _ _ _ _ r0 hF
  obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m1, z1⟩ := keeps_Attention_claim3 _ _ _ _ _ _ _ r1 z0
  obtain rfl := claim3_gives h _ _ _ _ _ _ r1
  obtain ⟨_, a1, k1, s1⟩ := H3 _ _ _ _ _ r1 a0.sized
  obtain ⟨_, l1, e1, b1⟩ := adds_claim3 h _ _ _ _ _ _ r1 a0.sized
  obtain ⟨j4, F2, c2, r2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m2, z2⟩ := keeps_Attention_claim4 _ _ _ _ _ _ _ r2 z1
  obtain rfl := claim4_gives h _ _ _ _ _ _ r2
  obtain ⟨_, a2, k2, s2⟩ := H4 _ _ _ _ _ r2 a1.sized
  obtain ⟨_, l2, e2, b2⟩ := adds_claim4 h _ _ _ _ _ _ r2 a1.sized
  obtain ⟨j5, F3, c3, r3, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m3, z3⟩ := keeps_Attention_claim5 _ _ _ _ _ _ _ r3 z2
  obtain rfl := claim5_gives h _ _ _ _ _ _ r3
  obtain ⟨w5, a3, k3, s3⟩ := H5 _ _ _ _ _ r3 a2.sized
  obtain ⟨_, l3, e3, b3⟩ := adds_claim5 h _ _ _ _ _ _ r3 a2.sized
  obtain ⟨_, F4, c4, r4, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m4, z4⟩ := keeps_Attention_allJoined _ _ _ _ _ _ r4 z3
  obtain ⟨_, l4, e4, a4⟩ := quiet_allJoined _ _ _ _ _ _ r4 a3.sized
  obtain rfl := List.length_eq_zero_iff.mp e4
  have k4 := (Ha _ _ _ _ _ r4 a3.sized).2.2
  obtain ⟨_, F5, c5, r5, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m5, z5⟩ := keeps_Attention_paddingLaid _ _ _ _ _ _ _ r5 z4
  obtain ⟨_, l5, e5, a5⟩ := quiet_paddingLaidA _ _ _ _ _ _ _ r5 a4.sized
  obtain rfl := List.length_eq_zero_iff.mp e5
  have k5 := (Hl _ _ _ _ _ r5 a4.sized).2.2
  obtain ⟨r, F6, c6, r6, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m6, z6⟩ := Keeps.join _ _ _ _ _ _ _ r6 z5
  obtain ⟨_, l6, e6, a6⟩ := quiet_join _ _ _ _ _ _ _ r6 a5.sized
  obtain rfl := List.length_eq_zero_iff.mp e6
  have k6 := (Hj _ _ _ _ _ r6 a5.sized).2.2
  obtain ⟨_, _, _, _, rfl⟩ := join_ok _ _ _ _ _ _ _ r6
  obtain ⟨_, F7, c7, r7, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m7, z7⟩ := Keeps.lin _ _ _ _ _ _ r7 z6
  have a7 := added_lin a6.sized ((SubM.lin_run _ _ _ _ _).1 r7).1
  have k7 := (Hn _ _ _ _ _ r7 a6.sized).2.2
  obtain ⟨_, F8, c8, r8, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m8, z8⟩ := keeps_Attention_claim6 _ _ _ _ _ _ r8 z7
  obtain ⟨_, a8, k8, s8⟩ := H6 _ _ _ _ _ r8 a7.sized
  obtain ⟨_, l8, e8, b8⟩ := adds_claim6 h _ _ _ _ _ r8 a7.sized
  obtain ⟨_, F9, c9, r9, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m9, z9⟩ := keeps_Attention_claim7 _ _ _ _ _ _ r9 z8
  obtain ⟨_, a9, k9, s9⟩ := H7 _ _ _ _ _ r9 a8.sized
  obtain ⟨_, l9, e9, b9⟩ := adds_claim7 h _ _ _ _ _ r9 a8.sized
  obtain ⟨_, F10, c10, r10, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m10, z10⟩ := keeps_Attention_claim8 _ _ _ _ _ _ r10 z9
  obtain ⟨_, a10, k10, s10⟩ := H8 _ _ _ _ _ r10 a9.sized
  obtain ⟨_, l10, e10, b10⟩ := adds_claim8 h _ _ _ _ _ r10 a9.sized
  have c0' : colsOf F0 = colsOf F := k0
  have c1' : colsOf F1 = colsOf F := k1.trans c0'
  have c2' : colsOf F2 = colsOf F := k2.trans c1'
  have c3' : colsOf F3 = colsOf F := k3.trans c2'
  have c7' : colsOf F7 = colsOf F := (((k7.trans k6).trans k5).trans k4).trans c3'
  have c8' : colsOf F8 = colsOf F := k8.trans c7'
  have c9' : colsOf F9 = colsOf F := k9.trans c8'
  have c10' : colsOf F10 = colsOf F := k10.trans c9'
  rw [c0'] at a1 s1
  rw [c1'] at a2 s2
  rw [c2'] at a3 s3
  rw [c7'] at a8 s8
  rw [c8'] at a9 s9
  rw [c9'] at a10 s10
  have pre := (((((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans
    a7).trans a8).trans a9).trans a10
  have n0 : F0.ns = F.ns := a0.ns
  have n1 : F1.ns = F.ns := a1.ns.trans n0
  have n2 : F2.ns = F.ns := a2.ns.trans n1
  have n6 : F6.ns = F.ns := a6.ns.trans (a5.ns.trans (a4.ns.trans (a3.ns.trans n2)))
  have n7 : F7.ns = F.ns := a7.ns.trans n6
  have n8 : F8.ns = F.ns := a8.ns.trans n7
  have n9 : F9.ns = F.ns := a9.ns.trans n8
  have n10 : F10.ns = F.ns := a10.ns.trans n9
  rw [n0] at s1
  rw [n1] at s2
  rw [n2] at s3
  rw [n7] at s8
  rw [n8] at s9
  rw [n9] at s10
  obtain ⟨_, aq, _, sq⟩ := Hq _ _ _ _ _ hr a10.sized
  rw [c10'] at aq sq
  rw [n10] at sq
  -- the rows
  have gR : ∀ f ∈ h.g.rows.toList, InU h.iU3 f := (inferInstance : Good h.iU3 h.g.rows).out
  have sR : ∀ f ∈ h.g.rows.toList, ∀ y ∈ f.slots.toList, y.1 < F.ns := by
    obtain ⟨_, G₁, q1, _⟩ := objects_ok _ _ _ _ _ r0
    exact lins_below _ _ _ hs q1
  -- the join's form
  haveI g5 : Good h.iU3 (joinsA h P.NC) := ⟨V5 _ _ w5⟩
  obtain ⟨_, _, Hj2, Vj, _⟩ := fixedUS_join (t0 := h.iU3) h.g (joinsA h P.NC).kf
  have gJ : InU h.iU3 (joinForm h.g (joinsA h P.NC).kf) := Vj _ _ (Hj2 _ _ _ _ _ r6 a5.sized).1
  have sJ : ∀ y ∈ (joinForm h.g (joinsA h P.NC).kf).slots.toList, y.1 < F.ns := by
    have := lin_below ((SubM.lin_run _ _ _ _ _).1 r7).1
    rwa [n6] at this
  have sAB : ∀ cl ∈ (L3 (colsOf F) ++ L4 (colsOf F) ++ L5 (colsOf F)) ++
      (L6 (colsOf F) ++ L7 (colsOf F) ++ L8 (colsOf F)), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns := by
    intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with ((q | q) | q) | ((q | q) | q)
    · exact s1 cl q
    · exact s2 cl q
    · exact s3 cl q
    · exact s8 cl q
    · exact s9 cl q
    · exact s10 cl q
  have pre' : Added F F10 ((h.g.rows.toList.map fun f => (f, #[])) ++
      (L3 (colsOf F) ++ L4 (colsOf F) ++ L5 (colsOf F)) ++
      [(joinForm h.g (joinsA h P.NC).kf, #[])] ++
      (L6 (colsOf F) ++ L7 (colsOf F) ++ L8 (colsOf F))) := by
    simpa only [List.append_nil, List.append_assoc] using pre
  have mL : Later F F10 :=
    (((((((((m0.trans m1).trans m2).trans m3).trans m4).trans m5).trans m6).trans m7).trans
      m8).trans m9).trans m10
  refine ⟨⟨?_, ?_, F10, c10, pre', c10',
    mL, z10, hr⟩, sAB, F10, c10, pre', c10', mL, z10, hr, aq, ?_⟩
  · show (L3 _ ++ L4 _ ++ L5 _).length = _
    rw [List.length_append, List.length_append, a1.length_eq b1, a2.length_eq b2,
      a3.length_eq b3, e1, e2, e3]
  · show (L6 _ ++ L7 _ ++ L8 _).length = _
    rw [List.length_append, List.length_append, a8.length_eq b8, a9.length_eq b9,
      a10.length_eq b10, e8, e9, e10]
  · intro cl hcl
    simp only [wholeA, List.mem_append, List.mem_map, List.mem_singleton] at hcl
    rcases hcl with (((⟨f, hf, rfl⟩ | q) | rfl) | q) | q
    · exact ⟨⟨gR f hf, fun _ hr => absurd hr (by simp)⟩, sR f hf⟩
    · have q' : cl ∈ L3 (colsOf F) ++ L4 (colsOf F) ++ L5 (colsOf F) := by
        simp only [List.mem_append]
        exact q
      exact ⟨QA _ cl (List.mem_append_left _ q'), sAB cl (List.mem_append_left _ q')⟩
    · exact ⟨⟨gJ, fun _ hr => absurd hr (by simp)⟩, sJ⟩
    · have q' : cl ∈ L6 (colsOf F) ++ L7 (colsOf F) ++ L8 (colsOf F) := by
        simp only [List.mem_append]
        exact q
      exact ⟨QA _ cl (List.mem_append_right _ q'), sAB cl (List.mem_append_right _ q')⟩
    · exact ⟨Qq _ cl q, sq cl q⟩

end Fo
