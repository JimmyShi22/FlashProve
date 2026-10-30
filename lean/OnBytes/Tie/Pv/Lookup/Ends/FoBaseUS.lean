-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBaseUS.lean.
One pair of lists for the attention sub-proof's claims, with all that is said of such lists.

`AttBase P h A B` (OnBytes/Tie/Pv/Lookup/Ends/FoBaseTotal.lean) says of two lists A and B, functions
of the arrays' numbers of columns, what the statement on the claims that a run of
`Attention.claims` adds says of its lists. `FixedUS` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean)
says of the list of a routine's added claims that its members read one array alone and name slots
below the number of slots. Each is an ∃ of its own, so nothing says that one pair of lists has both.
Here the first proof is made again on the lists of the second.

 * `AttBaseUS P h A B`: `AttBase P h A B`; every member of `A cols ++ B cols`, at all cols, reads
   the array of reads alone (`GoodCl h.iU3`); and for every run of `Attention.claims P h` that
   returns from a state F with a coefficient for each slot and its arrays at their sizes, every slot
   that the form of a member of `A (colsOf F) ++ B (colsOf F)` names is below `F.ns`.
 * `attBaseUS_ex`: for a record h that is good there is such a pair.

The proof follows that of `claims_addedL` (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean), with
`fixedUS_claim3` … `fixedUS_claim8` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedUSAtt.lean) in the places of
`fixed_claim3` … `fixed_claim8`. Two of these ask that the key forms behind claim 3, and behind
claim 4, are good. That is had on a run, from the clause of `FixedUS` on values. So the proof goes
by cases: if they are good, the lists are those six; if not, no run returns, and the empty lists
serve.

Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns, or
which the claims are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBaseTotal
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUSAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention Cb.Fo

/-- One pair of lists with all three properties. -/
def AttBaseUS (P : Plan) (h : Attention.Heard) (A B : (ℕ → ℕ) → List Cl) : Prop :=
  AttBase P h A B ∧
  (∀ cols, ∀ cl ∈ A cols ++ B cols, GoodCl h.iU3 cl) ∧
  ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
    F.LS.size = F.ns → Sized F →
    ∀ cl ∈ A (colsOf F) ++ B (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns

/-- The three properties from one statement on runs. -/
theorem attBaseUS_of {P : Plan} {h : Attention.Heard} {A B : (ℕ → ℕ) → List Cl}
    (hg : ∀ cols, ∀ cl ∈ A cols ++ B cols, GoodCl h.iU3 cl)
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
      ∀ cl ∈ A (colsOf F) ++ B (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) :
    AttBaseUS P h A B :=
  ⟨fun F G c c' r hs hF => (hr F G c c' r hs hF).1, hg,
    fun F G c c' r hs hF => (hr F G c c' r hs hF).2⟩

theorem attBaseUS_ex (P : Plan) (h : Attention.Heard) [Good h.iU3 h] :
    ∃ A B, AttBaseUS P h A B := by
  obtain ⟨v3, L3, H3, V3, Q3⟩ := fixedUS_claim3 h (Joins.empty P.NC)
  by_cases g3 : Good h.iU3 (joins3 h (Joins.empty P.NC))
  swap
  · refine ⟨fun _ => [], fun _ => [], attBaseUS_of (fun _ _ hc => absurd hc (by simp))
      fun F G c c' hr hs hF => ?_⟩
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
  · refine ⟨fun _ => [], fun _ => [], attBaseUS_of (fun _ _ hc => absurd hc (by simp))
      fun F G c c' hr hs hF => ?_⟩
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
  suffices hx : ∃ A B : (ℕ → ℕ) → List Cl, (∀ cols, ∀ cl ∈ A cols ++ B cols, GoodCl h.iU3 cl) ∧
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
      ∀ cl ∈ A (colsOf F) ++ B (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns by
    obtain ⟨A, B, x1, x2⟩ := hx
    exact ⟨A, B, attBaseUS_of x1 x2⟩
  obtain ⟨_, _, Ho⟩ := fixed_objects h.g
  obtain ⟨_, L5, H5, _, Q5⟩ := fixedUS_claim5 h (joins4 h (joins3 h (Joins.empty P.NC)))
  obtain ⟨_, _, Ha⟩ := fixed_allJoined (joinsA h P.NC)
  obtain ⟨_, _, Hl⟩ := fixed_paddingLaidA h.S h.g
  obtain ⟨_, _, Hj⟩ := fixed_join h.g (joinsA h P.NC).kf
  obtain ⟨_, _, Hn⟩ := Fixed.lin (joinForm h.g (joinsA h P.NC).kf)
  obtain ⟨_, L6, H6, _, Q6⟩ := fixedUS_claim6 h
  obtain ⟨_, L7, H7, _, Q7⟩ := fixedUS_claim7 h
  obtain ⟨_, L8, H8, _, Q8⟩ := fixedUS_claim8 h
  refine ⟨fun k => L3 k ++ L4 k ++ L5 k, fun k => L6 k ++ L7 k ++ L8 k, ?_,
    fun F G c c' hr hs hF => ?_⟩
  · intro k cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with ((q | q) | q) | ((q | q) | q)
    · exact Q3 k cl q
    · exact Q4 k cl q
    · exact Q5 k cl q
    · exact Q6 k cl q
    · exact Q7 k cl q
    · exact Q8 k cl q
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
  obtain ⟨_, a3, k3, s3⟩ := H5 _ _ _ _ _ r3 a2.sized
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
  have n7 : F7.ns = F.ns :=
    a7.ns.trans (a6.ns.trans (a5.ns.trans (a4.ns.trans (a3.ns.trans n2))))
  have n8 : F8.ns = F.ns := a8.ns.trans n7
  have n9 : F9.ns = F.ns := a9.ns.trans n8
  rw [n0] at s1
  rw [n1] at s2
  rw [n2] at s3
  rw [n7] at s8
  rw [n8] at s9
  rw [n9] at s10
  refine ⟨⟨?_, ?_, F10, c10, ?_, c10',
    (((((((((m0.trans m1).trans m2).trans m3).trans m4).trans m5).trans m6).trans m7).trans
      m8).trans m9).trans m10, z10, hr⟩, ?_⟩
  · show (L3 _ ++ L4 _ ++ L5 _).length = _
    rw [List.length_append, List.length_append, a1.length_eq b1, a2.length_eq b2,
      a3.length_eq b3, e1, e2, e3]
  · show (L6 _ ++ L7 _ ++ L8 _).length = _
    rw [List.length_append, List.length_append, a8.length_eq b8, a9.length_eq b9,
      a10.length_eq b10, e8, e9, e10]
  · simpa only [List.append_nil, List.append_assoc] using pre
  · intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with ((q | q) | q) | ((q | q) | q)
    · exact s1 cl q
    · exact s2 cl q
    · exact s3 cl q
    · exact s8 cl q
    · exact s9 cl q
    · exact s10 cl q

end Fo
