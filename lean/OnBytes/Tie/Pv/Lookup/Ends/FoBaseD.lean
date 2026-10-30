-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBaseD.lean.
The lists A, B, C of the claims that a run of `Attention.claims` adds, as terms.

`attBaseW_ex` (OnBytes/Tie/Pv/Lookup/Ends/FoBaseWhole.lean) says that there are lists A, B, C with
all that is said of the claims that a run of `Attention.claims` adds. They stand under an ∃, and
where a record of key forms is not good they are empty. `FixedD`
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean) holds such lists as data. Here A, B and C are terms made
of these data: definitions for which Lean has code, and which can be unfolded.

 * `attDA P h`: the data of claims 3, 4 and 5, one behind the other, each at the key forms that the
   one before returned. `attDB h`: of claims 6, 7 and 8. `attDC h`: of the three claims on the
   lookup's planes.
 * `attA P h`, `attB h`, `attC h`: their lists.
 * `attBaseD_run`: one statement on a run of `Attention.claims P h` that returns, from which the two
   below are read.
 * `attBaseD`: for a record h that is good: `AttBaseW P h (attA P h) (attB h) (attC h)`. No ∃ stands
   before the lists. No cases: that the key forms between the claims are good is taken from the law
   of the claim before.
 * `attC_three`: on a run of `Attention.claims P h` that returns, from a state with a coefficient
   for each slot and its arrays at their sizes, `attC h` has three members. (Of `attA` and `attB`
   the lengths stand in `AttBase`.)
 * `attA_unfold`: `attA P h k` is the list of claim 3, then what the bind lays behind it.

Limits. The data of the single claims are made by the tactic `fixedd`
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean): which the members of the three lists are is said by
no statement. That `attC h` is the list of the three forms that `Forest.planeClaims` returns is not
shown: its length alone, and that on a run. Inside `AttBaseW` the state Fp and the context cp still
stand under an ∃. No test computes one of the three lists
(OnBytes/Tie/Pv/Lookup/Test/TestFoFixedD.lean computes claim 3's at one made-up record). What the
sub-proof's check adds behind `Attention.claims` is not covered.

Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedDAtt
import OnBytes.Tie.Pv.Lookup.Ends.FoBaseWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention Cb.Fo

section
variable (P : Plan) (h : Attention.Heard) [Good h.iU3 h]

/-- Claims 3, 4 and 5. -/
def attDA : FixedD h.iU3
    (claim3 h (Joins.empty P.NC) >>= fun j3 => claim4 h j3 >>= fun j4 => claim5 h j4) :=
  (fixedD_claim3 h (Joins.empty P.NC)).bind fun j3 g3 =>
    (@fixedD_claim4 h _ j3 g3).bind fun j4 g4 => @fixedD_claim5 h _ j4 g4

/-- Claims 6, 7 and 8. -/
def attDB : FixedD h.iU3 (claim6 h >>= fun _ => claim7 h >>= fun _ => claim8 h) :=
  (fixedD_claim6 h).bind fun _ _ => (fixedD_claim7 h).bind fun _ _ => fixedD_claim8 h

/-- The three claims on the lookup's planes. -/
def attDC : FixedD h.iU3 (Forest.planeLins h.g h.S.cf.lmb
    (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
    (fun col => u3at h h.t.tPin col)) :=
  fixedD_planeLins h.g _ _ _ (fun _ _ => fixedD_u3at _ _ _) (fun _ => fixedD_u3at _ _ _)

def attA : (ℕ → ℕ) → List Cl := (attDA P h).L

def attB : (ℕ → ℕ) → List Cl := (attDB h).L

def attC : (ℕ → ℕ) → List Cl := (attDC h).L

theorem attA_unfold (k : ℕ → ℕ) :
    attA P h k = (fixedD_claim3 h (Joins.empty P.NC)).L k ++
      bindL (fixedD_claim3 h (Joins.empty P.NC))
        (fun j3 g3 => (@fixedD_claim4 h _ j3 g3).bind fun j4 g4 => @fixedD_claim5 h _ j4 g4) k :=
  rfl

/-- One statement on runs, from which the two theorems below are read. -/
theorem attBaseD_run (F G : Fork) (c c' : Ctx)
    (hr : Attention.claims P h F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) (hF : Sized F) :
    ((attA P h (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
      (attB h (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
      (attC h (colsOf F)).length = 3) ∧
    (∀ cl ∈ attA P h (colsOf F) ++ attB h (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) ∧
    ∃ (Fp : Fork) (cp : Ctx), Added F Fp (wholeA P h (attA P h) (attB h) (colsOf F)) ∧
      colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
      Forest.planeLins h.g h.S.cf.lmb
        (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
        (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c') ∧
      Added Fp G (attC h (colsOf F)) ∧
      ∀ cl ∈ wholeA P h (attA P h) (attB h) (colsOf F) ++ attC h (colsOf F),
        GoodCl h.iU3 cl ∧ ∀ y ∈ cl.1.slots.toList, y.1 < F.ns := by
  unfold Attention.claims at hr
  obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have a0 := objects_added r0 hs
  have k0 := ((fixedD_objects (t0 := h.iU3) h.g).run _ _ _ _ _ r0 hs).2.2.1
  obtain ⟨m0, z0⟩ := Keeps.objects _ _ _ _ _ _ r0 hF
  obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m1, z1⟩ := keeps_Attention_claim3 _ _ _ _ _ _ _ r1 z0
  obtain rfl := claim3_gives h _ _ _ _ _ _ r1
  obtain ⟨_, l1, e1, b1⟩ := adds_claim3 h _ _ _ _ _ _ r1 a0.sized
  obtain ⟨j4, F2, c2, r2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m2, z2⟩ := keeps_Attention_claim4 _ _ _ _ _ _ _ r2 z1
  obtain rfl := claim4_gives h _ _ _ _ _ _ r2
  obtain ⟨_, l2, e2, b2⟩ := adds_claim4 h _ _ _ _ _ _ r2 b1.sized
  obtain ⟨j5, F3, c3, r3, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m3, z3⟩ := keeps_Attention_claim5 _ _ _ _ _ _ _ r3 z2
  obtain rfl := claim5_gives h _ _ _ _ _ _ r3
  obtain ⟨_, l3, e3, b3⟩ := adds_claim5 h _ _ _ _ _ _ r3 b2.sized
  have rA := (bind_ok (claim3 h (Joins.empty P.NC))
    (fun j3 => claim4 h j3 >>= fun j4 => claim5 h j4) _ _ _).2
    ⟨_, _, _, r1, (bind_ok _ (fun j4 => claim5 h j4) _ _ _).2 ⟨_, _, _, r2, r3⟩⟩
  obtain ⟨w5, aA, kA, sA⟩ := (attDA P h).run _ _ _ _ _ rA a0.sized
  haveI g5 : Good h.iU3 (joinsA h P.NC) := ⟨(attDA P h).goodV _ _ w5⟩
  obtain ⟨_, F4, c4, r4, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m4, z4⟩ := keeps_Attention_allJoined _ _ _ _ _ _ r4 z3
  obtain ⟨_, l4, e4, a4⟩ := quiet_allJoined _ _ _ _ _ _ r4 aA.sized
  obtain rfl := List.length_eq_zero_iff.mp e4
  have k4 := ((fixedD_allJoined h.iU3 (joinsA h P.NC)).run _ _ _ _ _ r4 aA.sized).2.2.1
  obtain ⟨_, F5, c5, r5, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m5, z5⟩ := keeps_Attention_paddingLaid _ _ _ _ _ _ _ r5 z4
  obtain ⟨_, l5, e5, a5⟩ := quiet_paddingLaidA _ _ _ _ _ _ _ r5 a4.sized
  obtain rfl := List.length_eq_zero_iff.mp e5
  have k5 := ((fixedD_paddingLaidA h.iU3 h.S h.g).run _ _ _ _ _ r5 a4.sized).2.2.1
  obtain ⟨r, F6, c6, r6, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m6, z6⟩ := Keeps.join _ _ _ _ _ _ _ r6 z5
  obtain ⟨_, l6, e6, a6⟩ := quiet_join _ _ _ _ _ _ _ r6 a5.sized
  obtain rfl := List.length_eq_zero_iff.mp e6
  obtain ⟨wJ, _, k6, _⟩ :=
    (fixedD_join (t0 := h.iU3) h.g (joinsA h P.NC).kf).run _ _ _ _ _ r6 a5.sized
  have gJ' := (fixedD_join (t0 := h.iU3) h.g (joinsA h P.NC).kf).goodV _ _ wJ
  obtain ⟨_, _, _, _, rfl⟩ := join_ok _ _ _ _ _ _ _ r6
  have gJ : InU h.iU3 (joinForm h.g (joinsA h P.NC).kf) := gJ'
  haveI : Good h.iU3 (joinForm h.g (joinsA h P.NC).kf) := ⟨gJ⟩
  obtain ⟨_, F7, c7, r7, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m7, z7⟩ := Keeps.lin _ _ _ _ _ _ r7 z6
  have a7 := added_lin a6.sized ((SubM.lin_run _ _ _ _ _).1 r7).1
  have k7 := ((FixedD.lin (t0 := h.iU3) (joinForm h.g (joinsA h P.NC).kf)).run _ _ _ _ _ r7
    a6.sized).2.2.1
  obtain ⟨_, F8, c8, r8, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m8, z8⟩ := keeps_Attention_claim6 _ _ _ _ _ _ r8 z7
  obtain ⟨_, l8, e8, b8⟩ := adds_claim6 h _ _ _ _ _ r8 a7.sized
  obtain ⟨_, F9, c9, r9, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m9, z9⟩ := keeps_Attention_claim7 _ _ _ _ _ _ r9 z8
  obtain ⟨_, l9, e9, b9⟩ := adds_claim7 h _ _ _ _ _ r9 b8.sized
  obtain ⟨_, F10, c10, r10, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m10, z10⟩ := keeps_Attention_claim8 _ _ _ _ _ _ r10 z9
  obtain ⟨_, l10, e10, b10⟩ := adds_claim8 h _ _ _ _ _ r10 b9.sized
  have rB := (bind_ok (claim6 h) (fun _ => claim7 h >>= fun _ => claim8 h) _ _ _).2
    ⟨_, _, _, r8, (bind_ok (claim7 h) (fun _ => claim8 h) _ _ _).2 ⟨_, _, _, r9, r10⟩⟩
  obtain ⟨_, aB, kB, sB⟩ := (attDB h).run _ _ _ _ _ rB a7.sized
  obtain ⟨_, aq, _, sq⟩ := (attDC h).run _ _ _ _ _ hr aB.sized
  obtain ⟨pl, _, _, _, hp3, ap⟩ := planeLins_added (fun _ _ => quiet_u3at _ _ _)
    (fun _ => quiet_u3at _ _ _) hr aB.sized
  have c3' : colsOf F3 = colsOf F := kA.trans k0
  have c7' : colsOf F7 = colsOf F := (((k7.trans k6).trans k5).trans k4).trans c3'
  have c10' : colsOf F10 = colsOf F := kB.trans c7'
  rw [k0] at aA sA
  rw [c7'] at aB sB
  rw [c10'] at aq sq
  have n0 : F0.ns = F.ns := a0.ns
  have n6 : F6.ns = F.ns := a6.ns.trans (a5.ns.trans (a4.ns.trans (aA.ns.trans n0)))
  have n7 : F7.ns = F.ns := a7.ns.trans n6
  have n10 : F10.ns = F.ns := aB.ns.trans n7
  rw [n0] at sA
  rw [n7] at sB
  rw [n10] at sq
  have gR : ∀ f ∈ h.g.rows.toList, InU h.iU3 f := (inferInstance : Good h.iU3 h.g.rows).out
  have sR : ∀ f ∈ h.g.rows.toList, ∀ y ∈ f.slots.toList, y.1 < F.ns := by
    obtain ⟨_, G₁, q1, _⟩ := objects_ok _ _ _ _ _ r0
    exact lins_below _ _ _ hs q1
  have sJ : ∀ y ∈ (joinForm h.g (joinsA h P.NC).kf).slots.toList, y.1 < F.ns := by
    have := lin_below ((SubM.lin_run _ _ _ _ _).1 r7).1
    rwa [n6] at this
  have mL : Later F F10 :=
    (((((((((m0.trans m1).trans m2).trans m3).trans m4).trans m5).trans m6).trans m7).trans
      m8).trans m9).trans m10
  have pre' : Added F F10 (wholeA P h (attA P h) (attB h) (colsOf F)) := by
    have := (((((a0.trans aA).trans a4).trans a5).trans a6).trans a7).trans aB
    simpa only [wholeA, attA, attB, List.append_nil, List.append_assoc] using this
  have sAB : ∀ cl ∈ attA P h (colsOf F) ++ attB h (colsOf F),
      ∀ y ∈ cl.1.slots.toList, y.1 < F.ns := by
    intro cl hcl
    rcases List.mem_append.1 hcl with q | q
    · exact sA cl q
    · exact sB cl q
  refine ⟨⟨?_, ?_, ?_⟩, sAB, F10, c10, pre', c10', mL, z10, hr, aq, ?_⟩
  · show ((attDA P h).L (colsOf F)).length = _
    rw [aA.length_eq ((b1.trans b2).trans b3), List.length_append, List.length_append, e1, e2, e3]
  · show ((attDB h).L (colsOf F)).length = _
    rw [aB.length_eq ((b8.trans b9).trans b10), List.length_append, List.length_append, e8, e9,
      e10]
  · show ((attDC h).L (colsOf F)).length = _
    rw [aq.length_eq ap, List.length_map, Array.length_toList, hp3]
  · intro cl hcl
    rcases List.mem_append.1 hcl with q | q
    · unfold wholeA at q
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at q
      rcases q with ((⟨f, hf, rfl⟩ | q) | rfl) | q
      · exact ⟨⟨gR f hf, fun _ hr => absurd hr (by simp)⟩, sR f hf⟩
      · exact ⟨(attDA P h).goodL _ cl q, sA cl q⟩
      · exact ⟨⟨gJ, fun _ hr => absurd hr (by simp)⟩, sJ⟩
      · exact ⟨(attDB h).goodL _ cl q, sB cl q⟩
    · exact ⟨(attDC h).goodL _ cl q, sq cl q⟩

/-- **The three terms have all the properties.** -/
theorem attBaseD : AttBaseW P h (attA P h) (attB h) (attC h) := by
  refine attBaseW_of (fun k cl hc => ?_) (attDC h).goodL fun F G c c' hr hs hF => ?_
  · rcases List.mem_append.1 hc with q | q
    · exact (attDA P h).goodL k cl q
    · exact (attDB h).goodL k cl q
  · obtain ⟨⟨x1, x2, _⟩, x3, Fp, cp, y1, y2, y3, y4, y5, y6, y7⟩ :=
      attBaseD_run P h F G c c' hr hs hF
    exact ⟨⟨x1, x2, Fp, cp, y1, y2, y3, y4, y5⟩, x3, Fp, cp, y1, y2, y3, y4, y5, y6, y7⟩

theorem attC_three (F G : Fork) (c c' : Ctx)
    (hr : Attention.claims P h F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) (hF : Sized F) :
    (attC h (colsOf F)).length = 3 :=
  (attBaseD_run P h F G c c' hr hs hF).1.2.2

end
end Fo
