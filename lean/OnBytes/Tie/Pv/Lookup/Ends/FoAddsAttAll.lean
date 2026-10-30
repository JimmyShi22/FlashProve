-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttAll.lean.
The attention sub-proof: at which places of its list of claims the lookup's claims stand.

Attention.claims (OnBytes/Model/Attention.lean) adds all claims of the sub-proof and of its lookup
but those of the smallness test, which follow.

States:
  planeLins_split: a run of Forest.planeLins is a run of Forest.planeClaims from the same state and
    context, which adds nothing and returns three forms, and then adds these three.
  claims_added: there are lists A, B of claims and an array pl of forms, all three functions of the
    arrays' numbers of columns alone and chosen BEFORE the state (so before its theta, its
    coefficients and its number of claims), such that every run of Attention.claims that returns,
    from a state F with one coefficient for each slot to a state G, has added, in this order: the
    lookup's rows on mask entries (the record's rows); A: cnt3 + cnt4 + cnt5 claims of the
    sub-proof's own; the lookup's join, at the key forms Fo.joinsA; B: cnt6 + cnt7 + cnt8 claims of
    the sub-proof's own; the three forms pl. The run keeps the numbers of columns. And there are
    states Fp, Fq and contexts cp, cq such that Forest.planeClaims returns pl from (Fp, cp), to
    (Fq, cq); all but the last three have been added from F to Fp (Fo.Added); Fp has F's numbers of
    columns; the three have been added from Fq to G. The proof takes Fp from inside the run; the
    statement ties it by these clauses, which are on values and numbers, and cp, cq by the run of
    Forest.planeClaims alone. claims_addedL (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean) ties
    more.
  claims_total: one equation on the total, each stretch under the powers of theta from its own first
    place on: the rows begin at place n0 (the number of claims before the run), the join stands at
    n0 + (the number of rows) + cnt3 + cnt4 + cnt5, and the planes' three begin behind it and the
    cnt6 + cnt7 + cnt8 claims that follow it. It has A, B and pl under an ∃ of its own (the proof
    takes those of claims_added), and of pl it keeps only that it is fixed before the state and has
    three members: that Forest.planeClaims returns it is not said there.
Limits: identities at the one element theta of the state. A, B and pl are chosen behind P and h:
they can hang on the plan and on the record of what was heard; that these hold nothing drawn with or
after theta is the caller's to say. Which the members of A and B are is not said. The statements
speak of runs that return. If, for given arguments and numbers of columns, a run returned at one
theta alone, a function of the numbers of columns could still fit that theta: that the run from a
state with another theta returns too, with the same value and the same list, is not shown. A count
at totals does not need it: for every theta at which the run returns, the total has grown by the sum
of theta^i times the value of member i of ONE list, the same for all such runs with these arguments
from states with these numbers of columns. No statement here draws a consequence from that: neither
that the members' values are thereby unique, nor an identity of polynomials in theta.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAtt
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsLook
import OnBytes.Tie.Pv.Lookup.Ends.FoAttSeam
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

theorem quiet_allJoined (j : Joins) : Quiet (allJoined j) := by
  unfold allJoined
  quiet

theorem quiet_paddingLaidA (S : Shape) (g : Forest.Heard) : Quiet (Attention.paddingLaid S g) := by
  unfold Attention.paddingLaid
  quiet

/-- Two lists of claims between the same two states are equally long. -/
theorem Added.length_eq {F G : Fork} {l l' : List Cl} (h : Added F G l) (h' : Added F G l') :
    l.length = l'.length := by
  have := h.nClaim.symm.trans h'.nClaim
  omega

/-- A run of Forest.planeLins, cut behind Forest.planeClaims. -/
theorem planeLins_split {g : Forest.Heard} {lm : ℕ} {bit : ℕ → ℕ → SubM Aff} {pin : ℕ → SubM Aff}
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col)) {F G : Fork} {c c' : Ctx}
    (h : Forest.planeLins g lm bit pin F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    ∃ (pl : Array Aff) (F1 : Fork) (c1 : Ctx),
      Forest.planeClaims g lm bit pin F c = .ok ((pl, F1), c1) ∧ pl.size = 3 ∧ Added F F1 [] ∧
        Added F1 G (pl.toList.map fun f => (f, #[])) := by
  unfold Forest.planeLins at h
  obtain ⟨pl, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨u, F2, c2, h3, h4⟩ := (bind_ok _ _ _ _ _).1 h2
  obtain ⟨e3, l0, el0, a0⟩ := planeClaims_three g lm bit pin hb hp _ _ _ _ _ h1 hs
  obtain rfl := List.length_eq_zero_iff.mp el0
  have h3' : (pl.toList.foldlM (fun _ a => SubM.lin a) ()) F1 c1 = .ok ((u, F2), c2) := by
    rw [Array.foldlM_toList]
    exact h3
  have a1 := added_forms h3' a0.sized
  obtain ⟨_, l2, el2, a2⟩ := quiet_planesAdded g _ _ _ _ _ h4 a1.sized
  obtain rfl := List.length_eq_zero_iff.mp el2
  have := a1.trans a2
  rw [List.append_nil] at this
  exact ⟨pl, F1, c1, h1, e3, a0, this⟩

/-- The claims that a run of Attention.claims adds, in their order: the lookup's as terms, the
sub-proof's own as lists that are fixed before the state. -/
theorem claims_added (P : Plan) (h : Attention.Heard) :
    ∃ (A B : (ℕ → ℕ) → List Cl) (pl : (ℕ → ℕ) → Array Aff),
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧ (pl (colsOf F)).size = 3 ∧
        colsOf G = colsOf F ∧
        Added F G ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
          [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F) ++
          (pl (colsOf F)).toList.map fun f => (f, #[])) ∧
        ∃ (Fp Fq : Fork) (cp cq : Ctx),
          Added F Fp ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
            [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F)) ∧
          colsOf Fp = colsOf F ∧
          Forest.planeClaims h.g h.S.cf.lmb
            (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
            (fun col => u3at h h.t.tPin col) Fp cp = .ok ((pl (colsOf F), Fq), cq) ∧
          Added Fq G ((pl (colsOf F)).toList.map fun f => (f, #[])) := by
  obtain ⟨_, _, Ho⟩ := fixed_objects h.g
  obtain ⟨_, L3, H3⟩ := fixed_claim3 h (Joins.empty P.NC)
  obtain ⟨_, L4, H4⟩ := fixed_claim4 h (joins3 h (Joins.empty P.NC))
  obtain ⟨_, L5, H5⟩ := fixed_claim5 h (joins4 h (joins3 h (Joins.empty P.NC)))
  obtain ⟨_, _, Ha⟩ := fixed_allJoined (joinsA h P.NC)
  obtain ⟨_, _, Hl⟩ := fixed_paddingLaidA h.S h.g
  obtain ⟨_, _, Hj⟩ := fixed_join h.g (joinsA h P.NC).kf
  obtain ⟨_, _, Hn⟩ := Fixed.lin (joinForm h.g (joinsA h P.NC).kf)
  obtain ⟨_, L6, H6⟩ := fixed_claim6 h
  obtain ⟨_, L7, H7⟩ := fixed_claim7 h
  obtain ⟨_, L8, H8⟩ := fixed_claim8 h
  obtain ⟨vp, _, Hp⟩ := fixed_planeClaims h.g h.S.cf.lmb
    (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
    (fun col => u3at h h.t.tPin col) (fun _ _ => fixed_u3at _ _ _) (fun _ => fixed_u3at _ _ _)
  obtain ⟨_, _, Hq⟩ := fixed_planeLins h.g h.S.cf.lmb
    (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
    (fun col => u3at h h.t.tPin col) (fun _ _ => fixed_u3at _ _ _) (fun _ => fixed_u3at _ _ _)
  refine ⟨fun k => L3 k ++ L4 k ++ L5 k, fun k => L6 k ++ L7 k ++ L8 k, fun k => (vp k).getD #[],
    fun F G c c' hr hs => ?_⟩
  unfold Attention.claims at hr
  obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have a0 := objects_added r0 hs
  have k0 := (Ho _ _ _ _ _ r0 hs).2.2
  obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain rfl := claim3_gives h _ _ _ _ _ _ r1
  obtain ⟨_, a1, k1⟩ := H3 _ _ _ _ _ r1 a0.sized
  obtain ⟨_, l1, e1, b1⟩ := adds_claim3 h _ _ _ _ _ _ r1 a0.sized
  obtain ⟨j4, F2, c2, r2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain rfl := claim4_gives h _ _ _ _ _ _ r2
  obtain ⟨_, a2, k2⟩ := H4 _ _ _ _ _ r2 a1.sized
  obtain ⟨_, l2, e2, b2⟩ := adds_claim4 h _ _ _ _ _ _ r2 a1.sized
  obtain ⟨j5, F3, c3, r3, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain rfl := claim5_gives h _ _ _ _ _ _ r3
  obtain ⟨_, a3, k3⟩ := H5 _ _ _ _ _ r3 a2.sized
  obtain ⟨_, l3, e3, b3⟩ := adds_claim5 h _ _ _ _ _ _ r3 a2.sized
  obtain ⟨_, F4, c4, r4, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, l4, e4, a4⟩ := quiet_allJoined _ _ _ _ _ _ r4 a3.sized
  obtain rfl := List.length_eq_zero_iff.mp e4
  have k4 := (Ha _ _ _ _ _ r4 a3.sized).2.2
  obtain ⟨_, F5, c5, r5, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, l5, e5, a5⟩ := quiet_paddingLaidA _ _ _ _ _ _ _ r5 a4.sized
  obtain rfl := List.length_eq_zero_iff.mp e5
  have k5 := (Hl _ _ _ _ _ r5 a4.sized).2.2
  obtain ⟨r, F6, c6, r6, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, l6, e6, a6⟩ := quiet_join _ _ _ _ _ _ _ r6 a5.sized
  obtain rfl := List.length_eq_zero_iff.mp e6
  have k6 := (Hj _ _ _ _ _ r6 a5.sized).2.2
  obtain ⟨_, _, _, _, rfl⟩ := join_ok _ _ _ _ _ _ _ r6
  obtain ⟨_, F7, c7, r7, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have a7 := added_lin a6.sized ((SubM.lin_run _ _ _ _ _).1 r7).1
  have k7 := (Hn _ _ _ _ _ r7 a6.sized).2.2
  obtain ⟨_, F8, c8, r8, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, a8, k8⟩ := H6 _ _ _ _ _ r8 a7.sized
  obtain ⟨_, l8, e8, b8⟩ := adds_claim6 h _ _ _ _ _ r8 a7.sized
  obtain ⟨_, F9, c9, r9, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, a9, k9⟩ := H7 _ _ _ _ _ r9 a8.sized
  obtain ⟨_, l9, e9, b9⟩ := adds_claim7 h _ _ _ _ _ r9 a8.sized
  obtain ⟨_, F10, c10, r10, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, a10, k10⟩ := H8 _ _ _ _ _ r10 a9.sized
  obtain ⟨_, l10, e10, b10⟩ := adds_claim8 h _ _ _ _ _ r10 a9.sized
  obtain ⟨pl, Fq, cq, hp1, hp2, ap, aq⟩ := planeLins_split (fun _ _ => quiet_u3at _ _ _)
    (fun _ => quiet_u3at _ _ _) hr a10.sized
  have kG := (Hq _ _ _ _ _ hr a10.sized).2.2
  -- the numbers of columns are those of F all along
  have c0' : colsOf F0 = colsOf F := k0
  have c1' : colsOf F1 = colsOf F := k1.trans c0'
  have c2' : colsOf F2 = colsOf F := k2.trans c1'
  have c3' : colsOf F3 = colsOf F := k3.trans c2'
  have c7' : colsOf F7 = colsOf F := (((k7.trans k6).trans k5).trans k4).trans c3'
  have c8' : colsOf F8 = colsOf F := k8.trans c7'
  have c9' : colsOf F9 = colsOf F := k9.trans c8'
  have c10' : colsOf F10 = colsOf F := k10.trans c9'
  rw [c0'] at a1
  rw [c1'] at a2
  rw [c2'] at a3
  rw [c7'] at a8
  rw [c8'] at a9
  rw [c9'] at a10
  have hv : vp (colsOf F) = some pl := by
    rw [← c10']
    exact (Hp _ _ _ _ _ hp1 a10.sized).1
  have hpl : (vp (colsOf F)).getD #[] = pl := by rw [hv]; rfl
  have pre := (((((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans
    a7).trans a8).trans a9).trans a10
  simp only [hpl]
  refine ⟨?_, ?_, hp2, kG.trans c10', ?_, F10, Fq, c10, cq, ?_, c10', hp1, aq⟩
  · rw [List.length_append, List.length_append, a1.length_eq b1, a2.length_eq b2,
      a3.length_eq b3, e1, e2, e3]
  · rw [List.length_append, List.length_append, a8.length_eq b8, a9.length_eq b9,
      a10.length_eq b10, e8, e9, e10]
  · have := (pre.trans ap).trans aq
    simpa only [List.append_nil, List.append_assoc] using this
  · simpa only [List.append_nil, List.append_assoc] using pre

/-- The same as one equation on the total, each stretch from its own first place on. -/
theorem claims_total (P : Plan) (h : Attention.Heard) :
    ∃ (A B : (ℕ → ℕ) → List Cl) (pl : (ℕ → ℕ) → Array Aff),
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧ (pl (colsOf F)).size = 3 ∧
        G.nClaim = F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1 +
          (cnt6 h + cnt7 h + cnt8 h) + 3 ∧
        G.theta = F.theta ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K),
          G.total ρ W = F.total ρ W +
            claimsValue ρ W (ρ.val F.theta) F.nClaim h.g.rows.toList +
            clsValue ρ W (ρ.val F.theta) (F.nClaim + h.g.rows.size) (A (colsOf F)) +
            ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
              (joinForm h.g (joinsA h P.NC).kf).value ρ W +
            clsValue ρ W (ρ.val F.theta)
              (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1) (B (colsOf F)) +
            claimsValue ρ W (ρ.val F.theta)
              (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1 +
                (cnt6 h + cnt7 h + cnt8 h)) (pl (colsOf F)).toList := by
  obtain ⟨A, B, pl, H⟩ := claims_added P h
  refine ⟨A, B, pl, fun F G c c' hr hs => ?_⟩
  obtain ⟨hA, hB, hp2, _, ad, _⟩ := H F G c c' hr hs
  refine ⟨hA, hB, hp2, ?_, ad.theta, fun K _ ρ W => ?_⟩
  · rw [ad.nClaim]
    simp only [List.length_append, List.length_map, Array.length_toList, List.length_cons,
      List.length_nil, hA, hB, hp2]
    omega
  · rw [ad.total]
    simp only [clsValue_append, clsValue_forms, List.length_append, List.length_map,
      Array.length_toList, List.length_cons, List.length_nil, hA, hB]
    have e1 : clsValue ρ W (ρ.val F.theta)
        (F.nClaim + (h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)))
        [(joinForm h.g (joinsA h P.NC).kf, #[])] =
        ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
          (joinForm h.g (joinsA h P.NC).kf).value ρ W := by
      simp [clsValue, sumFrom, value_form, Nat.add_assoc]
    rw [e1]
    simp only [Nat.add_assoc, Nat.zero_add]
    ring

end Fo
