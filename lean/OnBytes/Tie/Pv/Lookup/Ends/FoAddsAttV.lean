-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttV.lean.
The attention sub-proof: its lookup's claims inside the one equation, by value.

States:
  worldOf_theta: the world of a state does not read the state's theta.
  joinForm_claim: the value of the form that Forest.join returns is Fo.claimJoin at the values of
    the caller's key forms, in every state later than the one with which the lookup's record holds
    the flat function's end values (Fo.HeardIs). Under: the shape is lawful (FoNums.ok); the caller
    hands in one key form for each call.
  claims_addedL: there are lists A, B of claims, functions of the arrays' numbers of columns alone
    and chosen BEFORE the state, such that every run of Attention.claims that returns, from a state
    F (one coefficient for each slot; the slots' arrays at their sizes) and a context c to G and c',
    is: a stretch from F to a state Fp that has added the lookup's rows, A, the lookup's join and B,
    in this order, and keeps what lies under the filled slots and the numbers of columns; and then a
    run of Forest.planeLins from Fp and some context cp that ends in G and c'. The stretch is said
    by Fo.Added, Later, Sized and the numbers of columns, not by a run equation; cp is tied to c'
    by the run of Forest.planeLins, and to c by nothing.
  att_look_total: there are such A, B (an ∃ of its own; the proof takes those of claims_addedL),
    chosen before the state, the field, the reading, the rounds and the world, such that for every
    run as in claims_addedL: if the lookup's record holds the flat function's end values with a
    state F0 than which F is later, the shape is lawful (FoNums.ok) and P.NC is its number of
    calls, then in every state later than G, for every reading ν of the lookup's places and all
    entries of virtual rows that meet the law of the reads (Fo.ReadsLaw, at the number of columns
    that the array of reads has in F), the
    total has grown by: powSum, from place n0 on, of the flat function's rows; A; theta^(the join's
    place) times Fo.claimJoin at the values of the key forms Fo.kfA; B; powSum, from the planes'
    place on, of Fo.claimLeaves, Fo.claimBits and the counts' sum at the columns' sums of the
    lookup's cells.
  The lookup's members are terms in the shape, lmb, the first slot, the rounds, ν, and (the join)
    the values of the key forms in the world: no state and no theta is among their arguments.
Limits: A and B are chosen behind P and h: they can hang on the plan and the record of what was
heard; that these hold nothing drawn with or after theta is the caller's to say. Which their members
are is not said. Whether ν, the world's slots, or the entries of which the law of the reads speaks
hang on theta is not said. The statements speak of runs that return. If, for given arguments and
numbers of columns, a run returned at one theta alone, a function of the numbers of columns could
still fit that theta: that the run from a state with another theta returns too, with the same value
and the same list, is not shown. A count at totals does not need it: for every theta at which the
run returns, the total has grown by the sum of theta^i times the value of member i of ONE list, the
same for all such runs with these arguments from states with these numbers of columns. The members'
values are read in the world of a later state H: that world's slots are made of what was shown and
of the factors under H's slots and of the mask row (worldOf_theta: it does not read H's theta); its
entries of virtual rows are the caller's letter. The law of the reads asks three tables of one
function of entries: some world meets it if the three lie one behind the other (readsLaw_some,
OnBytes/Tie/Pv/Lookup/Port/FoReads.lean); that h.t.tBit0, tBit1 and tPin do is no premise and is not
shown here, and where they overlapped the statement could be idle. No statement here draws a
consequence from the one list: neither that the members' values are unique, nor an identity of
polynomials in theta.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAttAll
import OnBytes.Tie.Pv.Lookup.Ends.FoLookGrows
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention Cb.Fo

/-- The claims that a run of Attention.claims adds, and what it keeps. -/
theorem claims_addedL (P : Plan) (h : Attention.Heard) :
    ∃ (A B : (ℕ → ℕ) → List Cl),
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns → Sized F →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∃ (Fp : Fork) (cp : Ctx),
          Added F Fp ((h.g.rows.toList.map fun f => (f, #[])) ++ A (colsOf F) ++
            [(joinForm h.g (joinsA h P.NC).kf, #[])] ++ B (colsOf F)) ∧
          colsOf Fp = colsOf F ∧ Later F Fp ∧ Sized Fp ∧
          Forest.planeLins h.g h.S.cf.lmb
            (fun e col => u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col)
            (fun col => u3at h h.t.tPin col) Fp cp = .ok (((), G), c') := by
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
  refine ⟨fun k => L3 k ++ L4 k ++ L5 k, fun k => L6 k ++ L7 k ++ L8 k,
    fun F G c c' hr hs hF => ?_⟩
  unfold Attention.claims at hr
  obtain ⟨_, F0, c0, r0, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have a0 := objects_added r0 hs
  have k0 := (Ho _ _ _ _ _ r0 hs).2.2
  obtain ⟨m0, z0⟩ := Keeps.objects _ _ _ _ _ _ r0 hF
  obtain ⟨j3, F1, c1, r1, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m1, z1⟩ := keeps_Attention_claim3 _ _ _ _ _ _ _ r1 z0
  obtain rfl := claim3_gives h _ _ _ _ _ _ r1
  obtain ⟨_, a1, k1⟩ := H3 _ _ _ _ _ r1 a0.sized
  obtain ⟨_, l1, e1, b1⟩ := adds_claim3 h _ _ _ _ _ _ r1 a0.sized
  obtain ⟨j4, F2, c2, r2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m2, z2⟩ := keeps_Attention_claim4 _ _ _ _ _ _ _ r2 z1
  obtain rfl := claim4_gives h _ _ _ _ _ _ r2
  obtain ⟨_, a2, k2⟩ := H4 _ _ _ _ _ r2 a1.sized
  obtain ⟨_, l2, e2, b2⟩ := adds_claim4 h _ _ _ _ _ _ r2 a1.sized
  obtain ⟨j5, F3, c3, r3, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m3, z3⟩ := keeps_Attention_claim5 _ _ _ _ _ _ _ r3 z2
  obtain rfl := claim5_gives h _ _ _ _ _ _ r3
  obtain ⟨_, a3, k3⟩ := H5 _ _ _ _ _ r3 a2.sized
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
  obtain ⟨_, a8, k8⟩ := H6 _ _ _ _ _ r8 a7.sized
  obtain ⟨_, l8, e8, b8⟩ := adds_claim6 h _ _ _ _ _ r8 a7.sized
  obtain ⟨_, F9, c9, r9, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m9, z9⟩ := keeps_Attention_claim7 _ _ _ _ _ _ r9 z8
  obtain ⟨_, a9, k9⟩ := H7 _ _ _ _ _ r9 a8.sized
  obtain ⟨_, l9, e9, b9⟩ := adds_claim7 h _ _ _ _ _ r9 a8.sized
  obtain ⟨_, F10, c10, r10, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨m10, z10⟩ := keeps_Attention_claim8 _ _ _ _ _ _ r10 z9
  obtain ⟨_, a10, k10⟩ := H8 _ _ _ _ _ r10 a9.sized
  obtain ⟨_, l10, e10, b10⟩ := adds_claim8 h _ _ _ _ _ r10 a9.sized
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
  have pre := (((((((((a0.trans a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans
    a7).trans a8).trans a9).trans a10
  refine ⟨?_, ?_, F10, c10, ?_, c10',
    (((((((((m0.trans m1).trans m2).trans m3).trans m4).trans m5).trans m6).trans m7).trans
      m8).trans m9).trans m10, z10, hr⟩
  · show (L3 _ ++ L4 _ ++ L5 _).length = _
    rw [List.length_append, List.length_append, a1.length_eq b1, a2.length_eq b2,
      a3.length_eq b3, e1, e2, e3]
  · show (L6 _ ++ L7 _ ++ L8 _).length = _
    rw [List.length_append, List.length_append, a8.length_eq b8, a9.length_eq b9,
      a10.length_eq b10, e8, e9, e10]
  · simpa only [List.append_nil, List.append_assoc] using pre

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The world of a state does not read the state's theta. -/
theorem worldOf_theta (H : Fork) (t : E) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    ({ H with theta := t } : Fork).worldOf ρ mask entry = H.worldOf ρ mask entry := rfl

/-- The value of the form that Forest.join returns. -/
theorem joinForm_claim (g : Forest.Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 : Fork)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (KF : Array Aff) (hs : KF.size = g.shape.NC) (H : Fork) (hH : Later F0 H) (ν : Pl → K)
    (entry : ℕ → ℕ → ℕ → K) :
    (joinForm g KF).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      claimJoin g.shape lm jLK rsK ν fun k =>
        (KF.getD k (Aff.ofConst zeroE)).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) := by
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H hH).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (PlaneClaims.onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  exact join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hs lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE

end

/-- The attention sub-proof's lookup inside the one equation, beside two lists for the sub-proof's
own claims that are fixed before the state, the reading and the world. -/
theorem att_look_total (P : Plan) (h : Attention.Heard) :
    ∃ (A B : (ℕ → ℕ) → List Cl),
      ∀ (F G : Fork) (c c' : Ctx), Attention.claims P h F c = .ok (((), G), c') →
        F.LS.size = F.ns → Sized F →
        (A (colsOf F)).length = cnt3 h + cnt4 h + cnt5 h ∧
        (B (colsOf F)).length = cnt6 h + cnt7 h + cnt8 h ∧
        ∀ (K : Type) [CommRing K] (ρ : Reading K) (F0 : Fork) (jLK : ℕ) (rsK : Rounds K),
          HeardIs ρ h.g F0 (endsOf h.g.shape h.S.cf.lmb jLK rsK) → Later F0 F →
          FoNums.ok h.g.shape = true → P.NC = h.g.shape.NC →
          ∀ (H : Fork), Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
            ReadsLaw h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb0
              (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb1 ν entry h.iU3 (colsOf F h.iU3) h.t.tBit0
              h.t.tBit1 h.t.tPin →
            G.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
              F.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
                powSum (ρ.val F.theta) F.nClaim
                  ((endsOf h.g.shape h.S.cf.lmb jLK rsK).rows.map (rowRes ν)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size) (A (colsOf F)) +
                ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
                  claimJoin h.g.shape h.S.cf.lmb jLK rsK ν
                    (fun q => (kfA h q).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) +
                clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1) (B (colsOf F)) +
                powSum (ρ.val F.theta)
                  (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h) + 1 +
                    (cnt6 h + cnt7 h + cnt8 h))
                  [claimLeaves h.g.shape h.S.cf.lmb jLK rsK ν
                      (colsK h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb0 ν),
                    claimBits h.g.shape h.S.cf.lmb jLK rsK ν
                      (colsK h.g.shape h.S.cf.lmb (endsOf h.g.shape h.S.cf.lmb jLK rsK).zb1 ν),
                    Pin.countK h.g.shape h.S.cf.lmb (Pin.pinColK h.S.cf.lmb ν)] := by
  obtain ⟨A, B, HH⟩ := claims_addedL P h
  refine ⟨A, B, fun F G c c' hr hs hF => ?_⟩
  obtain ⟨hA, hB, Fp, cp, pre, kp, lp, zp, hpl⟩ := HH F G c c' hr hs hF
  refine ⟨hA, hB, fun K _ ρ F0 jLK rsK hI h0 hok hNC H hH ν entry Lw => ?_⟩
  have R := readsAt_attention h Fp cp
  rw [congrFun kp h.iU3] at R
  obtain ⟨lq, _, _, hg⟩ := planeLins_reads ρ h.g h.S.cf.lmb jLK rsK (bitAtt h) (pinAtt h) F0 Fp G
    cp c' R hpl hI (h0.trans lp) hok pre.sized zp
  obtain ⟨t1, _, _⟩ := hg H hH ν entry Lw
  have hsz : (joinsA h P.NC).kf.size = h.g.shape.NC := (kf_size h P.NC).trans hNC
  have lH : Later F0 H := ((h0.trans lp).trans lq).trans hH
  have eR := PlaneClaims.rows_claim ρ h.g h.S.cf.lmb jLK rsK F0 hI H lH ν entry
  have eJ : (joinForm h.g (joinsA h P.NC).kf).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      claimJoin h.g.shape h.S.cf.lmb jLK rsK ν
        (fun q => (kfA h q).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) := by
    rw [joinForm_claim ρ h.g h.S.cf.lmb jLK rsK F0 hI hok _ hsz H lH ν entry]
    refine claimJoin_congr _ _ _ _ _ _ _ fun q hq => ?_
    rw [kf_at h P.NC q (by rw [hNC]; exact hq)]
  rw [t1, pre.total, pre.theta, pre.nClaim]
  simp only [clsValue_append, clsValue_forms, claimsValue_powSum, List.length_append,
    List.length_map, Array.length_toList, List.length_cons, List.length_nil, hA, hB]
  rw [eR]
  have e1 : clsValue ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) (ρ.val F.theta)
      (F.nClaim + (h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)))
      [(joinForm h.g (joinsA h P.NC).kf, #[])] =
      ρ.val F.theta ^ (F.nClaim + h.g.rows.size + (cnt3 h + cnt4 h + cnt5 h)) *
        (joinForm h.g (joinsA h P.NC).kf).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry) := by
    simp [clsValue, sumFrom, value_form, Nat.add_assoc]
  rw [e1, eJ]
  simp only [Nat.add_assoc, Nat.zero_add]
  ring

end Fo
