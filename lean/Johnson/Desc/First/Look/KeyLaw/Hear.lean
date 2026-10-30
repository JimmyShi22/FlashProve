-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Hear.lean: the stretches joined: the front of the hearing (alpha, the
tie, the parts, the join, the key trees, the table's tree) against the first five stretches of the
course.

Main names:
  joinAff, owed3: the form that joins the planes' claims; the ledger with the three debts entered.
  messages_inv: a run of messagesG that returns, call by call.
  start0, stand5, DataIs: the course's first stand; its stand behind the fifth stretch; what is
    asked of its public data.
  front_sim: the first five stretches.

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World eqTab orderDefault ofNat)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried)
open Lk6 (Dat Pub)
open Lk6.PortSim (noClaim sBits sLeaves byVarF joinF)
open Lk6.Mid (Dt Cs RowF pscC eqPairsF cLevels ordFirst ordDown cKey cKeys cHead cParts cJoin
  cTable cClo cZero cBits cntRowF chnC course dtOf)

/-- The form that makes the planes' claims one. -/
def joinAff (f : Face) (sG : Array ℕ) (x3 : Array E) : Aff :=
  (List.range (2 ^ f.mu)).foldl
    (fun (c : Aff) j =>
      if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) ((eqTab x3.reverse).getD j zeroE)
      else c + Aff.ofConst ((eqTab x3.reverse).getD j zeroE)) (Aff.ofConst zeroE)

/-- The ledger with the hearing's three debts entered. -/
def owed3 (F : Fork) : Fork :=
  (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").2

/-- **A run of the hearing without a shift that returns, call by call.** -/
theorem messages_inv {f : Face} {F G : Fork} {t u : Tape} {g : HeardG} (hs : f.shifted = false)
    (h : messagesG f F t = some (g, G, u)) :
    ∃ (alpha : E) (F5 : Fork) (t5 : Tape) (rows1 : Array Aff) (sZ : ℕ) (sG : Array ℕ) (F6 : Fork)
      (t6 : Tape) (rows2 : Array Aff) (roots : List Aff) (F7 : Fork) (t7 : Tape) (x3 : Array E)
      (F8 : Fork) (t8 : Tape) (rows3 : Array Aff) (keys : List (Array E × Aff)) (F9 : Fork)
      (t9 : Tape) (table : Carried) (F11 : Fork) (t11 : Tape) (lv0 : Psc) (F13 : Fork) (t13 : Tape)
      (zb0 : Array E) (lv : Psc) (F14 : Fork) (t14 : Tape) (x5 : Array E) (F15 : Fork) (t15 : Tape)
      (bits : Whole),
      Fl.answer .lkp (owed3 F) t = some (alpha, F5, t5) ∧
      tieG f.planes (f.factor zeroE alpha) F5 t5 = some ((rows1, sZ, sG), F6, t6) ∧
      partsG (f.parts.length - 1) rows1 (Aff.slot sZ) F6 t6 = some ((rows2, roots), F7, t7) ∧
      Fl.point .lkpPlanes f.mu F7 t7 = some (x3, F8, t8) ∧
      keysG f f.parts.zipIdx roots rows2 F8 t8 = some ((rows3, keys), F9, t9) ∧
      First.Prod.run f.mu f.d orderDefault
        { rows := rows3, point := x3.reverse, form := joinAff f sG x3 } F9 t9 =
          some (table, F11, t11) ∧
      Fl.pscBegin table.form F11 t11 = some (lv0, F13, t13) ∧
      Fl.roundsIn .eq lv0 ((List.range (f.mu + f.d)).map fun j =>
        (table.point.getD j zeroE, if j < f.d then 2 else 1)) F13 t13 = some ((zb0, lv), F14, t14) ∧
      Fl.point .zero (f.mu + f.d) F14 t14 = some (x5, F15, t15) ∧
      wholeStandIn (Aff.ofConst zeroE) x5.reverse.toList 2 1 (fun x =>
        subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F15 t15 =
          some (bits, G, u) ∧
      g.theta = zeroE ∧ g.alpha = alpha ∧ g.rows = table.rows.push bits.row ∧ g.leaves = lv ∧
      g.sBit = bits.sEnd ∧ g.keys = keys ∧ g.zb0 = zb0 ∧
      g.zb1 = (bits.challenges.take (f.mu + f.d)).toArray ∧ G.next = F.next + f.slots := by
  unfold messagesG at h
  rw [hs] at h
  replace h := bind_some h
  obtain ⟨slot0, F0, t0, e0, h⟩ := h
  replace e0 := slot_some e0
  obtain ⟨rfl, rfl, rfl⟩ := e0
  replace h := bind_some h
  obtain ⟨w1, F1, t1, e1, h⟩ := h
  replace e1 := owe_some e1
  obtain ⟨rfl, rfl⟩ := e1
  replace h := bind_some h
  obtain ⟨w2, F2, t2, e2, h⟩ := h
  replace e2 := owe_some e2
  obtain ⟨rfl, rfl⟩ := e2
  replace h := bind_some h
  obtain ⟨w3, F3, t3, e3, h⟩ := h
  replace e3 := owe_some e3
  obtain ⟨rfl, rfl⟩ := e3
  replace h := bind_some h
  obtain ⟨theta, F4, t4, e4, h⟩ := h
  cases pure_some e4
  replace h := bind_some h
  obtain ⟨alpha, F5, t5, e5, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows1, sZ, sG⟩, F6, t6, e6, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows2, roots⟩, F7, t7, e7, h⟩ := h
  replace h := bind_some h
  obtain ⟨x3, F8, t8, e8, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows3, keys⟩, F9, t9, e9, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F10, t10, e10, h⟩ := h
  replace e10 := must_some e10
  obtain ⟨-, rfl, rfl⟩ := e10
  replace h := bind_some h
  obtain ⟨table, F11, t11, e11, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F12, t12, e12, h⟩ := h
  replace e12 := must_some e12
  obtain ⟨-, rfl, rfl⟩ := e12
  replace h := bind_some h
  obtain ⟨lv0, F13, t13, e13, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨zb0, lv⟩, F14, t14, e14, h⟩ := h
  replace h := bind_some h
  obtain ⟨x5, F15, t15, e15, h⟩ := h
  replace h := bind_some h
  obtain ⟨bits, F16, t16, e16, h⟩ := h
  replace h := bind_some h
  obtain ⟨sl, F17, t17, e17, h⟩ := h
  replace e17 := slot_some e17
  obtain ⟨rfl, rfl, rfl⟩ := e17
  replace h := bind_some h
  obtain ⟨_, F18, t18, e18, h⟩ := h
  replace e18 := must_some e18
  obtain ⟨hmust, rfl, rfl⟩ := e18
  cases pure_some h
  exact ⟨alpha, F5, t5, rows1, sZ, sG, F6, t6, rows2, roots, F7, t7, x3, F8, t8, rows3, keys, _, _,
    table, _, _, lv0, F13, t13, zb0, lv, F14, t14, x5, F15, t15, bits, e5, e6, e7, e8, e9, e11, e13,
    e14, e15, e16, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by
      simp only [Bool.and_eq_true, beq_iff_eq] at hmust
      exact hmust.1⟩


variable {W : PscF.World} {home : ℕ → Slot}

/-- The stand at which a course begins. -/
def start0 (fl : List (Lk6.Flat.RV GE)) : Cs :=
  ⟨fl, 0, 0, [], 0, noClaim, noClaim, noClaim, noClaim, fun _ => noClaim, fun _ => noClaim,
    fun _ => noClaim, []⟩

/-- The course's stand behind its fifth stretch. -/
def stand5 (D : Dt) (fl : List (Lk6.Flat.RV GE)) : Cs :=
  cTable D (cKeys D (cJoin D (cParts D (cHead D fl 0 0))))

/-- What the public data of the course must be: the face's numbers, orders and factor. -/
structure DataIs (D : Dt) (f : Face) : Prop where
  pl : D.S.pl = f.planes
  m : D.S.m = f.parts.length
  mu : D.S.mu = f.mu
  d : D.S.d = f.d
  v : ∀ i, D.S.v i = f.parts.getD i 0
  two : 2 ≤ f.planes
  one : 1 ≤ f.parts.length
  oneD : 1 ≤ f.d
  orders : ∀ i m, f.orders i m = if m + 1 = D.S.v i then ordFirst D.S.order m else ordDown m
  factor : ∀ al, readE (f.factor zeroE al) = D.fac (readE al)

/-- **The first five stretches.** -/
theorem front_sim {D : Dt} {f : Face} (hD : DataIs D f) (hok : f.ok = true) {F : Fork} {t : Tape}
    (hF : Sized F) {pat : List Bool}
    (hal : Al home D.ms D.ix (own (7 + 6 * (f.planes - 2)) ++ (own (5 * (f.parts.length - 1)) ++
      (keysPat f.parts ++ (levelsPat false f.mu f.d 0 ++ pat)))) F.next 0 0)
    {alpha : E} {F5 : Fork} {t5 : Tape} {rows1 : Array Aff} {sZ : ℕ} {sG : Array ℕ} {F6 : Fork}
    {t6 : Tape} {rows2 : Array Aff} {roots : List Aff} {F7 : Fork} {t7 : Tape} {x3 : Array E}
    {F8 : Fork} {t8 : Tape} {rows3 : Array Aff} {keys : List (Array E × Aff)} {F9 : Fork}
    {t9 : Tape} {table : Carried} {F11 : Fork} {t11 : Tape}
    (e5 : Fl.answer .lkp (owed3 F) t = some (alpha, F5, t5))
    (e6 : tieG f.planes (f.factor zeroE alpha) F5 t5 = some ((rows1, sZ, sG), F6, t6))
    (e7 : partsG (f.parts.length - 1) rows1 (Aff.slot sZ) F6 t6 = some ((rows2, roots), F7, t7))
    (e8 : Fl.point .lkpPlanes f.mu F7 t7 = some (x3, F8, t8))
    (e9 : keysG f f.parts.zipIdx roots rows2 F8 t8 = some ((rows3, keys), F9, t9))
    (e11 : First.Prod.run f.mu f.d orderDefault
      { rows := rows3, point := x3.reverse, form := joinAff f sG x3 } F9 t9 =
        some (table, F11, t11)) :
    St W home D F11 t11 (stand5 D (flatK (t.map key))) pat table.rows.toList ∧
      RC W home F11 table.form (stand5 D (flatK (t.map key))).top ∧
      (stand5 D (flatK (t.map key))).top.point = table.point.toList.reverse.map readE ∧
      table.point.size = f.mu + f.d ∧
      (stand5 D (flatK (t.map key))).alpha = readE alpha ∧ Later F F11 ∧
      (flatK (t.map key)).head? = some ([], [readE alpha]) ∧ keys.length = f.parts.length ∧
      (∀ q < f.parts.length, RC W home F11 (keys.getD q (#[], {})).2
          ((stand5 D (flatK (t.map key))).leaves q) ∧
        ((stand5 D (flatK (t.map key))).leaves q).point =
          (keys.getD q (#[], {})).1.toList.reverse.map readE) ∧
      Shp t t11 ([(RoundName.lkp.name, 0, 1, 0)] ++ ((pscShape [] (some (3, 3)) ++
          (List.range (f.planes - 2)).flatMap fun _ => pscShape [] (some (3, 2))) ++
        (((List.range (f.parts.length - 1)).flatMap fun _ => pscShape [] (some (2, 2))) ++
          ([(RoundName.lkpPlanes.name, 0, f.mu, 0)] ++ (keysShape f.parts ++
            levelsShape f.mu f.d 0))))) := by
  have st0 : St W home D (owed3 F) t (start0 (flatK (t.map key))) _ [] :=
    ⟨⟨hF, rfl⟩, hal, List.Forall₂.nil⟩
  obtain ⟨rfl, st1, hdraw, sh1⟩ := answer_st e5 st0
  obtain ⟨a1, a2, a2p, a3, a4, a5, a6⟩ := tie_sim
    (s1 := { (start0 (flatK (t.map key))).next with alpha := (start0 (flatK (t.map key))).draw })
    e6 hD.two hD.pl (st1.congr rfl rfl rfl rfl) (by
      show _ = D.fac (start0 (flatK (t.map key))).draw
      rw [hdraw, hD.factor])
  obtain ⟨sA, hsA⟩ : ∃ s, s = cHead D (flatK (t.map key)) 0 0 := ⟨_, rfl⟩
  have hsA' : headTail D { (start0 (flatK (t.map key))).next with
      alpha := (start0 (flatK (t.map key))).draw } = sA := by rw [hsA]; rfl
  rw [hsA'] at a1 a2 a2p a3 a4
  have a4' : sA.alpha = readE alpha := a4.trans hdraw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := parts_sim hD.m hD.one e7 a1 a2 a2p
  obtain ⟨sB, hsB⟩ : ∃ s, s = cParts D sA := ⟨_, rfl⟩
  rw [← hsB] at b1 b3 b4 b5
  obtain ⟨rfl, c1, c2, c3, c4⟩ := point_st e8 b1
  obtain ⟨sC, hsC⟩ : ∃ s, s = cJoin D sB := ⟨_, rfl⟩
  have c1' : St W home D F8 t8 sC (keysPat f.parts ++ (levelsPat false f.mu f.d 0 ++ pat))
      rows2.toList := by
    rw [hsC]; exact c1.congr rfl rfl rfl rfl
  have hCroots : sC.roots = sB.roots := by rw [hsC]; rfl
  have hCalpha : sC.alpha = sB.alpha := by rw [hsC]; rfl
  have hCtop : sC.top = joinF D.S.mu sB.draws ((List.range D.S.pl).map sB.planes) := by
    rw [hsC]; rfl
  have hT : RC W home F8 (joinAff f sG x3) sC.top := by
    rw [hCtop, hD.mu, hD.pl, c2]
    exact join_loop_sim (fun j hj => by rw [b4]; exact (a3 j hj).later b6) _ _ _
      ((Reads.const F8 zeroE).congr rfl readE_zero.symm)
      (fun j hj => eqTab_read x3 j (by rw [c3]; exact List.mem_range.1 hj))
  have hTp : sC.top.point = x3.reverse.toList.reverse.map readE := by
    rw [hCtop, Lk6.PortSim.joinF_point, c2]
    simp
  obtain ⟨d1, d2, d3, -, d5, d6, d7, d8⟩ := keys_sim f f.parts 0 roots rows2 F8 F9 t8 t9
    (rows3, keys) sC (levelsPat false f.mu f.d 0 ++ pat) e9 b2
    (fun q hq => by
      rw [Nat.zero_add]
      exact ⟨hD.v q, ordIs_keys D (f.orders q) _ (fun m => by rw [hD.orders, hD.v])
        (ok_orders hok q hq) _ 0 (Nat.zero_add _)⟩)
    c1'
    (fun q hq => by
      rw [Nat.zero_add, hCroots]
      exact b3 q hq)
  obtain ⟨sD, hsD⟩ : ∃ s, s = cKeys D sC := ⟨_, rfl⟩
  have hsD' : cKey D f.parts.length 0 sC = sD := by rw [hsD, ← hD.m]; rfl
  rw [hsD'] at d1 d3 d5 d6
  unfold First.Prod.run at e11
  rw [List.range_eq_range'] at e11
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := levels_sim false f.mu orderDefault f.d 0 _ table F9 F11 t9
    t11 sD.top sD pat e11 (ordIs_table D f.mu f.d 0) d1 (by rw [d6]; exact hT.later d7)
    (by rw [d6]; exact hTp) (by simp [c3])
  have hs5 : stand5 D (flatK (t.map key)) =
      { (cLevels D false f.mu f.d 0 sD.top sD).2 with
        top := (cLevels D false f.mu f.d 0 sD.top sD).1 } := by
    unfold stand5
    rw [← hsA, ← hsB, ← hsC, ← hsD, ← hD.mu, ← hD.d]
    rfl
  rw [hs5]
  have lF : Later F (owed3 F) :=
    ((PscRun.owe_later F _).trans (PscRun.owe_later _ _)).trans (PscRun.owe_later _ _)
  have hhead : (flatK (t.map key)).head? = some ([], [readE alpha]) := by
    obtain ⟨w, rfl, -⟩ := answer_fl e5
    rfl
  refine ⟨l1.congr rfl rfl rfl rfl, l2, l3, by omega, ?_,
    lF.trans (a5.trans (b6.trans (d7.trans l6))), hhead, d2, fun q hq => ?_, ?_⟩
  · show (cLevels D false f.mu f.d 0 sD.top sD).2.alpha = _
    rw [l5.alpha, d5, hCalpha, b5, a4']
  · show RC W home F11 _ ((cLevels D false f.mu f.d 0 sD.top sD).2.leaves q) ∧
      ((cLevels D false f.mu f.d 0 sD.top sD).2.leaves q).point = _
    rw [l5.leaves]
    have := d3 q hq
    rw [Nat.zero_add] at this
    exact ⟨this.1.later l6, this.2⟩
  · exact sh1.trans (a6.trans (b7.trans (c4.trans (d8.trans l7))))

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.front_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.messages_inv
