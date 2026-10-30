-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/HearSaid.lean: what the port's routines for an attention sub-proof's own messages
have heard, together with what their records hold of it, and the typed side of each sumcheck in the
port's records.

OnBytes/Tie/Pv/Att/HearStages.lean says what was heard. Here the same stages come with the records:
the lists that were heard are those from which each record's running claim, challenges and weights
are made, and each start form's public part is named.

Main names:
  Rec p r C t ws dY n H: the record p of a sumcheck, with the challenges r, is that of what was
    heard (H): its weights, challenges and running claim are those of H under ws and the weight of
    the further variable (PscAt, OnBytes/Tie/Pv/Psc/PscTie.lean); its eps is H's; its start form is
    C and its target t; each round has as many scalars as its weight says; there are dY scalars in
    the round of the further variable and n end values.
  pair_said, key_said: a sumcheck of products with its row, and keyAtIndexIn: the stage heard, the
    public part of the start form, and Rec, at the same lists.
  UnitsSaid, units_said: the score units.
  DivideSaid, divide_said, AttainSaid, attain_said: the stages of divide and of attain with their
    records; gam; the number of elements of the point (OnBytes/Tie/Pv/Att/HearPoint.lean) and its
    parts tg and ti.
  own_said: scores, divide and attain, one after the other.
  said_out: the typed side: for letters S of a sumcheck and data D (SumH,
    OnBytes/Tie/Pv/Att/OwnTie.lean) whose lists are those of a record with Rec at S's degrees and at
    the target D.t: the output D.out has the reading of the record's eps and of its running claim;
    its point is the reading of the record's challenges, then of beta; its end values are D.v.

Limits: one direction: from the routines' success, from a state whose arrays on slots have their
length. What the rows and the slots of the end values are worth is said in
OnBytes/Tie/Pv/Att/RowTie.lean and TiesFull.lean for each sumcheck.
That the reading of a beta is not 0 is a premise (a field of SumH).
-/
import OnBytes.Tie.Pv.Att.OwnTie
import OnBytes.Tie.Pv.Att.HearPoint
import OnBytes.Tie.Pv.Psc.Run.PscMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Psc (Weight hearMany hearOne)

/-! ## What lies under a filled slot stays -/

/-- Under slot j lies the scalar y. -/
def Lies (F : Fork) (j : Nat) (y : E) : Prop :=
  F.gotF.getD j false = true ∧ F.vp.getD j zeroE = y

/-- What lies under a slot in F lies there in G. -/
def Kept (F G : Fork) : Prop := ∀ j y, Lies F j y → Lies G j y

theorem Kept.refl (F : Fork) : Kept F F := fun _ _ h => h

theorem Kept.trans {F G H : Fork} (a : Kept F G) (b : Kept G H) : Kept F H :=
  fun j y h => b j y (a j y h)

theorem got_both (a : Array Bool) (j : Nat) (h1 : a.getD j false = true)
    (h2 : a.getD j true = false) : False := by
  by_cases hj : j < a.size
  · simp [Array.getD, hj] at h1 h2
    rw [h1] at h2
    cases h2
  · simp [Array.getD, hj] at h1

/-- A run of hidden values writes under slots that were empty. -/
theorem filled_kept {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) : Kept F G := fun j y h => by
  by_cases hr : j < first ∨ first + l.length ≤ j
  · obtain ⟨b1, _, b3⟩ := a.other j hr
    exact ⟨by rw [b3 false]; exact h.1, by rw [b1]; exact h.2⟩
  · have hi : j - first < l.length := by omega
    obtain ⟨_, _, _, b4⟩ := a.here (j - first) hi
    rw [show first + (j - first) = j by omega] at b4
    exact (got_both _ j h.1 b4).elim

theorem filled_lies {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) (i : Nat) (hi : i < l.length) :
    Lies G (first + i) (l.getD i zeroE) := by
  obtain ⟨b1, _, b3, _⟩ := a.here i hi
  exact ⟨b3, b1⟩

/-- The world in which each hidden value is what was shown for it, and each entry is 0. -/
def shownW {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) : World K :=
  ⟨fun j => ρ.val (F.vp.getD j zeroE), fun _ _ _ => 0⟩

/-- The public part of a form, read, is the form's value in that world. -/
theorem public_value {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) (C : Aff) (t : E)
    (h : F.publicPart C = some t) : ρ.val t = C.value ρ (shownW ρ F) := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  rw [publicPart_fold ρ F _ _ _ h]
  have he : (C.ents.toList.map (Ent.value ρ (shownW ρ F))).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      simp [Ent.value, shownW]
  unfold Aff.value
  rw [he, zero_add, add_comm]
  rfl

/-- The value of a weighted sum of forms. -/
theorem value_weightedSum {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (w : Array E)
    (form : Nat → Aff) : ∀ n : Nat, (weightedSum n w form).value ρ W =
      ∑ b : Fin n, ρ.val (w.getD b.1 zeroE) * (form b.1).value ρ W
  | 0 => by simp [weightedSum, Aff.value_ofConst, ρ.zero]
  | n + 1 => by
    have ih := value_weightedSum ρ W w form n
    unfold weightedSum at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Aff.value_addMul, ih,
      Fin.sum_univ_castSucc]
    rfl

/-- The record is that of what was heard. -/
structure Rec (p : Psc) (r : Array E) (C : Aff) (t : E) (ws : List Weight) (dY n : Nat)
    (H : PscH) : Prop where
  at_ : PscAt p (ws ++ [Weight.atZero (dY + 1)]) (H.rs ++ [(H.sentY, H.beta)]) H.mu
  eps : p.eps = H.eps
  start : p.start = C
  target : p.target = t
  r : r.toList = H.rs.map (·.2)
  lens : H.rs.map (·.1.length) = ws.map fun w => w.d - 1
  lenY : H.sentY.length = dY
  lenV : H.v.length = n

/-- Two of the port's elements are read alike by every reading. -/
def SameRead (t y : E) : Prop := ∀ (K : Type) [CommRing K] (ρ : Reading K), ρ.val t = ρ.val y

/-- t is read as the sum over b < n of w[b] times y b. -/
def SumRead (t : E) (n : Nat) (w : Array E) (y : Nat → E) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K),
    ρ.val t = ∑ b : Fin n, ρ.val (w.getD b.1 zeroE) * ρ.val (y b.1)

/-- The public part of the form of one slot is read as what lies under the slot. -/
theorem slot_read {F : Fork} {j : Nat} {y t : E} (hl : Lies F j y)
    (h : F.publicPart (Aff.slot j) = some t) : SameRead t y := fun K _ ρ => by
  rw [public_value ρ F _ t h, Aff.value_slot]
  show ρ.val (F.vp.getD j zeroE) = _
  rw [hl.2]

/-- The public part of a weighted sum of slots. -/
theorem sum_read {F : Fork} {n : Nat} {w : Array E} {s : Nat → Nat} {y : Nat → E} {t : E}
    (hl : ∀ b, b < n → Lies F (s b) (y b))
    (h : F.publicPart (weightedSum n w fun b => Aff.slot (s b)) = some t) : SumRead t n w y :=
  fun K _ ρ => by
    rw [public_value ρ F _ t h, value_weightedSum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Aff.value_slot]
    show _ * ρ.val (F.vp.getD (s b.1) zeroE) = _
    rw [(hl b.1 b.2).2]

/-- Hidden values that ride in a message: what lies under their slots, and what stays. -/
theorem claimsIn_lies (n : Nat) (F G : Fork) (c c' : Ctx) (j : Nat)
    (h : SubM.claimsIn n F c = .ok ((j, G), c')) (hz : Sized F) :
    ∃ v : List E, (Blk.recvEs n).Yields c v c' ∧ v.length = n ∧ j = F.next ∧ Sized G ∧ Kept F G ∧
      ∀ i, i < n → Lies G (j + i) (v.getD i zeroE) := by
  obtain ⟨v, a1, a2, a3, a4, a5⟩ := claimsIn_said n F G c c' j h hz
  exact ⟨v, a1, a2, a3, a5, fun j y hl => filled_kept a4 j y hl, fun i hi => by
    rw [a3]
    exact filled_lies a4 i (by rw [a2]; exact hi)⟩

/-- A sumcheck of products behind scalars that are still open. -/
theorem pair_said {nv nb : Nat} {C : Aff} {W : Array E → Array E} {o : Attention.Sc3}
    {F G : Fork} {c c' : Ctx} (h : Pair nv nb C W o F c G c') (hz : Sized F) (pre : List E)
    (c0 : Ctx) (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    ∃ (t : E) (H : PscH), F.publicPart C = some t ∧ HeardAs [.sum pre (ws3 nv) 2 H] c0 c' ∧
      Rec o.p o.r C t (ws3 nv) 2 (2 * nb) H ∧ Kept F G ∧
      ∀ i, i < 2 * nb → Lies G (o.sEnd + i) (H.v.getD i zeroE) := by
  obtain ⟨o1, F2, c2, h1, h2⟩ := h
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, _, _, a12⟩ :=
    sc3In_seam _ _ _ o1 F F2 c c2 h1 hz
  obtain ⟨b1, _, _, b3, b4, b5, _, b8⟩ := sc3Row_ok o1 o _ F2 G c2 c' h2 a12.sized
  have hat := ended_pscAt a3
  refine ⟨τ, ⟨mu, o1.p.eps, rs, sentY, beta, v⟩, a1, ⟨c, c', ?_, rfl⟩, ?_,
    fun j y hl => filled_kept b8 j y (filled_kept a12 j y hl), fun i hi => ?_⟩
  · rw [b1]
    exact Parts.ride h0 a2
  · rw [b3, b4]
    exact ⟨⟨hat.vars, hat.r, hat.claim⟩, rfl, a3.start, a3.target, a4,
      by rw [List.map_replicate]; exact a5, a6, a7⟩
  · rw [b5]
    exact filled_kept b8 _ _ (filled_lies a12 i (by rw [a7]; exact hi))

/-- The weights of the sumcheck by degrees. -/
abbrev wsD (S : Attention.Shape) : List Weight := S.scdDegrees.map fun d => Weight.plain (d + 1)

/-- The sumcheck by degrees with the round that batches its pairs. -/
theorem key_said (S : Attention.Shape) (scF : Attention.Sc3) (o : Attention.Scd) (F G : Fork)
    (c c' : Ctx)
    (h : keyAtIndexIn S scF F c = .ok ((o, G), c')) (hz : Sized F) :
    ∃ (x t : E) (H : PscH),
      F.publicPart (weightedSum S.NP (powers x S.NP) (sc3B scF)) = some t ∧
      HeardAs [.bat [] S.NP x, .sum [] (wsD S) (S.cf.lt + 1) H] c c' ∧
      Rec o.p o.r (weightedSum S.NP (powers x S.NP) (sc3B scF)) t (wsD S) (S.cf.lt + 1)
        (S.Lam + S.NP * S.cf.lt) H ∧ Sized G := by
  obtain ⟨om4, F1, c1, o1, F2, c2, h1, h2, h3⟩ := keyAtIndexIn_flat S scF o F G c c' h
  obtain ⟨eF, x, f1, f2⟩ := batch_heard S.NP F F1 c c1 om4 h1 [] c (recvEs_zero c)
  rw [eF, f2] at h2
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, _, _, _, a12⟩ :=
    scdIn_seam _ _ _ _ o1 F F2 c1 c2 h2 hz
  obtain ⟨b1, _, b3, b4, _, b6⟩ := scdRow_ok o1 o _ F2 G c2 c' h3 a12.sized
  have hat := ended_pscAt a3
  refine ⟨x, τ, ⟨mu, o1.p.eps, rs, sentY, beta, v⟩, a1,
    HeardAs.append [_] _ c c1 c' f1 ⟨c1, c', ?_, rfl⟩, ?_, b6.sized⟩
  · rw [b1]
    exact a2
  · rw [b3, b4]
    exact ⟨⟨hat.vars, hat.r, hat.claim⟩, rfl, a3.start, a3.target, a4,
      (plain_sizes S.scdDegrees).symm ▸ a5, a6, a7⟩

/-- The score units' stages with their records. pre: the scalars open before the first. Each
unit's target is read as the last of its seven scalars. -/
def UnitsSaid (S : Attention.Shape) (zk : Array (Array E)) : List (Nat × ACall × Seg) →
    List Score → List E → List StageH → Prop
  | [], [], _, [] => True
  | u :: us, k :: ks, pre, .sum riders ws dY H :: l =>
    ws = ws3 (S.nvKF u.2.2) ∧ dY = 2 ∧
      (∃ (v7 : List E) (t : E), v7.length = 7 ∧ riders = pre ++ v7 ∧
        SameRead t (v7.getD 6 zeroE) ∧
        Rec k.sc.p k.sc.r (Aff.slot (k.s0 + 6)) t (ws3 (S.nvKF u.2.2)) 2
          (2 * (pieces u.2.1 (zk.getD u.1 #[]) u.2.2).size) H) ∧
      UnitsSaid S zk us ks [] l
  | _, _, _, _ => False

theorem units_said (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (ks : List Score) (F G : Fork) (c c' : Ctx) (pre : List E)
      (c0 : Ctx), UnitsRan S zk us ks F c G c' → Sized F →
      (Blk.recvEs pre.length).Yields c0 pre c →
      ∃ (st : List StageH) (left : List E) (cm : Ctx), HeardAs st c0 cm ∧
        (Blk.recvEs left.length).Yields cm left c' ∧ Sized G ∧ UnitsSaid S zk us ks pre st ∧
        left = (if us = [] then pre else [])
  | [], [], F, G, c, c', pre, c0, h, hz, h0 => by
    obtain ⟨e1, e2⟩ := h
    rw [e1, e2]
    exact ⟨[], pre, c0, rfl, h0, hz, trivial, rfl⟩
  | u :: us, k :: ks, F, G, c, c', pre, c0, h, hz, h0 => by
    obtain ⟨F1, c1, ⟨Fa, ca, ha, hp⟩, hr⟩ := h
    obtain ⟨v7, a1, a2, _, a5, _, a7⟩ := claimsIn_lies 7 F Fa c ca k.s0 ha hz
    have hj : (Blk.recvEs (pre ++ v7).length).Yields c0 (pre ++ v7) ca := by
      rw [List.length_append, a2]
      exact recvEs_add pre.length 7 pre v7 c0 c ca h0 a1
    obtain ⟨t, H, b0, b1, b2, _, _⟩ := pair_said hp a5 (pre ++ v7) c0 hj
    obtain ⟨st, left, cm, d1, d2, d3, d4, d5⟩ :=
      units_said S zk us ks F1 G c1 c' [] c1 hr (hp.sized a5) (recvEs_zero c1)
    refine ⟨.sum (pre ++ v7) (ws3 (S.nvKF u.2.2)) 2 H :: st, left, cm,
      HeardAs.append [_] st c0 c1 cm b1 d1, d2, d3,
      ⟨rfl, rfl, ⟨v7, t, a2, rfl, slot_read (a7 6 (by omega)) b0, b2⟩, d4⟩, ?_⟩
    rw [d5]
    simp
  | [], _ :: _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => h.elim

/-- The four stages of divide with their records. Each target is read as the scalar heard from
which its sumcheck starts. -/
structure DivideSaid (S : Attention.Shape) (d : Divide) (pre : List E) (c0 c' : Ctx)
    (v5 vI v2 vC : List E)
    (x : E) (HE HM HD : PscH) (tE tM tD : E) : Prop where
  heard : HeardAs [.sum (pre ++ (v5 ++ (vI ++ v2))) (ws3 S.nvE) 2 HE, .bat [] 2 x,
    .sum vC (ws3 S.nvVM) 2 HM, .sum [] (ws3 S.nvVD) 2 HD] c0 c'
  l5 : v5.length = 5
  lI : vI.length = S.cf.lt
  l2 : v2.length = 2
  lC : vC.length = 2
  gam : d.gam = (powers x 2).getD 1 zeroE
  rE : Rec d.scE.p d.scE.r (Aff.slot (d.s5 + 1)) tE (ws3 S.nvE) 2 (2 * S.NP) HE
  rM : Rec d.vpm.p d.vpm.r (Aff.slot d.sCl) tM (ws3 S.nvVM) 2 (2 * S.NP) HM
  rD : Rec d.vpd.p d.vpd.r (Aff.slot (d.sCl + 1)) tD (ws3 S.nvVD) 2 (2 * S.NP) HD
  tEr : SameRead tE (v5.getD 1 zeroE)
  tMr : SameRead tM (vC.getD 0 zeroE)
  tDr : SameRead tD (vC.getD 1 zeroE)

theorem divide_said (S : Attention.Shape) (d : Divide) (F G : Fork) (c c' : Ctx)
    (h : DivideRan S d F G c c') (hz : Sized F) (pre : List E) (c0 : Ctx)
    (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    ∃ (v5 vI v2 vC : List E) (x : E) (HE HM HD : PscH) (tE tM tD : E),
      DivideSaid S d pre c0 c' v5 vI v2 vC x HE HM HD tE tM tD ∧ Sized G := by
  obtain ⟨F1, c1, F2, c2, F3, c3, F4, c4, gamP, F5, c5, F6, c6, F7, c7, h1, h2, h3, pE, hb, hg, h6,
    pM, pD⟩ := h.ran
  obtain ⟨v5, a1, a2, _, a5, _, a7⟩ := claimsIn_lies 5 F F1 c c1 _ h1 hz
  obtain ⟨vI, b1, b2, _, b5, b6, _⟩ := claimsIn_lies _ F1 F2 c1 c2 _ h2 a5
  obtain ⟨v2, d1, d2, _, d5, d6, _⟩ := claimsIn_lies 2 F2 F3 c2 c3 _ h3 b5
  have hj : (Blk.recvEs (pre ++ (v5 ++ (vI ++ v2))).length).Yields c0 (pre ++ (v5 ++ (vI ++ v2)))
      c3 := by
    simp only [List.length_append]
    rw [a2, b2, d2]
    exact recvEs_add _ _ _ _ c0 c c3 h0 (recvEs_add _ _ _ _ c c1 c3 a1
      (recvEs_add _ _ _ _ c1 c2 c3 b1 d1))
  obtain ⟨tE, HE, e0, e1, e2, _, _⟩ := pair_said pE d5 _ c0 hj
  have s4 := pE.sized d5
  obtain ⟨eF, x, f1, f2⟩ := batch_heard 2 F4 F5 c4 c5 gamP hb [] c4 (recvEs_zero c4)
  rw [eF] at h6
  obtain ⟨vC, g1, g2, _, g5, _, g7⟩ := claimsIn_lies 2 F4 F6 c5 c6 _ h6 s4
  obtain ⟨tM, HM, m0, m1, m2, m3, _⟩ := pair_said pM g5 vC c5 (by rw [g2]; exact g1)
  have s7 := pM.sized g5
  obtain ⟨tD, HD, n0, n1, n2, _, _⟩ := pair_said pD s7 [] c7 (recvEs_zero c7)
  exact ⟨v5, vI, v2, vC, x, HE, HM, HD, tE, tM, tD,
    ⟨HeardAs.append [_] _ c0 c4 c' e1 (HeardAs.append [_] _ c4 c5 c' f1
      (HeardAs.append [_] _ c5 c7 c' m1 n1)), a2, b2, d2, g2, by rw [hg, f2], e2, m2, n2,
      slot_read (d6 _ _ (b6 _ _ (a7 1 (by omega)))) e0, slot_read (g7 0 (by omega)) m0,
      slot_read (m3 _ _ (g7 1 (by omega))) n0⟩,
    pD.sized s7⟩

/-- The seven stages of attain with their records. The targets are read as the batches, by the
powers of the elements drawn, of the maxima heard and of the second end values heard; the last
as 0. -/
structure AttainSaid (S : Attention.Shape) (x : Attain) (c c' : Ctx) (d : Fmt.Drawn) (vM : List E)
    (xF xD xH : E) (HF HD HH : PscH) (tF tD tH : E) : Prop where
  heard : HeardAs [.point d, .bat vM S.NP xF, .sum [] (ws3 S.nvF) 2 HF, .bat [] S.NP xD,
    .sum [] (wsD S) (S.cf.lt + 1) HD, .bat [] S.NP xH, .sum [] (ws3 S.nvH) 2 HH] c c'
  lP : d.elems.length = 2 * S.cf.lgk + 2 * S.cf.lt + 4
  lM : vM.length = S.NP
  tg : x.tg = (d.elems.map E.ofTriple).toArray.extract 0 S.cf.lgk
  ti : x.ti = (d.elems.map E.ofTriple).toArray.extract S.cf.lgk (S.cf.lgk + S.cf.lt)
  rF : Rec x.scF.p x.scF.r (weightedSum S.NP (powers xF S.NP) fun b => Aff.slot (x.sM6 + b)) tF
    (ws3 S.nvF) 2 (2 * S.NP) HF
  rD : Rec x.scd.p x.scd.r (weightedSum S.NP (powers xD S.NP) (sc3B x.scF)) tD (wsD S)
    (S.cf.lt + 1) (S.Lam + S.NP * S.cf.lt) HD
  rH : Rec x.scH.p x.scH.r (Aff.ofConst zeroE) tH (ws3 S.nvH) 2 (2 * S.NP) HH
  tFr : SumRead tF S.NP (powers xF S.NP) fun b => vM.getD b zeroE
  tDr : SumRead tD S.NP (powers xD S.NP) fun b => HF.v.getD (2 * b + 1) zeroE
  tHr : SameRead tH zeroE

theorem attain_said (S : Attention.Shape) (x : Attain) (F G : Fork) (c c' : Ctx)
    (h : AttainRan S x F G c c') (hz : Sized F) :
    ∃ (d : Fmt.Drawn) (vM : List E) (xF xD xH : E) (HF HD HH : PscH) (tF tD tH : E),
      AttainSaid S x c c' d vM xF xD xH HF HD HH tF tD tH ∧ Sized G := by
  obtain ⟨pts, Fp, cp, F0, c0, om, F1, c1, F2, c2, F3, c3, om5, F4, c4, hp, t1, t2, hM, hb, pF, hK,
    hb5, pH⟩ := h.ran
  obtain ⟨eP, d, p1, p2, p3⟩ := point_said _ F Fp c cp pts hp
  rw [eP] at hM
  obtain ⟨vM, a1, a2, _, a5, _, a7⟩ := claimsIn_lies _ F F0 cp c0 _ hM hz
  obtain ⟨eF, xF, f1, f2⟩ := batch_heard S.NP F0 F1 c0 c1 om hb vM cp (by rw [a2]; exact a1)
  rw [eF, f2] at pF
  obtain ⟨tF, HF, g0, g1, g2, _, g4⟩ := pair_said pF a5 [] c1 (recvEs_zero c1)
  have s2 := pF.sized a5
  obtain ⟨xD, tD, HD, k0, k1, k2, k3⟩ := key_said S x.scF x.scd F2 F3 c2 c3 hK s2
  obtain ⟨e5, xH, m1, _⟩ := batch_heard S.NP F3 F4 c3 c4 om5 hb5 [] c3 (recvEs_zero c3)
  rw [e5] at pH
  obtain ⟨tH, HH, n0, n1, n2, _, _⟩ := pair_said pH k3 [] c4 (recvEs_zero c4)
  exact ⟨d, vM, xF, xD, xH, HF, HD, HH, tF, tD, tH,
    ⟨HeardAs.append [_] _ c cp c' ⟨cp, p1, rfl⟩ (HeardAs.append [_] _ cp c1 c' f1
      (HeardAs.append [_] _ c1 c2 c' g1 (HeardAs.append [_, _] _ c2 c3 c' k1
        (HeardAs.append [_] _ c3 c4 c' m1 n1)))), p3, a2, by rw [t1, p2], by rw [t2, p2], g2, k2,
      n2, sum_read a7 g0, sum_read (fun b hb => g4 (2 * b + 1) (by omega)) k0,
      fun K _ ρ => by rw [public_value ρ F3 _ tH n0, Aff.value_ofConst]⟩,
    pH.sized k3⟩

/-- scores, divide and attain, one after the other, with their records. -/
theorem own_said (S : Attention.Shape) (zk : Array (Array E))
    (sc : Array PlaneClaim × Array Score)
    (d : Divide) (x : Attain) (F F1 F2 G : Fork) (c c1 c2 c' : Ctx)
    (hs : scores S zk F c = .ok ((sc, F1), c1)) (hd : divide S zk F1 c1 = .ok ((d, F2), c2))
    (hx : attain S F2 c2 = .ok ((x, G), c')) (hz : Sized F) :
    ∃ (ks : List Score) (planes : List E) (units : List StageH) (cm : Ctx)
      (v5 vI v2 vC : List E) (xV : E) (HE HM HVD : PscH) (tE tM tVD : E) (dr : Fmt.Drawn)
      (vM : List E) (xF xD xH : E) (HF HD HH : PscH) (tF tD tH : E),
      sc.2 = ks.toArray ∧ planes.length = 3 * (unitsOf S Table.kr [Seg.rm, Seg.rd]).length ∧
      UnitsSaid S zk (unitsOf S Table.kfd [Seg.fm, Seg.fd]) ks planes units ∧
      HeardAs units c cm ∧
      DivideSaid S d (if unitsOf S Table.kfd [Seg.fm, Seg.fd] = [] then planes else []) cm c2
        v5 vI v2 vC xV HE HM HVD tE tM tVD ∧
      AttainSaid S x c2 c' dr vM xF xD xH HF HD HH tF tD tH ∧ Sized G := by
  obtain ⟨Fa, ca, ks, p1, p2, p3⟩ := scores_ran S zk sc F F1 c c1 hs
  obtain ⟨planes, a1, a2, a3⟩ := planes_open _ F Fa c ca p1 hz
  obtain ⟨units, left, cm, b1, b2, b3, b4, b5⟩ :=
    units_said S zk _ ks Fa F1 ca c1 planes c p3 a3 a1
  obtain ⟨v5, vI, v2, vC, xV, HE, HM, HVD, tE, tM, tVD, d1, d2⟩ :=
    divide_said S d F1 F2 c1 c2 (divide_ran S zk d F1 F2 c1 c2 hd) b3 left cm b2
  obtain ⟨dr, vM, xF, xD, xH, HF, HD, HH, tF, tD, tH, e1, e2⟩ :=
    attain_said S x F2 G c2 c' (attain_ran S x F2 G c2 c' hx) d2
  rw [b5] at d1
  exact ⟨ks, planes, units, cm, v5, vI, v2, vC, xV, HE, HM, HVD, tE, tM, tVD, dr, vM, xF, xD, xH,
    HF, HD, HH, tF, tD, tH, p2, a2, b4, b1, d1, e1, e2⟩

/-! ## The typed side -/

section Typed
variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

/-- The output of a sumcheck's stage in the port's record. -/
theorem said_out (S : SumL K M X) (D : SumH ρ S) (p : Psc) (r : Array E) (C : Aff) (n : Nat)
    (h : Rec p r C D.t ((List.ofFn S.T.deg).map fun d => Weight.plain (d + 1)) S.T.DY n D.H) :
    D.out.st = D.st ∧ D.out.eps = ρ.val p.eps ∧ D.out.fin = ρ.val p.claim ∧
      (∀ i : Fin S.T.nv, ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt i =
        ρ.val (r.getD i.1 zeroE)) ∧
      ldPartLast S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt = ρ.val D.H.beta ∧
      D.out.vals = D.v := by
  have hl : D.H.rs.map (·.1.length) = List.ofFn S.T.deg := by
    rw [h.lens, plain_sizes]
  refine ⟨rfl, by rw [h.eps]; rfl, ?_, fun i => ?_,
    plain_last ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _,
    plain_vals ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _⟩
  · show (plainOut ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v).fin = _
    rw [plain_fin ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _ S.ok.one hl h.lenY,
      h.at_.claim, h.eps, h.target]
    rfl
  · rw [toList_getD r _ h.r, snd_getD]
    exact plain_ini ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _ i

end Typed

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.pair_said
#print axioms OnBytes.Tie.Pv.Att.key_said
#print axioms OnBytes.Tie.Pv.Att.units_said
#print axioms OnBytes.Tie.Pv.Att.divide_said
#print axioms OnBytes.Tie.Pv.Att.attain_said
#print axioms OnBytes.Tie.Pv.Att.own_said
#print axioms OnBytes.Tie.Pv.Att.said_out
