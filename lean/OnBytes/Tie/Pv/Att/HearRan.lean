-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/HearRan.lean: the port's routines that receive an attention sub-proof's own
messages, taken apart: if a routine succeeds, each of its calls on the channel has succeeded, in the
order of the text, from the state and context that the call before it left.

The routines: planeUnits, scoreUnit and scoreUnits (OnBytes/Model/AttentionScores.lean); productIn,
valueBelowIn, valueOnIn, divide, scoreAtIndexIn, bitsIn and attain
(OnBytes/Model/AttentionDivide.lean). keyAtIndexIn is taken apart in OnBytes/Tie/Pv/Att/Seams.lean.

Main names:
  Pair nv nb C W o F c G c': a sumcheck of products with its row: sc3In nv nb C succeeds from (F, c)
    with a record o1, and sc3Row o1 (W o1.r), right behind it, succeeds with the record o and leaves
    (G, c'). W: the weights as a function of the challenges.
  productIn_ran, valueBelowIn_ran, valueOnIn_ran, bitsIn_ran, scoreAtIndexIn_ran: each of these
    routines is such a pair, behind the calls that the statement names, with its start form and its
    weights written out.
  scoreUnit_ran: seven hidden values, then a pair that starts from the seventh.
  DivideRan, divide_ran: the calls of divide: 5, lt and 2 hidden values; the pair of the denominator
    times the output, which starts from the second of the five; the round that batches 2 rows; 2
    hidden values; the two pairs of the value product, which start from these two.
  AttainRan, attain_ran: the calls of attain: the point; the NP maxima and the round that batches
    them; the pair of the score at the index; keyAtIndexIn; the round that batches NP rows and the
    pair of the bits.

Limits: one direction: from a routine's success. The statements name calls and their arguments; what
a call has heard and done is said in OnBytes/Tie/Pv/Att/HearKit.lean, Sc3Top.lean and ScdTop.lean.
The tests on public numbers at the head of scoreUnit and divide are not repeated here.
-/
import OnBytes.Tie.Pv.Att.HearKit
import OnBytes.Model.AttentionScores
import OnBytes.Model.AttentionDivide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention

/-- A sumcheck of products with its row. -/
def Pair (nv nb : Nat) (C : Aff) (W : Array E → Array E) (o : Attention.Sc3) (F : Fork) (c : Ctx)
    (G : Fork) (c' : Ctx) : Prop :=
  ∃ (o1 : Attention.Sc3) (F2 : Fork) (c2 : Ctx), sc3In nv nb C F c = .ok ((o1, F2), c2) ∧
    sc3Row o1 (W o1.r) F2 c2 = .ok ((o, G), c')

theorem Pair.sized {nv nb : Nat} {C : Aff} {W : Array E → Array E} {o : Attention.Sc3} {F G : Fork}
    {c c' : Ctx} (h : Pair nv nb C W o F c G c') (hz : Sized F) : Sized G := by
  obtain ⟨o1, F2, c2, h1, h2⟩ := h
  exact sc3_sized _ _ _ _ o1 o F F2 G c c2 c' h1 h2 hz

theorem productIn_ran (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat)
    (o : Attention.Sc3) (F G : Fork) (c c' : Ctx)
    (h : productIn S pwW zgW ziW sZO F c = .ok ((o, G), c')) :
    Pair S.nvE S.NP (Aff.slot sZO)
      (fun r => timesW pwW (mulE (eqPts zgW (r.extract 0 S.cf.lgk))
        (eqPts ziW (r.extract S.cf.lgk (S.cf.lgk + S.cf.lt))))) o F c G c' := by
  simp only [productIn] at h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  exact ⟨o1, F2, c2, h1, k1⟩

theorem valueOnIn_ran (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat)
    (o : Attention.Sc3) (F G : Fork) (c c' : Ctx)
    (h : valueOnIn S pwW zgW zihi sCl1 F c = .ok ((o, G), c')) :
    Pair S.nvVD S.NP (Aff.slot sCl1)
      (fun r => timesW pwW (mulE (eqPts zgW (r.extract 0 S.cf.lgk))
        (eqPts zihi (r.extract S.cf.lgk (S.cf.lgk + S.lnT))))) o F c G c' := by
  simp only [valueOnIn] at h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  exact ⟨o1, F2, c2, h1, k1⟩

theorem valueBelowIn_ran (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat)
    (x : Attention.Sc3 × Array E) (F G : Fork) (c c' : Ctx)
    (h : valueBelowIn S pwW zgW zihi sCl F c = .ok ((x, G), c')) :
    Pair S.nvVM S.NP (Aff.slot sCl)
      (fun r => timesW pwW (mulE (overTileRows S
          (tileSums S (Model.eqTab (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))))
            (Model.eqTab (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)))).1
          (Model.eqTab zihi)) (eqPts zgW (r.extract 0 S.cf.lgk)))) x.1 F c G c' := by
  simp only [valueBelowIn] at h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨o, F3, c3, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
  rw [e1, e2, e3]
  exact ⟨o1, F2, c2, h1, h2⟩

theorem bitsIn_ran (S : Shape) (tk tbg tbi : Array E) (o : Attention.Sc3) (F G : Fork)
    (c c' : Ctx) (h : bitsIn S tk tbg tbi F c = .ok ((o, G), c')) :
    ∃ (om5 : Array E) (F1 : Fork) (c1 : Ctx), coinsOm S.NP F c = .ok ((om5, F1), c1) ∧
      Pair S.nvH S.NP (Aff.ofConst zeroE)
        (fun r => scaled om5 (mulE (mulE (eqPts tbi (r.extract 0 S.cf.lt))
          (eqPts tbg (r.extract S.cf.lt (S.cf.lt + S.cf.lgk))))
          (eqPts tk (r.extract (S.cf.lt + S.cf.lgk) (S.cf.lt + S.cf.lgk + 4))))) o F1 c1 G c' := by
  simp only [bitsIn] at h
  obtain ⟨om5, F1, c1, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
  exact ⟨om5, F1, c1, h0, o1, F2, c2, h1, k1⟩

theorem scoreAtIndexIn_ran (S : Shape) (tg ti : Array E) (x : Nat × Attention.Sc3) (F G : Fork)
    (c c' : Ctx) (h : scoreAtIndexIn S tg ti F c = .ok ((x, G), c')) :
    ∃ (F0 : Fork) (c0 : Ctx) (om : Array E) (F1 : Fork) (c1 : Ctx),
      SubM.claimsIn S.NP F c = .ok ((x.1, F0), c0) ∧ coinsOm S.NP F0 c0 = .ok ((om, F1), c1) ∧
      Pair S.nvF S.NP (weightedSum S.NP om fun b => Aff.slot (x.1 + b))
        (fun r => scaled om (mulE (eqPts tg (r.extract S.cf.lt (S.cf.lt + S.cf.lgk)))
          (eqPts ti (r.extract 0 S.cf.lt)))) x.2 F1 c1 G c' := by
  simp only [scoreAtIndexIn] at h
  obtain ⟨sM6, F0, c0, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨om, F1, c1, h0, k0⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
  obtain ⟨o, F3, c3, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
  rw [e1, e2, e3]
  exact ⟨F0, c0, om, F1, c1, ha, h0, o1, F2, c2, h1, h2⟩

/-- The calls of attain. -/
structure AttainRan (S : Shape) (x : Attain) (F G : Fork) (c c' : Ctx) : Prop where
  ran : ∃ (pts : Array E) (Fp : Fork) (cp : Ctx) (F0 : Fork) (c0 : Ctx) (om : Array E) (F1 : Fork)
      (c1 : Ctx) (F2 : Fork) (c2 : Ctx) (F3 : Fork) (c3 : Ctx) (om5 : Array E) (F4 : Fork)
      (c4 : Ctx),
    SubM.point .zero (2 * S.cf.lgk + 2 * S.cf.lt + 4) F c = .ok ((pts, Fp), cp) ∧
    x.tg = pts.extract 0 S.cf.lgk ∧ x.ti = pts.extract S.cf.lgk (S.cf.lgk + S.cf.lt) ∧
    SubM.claimsIn S.NP Fp cp = .ok ((x.sM6, F0), c0) ∧
    coinsOm S.NP F0 c0 = .ok ((om, F1), c1) ∧
    Pair S.nvF S.NP (weightedSum S.NP om fun b => Aff.slot (x.sM6 + b))
      (fun r => scaled om (mulE (eqPts x.tg (r.extract S.cf.lt (S.cf.lt + S.cf.lgk)))
        (eqPts x.ti (r.extract 0 S.cf.lt)))) x.scF F1 c1 F2 c2 ∧
    keyAtIndexIn S x.scF F2 c2 = .ok ((x.scd, F3), c3) ∧
    coinsOm S.NP F3 c3 = .ok ((om5, F4), c4) ∧
    Pair S.nvH S.NP (Aff.ofConst zeroE)
      (fun r => scaled om5 (mulE (mulE
        (eqPts (pts.extract (2 * S.cf.lgk + S.cf.lt + 4) (2 * S.cf.lgk + 2 * S.cf.lt + 4))
          (r.extract 0 S.cf.lt))
        (eqPts (pts.extract (S.cf.lgk + S.cf.lt + 4) (2 * S.cf.lgk + S.cf.lt + 4))
          (r.extract S.cf.lt (S.cf.lt + S.cf.lgk))))
        (eqPts (pts.extract (S.cf.lgk + S.cf.lt) (S.cf.lgk + S.cf.lt + 4))
          (r.extract (S.cf.lt + S.cf.lgk) (S.cf.lt + S.cf.lgk + 4))))) x.scH F4 c4 G c'

theorem attain_ran (S : Shape) (x : Attain) (F G : Fork) (c c' : Ctx)
    (h : attain S F c = .ok ((x, G), c')) : AttainRan S x F G c c' := by
  simp only [attain] at h
  obtain ⟨pts, Fp, cp, hp, kp⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨⟨sM6, scF⟩, F2, c2, hF, kF⟩ := (bind_ok _ _ _ _ _).1 kp
  obtain ⟨scd, F3, c3, hD, kD⟩ := (bind_ok _ _ _ _ _).1 kF
  obtain ⟨scH, F5, c5, hH, kH⟩ := (bind_ok _ _ _ _ _).1 kD
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 kH
  obtain ⟨F0, c0, om, F1, c1, a1, a2, a3⟩ := scoreAtIndexIn_ran S _ _ _ Fp F2 cp c2 hF
  obtain ⟨om5, F4, c4, b1, b2⟩ := bitsIn_ran S _ _ _ scH F3 F5 c3 c5 hH
  rw [e1, e2, e3]
  exact ⟨pts, Fp, cp, F0, c0, om, F1, c1, F2, c2, F3, c3, om5, F4, c4, hp, rfl, rfl, a1, a2, a3,
    hD, b1, b2⟩

/-- The calls of divide. -/
structure DivideRan (S : Shape) (d : Divide) (F G : Fork) (c c' : Ctx) : Prop where
  ran : ∃ (F1 : Fork) (c1 : Ctx) (F2 : Fork) (c2 : Ctx) (F3 : Fork) (c3 : Ctx) (F4 : Fork)
      (c4 : Ctx) (gamP : Array E) (F5 : Fork) (c5 : Ctx) (F6 : Fork) (c6 : Ctx) (F7 : Fork)
      (c7 : Ctx),
    SubM.claimsIn 5 F c = .ok ((d.s5, F1), c1) ∧
    SubM.claimsIn S.cf.lt F1 c1 = .ok ((d.sIB, F2), c2) ∧
    SubM.claimsIn 2 F2 c2 = .ok ((d.s5h, F3), c3) ∧
    Pair S.nvE S.NP (Aff.slot (d.s5 + 1))
      (fun r => timesW d.pwW (mulE (eqPts d.zgW (r.extract 0 S.cf.lgk))
        (eqPts d.ziW (r.extract S.cf.lgk (S.cf.lgk + S.cf.lt))))) d.scE F3 c3 F4 c4 ∧
    SubM.batch 2 F4 c4 = .ok ((gamP, F5), c5) ∧ d.gam = gamP.getD 1 zeroE ∧
    SubM.claimsIn 2 F5 c5 = .ok ((d.sCl, F6), c6) ∧
    Pair S.nvVM S.NP (Aff.slot d.sCl)
      (fun r => timesW d.pwW (mulE (overTileRows S
          (tileSums S (Model.eqTab (r.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))))
            (Model.eqTab (r.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)))).1
          (Model.eqTab (d.ziW.extract 0 S.lnT))) (eqPts d.zgW (r.extract 0 S.cf.lgk))))
      d.vpm F6 c6 F7 c7 ∧
    Pair S.nvVD S.NP (Aff.slot (d.sCl + 1))
      (fun r => timesW d.pwW (mulE (eqPts d.zgW (r.extract 0 S.cf.lgk))
        (eqPts (d.ziW.extract 0 S.lnT) (r.extract S.cf.lgk (S.cf.lgk + S.lnT))))) d.vpd F7 c7 G c'

theorem divide_ran (S : Shape) (zk : Array (Array E)) (d : Divide) (F G : Fork) (c c' : Ctx)
    (h : divide S zk F c = .ok ((d, G), c')) : DivideRan S d F G c c' := by
  simp only [divide] at h
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ma, ea⟩ := (lift_ok _ _ _ _ _ _).1 ha
  obtain ⟨_, ea'⟩ := (mustAs_ok _ _ _ _ _).1 ma
  obtain ⟨⟨_, pwW, zW⟩, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨_, eb, eb'⟩ := (getS_ok _ _ _ _ _ _).1 hb
  obtain ⟨⟨_, pwX, zX⟩, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨_, ed, ed'⟩ := (getS_ok _ _ _ _ _ _).1 hd
  obtain ⟨⟨qWH, pwH, zH⟩, Fe, ce, he, ke⟩ := (bind_ok _ _ _ _ _).1 kd
  obtain ⟨_, ee, ee'⟩ := (getS_ok _ _ _ _ _ _).1 he
  obtain ⟨_, Ff, cf, hf, kf⟩ := (bind_ok _ _ _ _ _).1 ke
  obtain ⟨mf, ef⟩ := (lift_ok _ _ _ _ _ _).1 hf
  obtain ⟨_, ef'⟩ := (mustAs_ok _ _ _ _ _).1 mf
  obtain ⟨_, Fg, cg, hg, kg⟩ := (bind_ok _ _ _ _ _).1 kf
  obtain ⟨_, eg, eg'⟩ := (must_ok _ _ _ _ _ _).1 hg
  have hF : Fg = F := by rw [eg, ef, ee, ed, eb, ea]
  have hc : cg = c := by rw [eg', ef', ee', ed', eb', ea']
  rw [hF, hc] at kg
  obtain ⟨s5, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 kg
  obtain ⟨sIB, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨s5h, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨scE, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨gamP, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨sCl, F6, c6, h6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨⟨vpm, wJv⟩, F7, c7, h7, k7⟩ := (bind_ok _ _ _ _ _).1 k6
  obtain ⟨vpd, F8, c8, h8, k8⟩ := (bind_ok _ _ _ _ _).1 k7
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k8
  rw [e1, e2, e3]
  exact ⟨F1, c1, F2, c2, F3, c3, F4, c4, gamP, F5, c5, F6, c6, F7, c7, h1, h2, h3,
    productIn_ran S _ _ _ _ scE F3 F4 c3 c4 h4, h5, rfl, h6,
    valueBelowIn_ran S _ _ _ _ (vpm, wJv) F6 F7 c6 c7 h7,
    valueOnIn_ran S _ _ _ _ vpd F7 F8 c7 c8 h8⟩

/-! ## The scores -/

/-- The weights of a score unit's sumcheck, as a function of its challenges. -/
def unitWeights (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg) (r : Array E) :
    Array E :=
  let s := u.2.2
  let fm := s == Seg.fm
  let key := zk.getD u.1 #[]
  let z := inner S key s
  let lgk := S.cf.lgk
  let a := lgk + (S.lnT - 1)
  let b := if fm then a + S.lnT else lgk + S.lnT
  timesW (pieces u.2.1 key s) (scoreFactor S s (z.extract 0 lgk)
    (if fm then z.extract lgk a else #[]) (if fm then z.extract a b else #[])
    (if fm then #[] else z.extract lgk b) r)

/-- A score unit: seven hidden values, then a pair that starts from the seventh. -/
def UnitRan (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg) (k : Score) (F G : Fork)
    (c c' : Ctx) : Prop :=
  ∃ (F1 : Fork) (c1 : Ctx), SubM.claimsIn 7 F c = .ok ((k.s0, F1), c1) ∧
    Pair (S.nvKF u.2.2) (pieces u.2.1 (zk.getD u.1 #[]) u.2.2).size (Aff.slot (k.s0 + 6))
      (unitWeights S zk u) k.sc F1 c1 G c'

theorem scoreUnit_ran (S : Shape) (zk : Array (Array E)) (claim : Nat) (u : Nat × ACall × Seg)
    (x : PlaneClaim × Score) (F G : Fork) (c c' : Ctx)
    (h : scoreUnit S zk claim u F c = .ok ((x, G), c')) : UnitRan S zk u x.2 F G c c' := by
  simp only [scoreUnit] at h
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, ea, ea'⟩ := (must_ok _ _ _ _ _ _).1 ha
  rw [ea, ea'] at ka
  obtain ⟨s0, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨o1, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨o, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  rw [e1, e2, e3]
  exact ⟨F1, c1, h1, o1, F2, c2, h2, h3⟩

/-- The score units, one after the other. -/
def UnitsRan (S : Shape) (zk : Array (Array E)) : List (Nat × ACall × Seg) → List Score → Fork →
    Ctx → Fork → Ctx → Prop
  | [], [], F, c, G, c' => G = F ∧ c' = c
  | u :: us, k :: ks, F, c, G, c' =>
    ∃ (F1 : Fork) (c1 : Ctx), UnitRan S zk u k F F1 c c1 ∧ UnitsRan S zk us ks F1 c1 G c'
  | _, _, _, _, _, _ => False

theorem scoreUnits_ran (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes : Array PlaneClaim) (stored : Array Score)
      (x : Array PlaneClaim × Array Score) (F G : Fork) (c c' : Ctx),
      scoreUnits S zk us planes stored F c = .ok ((x, G), c') →
      ∃ ks : List Score, x.2 = stored ++ ks.toArray ∧ UnitsRan S zk us ks F c G c'
  | [], planes, stored, x, F, G, c, c', h => by
    simp only [scoreUnits] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    exact ⟨[], by rw [e1]; simp, e2, e3⟩
  | u :: us, planes, stored, x, F, G, c, c', h => by
    simp only [scoreUnits] at h
    obtain ⟨y, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨ks, e, r⟩ := scoreUnits_ran S zk us _ _ x F1 G c1 c' k1
    exact ⟨y.2 :: ks, by rw [e]; simp, F1, c1, scoreUnit_ran S zk _ u y F F1 c c1 h1, r⟩

/-- n times three hidden values. -/
def PlanesRan : Nat → Fork → Ctx → Fork → Ctx → Prop
  | 0, F, c, G, c' => G = F ∧ c' = c
  | n + 1, F, c, G, c' =>
    ∃ (j : Nat) (F1 : Fork) (c1 : Ctx), SubM.claimsIn 3 F c = .ok ((j, F1), c1) ∧
      PlanesRan n F1 c1 G c'

theorem planeUnits_ran (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (planes x : Array PlaneClaim) (F G : Fork) (c c' : Ctx),
      planeUnits S zk us planes F c = .ok ((x, G), c') → PlanesRan us.length F c G c'
  | [], planes, x, F, G, c, c', h => by
    simp only [planeUnits] at h
    obtain ⟨_, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    exact ⟨e2, e3⟩
  | u :: us, planes, x, F, G, c, c', h => by
    simp only [planeUnits] at h
    obtain ⟨p, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    simp only [planeUnit] at h1
    obtain ⟨s0, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 h1
    obtain ⟨_, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
    rw [e2, e3] at k1
    exact ⟨s0, F2, c2, h2, planeUnits_ran S zk us _ x F2 G c2 c' k1⟩

/-- The calls of scores. -/
theorem scores_ran (S : Shape) (zk : Array (Array E)) (x : Array PlaneClaim × Array Score)
    (F G : Fork) (c c' : Ctx) (h : scores S zk F c = .ok ((x, G), c')) :
    ∃ (F1 : Fork) (c1 : Ctx) (ks : List Score),
      PlanesRan (unitsOf S Table.kr [Seg.rm, Seg.rd]).length F c F1 c1 ∧ x.2 = ks.toArray ∧
      UnitsRan S zk (unitsOf S Table.kfd [Seg.fm, Seg.fd]) ks F1 c1 G c' := by
  simp only [scores] at h
  obtain ⟨planes, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ks, e, r⟩ := scoreUnits_ran S zk _ _ _ x F1 G c1 c' k1
  exact ⟨F1, c1, ks, planeUnits_ran S zk _ _ planes F F1 c c1 h1, by rw [e]; simp, r⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.divide_ran
#print axioms OnBytes.Tie.Pv.Att.scoreUnit_ran
#print axioms OnBytes.Tie.Pv.Att.scoreUnits_ran
#print axioms OnBytes.Tie.Pv.Att.planeUnits_ran
#print axioms OnBytes.Tie.Pv.Att.scores_ran
#print axioms OnBytes.Tie.Pv.Att.productIn_ran
#print axioms OnBytes.Tie.Pv.Att.valueBelowIn_ran
#print axioms OnBytes.Tie.Pv.Att.valueOnIn_ran
#print axioms OnBytes.Tie.Pv.Att.bitsIn_ran
#print axioms OnBytes.Tie.Pv.Att.scoreAtIndexIn_ran
#print axioms OnBytes.Tie.Pv.Att.attain_ran
