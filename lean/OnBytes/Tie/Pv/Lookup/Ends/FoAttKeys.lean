-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttKeys.lean.
The attention sub-proof: each call's key form reads the extension of the call's key vector, under
the rule on the hidden values under the slots.

The key form of call q (Fo.kfA, OnBytes/Tie/Pv/Lookup/Ends/FoAttKfAt.lean) names slots and public
constants. The call's key vector (kvA, OnBytes/Tie/Pv/Lookup/Ends/A.lean) is a function of the
cells. That the form's value is the extension of the vector at the call's key point is no identity:
it holds where each slot that the form names has its rule value, a sum over the unit's pieces of
weights times extensions of functions of the cells.

States:
  unitsKR h q, unitsKFD h q: the plane claims, the units of scores, of call q, in the record's
    order.
  PubKR, PubKFD, PubR16, PubWH: for a call of each kind, the premises on public numbers and values
    of the theorem on that kind (algW_KR, algW_KFD, algW_R16, algW_WH,
    OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean).
  PubA h NC: every call below NC is a call of the shape and meets the public premises of its kind;
    the call of kind WH is taken to be the one at the number h.d.qWH.
  LinKR, LinKFD, LinR16, LinWH; LinA: the rule's lines whose rule value is linear in the cells.
  ProdKFD, ProdR16; ProdA: the rule's lines whose rule value is a product of cells.
  RuleA W cell h NC: the three together.
  att_keys: under RuleA, for every call q below NC: the value of Fo.kfA h q, under the reading of
    the byte-level field in the library's field and in the world W, is the extension of kvA at the
    call's key point, read.
Limits: RuleA is a hypothesis. A call of kind R16 is covered only where it holds both segments wl
and ix (as algW_R16 has it): where a configuration lays them in two calls, PubA is not met. At the
test configuration's two attention plans the one call of kind R16 holds both: by an evaluation that
is not in this file. That the lines can be met together is not shown: no statement of this library
concludes RuleA. That the world of a run meets them is what the sub-proof's later claims are for.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKfVal
import OnBytes.Tie.Pv.Lookup.Ends.AlgAW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Attention OnBytes.Ends OnBytes.Ends.A

/-- The plane claims of call q. -/
def unitsKR (h : Attention.Heard) (q : ℕ) : List PlaneClaim :=
  h.planes.toList.filter fun pc => pc.call == q

/-- The units of scores of call q. -/
def unitsKFD (h : Attention.Heard) (q : ℕ) : List Score :=
  (h.scores.toList.zipIdx.filter fun x => x.1.call == q).map fun x => x.1

/-! ### on public numbers and values -/

section
variable (h : Attention.Heard) (q : ℕ) (c : ACall)

/-- A call of kind KR. -/
structure PubKR : Prop where
  ok : PcsOK c.call.n c.pcs.toList
  size : (h.g.zk.getD q #[]).size = c.call.n
  pad : (tauN h.g.shape q (t0N h.g.shape q) : Cb.Gl.E) = 0
  nodup : ((unitsKR h q).map fun pc => pc.seg).Nodup
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ (unitsKR h q).map fun pc => pc.seg
  segs : ∀ pc ∈ unitsKR h q, pc.seg = Seg.rm ∨ pc.seg = Seg.rd
  pw : ∀ pc ∈ unitsKR h q, pc.pw = pieces c (h.g.zk.getD q #[]) pc.seg

/-- A call of kind KFD. -/
structure PubKFD : Prop where
  call : h.g.shape.calls[q]? = some c.call
  ok : PcsOK c.call.n c.pcs.toList
  size : (h.g.zk.getD q #[]).size = c.call.n
  nodup : ((unitsKFD h q).map fun k => k.seg).Nodup
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ (unitsKFD h q).map fun k => k.seg
  segs : ∀ k ∈ unitsKFD h q, k.seg = Seg.fm ∨ k.seg = Seg.fd
  pw : ∀ k ∈ unitsKFD h q, k.pw = pieces c (h.g.zk.getD q #[]) k.seg
  pub : ∀ k ∈ unitsKFD h q,
    (if k.seg == Seg.fm then
        ((h.S.shd c.sh).C : Cb.Gl.E) * readE (sumW k.pw) * readE (onesOf k.zs)
      else ((h.S.shd c.sh).Om : Cb.Gl.E) * readE (sumW k.pw) * (1 - readE (leOf k.zj k.zi))) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) k.seg
      fun _ => gcAt h.S c.sh (k.seg == Seg.fd)

/-- A call of kind R16, which holds the segments wl and ix. -/
structure PubR16 (b' : ℕ) : Prop where
  wl : c.holds .wl = true
  ix : c.holds .ix = true
  ok : PcsOK c.call.n c.pcs.toList
  size : (h.g.zk.getD q #[]).size = c.call.n
  pad : (tauN h.g.shape q (t0N h.g.shape q) : Cb.Gl.E) = 0
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ [Seg.wl, Seg.ix]
  pow : h.S.dh * h.S.T * h.S.G = 2 ^ b'
  bits : ∀ p ∈ ofSeg c.pcs.toList .wl, p.b = 1 + b'
  pw : h.d.pwW = pieces c (h.g.zk.getD q #[]) .wl
  zsl : readE h.d.zsl = readV (h.g.zk.getD q #[]) (c.call.n - (1 + b'))
  pub : readE (sumW h.d.pwX) * readE (idOf h.d.ziX) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) .ix
      fun _ κ => ((κ % h.S.T : ℕ) : Cb.Gl.E)

/-- The call of kind WH. -/
structure PubWH : Prop where
  ok : PcsOK c.call.n c.pcs.toList
  size : (h.g.zk.getD q #[]).size = c.call.n
  pad : (tauN h.g.shape q (t0N h.g.shape q) : Cb.Gl.E) = 0
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ [Seg.wh]
  pw : h.d.pwH = pieces c (h.g.zk.getD q #[]) .wh

/-- The public premises of the call's kind. b': the logarithm of the size of a piece of wl, halved.
-/
def PubOf (b' : ℕ) : Prop :=
  (h.d.qWH = q ∧ PubWH h q c) ∨ (h.d.qWH ≠ q ∧ c.kind = .r16 ∧ PubR16 h q c b') ∨
    (h.d.qWH ≠ q ∧ c.kind = .kfd ∧ PubKFD h q c) ∨ (h.d.qWH ≠ q ∧ c.kind = .kr ∧ PubKR h q c)

end

/-- The public premises at the attention sub-proof. -/
def PubA (h : Attention.Heard) (NC b' : ℕ) : Prop :=
  ∀ q < NC, ∃ c, h.S.calls[q]? = some c ∧ PubOf h q c b'

/-! ### the rule's lines -/

section
variable (W : World Cb.Gl.E) (cell : NameA → Cb.Gl.E) (h : Attention.Heard) (q : ℕ) (c : ACall)

def LinKR : Prop :=
  ∀ pc ∈ unitsKR h q, ∀ x < 3, W.slot (pc.s0 + x) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) pc.seg
      fun p => asC h.S cell x p.lam p.a (pc.seg == Seg.rd)

def LinKFD : Prop :=
  (∀ k ∈ unitsKFD h q, ∀ x < 5, W.slot (k.s0 + x) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) k.seg
      fun p => asC h.S cell x p.lam p.a (k.seg == Seg.fd)) ∧
  ∀ k ∈ unitsKFD h q, W.slot (k.s0 + 5) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) k.seg
      (msAt h.S cell (k.seg == Seg.fd))

def ProdKFD : Prop :=
  ∀ k ∈ unitsKFD h q, W.slot (k.s0 + 6) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) k.seg
      fun p => ssAt h.S cell (k.seg == Seg.fd) p.lam p.a

def LinR16 (b' : ℕ) : Prop :=
  W.slot h.d.sZC = ruleW c.call.n b' c.pcs.toList (readV (h.g.zk.getD q #[])) (denW h.S cell) ∧
  W.slot h.d.sRH =
    ruleW c.call.n b' c.pcs.toList (readV (h.g.zk.getD q #[])) (rhL h.S cell false) ∧
  W.slot h.d.sRHP =
    ruleW c.call.n b' c.pcs.toList (readV (h.g.zk.getD q #[])) (rhL h.S cell true) ∧
  ∀ k < h.S.cf.lt, W.slot (h.d.sIB + k) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) .ix (ibX h.S cell k)

def ProdR16 (b' : ℕ) : Prop :=
  W.slot h.d.sACC = ruleW c.call.n b' c.pcs.toList (readV (h.g.zk.getD q #[])) (accW h.S cell) ∧
  W.slot h.d.sZO = ruleW c.call.n b' c.pcs.toList (readV (h.g.zk.getD q #[])) (zoW h.S cell)

def LinWH : Prop :=
  W.slot h.d.s5h =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) .wh (rhW h.S cell false) ∧
  W.slot (h.d.s5h + 1) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) .wh (rhW h.S cell true)

end

section
variable (W : World Cb.Gl.E) (cell : NameA → Cb.Gl.E) (h : Attention.Heard) (NC b' : ℕ)

/-- The lines whose rule value is linear in the cells. -/
def LinA : Prop :=
  ∀ q < NC, ∀ c, h.S.calls[q]? = some c →
    (h.d.qWH = q → LinWH W cell h q c) ∧
    (h.d.qWH ≠ q → c.kind = .r16 → LinR16 W cell h q c b') ∧
    (h.d.qWH ≠ q → c.kind = .kfd → LinKFD W cell h q c) ∧
    (h.d.qWH ≠ q → c.kind = .kr → LinKR W cell h q c)

/-- The lines whose rule value is a product of cells. -/
def ProdA : Prop :=
  ∀ q < NC, ∀ c, h.S.calls[q]? = some c →
    (h.d.qWH ≠ q → c.kind = .r16 → ProdR16 W cell h q c b') ∧
    (h.d.qWH ≠ q → c.kind = .kfd → ProdKFD W cell h q c)

/-- The rule at the attention sub-proof. -/
structure RuleA : Prop where
  pub : PubA h NC b'
  lin : LinA W cell h NC b'
  prod : ProdA W cell h NC b'

end

/-- Each call's key form reads the extension of the call's key vector. -/
theorem att_keys (W : World Cb.Gl.E) (cell : NameA → Cb.Gl.E) (h : Attention.Heard) (NC b' : ℕ)
    (hR : RuleA W cell h NC b') (q : ℕ) (hq : q < NC) :
    ∃ c, h.S.calls[q]? = some c ∧
      (kfA h q).value Reading.gl W =
        Blocks.ext c.call.n (kvA h.S h.g.shape cell q) (readV (h.g.zk.getD q #[])) := by
  obtain ⟨c, hc, hcase⟩ := hR.pub q hq
  obtain ⟨l1, l2, l3, l4⟩ := hR.lin q hq c hc
  obtain ⟨p2, p3⟩ := hR.prod q hq c hc
  refine ⟨c, hc, ?_⟩
  unfold kfA
  rcases hcase with ⟨hw, C⟩ | ⟨hw, hk, C⟩ | ⟨hw, hk, C⟩ | ⟨hw, hk, C⟩
  · rw [if_pos hw]
    exact algW_WH W h.S h.g.shape cell q c hc C.ok _ C.size C.pad C.cover h.d C.pw (l1 hw).1
      (l1 hw).2
  · rw [if_neg hw, hc]
    show (if (c.kind == Table.r16) = true then _ else _ : Aff).value Reading.gl W = _
    rw [if_pos (by rw [hk]; rfl), kfR16_value, if_pos C.wl, if_pos C.ix]
    obtain ⟨a1, a2, a3, a4⟩ := l2 hw hk
    exact algW_R16 W h.S h.g.shape cell q c hc C.ok _ C.size C.pad C.cover b' C.pow C.bits h.d C.pw
      C.zsl a1 a2 a3 a4 (p2 hw hk).1 (p2 hw hk).2 C.pub
  · rw [if_neg hw, hc]
    show (if (c.kind == Table.r16) = true then _ else
      if (c.kind == Table.kfd) = true then _ else _ : Aff).value Reading.gl W = _
    rw [if_neg (by rw [hk]; decide), if_pos (by rw [hk]; rfl)]
    have e : (kfKFD h q c).value Reading.gl W =
        (padTerm c (h.g.zk.getD q #[])).value Reading.gl W +
          ((unitsKFD h q).map fun k => (keyKFD (h.S.shd c.sh) k).value Reading.gl W).sum := by
      rw [kfKFD_value]
      unfold unitsKFD padTerm
      rw [Aff.value_ofConst, List.map_map]
      rfl
    rw [e]
    exact algW_KFD W h.S h.g.shape cell q c hc C.call C.ok _ C.size _ C.nodup C.cover C.segs C.pw
      (l3 hw hk).1 (l3 hw hk).2 (p3 hw hk) C.pub
  · rw [if_neg hw, hc]
    show (if (c.kind == Table.r16) = true then _ else
      if (c.kind == Table.kfd) = true then _ else
      if (c.kind == Table.kr) = true then _ else _ : Aff).value Reading.gl W = _
    rw [if_neg (by rw [hk]; decide), if_neg (by rw [hk]; decide), if_pos (by rw [hk]; rfl),
      kfKR_value]
    exact algW_KR W h.S h.g.shape cell q c hc C.ok _ C.size C.pad _ C.nodup C.cover C.segs C.pw
      (l4 hw hk)

end Fo
