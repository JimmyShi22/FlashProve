-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean: for whole calls of the lookup of an attention sub-proof's own
calls: the sum of the values, in a world W, of the key forms of the Lean verifier under OnBytes/
(here: the port) is the extension of the call's key vector at the key point, read.

Statements and proofs, over Cb.Gl.E. z is the array of the call's key point; the terms and the
units' theorems are those of A, AlgA, AlgA2, AlgA3, PortA and PortA2 beside this file.
Main names:
  `pad_read`: if h.calls[q]? = some c.call, the port's padding row, read, is tauN h q (t0N h q),
    cast.
  `algW_KR`: the sum over a list us of plane claims of the values of keyKR is ext n (kvA q) (readV
    z).
  `algW_KFD`: the value of padTerm plus the sum over a list us of units of scores of the values of
    keyKFD is that extension.
  `algW_R16`: the value of keyWL plus the value of keyIX is that extension. `algW_WH`: the value of
    keyWH is.
  `rule_not_empty`: for one plane claim there is a world in which its rule holds.
Under, in all four: S.calls[q]? = some c; PcsOK c.call.n c.pcs.toList; z.size = c.call.n; each
record's pieces are the port's pieces c z s; and the rule on W's slots, at the slots that the forms
read, those that are linear in the cells and those of degree two as premises of their own. Further:
  algW_KR: the call's padding row is 0 in Cb.Gl.E; the segments of us are without doubles, cover c's
    pieces, and each is rm or rd.
  algW_KFD: h.calls[q]? = some c.call; the segments of us are without doubles, cover c's pieces, and
    each is fm or fd; for each unit the premise pub: the port's closed form of the gap's public
    part, read, is the rule value of gcAt.
  algW_R16: the padding row is 0; every piece is of segment wl or ix; dh T G = 2^b'; p.b = 1 + b'
    for every piece of wl; zsl, read, is coordinate n - (1 + b') of the key point; the premise pub:
    LW id(ziX), read, is the rule value of the token's number.
  algW_WH: the padding row is 0; every piece is of segment wh.
Limits: the premises pub are not proved in this file;
the premise on zsl is proved in none of these files. rule_not_empty is of one unit alone:
that all units' lines hold in one world is not shown in this file, also not where the units'
slots are pairwise different. algW_R16 has the terms of wl and of ix on its left side; to a call of
kind R16 that holds one of the two the port gives that one's term alone (joinR16,
OnBytes/Model/AttentionClaimsB.lean), and no statement here is of such a call. That the left sides
are the values of the forms that the port hands to the join for call q is not stated here. That the
premises hold at a shape or a proof is not shown.

-/
import OnBytes.Tie.Pv.Lookup.Ends.PortA2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Attention (Seg ACall PlaneClaim Score Divide PW sumW keyKR keyKFD keyWL keyIX keyWH
  padTerm wall pieces onesOf leOf idOf)

variable (W : World GE)

/-- **The port's padding row, read.** -/
theorem pad_read (h : Forest.Shape) (q : ℕ) (c : ACall) (hq : h.calls[q]? = some c.call) :
    algebraMap Cb.Gl.F GE (toF (c.call.tauAt c.call.t0)) = (tauN h q (t0N h q) : GE) := by
  unfold tauN t0N
  rw [hq]
  simp only [Option.map_some, Option.getD_some]
  unfold toF
  rw [map_natCast]

/-- **A call of kind KR, over the port's world.** -/
theorem algW_KR (S : Sh) (h : Forest.Shape) (cell : NameA → GE) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK c.call.n c.pcs.toList) (zk : Array E)
    (hn : zk.size = c.call.n) (hpad : (tauN h q (t0N h q) : GE) = 0) (us : List PlaneClaim)
    (hnd : (us.map fun pc => pc.seg).Nodup)
    (hcov : ∀ p ∈ c.pcs.toList, p.seg ∈ us.map fun pc => pc.seg)
    (hs : ∀ pc ∈ us, pc.seg = Seg.rm ∨ pc.seg = Seg.rd)
    (hpw : ∀ pc ∈ us, pc.pw = pieces c zk pc.seg)
    (rule : ∀ pc ∈ us, ∀ x < 3, W.slot (pc.s0 + x) = ruleAt c.call.n c.pcs.toList (readV zk) pc.seg
      fun p => asC S cell x p.lam p.a (pc.seg == Seg.rd)) :
    (us.map fun pc => (keyKR pc).value Reading.gl W).sum =
      Blocks.ext c.call.n (kvA S h cell q) (readV zk) := by
  rw [call_split S h cell q c.call.n c hc ok (readV zk) _ hnd hcov, hpad, zero_mul, add_zero,
    List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pc hp
  exact unitW_KR W S cell c zk hn pc (hs pc hp) (hpw pc hp) (rule pc hp)

/-- **A call of kind KFD, over the port's world**, with the port's padding's term. -/
theorem algW_KFD (S : Sh) (h : Forest.Shape) (cell : NameA → GE) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (hq : h.calls[q]? = some c.call)
    (ok : PcsOK c.call.n c.pcs.toList) (zk : Array E) (hn : zk.size = c.call.n) (us : List Score)
    (hnd : (us.map fun k => k.seg).Nodup)
    (hcov : ∀ p ∈ c.pcs.toList, p.seg ∈ us.map fun k => k.seg)
    (hs : ∀ k ∈ us, k.seg = Seg.fm ∨ k.seg = Seg.fd)
    (hpw : ∀ k ∈ us, k.pw = pieces c zk k.seg)
    (rule : ∀ k ∈ us, ∀ x < 5, W.slot (k.s0 + x) = ruleAt c.call.n c.pcs.toList (readV zk) k.seg
      fun p => asC S cell x p.lam p.a (k.seg == Seg.fd))
    (ruleM : ∀ k ∈ us, W.slot (k.s0 + 5) =
      ruleAt c.call.n c.pcs.toList (readV zk) k.seg (msAt S cell (k.seg == Seg.fd)))
    (ruleS : ∀ k ∈ us, W.slot (k.s0 + 6) = ruleAt c.call.n c.pcs.toList (readV zk) k.seg
      fun p => ssAt S cell (k.seg == Seg.fd) p.lam p.a)
    (pub : ∀ k ∈ us,
      (if k.seg == Seg.fm then ((S.shd c.sh).C : GE) * readE (sumW k.pw) * readE (onesOf k.zs)
        else ((S.shd c.sh).Om : GE) * readE (sumW k.pw) * (1 - readE (leOf k.zj k.zi))) =
      ruleAt c.call.n c.pcs.toList (readV zk) k.seg fun _ => gcAt S c.sh (k.seg == Seg.fd)) :
    (padTerm c zk).value Reading.gl W +
        (us.map fun k => (keyKFD (S.shd c.sh) k).value Reading.gl W).sum =
      Blocks.ext c.call.n (kvA S h cell q) (readV zk) := by
  rw [call_split S h cell q c.call.n c hc ok (readV zk) _ hnd hcov, value_padTerm,
    pad_read h q c hq, readE_wall c zk hn, List.map_map, add_comm]
  refine congrArg₂ (· + ·) ?_ rfl
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  exact unitW_KFD W S cell c zk hn k (hs k hk) (hpw k hk) (rule k hk) (ruleM k hk) (ruleS k hk)
    (pub k hk)

/-- **A call of kind R16 that holds wl and ix, over the port's world.** -/
theorem algW_R16 (S : Sh) (h : Forest.Shape) (cell : NameA → GE) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK c.call.n c.pcs.toList) (zk : Array E)
    (hn : zk.size = c.call.n) (hpad : (tauN h q (t0N h q) : GE) = 0)
    (hcov : ∀ p ∈ c.pcs.toList, p.seg ∈ [Seg.wl, Seg.ix]) (b' : ℕ)
    (hsz : S.dh * S.T * S.G = 2 ^ b') (hb : ∀ p ∈ ofSeg c.pcs.toList .wl, p.b = 1 + b')
    (d : Divide) (hpwW : d.pwW = pieces c zk .wl)
    (hz : readE d.zsl = readV zk (c.call.n - (1 + b')))
    (rZC : W.slot d.sZC = ruleW c.call.n b' c.pcs.toList (readV zk) (denW S cell))
    (rRH : W.slot d.sRH = ruleW c.call.n b' c.pcs.toList (readV zk) (rhL S cell false))
    (rRHP : W.slot d.sRHP = ruleW c.call.n b' c.pcs.toList (readV zk) (rhL S cell true))
    (rIB : ∀ k < S.cf.lt,
      W.slot (d.sIB + k) = ruleAt c.call.n c.pcs.toList (readV zk) .ix (ibX S cell k))
    (rAC : W.slot d.sACC = ruleW c.call.n b' c.pcs.toList (readV zk) (accW S cell))
    (rZO : W.slot d.sZO = ruleW c.call.n b' c.pcs.toList (readV zk) (zoW S cell))
    (pub : readE (sumW d.pwX) * readE (idOf d.ziX) =
      ruleAt c.call.n c.pcs.toList (readV zk) .ix fun _ κ => ((κ % S.T : ℕ) : GE)) :
    (keyWL d).value Reading.gl W + (keyIX S d).value Reading.gl W =
      Blocks.ext c.call.n (kvA S h cell q) (readV zk) := by
  rw [call_split S h cell q c.call.n c hc ok (readV zk) [Seg.wl, Seg.ix] (by decide) hcov, hpad,
    zero_mul, add_zero, unitW_WL W S cell c zk hn b' hsz hb d hpwW hz rAC rZO rZC rRH rRHP,
    unitW_IX W S cell c zk d rIB pub]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **The call of kind WH, over the port's world.** -/
theorem algW_WH (S : Sh) (h : Forest.Shape) (cell : NameA → GE) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK c.call.n c.pcs.toList) (zk : Array E)
    (hn : zk.size = c.call.n) (hpad : (tauN h q (t0N h q) : GE) = 0)
    (hcov : ∀ p ∈ c.pcs.toList, p.seg ∈ [Seg.wh]) (d : Divide) (hpw : d.pwH = pieces c zk .wh)
    (r2 : W.slot d.s5h = ruleAt c.call.n c.pcs.toList (readV zk) .wh (rhW S cell false))
    (r2p : W.slot (d.s5h + 1) = ruleAt c.call.n c.pcs.toList (readV zk) .wh (rhW S cell true)) :
    (keyWH d).value Reading.gl W = Blocks.ext c.call.n (kvA S h cell q) (readV zk) := by
  rw [call_split S h cell q c.call.n c hc ok (readV zk) [Seg.wh] (by decide) hcov, hpad, zero_mul,
    add_zero, unitW_WH W S cell c zk hn d hpw r2 r2p]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **A toy: the rule can be met.** For a plane claim there is a world whose slots are the rule
values. -/
theorem rule_not_empty (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (pc : PlaneClaim) :
    ∃ W : World GE, ∀ x < 3, W.slot (pc.s0 + x) = ruleAt c.call.n c.pcs.toList (readV zk) pc.seg
      fun p => asC S cell x p.lam p.a (pc.seg == Seg.rd) :=
  ⟨{ slot := fun j => ruleAt c.call.n c.pcs.toList (readV zk) pc.seg
        fun p => asC S cell (j - pc.s0) p.lam p.a (pc.seg == Seg.rd)
     entry := fun _ _ _ => 0 },
    fun x _ => by simp only [Nat.add_sub_cancel_left]⟩

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.algW_KR
#print axioms OnBytes.Ends.A.algW_KFD
#print axioms OnBytes.Ends.A.algW_R16
#print axioms OnBytes.Ends.A.algW_WH
#print axioms OnBytes.Ends.A.rule_not_empty
