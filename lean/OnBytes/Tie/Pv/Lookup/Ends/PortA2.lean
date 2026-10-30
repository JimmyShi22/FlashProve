-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/PortA2.lean: the weights of an attention sub-proof's pieces in the Lean
verifier under OnBytes/ (here: the port), read into the library's field; and, unit by unit, the
value of the port's own key form as the unit's share of the extension of the call's key vector.

Definitions, statements and proofs. readE and readV read the port's field elements and arrays into
Cb.Gl.E (OnBytes/Slice/ProgField.lean); W is a World of the port, and a form's value is Aff.value
Reading.gl W. z is the array of the call's key point. The terms are those of A, AlgA, AlgA2, AlgA3
and PortA beside this file.
Main names:
  `readE_eqAt`: without a premise, the port's eqAt, read, is the library's Blocks.eqN.
  `readE_wp`: under z.size = n, a piece's weight as the port's pieces forms it, read, is wpAt.
  `readE_sumW_pieces`: under z.size = c.call.n, the read sum of the weights of the port's pieces c z
    s is lwAt. `readE_wall`: under the same, the port's wall, read, is the sum of all pieces'
    weights.
  `share`: a segment's share: the weighted sum, over the segment's pieces, of the extensions of the
    pieces' keys.
  `sum_bySeg`, `call_split`: under S.calls[q]? = some c, PcsOK n c.pcs.toList, and a list of
    segments without doubles that covers c's pieces: ext n (kvA q) pt is the sum of these segments'
    shares plus the padding's term.
  `value_indexForm`, `value_keyIX`: without a premise, the value of the port's keyIX is kfIX at W's
    slots and at the read LW id(ziX).
  `unitW_KR`, `unitW_KFD`, `unitW_WL`, `unitW_IX`, `unitW_WH`: the value of the port's own key form
    of a unit is the unit's share. Their premises:
      all but unitW_IX: z.size = c.call.n, and the record's pieces (pw, pwH, pwW) are the port's
        pieces c z s;
      all: the rule on W's slots: each slot that the form reads has its rule value (ruleAt; for wl
        ruleW) at the point readV z. The rule names these slots alone (s0 + x for x < 3 at KR; s0 +
        x for x < 5, s0 + 5 and s0 + 6 at KFD; sACC, sZO, sZC, sRH and sRHP at wl; sIB + k for k <
        lt at ix; s5h and s5h + 1 at wh), so that the lines of several units can hold in one world,
        if the units' slots are pairwise different (said without a theorem in this file);
      unitW_KR: pc.seg is rm or rd. unitW_KFD: k.seg is fm or fd;
      unitW_WL: dh T G = 2^b'; p.b = 1 + b' for every piece of wl; and zsl, read, is coordinate n -
        (1 + b') of the key point;
      unitW_KFD: the port's closed form of the gap's public part (C LW ones(zs); Om LW (1 - LE(zj,
        zi))), read, is the rule value of gcAt;
      unitW_IX: LW id(ziX), read, is the rule value of the token's number.
Limits: the last three premises, on public values, are premises here and are proved nowhere in this
file; that on zsl is proved in none of these files.
That the port's routines
planeUnit, scoreUnit and divide set a record's pieces to pieces c z s is by reading their text; no
theorem here. That the rule holds of W's slots at a proof is not shown. Nor is it shown that a shape
of the port meets PcsOK, dh T G = 2^b' or p.b = 1 + b'.

-/
import OnBytes.Slice.ProgMle
import OnBytes.Tie.Pv.Lookup.Ends.PortA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Attention (Seg ACall PlaneClaim Score Divide PW sumW keyKR keyKFD keyWL keyIX keyWH
  padTerm wall eqAt pieces onesOf leOf idOf ShD indexForm)

/-! ## The port's weights, read -/

/-- The port's test of a bit is testBit. -/
theorem bit_eq (idx k : ℕ) : ((idx >>> k) % 2 == 1) = idx.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, beq_eq_decide]

/-- **The port's eqAt, read, is the library's eqN.** -/
theorem readE_eqAt (z : Array E) (idx : ℕ) :
    readE (eqAt z idx) = Blocks.eqN z.size 0 (readV z) idx := by
  have h0 : eqAt z idx = (List.range z.size).foldl (fun s i => mulE s
      (if (idx >>> (z.size - 1 - i)) % 2 == 1 then z.getD i zeroE
        else subE oneE (z.getD i zeroE))) oneE := rfl
  rw [h0, readE_foldl_range, readE_one, one_mul]
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [bit_eq, Nat.zero_add]
  cases idx.testBit (z.size - 1 - t)
  · simp only [Bool.false_eq_true, if_false, readE_sub, readE_one]
    rfl
  · simp only [if_true]
    rfl

/-- eqN reads the m coordinates from off on alone. -/
theorem eqN_congr (m off : ℕ) (a a' : ℕ → GE) (z : ℕ) (h : ∀ t < m, a (off + t) = a' (off + t)) :
    Blocks.eqN m off a z = Blocks.eqN m off a' z := by
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [h t (Finset.mem_range.1 ht)]

/-- The first k coordinates of a point, read. -/
theorem readV_extract0 (z : Array E) (k t : ℕ) (ht : t < k) :
    readV (z.extract 0 k) t = readV z t := by
  rw [readV_eq_readL, readV_eq_readL, Array.toList_extract, List.extract_eq_drop_take,
    List.drop_zero, Nat.sub_zero, readL_take k _ t ht]

/-- **A piece's weight, read.** -/
theorem readE_wp (zk : Array E) (n off b : ℕ) (hn : zk.size = n) :
    readE (eqAt (zk.extract 0 (n - b)) (off >>> b)) = wpAt n off b (readV zk) := by
  have hs : (zk.extract 0 (n - b)).size = n - b := by
    rw [Array.size_extract, hn]
    omega
  rw [readE_eqAt, hs, Nat.shiftRight_eq_div_pow]
  unfold wpAt
  apply eqN_congr
  intro t ht
  rw [Nat.zero_add]
  exact readV_extract0 zk (n - b) t ht

/-- The read sum of the weights of an array of pieces. -/
theorem readE_sumW (v : Array PW) : readE (sumW v) = (v.toList.map fun x => readE x.wp).sum := by
  have h : ∀ (l : List PW) (s : E), readE (l.foldl (fun s x => addE s x.wp) s) =
      readE s + (l.map fun x => readE x.wp).sum := by
    intro l
    induction l with
    | nil =>
      intro s
      rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, readE_add, add_assoc]
  rw [sumW, ← Array.foldl_toList, h, readE_zero, zero_add]

/-- The port's list of a segment's pieces, before it is sorted. -/
theorem found_eq (l : List Pc) (s : Seg) (g : Pc → PW) :
    (l.filterMap fun pc => if pc.seg == s then some (g pc) else none) = (ofSeg l s).map g := by
  unfold ofSeg
  induction l with
  | nil => rfl
  | cons p l ih =>
    by_cases hp : (p.seg == s) = true
    · have e1 : (p :: l).filterMap (fun pc => if pc.seg == s then some (g pc) else none) =
          g p :: l.filterMap (fun pc => if pc.seg == s then some (g pc) else none) :=
        List.filterMap_cons_some (if_pos hp)
      have e2 : (p :: l).filter (fun x : Pc => x.seg == s) =
          p :: l.filter (fun x : Pc => x.seg == s) := List.filter_cons_of_pos hp
      rw [e1, e2, List.map_cons, ih]
    · have e1 : (p :: l).filterMap (fun pc => if pc.seg == s then some (g pc) else none) =
          l.filterMap (fun pc => if pc.seg == s then some (g pc) else none) :=
        List.filterMap_cons_none (if_neg hp)
      have e2 : (p :: l).filter (fun x : Pc => x.seg == s) = l.filter (fun x : Pc => x.seg == s) :=
        List.filter_cons_of_neg hp
      rw [e1, e2, ih]

/-- **LW, read.** -/
theorem readE_sumW_pieces (c : ACall) (zk : Array E) (s : Seg) (hn : zk.size = c.call.n) :
    readE (sumW (pieces c zk s)) = lwAt c.call.n c.pcs.toList (readV zk) s := by
  rw [readE_sumW]
  unfold pieces lwAt
  simp only [List.toList_toArray]
  rw [((List.mergeSort_perm _ _).map fun x : PW => readE x.wp).sum_eq, found_eq, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact readE_wp zk c.call.n p.off p.b hn

/-- **The port's wall, read.** -/
theorem readE_wall (c : ACall) (zk : Array E) (hn : zk.size = c.call.n) :
    readE (wall c zk) = (c.pcs.toList.map fun p => wpAt c.call.n p.off p.b (readV zk)).sum := by
  have h : ∀ (l : List Pc) (s : E),
      readE (l.foldl
        (fun s pc => addE s (eqAt (zk.extract 0 (c.call.n - pc.b)) (pc.off >>> pc.b))) s) =
      readE s + (l.map fun p => wpAt c.call.n p.off p.b (readV zk)).sum := by
    intro l
    induction l with
    | nil =>
      intro s
      rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, readE_add,
        readE_wp zk c.call.n x.off x.b hn, add_assoc]
  rw [wall, ← Array.foldl_toList, h, readE_zero, zero_add]

/-! ## A call by its segments -/

/-- A segment's share of the extension of a call's key vector. -/
def share {K : Type} [Field K] (S : Sh) (cell : NameA → K) (sh n : ℕ) (ps : List Pc) (pt : ℕ → K)
    (s : Seg) : K :=
  ((ofSeg ps s).map fun p => wpAt n p.off p.b pt *
    Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum

/-- A sum over pieces, by a list of segments without doubles that covers them. -/
theorem sum_bySeg {K : Type} [Field K] (segs : List Seg) (hnd : segs.Nodup) (ps : List Pc)
    (hcov : ∀ p ∈ ps, p.seg ∈ segs) (G : Pc → K) :
    (ps.map G).sum = (segs.map fun s => ((ofSeg ps s).map G).sum).sum := by
  induction ps with
  | nil => simp [ofSeg]
  | cons p ps ih =>
    have h1 : ∀ (l : List Seg), l.Nodup →
        (l.map fun s => ((ofSeg (p :: ps) s).map G).sum).sum =
          (if p.seg ∈ l then G p else 0) + (l.map fun s => ((ofSeg ps s).map G).sum).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons s l ihl =>
        intro hl
        obtain ⟨hs, hl'⟩ := List.nodup_cons.1 hl
        simp only [List.map_cons, List.sum_cons]
        rw [ihl hl']
        by_cases hps : p.seg = s
        · have hb : (p.seg == s) = true := by rw [hps]; exact beq_self_eq_true s
          have hnot : p.seg ∉ l := by rw [hps]; exact hs
          have e : ofSeg (p :: ps) s = p :: ofSeg ps s := List.filter_cons_of_pos hb
          rw [e, if_neg hnot, if_pos (by rw [hps]; exact List.mem_cons_self ..)]
          simp only [List.map_cons, List.sum_cons]
          ring
        · have hb : ¬(p.seg == s) = true := fun hh => hps (eq_of_beq hh)
          have e : ofSeg (p :: ps) s = ofSeg ps s := List.filter_cons_of_neg hb
          rw [e]
          by_cases hm : p.seg ∈ l
          · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
            ring
          · rw [if_neg hm, if_neg (fun hh => by
              rcases List.mem_cons.1 hh with h2 | h2
              · exact hps h2
              · exact hm h2)]
            ring
    rw [h1 segs hnd, if_pos (hcov p (List.mem_cons_self ..)), List.map_cons, List.sum_cons,
      ih fun x hx => hcov x (List.mem_cons_of_mem _ hx)]

/-- **The extension of a call's key vector: its segments' shares and the padding's term.** -/
theorem call_split {K : Type} [Field K] (S : Sh) (h : Forest.Shape) (cell : NameA → K) (q n : ℕ)
    (c : ACall) (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → K)
    (segs : List Seg) (hnd : segs.Nodup) (hcov : ∀ p ∈ c.pcs.toList, p.seg ∈ segs) :
    Blocks.ext n (kvA S h cell q) pt =
      (segs.map (share S cell c.sh n c.pcs.toList pt)).sum +
      (tauN h q (t0N h q) : K) * (1 - (c.pcs.toList.map fun p => wpAt n p.off p.b pt).sum) := by
  rw [alg_pieces S h cell q n c hc ok pt, sum_bySeg segs hnd c.pcs.toList hcov]
  rfl

/-! ## Each unit over the port's world -/

variable (W : World GE)

/-- **A unit of kind KR.** -/
theorem unitW_KR (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (hn : zk.size = c.call.n)
    (pc : PlaneClaim) (hs : pc.seg = Seg.rm ∨ pc.seg = Seg.rd) (hpw : pc.pw = pieces c zk pc.seg)
    (rule : ∀ x < 3, W.slot (pc.s0 + x) = ruleAt c.call.n c.pcs.toList (readV zk) pc.seg
      fun p => asC S cell x p.lam p.a (pc.seg == Seg.rd)) :
    (keyKR pc).value Reading.gl W = share S cell c.sh c.call.n c.pcs.toList (readV zk) pc.seg := by
  have r0 := rule 0 (by omega)
  rw [Nat.add_zero] at r0
  unfold share
  rw [value_keyKR, hpw, readE_sumW_pieces c zk pc.seg hn, unit_KR S cell c.sh _ _ _ pc.seg hs, r0,
    rule 1 (by omega), rule 2 (by omega)]

/-- **The unit of segment wh.** -/
theorem unitW_WH (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (hn : zk.size = c.call.n)
    (d : Divide) (hpw : d.pwH = pieces c zk .wh)
    (r2 : W.slot d.s5h = ruleAt c.call.n c.pcs.toList (readV zk) .wh (rhW S cell false))
    (r2p : W.slot (d.s5h + 1) = ruleAt c.call.n c.pcs.toList (readV zk) .wh (rhW S cell true)) :
    (keyWH d).value Reading.gl W = share S cell c.sh c.call.n c.pcs.toList (readV zk) .wh := by
  unfold share
  rw [value_keyWH, hpw, readE_sumW_pieces c zk .wh hn, unit_WH, r2, r2p]

/-- **A unit of kind KFD.** pub: the port's closed form of the gap's public part, read, is its rule
value. -/
theorem unitW_KFD (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (hn : zk.size = c.call.n)
    (k : Score) (hs : k.seg = Seg.fm ∨ k.seg = Seg.fd) (hpw : k.pw = pieces c zk k.seg)
    (rule : ∀ x < 5, W.slot (k.s0 + x) = ruleAt c.call.n c.pcs.toList (readV zk) k.seg
      fun p => asC S cell x p.lam p.a (k.seg == Seg.fd))
    (ruleM : W.slot (k.s0 + 5) =
      ruleAt c.call.n c.pcs.toList (readV zk) k.seg (msAt S cell (k.seg == Seg.fd)))
    (ruleS : W.slot (k.s0 + 6) = ruleAt c.call.n c.pcs.toList (readV zk) k.seg
      fun p => ssAt S cell (k.seg == Seg.fd) p.lam p.a)
    (pub : (if k.seg == Seg.fm then ((S.shd c.sh).C : GE) * readE (sumW k.pw) * readE (onesOf k.zs)
        else ((S.shd c.sh).Om : GE) * readE (sumW k.pw) * (1 - readE (leOf k.zj k.zi))) =
      ruleAt c.call.n c.pcs.toList (readV zk) k.seg fun _ => gcAt S c.sh (k.seg == Seg.fd)) :
    (keyKFD (S.shd c.sh) k).value Reading.gl W =
      share S cell c.sh c.call.n c.pcs.toList (readV zk) k.seg := by
  have r0 := rule 0 (by omega)
  rw [Nat.add_zero] at r0
  unfold share
  rw [value_keyKFD, pub, hpw, readE_sumW_pieces c zk k.seg hn, unit_KFD S cell c.sh _ _ _ k.seg hs,
    r0, rule 1 (by omega), rule 2 (by omega), rule 3 (by omega), rule 4 (by omega), ruleM, ruleS]

/-- **The unit of segment wl.** -/
theorem unitW_WL (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (hn : zk.size = c.call.n)
    (b' : ℕ) (hsz : S.dh * S.T * S.G = 2 ^ b') (hb : ∀ p ∈ ofSeg c.pcs.toList .wl, p.b = 1 + b')
    (d : Divide) (hpw : d.pwW = pieces c zk .wl)
    (hz : readE d.zsl = readV zk (c.call.n - (1 + b')))
    (rAC : W.slot d.sACC = ruleW c.call.n b' c.pcs.toList (readV zk) (accW S cell))
    (rZO : W.slot d.sZO = ruleW c.call.n b' c.pcs.toList (readV zk) (zoW S cell))
    (rZC : W.slot d.sZC = ruleW c.call.n b' c.pcs.toList (readV zk) (denW S cell))
    (rRH : W.slot d.sRH = ruleW c.call.n b' c.pcs.toList (readV zk) (rhL S cell false))
    (rRHP : W.slot d.sRHP = ruleW c.call.n b' c.pcs.toList (readV zk) (rhL S cell true)) :
    (keyWL d).value Reading.gl W = share S cell c.sh c.call.n c.pcs.toList (readV zk) .wl := by
  unfold share
  rw [value_keyWL, hpw, readE_sumW_pieces c zk .wl hn, unit_WL S cell c.sh _ b' _ _ hsz hb, hz, rAC,
    rZO, rZC, rRH, rRHP]

/-- indexForm, valued. -/
theorem value_indexForm (d : Divide) (lt : ℕ) :
    (indexForm d lt).value Reading.gl W =
      sumN lt fun k => ((2 ^ k : ℕ) : GE) * W.slot (d.sIB + k) := by
  have h : ∀ (l : List ℕ) (f : Aff) (s : GE), f.value Reading.gl W = s →
      (l.foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (ofNat (2 ^ k))) f).value
        Reading.gl W = l.foldl (fun s k => s + ((2 ^ k : ℕ) : GE) * W.slot (d.sIB + k)) s := by
    intro l
    induction l with
    | nil => intro f s hf; exact hf
    | cons k l ih =>
      intro f s hf
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      rw [Aff.value_addMul, Aff.value_slot, hf, gl_val, readE_ofNat]
  unfold indexForm sumN
  exact h _ _ _ (by rw [Aff.value_ofConst, gl_val, readE_zero])

/-- **keyIX, valued.** -/
theorem value_keyIX (S : Sh) (d : Divide) :
    (keyIX S d).value Reading.gl W =
      kfIX S.cf.lt (readE (sumW d.pwX) * readE (idOf d.ziX)) fun k => W.slot (d.sIB + k) := by
  unfold keyIX kfIX
  rw [Aff.value_scale, Aff.value_sub, Aff.value_ofConst, value_indexForm, gl_val, gl_val,
    readE_ofNat, readE_mul]

/-- **The unit of segment ix.** pub: LW id(ziX), read, is the rule value of the token's number. -/
theorem unitW_IX (S : Sh) (cell : NameA → GE) (c : ACall) (zk : Array E) (d : Divide)
    (rIB : ∀ k < S.cf.lt,
      W.slot (d.sIB + k) = ruleAt c.call.n c.pcs.toList (readV zk) .ix (ibX S cell k))
    (pub : readE (sumW d.pwX) * readE (idOf d.ziX) =
      ruleAt c.call.n c.pcs.toList (readV zk) .ix fun _ κ => ((κ % S.T : ℕ) : GE)) :
    (keyIX S d).value Reading.gl W = share S cell c.sh c.call.n c.pcs.toList (readV zk) .ix := by
  unfold share
  rw [value_keyIX, pub, unit_IX]
  unfold kfIX
  rw [sumN_eq, sumN_eq]
  congr 3
  apply List.map_congr_left
  intro k hk
  beta_reduce
  rw [rIB k (List.mem_range.1 hk)]

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.readE_eqAt
#print axioms OnBytes.Ends.A.readE_sumW_pieces
#print axioms OnBytes.Ends.A.readE_wall
#print axioms OnBytes.Ends.A.call_split
#print axioms OnBytes.Ends.A.unitW_KR
#print axioms OnBytes.Ends.A.unitW_KFD
#print axioms OnBytes.Ends.A.unitW_WL
#print axioms OnBytes.Ends.A.unitW_IX
#print axioms OnBytes.Ends.A.unitW_WH
