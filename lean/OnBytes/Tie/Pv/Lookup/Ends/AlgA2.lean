-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/AlgA2.lean: as OnBytes/Tie/Pv/Lookup/Ends/AlgA.lean,
for the segments wh, ix, fm and fd: a unit's weighted sum of the extensions of its pieces' keys is a
key form in the unit's scalars at their rule values.

Definitions, statements and proofs, over any field E. The terms are those of
OnBytes/Tie/Pv/Lookup/Ends/A.lean, of the file named above, of Cb/Pv/Lookup/Ends/Lin.lean and of the
library's Blocks.ext. "The port" is the Lean verifier under OnBytes/.
Main names:
  `rhW`, `ibX`, `msAt`, `gcAt`: functions of a piece and a place, whose rule values the scalars
    are: the high parts of the remainders; bit k of the index; the row maximum's part of the gap;
    the gap's public part (C at the empty tile slot, Om above the diagonal).
  `kfWH`, `kfIX`, `kfKFD`: key forms as terms in the scalars, written after the port's keyWH, keyIX
    (OnBytes/Model/AttentionClaimsB.lean) and keyKFD (OnBytes/Model/AttentionClaimsA.lean).
  `unit_WH`, `unit_IX`: without a premise: the weighted sum over the pieces of segment wh is kfWH,
    and that of segment ix is kfIX, at the rule values.
  `unit_KFD`: for s = fm or s = fd, the weighted sum over the pieces of segment s is kfKFD at the
    rule values of planes 0 to 4 of "as", of msAt, of ssAt and of gcAt. msAt is linear in the cells;
    ssAt is of degree two in the cells. `gapAt_split`: the gap is msAt + gcAt.
  `alg_WH`: under S.calls[q]? = some c; PcsOK n c.pcs.toList; every piece of c is of segment wh; the
    call's padding row is 0 in E; and the rule for the two scalars r2 and r2p: kfWH is
    ext n (kvA q) pt.
  `alg_KFD`: under S.calls[q]? = some c; PcsOK n c.pcs.toList; every piece of c is of segment fm or
    fd; and the rules for pl, ms and ss, asked at all s and x: the padding row times (1 - the sum of
    the weights), plus kfKFD at fm's scalars, plus kfKFD at fd's, is ext n (kvA q) pt.
Limits: the public values are left as extensions here. idLW is the rule value of κ ↦ the token's
number; gc is the rule value of gcAt. Their closed forms are not stated here. Tools for them are
ext_field and ext_allOnes (Cb/Pv/Lookup/Ends/Lin.lean);
that the rule values are the closed forms is proved in none of these
files. No whole call with segment ix is stated here. That the port's forms have these values is not
stated here. The premises on the shape and the rules are shown of no shape and no proof.

-/
import OnBytes.Tie.Pv.Lookup.Ends.AlgA
import Cb.Pv.Lookup.Ends.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes.Model
open OnBytes.Attention (Seg ACall)

variable {E : Type} [Field E]

/-- A member of ofSeg has the segment. -/
theorem seg_of_mem {ps : List Pc} {s : Seg} {p : Pc} (hp : p ∈ ofSeg ps s) : p.seg = s :=
  eq_of_beq (List.mem_filter.1 hp).2

/-- sumN is the sum of the list of values. -/
theorem sumN_eq (n : ℕ) (f : ℕ → E) : sumN n f = ((List.range n).map f).sum := by
  have h : ∀ (l : List ℕ) (s : E), l.foldl (fun s i => s + f i) s = s + (l.map f).sum := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x l ih =>
      intro s
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring
  unfold sumN
  rw [h, zero_add]

/-! ## Segment wh -/

/-- RH2's and RHP2's term: the remainders' high parts at place κ = (g | i | n) of the piece. -/
def rhW (S : Sh) (cell : NameA → E) (second : Bool) (p : Pc) (κ : ℕ) : E :=
  let f := (κ / (S.dh * S.T) * S.HA + p.a) * S.dh + κ % S.dh
  if second then rhp S cell p.lam f (κ / S.dh % S.T) else rh S cell p.lam f (κ / S.dh % S.T)

/-- The key form of the call of kind WH (keyWH), in its two scalars. -/
def kfWH (r2 r2p lw : E) : E := (r2 + 128 * lw) + ((2 ^ 20 : ℕ) : E) * (r2p + 128 * lw)

/-- **Segment wh.** -/
theorem unit_WH (S : Sh) (cell : NameA → E) (sh n : ℕ) (ps : List Pc) (pt : ℕ → E) :
    ((ofSeg ps .wh).map fun p => wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum =
    kfWH (ruleAt n ps pt .wh (rhW S cell false)) (ruleAt n ps pt .wh (rhW S cell true))
      (lwAt n ps pt .wh) := by
  rw [unit_lin (ofSeg ps .wh) (fun p => wpAt n p.off p.b pt) (fun p => p.b)
    (fun p => innAt n p.b pt) (pcKey S cell sh) (128 + ((2 ^ 20 : ℕ) : E) * 128)
    [(1, rhW S cell false), (((2 ^ 20 : ℕ) : E), rhW S cell true)]]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    unfold kfWH ruleAt lwAt
    ring
  · intro p hp κ
    unfold pcKey
    rw [seg_of_mem hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, segKey, rhW,
      Bool.false_eq_true, if_false, if_true]
    ring

/-- A list all of whose members have the segment s is its own ofSeg. -/
theorem ofSeg_all {ps : List Pc} {s : Seg} (h : ∀ p ∈ ps, p.seg = s) : ofSeg ps s = ps :=
  List.filter_eq_self.2 fun p hp => by rw [h p hp]; exact beq_self_eq_true s

/-- **The identity at a call of kind WH.** -/
theorem alg_WH (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q n : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → E)
    (hseg : ∀ p ∈ c.pcs.toList, p.seg = Seg.wh) (hpad : (tauN h q (t0N h q) : E) = 0)
    (r2 r2p : E) (rule2 : r2 = ruleAt n c.pcs.toList pt .wh (rhW S cell false))
    (rule2p : r2p = ruleAt n c.pcs.toList pt .wh (rhW S cell true)) :
    kfWH r2 r2p (lwAt n c.pcs.toList pt .wh) = Blocks.ext n (kvA S h cell q) pt := by
  rw [alg_pieces S h cell q n c hc ok pt, hpad, zero_mul, add_zero, rule2, rule2p,
    ← unit_WH S cell c.sh n c.pcs.toList pt, ofSeg_all hseg]

/-! ## Segment ix -/

/-- IB_k's term: bit k of the index at place κ = (g | i) of the piece. -/
def ibX (S : Sh) (cell : NameA → E) (k : ℕ) (p : Pc) (κ : ℕ) : E :=
  ib S cell p.lam k (κ / S.T * S.HA + p.a) (κ % S.T)

/-- The term of segment ix in a key form (keyIX), in the scalars IB_k and the public value idLW. -/
def kfIX (lt : ℕ) (idLW : E) (ibs : ℕ → E) : E :=
  ((2 ^ (16 - lt) : ℕ) : E) * (idLW - sumN lt fun k => ((2 ^ k : ℕ) : E) * ibs k)

/-- A sum of multiples by - c d k. -/
theorem sum_neg_scale (l : List ℕ) (c : E) (d B : ℕ → E) :
    (l.map fun k => -(c * d k) * B k).sum = -(c * (l.map fun k => d k * B k).sum) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- **Segment ix.** -/
theorem unit_IX (S : Sh) (cell : NameA → E) (sh n : ℕ) (ps : List Pc) (pt : ℕ → E) :
    ((ofSeg ps .ix).map fun p => wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum =
    kfIX S.cf.lt (ruleAt n ps pt .ix fun _ κ => ((κ % S.T : ℕ) : E))
      (fun k => ruleAt n ps pt .ix (ibX S cell k)) := by
  rw [unit_lin (ofSeg ps .ix) (fun p => wpAt n p.off p.b pt) (fun p => p.b)
    (fun p => innAt n p.b pt) (pcKey S cell sh) 0
    ((((2 ^ (16 - S.cf.lt) : ℕ) : E), fun _ κ => ((κ % S.T : ℕ) : E)) ::
      (List.range S.cf.lt).map fun k =>
        (-(((2 ^ (16 - S.cf.lt) : ℕ) : E) * ((2 ^ k : ℕ) : E)), ibX S cell k))]
  · simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    rw [sum_neg_scale]
    unfold kfIX ruleAt
    rw [sumN_eq]
    ring
  · intro p hp κ
    unfold pcKey
    rw [seg_of_mem hp]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    rw [sum_neg_scale]
    simp only [segKey, ibX]
    rw [sumN_eq]
    ring

/-! ## Segments fm, fd -/

/-- MS's term: the row maximum's part of the gap at place κ: 0 at the empty tile slot. -/
def msAt (S : Sh) (cell : NameA → E) (isD : Bool) (p : Pc) (κ : ℕ) : E :=
  let i := κ / S.B % S.B
  if isD then
    mx S cell p.lam (κ / (S.B * S.B * S.nT) * S.HA + p.a) (κ / (S.B * S.B) % S.nT * S.B + i)
  else if κ / (S.B * S.B) % S.nT = S.nT - 1 then 0
  else mx S cell p.lam (κ / (S.B * S.B * S.nT * S.hP) * S.HA + p.a)
    ((S.cover (κ / (S.B * S.B * S.nT) % S.hP) (κ / (S.B * S.B) % S.nT)).1 * S.B + i)

/-- The gap's public part at place κ: C at the empty tile slot; Om above the diagonal. -/
def gcAt (S : Sh) (sh : ℕ) (isD : Bool) (κ : ℕ) : E :=
  if isD then (if κ / S.B % S.B < κ % S.B then ((S.shd sh).Om : E) else 0)
  else if κ / (S.B * S.B) % S.nT = S.nT - 1 then ((S.shd sh).C : E) else 0

/-- The gap is its row maximum's part plus its public part. -/
theorem gapAt_split (S : Sh) (cell : NameA → E) (sh : ℕ) (isD : Bool) (p : Pc) (κ : ℕ) :
    gapAt S cell sh isD p.lam p.a κ = msAt S cell isD p κ + gcAt S sh isD κ := by
  unfold gapAt msAt gcAt
  cases isD
  · simp only [Bool.false_eq_true, if_false]
    split_ifs
    · rw [zero_add]
    · rw [add_zero]
  · simp only [if_true]

/-- What one unit adds to the key form of a call of kind KFD (keyKFD), in its seven scalars and the
public value gc. -/
def kfKFD (r0 r1 fl e0 e1 ms ss gc lw : E) : E :=
  (ms - ss + gc) - (r0 + 128 * lw) - 256 * (r1 + 128 * lw) + ((2 ^ 32 : ℕ) : E) * fl +
    ((2 ^ 33 : ℕ) : E) * (e0 + 128 * lw + 256 * e1)

/-- **Segments fm and fd.** -/
theorem unit_KFD (S : Sh) (cell : NameA → E) (sh n : ℕ) (ps : List Pc) (pt : ℕ → E) (s : Seg)
    (hs : s = Seg.fm ∨ s = Seg.fd) :
    ((ofSeg ps s).map fun p => wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum =
    kfKFD (ruleAt n ps pt s fun p => asC S cell 0 p.lam p.a (s == Seg.fd))
      (ruleAt n ps pt s fun p => asC S cell 1 p.lam p.a (s == Seg.fd))
      (ruleAt n ps pt s fun p => asC S cell 2 p.lam p.a (s == Seg.fd))
      (ruleAt n ps pt s fun p => asC S cell 3 p.lam p.a (s == Seg.fd))
      (ruleAt n ps pt s fun p => asC S cell 4 p.lam p.a (s == Seg.fd))
      (ruleAt n ps pt s (msAt S cell (s == Seg.fd)))
      (ruleAt n ps pt s fun p => ssAt S cell (s == Seg.fd) p.lam p.a)
      (ruleAt n ps pt s fun _ => gcAt S sh (s == Seg.fd)) (lwAt n ps pt s) := by
  rw [unit_lin (ofSeg ps s) (fun p => wpAt n p.off p.b pt) (fun p => p.b)
    (fun p => innAt n p.b pt) (pcKey S cell sh)
    (-128 - 256 * 128 + ((2 ^ 33 : ℕ) : E) * 128)
    [(1, msAt S cell (s == Seg.fd)), (1, fun _ => gcAt S sh (s == Seg.fd)),
     (-1, fun p => ssAt S cell (s == Seg.fd) p.lam p.a),
     (-1, fun p => asC S cell 0 p.lam p.a (s == Seg.fd)),
     (-256, fun p => asC S cell 1 p.lam p.a (s == Seg.fd)),
     (((2 ^ 32 : ℕ) : E), fun p => asC S cell 2 p.lam p.a (s == Seg.fd)),
     (((2 ^ 33 : ℕ) : E), fun p => asC S cell 3 p.lam p.a (s == Seg.fd)),
     (((2 ^ 33 : ℕ) : E) * 256, fun p => asC S cell 4 p.lam p.a (s == Seg.fd))]]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    unfold kfKFD ruleAt lwAt
    ring
  · intro p hp κ
    unfold pcKey
    rw [seg_of_mem hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rcases hs with rfl | rfl
    · have hg := gapAt_split S cell sh false p κ
      have e : (Seg.fm == Seg.fd) = false := rfl
      rw [e]
      show gapAt S cell sh false p.lam p.a κ - ssAt S cell false p.lam p.a κ -
        (asC S cell 0 p.lam p.a false κ + 128) - 256 * (asC S cell 1 p.lam p.a false κ + 128) +
        ((2 ^ 32 : ℕ) : E) * asC S cell 2 p.lam p.a false κ +
        ((2 ^ 33 : ℕ) : E) * wt S cell p.lam p.a false κ = _
      rw [hg]
      unfold wt
      ring
    · have hg := gapAt_split S cell sh true p κ
      have e : (Seg.fd == Seg.fd) = true := rfl
      rw [e]
      show gapAt S cell sh true p.lam p.a κ - ssAt S cell true p.lam p.a κ -
        (asC S cell 0 p.lam p.a true κ + 128) - 256 * (asC S cell 1 p.lam p.a true κ + 128) +
        ((2 ^ 32 : ℕ) : E) * asC S cell 2 p.lam p.a true κ +
        ((2 ^ 33 : ℕ) : E) * wt S cell p.lam p.a true κ = _
      rw [hg]
      unfold wt
      ring

/-- **The identity at a call of kind KFD**, with the padding's term. The scalars of each of the two
units: pl s x (x below 5), ms s (linear in the cells), ss s (of degree two in the cells). -/
theorem alg_KFD (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q n : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → E)
    (hseg : ∀ p ∈ c.pcs.toList, p.seg = Seg.fm ∨ p.seg = Seg.fd) (pl : Seg → ℕ → E)
    (ms ss : Seg → E)
    (ruleP : ∀ s x, pl s x =
      ruleAt n c.pcs.toList pt s fun p => asC S cell x p.lam p.a (s == Seg.fd))
    (ruleM : ∀ s, ms s = ruleAt n c.pcs.toList pt s (msAt S cell (s == Seg.fd)))
    (ruleS : ∀ s, ss s = ruleAt n c.pcs.toList pt s fun p => ssAt S cell (s == Seg.fd) p.lam p.a) :
    (tauN h q (t0N h q) : E) * (1 - (c.pcs.toList.map fun p => wpAt n p.off p.b pt).sum) +
      (kfKFD (pl .fm 0) (pl .fm 1) (pl .fm 2) (pl .fm 3) (pl .fm 4) (ms .fm) (ss .fm)
          (ruleAt n c.pcs.toList pt .fm fun _ => gcAt S c.sh false) (lwAt n c.pcs.toList pt .fm) +
        kfKFD (pl .fd 0) (pl .fd 1) (pl .fd 2) (pl .fd 3) (pl .fd 4) (ms .fd) (ss .fd)
          (ruleAt n c.pcs.toList pt .fd fun _ => gcAt S c.sh true) (lwAt n c.pcs.toList pt .fd)) =
    Blocks.ext n (kvA S h cell q) pt := by
  have hs := sum_two (fun p : Pc => p.seg == Seg.fm) (fun p => p.seg == Seg.fd) c.pcs.toList
    (fun p => wpAt n p.off p.b pt * Blocks.ext p.b (pcKey S cell c.sh p) (innAt n p.b pt))
    (fun p hp => by
      beta_reduce
      rcases hseg p hp with h1 | h1 <;> rw [h1]
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩)
  rw [alg_pieces S h cell q n c hc ok pt, hs]
  simp only [ruleP, ruleM, ruleS]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ rfl
  exact congrArg₂ (· + ·) (unit_KFD S cell c.sh n _ pt .fm (Or.inl rfl)).symm
    (unit_KFD S cell c.sh n _ pt .fd (Or.inr rfl)).symm

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.unit_WH
#print axioms OnBytes.Ends.A.alg_WH
#print axioms OnBytes.Ends.A.unit_IX
#print axioms OnBytes.Ends.A.unit_KFD
#print axioms OnBytes.Ends.A.alg_KFD
