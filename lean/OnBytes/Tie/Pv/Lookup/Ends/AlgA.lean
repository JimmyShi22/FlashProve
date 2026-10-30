-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/AlgA.lean: the extension of a call's key vector, in the lookup of an
attention sub-proof's own calls, at a point: piece by piece, and, for a call of kind KR, as a key
form in six named scalars.

Definitions, statements and proofs, over any field E, in the terms of
OnBytes/Tie/Pv/Lookup/Ends/A.lean, of Cb/Pv/Lookup/Ends/Pieces.lean and of the library's Blocks.ext.
"The port" is the Lean verifier under OnBytes/. The statement on a kind is pointwise and has two
halves: the rule (each named scalar has its rule value at this reading of the cells), which is a
premise here, and an algebraic identity (under the rule, the key form's value is the extension of
the call's key vector at the point).
Main names:
  `pcKey`: the keys of a piece (segKey). `ofSeg`: the pieces of a segment.
  `PcsOK n ps`: the pieces of a call of 2^n keys are aligned, inside the call and pairwise apart:
    numbers alone.
  `ruleAt n ps pt s F`: the rule value of a scalar of the unit (call, s): the sum over the unit's
    pieces of the piece's weight times the extension, at the inner point, of a function F of the
    piece and the place. `lwAt`: the sum of the weights of the unit's pieces.
  `kfKR r0 r1 fl lw`: what one unit adds to the key form of a call of kind KR.
  `kvA_eq`: if S.calls[q]? = some c, then call q's key vector kvA is pwVec over c's pieces, with the
    call's padding row for the padding value.
  `alg_pieces`: under S.calls[q]? = some c and PcsOK n c.pcs.toList:
      ext n (kvA q) pt = the sum over the pieces of wpAt * ext b (pcKey of the piece) (inner point)
                         + (the call's padding row) * (1 - the sum of the weights).
  `unit_KR`: for s = rm or s = rd, the weighted sum over the pieces of segment s is kfKR at the
    three rule values and lwAt.
  `alg_KR`: under S.calls[q]? = some c; PcsOK n c.pcs.toList; every piece of c is of segment rm or
    rd; the call's padding row is 0 in E; and the rule, pl s x = ruleAt .. s (plane x of "as"), for
    all s and x: kfKR at rm's three scalars plus kfKR at rd's three is ext n (kvA q) pt.
  `ext_lin3`, `sum_lin3`: tools, without a premise. `sum_two`: if every member of a list passes
    exactly one of two tests, a sum over the list is the sum over the members that pass the first
    plus the sum over those that pass the second.
Limits: only the kind KR (segments rm, rd) is done here; nothing is stated here for the segments wh,
ix, wl, fm and fd (they are in AlgA2 and AlgA3 beside this file). kfKR is written after the port's
keyKR (OnBytes/Model/AttentionClaimsA.lean): that the port's form has this value is not stated here
(it is value_keyKR, in PortA beside this file). That PcsOK, the clause on the segments, the clause
on the padding row or the rule holds at a shape or a proof is not shown: all four are premises. The
rule is asked at all s and x, though only six values of pl occur in the statement. pl is an argument
that stands on the left of the rule alone, so the rule values themselves meet it.

-/
import OnBytes.Tie.Pv.Lookup.Ends.A
import Cb.Pv.Lookup.Ends.Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes.Model
open OnBytes.Attention (Seg ACall)

/-- The port's piece of a call of an attention sub-proof. -/
abbrev Pc : Type := OnBytes.Attention.Piece

variable {E : Type} [Field E]

/-! ## The call's key vector is laid in pieces -/

/-- The keys of a piece. -/
def pcKey (S : Sh) (cell : NameA → E) (sh : ℕ) (p : Pc) : ℕ → E :=
  segKey S cell sh p.seg p.lam p.a

/-- **Call q's key vector is pwVec over the port's own pieces.** -/
theorem kvA_eq (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) :
    kvA S h cell q = pwVec (fun p : Pc => p.off) (fun p => p.b) (pcKey S cell c.sh)
      (tauN h q (t0N h q) : E) c.pcs.toList := by
  funext X
  rw [← pwVec_find]
  unfold kvA kvSel
  rw [hc]
  dsimp only
  cases List.find? (fun p : Pc => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)) c.pcs.toList with
  | none => simp
  | some p => simp [pcKey]

/-- The pieces of a call of 2^n keys are aligned and pairwise apart. Numbers alone. -/
structure PcsOK (n : ℕ) (ps : List Pc) : Prop where
  /-- each piece is a whole aligned block inside the call -/
  al : ∀ p ∈ ps, p.b ≤ n ∧ 2 ^ p.b ∣ p.off ∧ p.off + 2 ^ p.b ≤ 2 ^ n
  /-- no two overlap -/
  ap : ps.Pairwise fun p q => p.off + 2 ^ p.b ≤ q.off ∨ q.off + 2 ^ q.b ≤ p.off

/-- **The extension of a call's key vector, piece by piece.** -/
theorem alg_pieces (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q n : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → E) :
    Blocks.ext n (kvA S h cell q) pt =
      (c.pcs.toList.map fun p => wpAt n p.off p.b pt *
        Blocks.ext p.b (pcKey S cell c.sh p) (innAt n p.b pt)).sum +
      (tauN h q (t0N h q) : E) * (1 - (c.pcs.toList.map fun p => wpAt n p.off p.b pt).sum) := by
  rw [kvA_eq S h cell q c hc]
  exact ext_pwVec (fun p : Pc => p.off) (fun p => p.b) n _ _ pt _ ok.al ok.ap

/-! ## Tools -/

/-- The extension of k + c1 A + c2 B + c3 C. -/
theorem ext_lin3 (b : ℕ) (k c1 c2 c3 : E) (A B C z : ℕ → E) :
    Blocks.ext b (fun κ => k + c1 * A κ + c2 * B κ + c3 * C κ) z =
      k + c1 * Blocks.ext b A z + c2 * Blocks.ext b B z + c3 * Blocks.ext b C z := by
  have e1 : Blocks.ext b (fun κ => k + c1 * A κ + c2 * B κ + c3 * C κ) z =
      Blocks.ext b (fun κ => k + c1 * A κ + c2 * B κ) z + Blocks.ext b (fun κ => c3 * C κ) z :=
    Blocks.ext_add b _ _ z
  have e2 : Blocks.ext b (fun κ => k + c1 * A κ + c2 * B κ) z =
      Blocks.ext b (fun κ => k + c1 * A κ) z + Blocks.ext b (fun κ => c2 * B κ) z :=
    Blocks.ext_add b _ _ z
  have e3 : Blocks.ext b (fun κ => k + c1 * A κ) z =
      Blocks.ext b (fun _ => k) z + Blocks.ext b (fun κ => c1 * A κ) z :=
    Blocks.ext_add b _ _ z
  rw [e1, e2, e3, Blocks.ext_const, Blocks.ext_smul, Blocks.ext_smul, Blocks.ext_smul]

/-- A sum over a list whose members are of two kinds. -/
theorem sum_two {ι : Type} (f g : ι → Bool) (l : List ι) (G : ι → E)
    (hfg : ∀ p ∈ l, (f p = true ∧ g p = false) ∨ (f p = false ∧ g p = true)) :
    (l.map G).sum = ((l.filter f).map G).sum + ((l.filter g).map G).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have ih' := ih fun x hx => hfg x (List.mem_cons_of_mem _ hx)
    rcases hfg p (List.mem_cons_self ..) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [List.filter_cons_of_pos h1, List.filter_cons_of_neg (by simp [h2])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih']
      ring
    · rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_pos h2]
      simp only [List.map_cons, List.sum_cons]
      rw [ih']
      ring

/-- A weighted sum of k + c1 A + c2 B + c3 C over a list. -/
theorem sum_lin3 {ι : Type} (l : List ι) (w A B C : ι → E) (k c1 c2 c3 : E) :
    (l.map fun p => w p * (k + c1 * A p + c2 * B p + c3 * C p)).sum =
      k * (l.map w).sum + c1 * (l.map fun p => w p * A p).sum +
        c2 * (l.map fun p => w p * B p).sum + c3 * (l.map fun p => w p * C p).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-! ## The rule's values -/

/-- The pieces of segment s. -/
def ofSeg (ps : List Pc) (s : Seg) : List Pc := ps.filter fun p => p.seg == s

/-- The rule value of a scalar of the unit (call, s): the sum over the unit's pieces of the piece's
weight times the extension, at the inner point, of a function F of the piece and the place. -/
def ruleAt (n : ℕ) (ps : List Pc) (pt : ℕ → E) (s : Seg) (F : Pc → ℕ → E) : E :=
  ((ofSeg ps s).map fun p => wpAt n p.off p.b pt * Blocks.ext p.b (F p) (innAt n p.b pt)).sum

/-- LW: the sum of the weights of the unit's pieces. -/
def lwAt (n : ℕ) (ps : List Pc) (pt : ℕ → E) (s : Seg) : E :=
  ((ofSeg ps s).map fun p => wpAt n p.off p.b pt).sum

/-! ## Kind KR -/

/-- What one unit adds to the key form of a call of kind KR (keyKR), in the three scalars. -/
def kfKR (r0 r1 fl lw : E) : E :=
  (r0 + 128 * lw) + ((2 ^ 20 : ℕ) : E) * (r1 + 128 * lw) + ((2 ^ 40 : ℕ) : E) * fl

/-- The weighted sum over the pieces of one segment of kind KR, in the rule's values. -/
theorem unit_KR (S : Sh) (cell : NameA → E) (sh n : ℕ) (ps : List Pc) (pt : ℕ → E) (s : Seg)
    (hs : s = Seg.rm ∨ s = Seg.rd) :
    ((ofSeg ps s).map fun p => wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum =
    kfKR (ruleAt n ps pt s fun p => asC S cell 0 p.lam p.a (s == Seg.rd))
      (ruleAt n ps pt s fun p => asC S cell 1 p.lam p.a (s == Seg.rd))
      (ruleAt n ps pt s fun p => asC S cell 2 p.lam p.a (s == Seg.rd)) (lwAt n ps pt s) := by
  have hk : ∀ p ∈ ofSeg ps s, Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt) =
      (128 + ((2 ^ 20 : ℕ) : E) * 128) +
        1 * Blocks.ext p.b (asC S cell 0 p.lam p.a (s == Seg.rd)) (innAt n p.b pt) +
        ((2 ^ 20 : ℕ) : E) *
          Blocks.ext p.b (asC S cell 1 p.lam p.a (s == Seg.rd)) (innAt n p.b pt) +
        ((2 ^ 40 : ℕ) : E) *
          Blocks.ext p.b (asC S cell 2 p.lam p.a (s == Seg.rd)) (innAt n p.b pt) := by
    intro p hp
    have hps : p.seg = s := by
      have := (List.mem_filter.1 hp).2
      exact eq_of_beq this
    rw [← ext_lin3]
    apply Blocks.ext_congr
    intro κ _
    unfold pcKey
    rw [hps]
    rcases hs with rfl | rfl
    · show (asC S cell 0 p.lam p.a false κ + 128) +
        ((2 ^ 20 : ℕ) : E) * (asC S cell 1 p.lam p.a false κ + 128) +
        ((2 ^ 40 : ℕ) : E) * asC S cell 2 p.lam p.a false κ = _
      show _ = (128 + ((2 ^ 20 : ℕ) : E) * 128) + 1 * asC S cell 0 p.lam p.a false κ +
        ((2 ^ 20 : ℕ) : E) * asC S cell 1 p.lam p.a false κ +
        ((2 ^ 40 : ℕ) : E) * asC S cell 2 p.lam p.a false κ
      ring
    · show (asC S cell 0 p.lam p.a true κ + 128) +
        ((2 ^ 20 : ℕ) : E) * (asC S cell 1 p.lam p.a true κ + 128) +
        ((2 ^ 40 : ℕ) : E) * asC S cell 2 p.lam p.a true κ = _
      show _ = (128 + ((2 ^ 20 : ℕ) : E) * 128) + 1 * asC S cell 0 p.lam p.a true κ +
        ((2 ^ 20 : ℕ) : E) * asC S cell 1 p.lam p.a true κ +
        ((2 ^ 40 : ℕ) : E) * asC S cell 2 p.lam p.a true κ
      ring
  rw [List.map_congr_left fun p hp => by rw [hk p hp], sum_lin3]
  unfold kfKR ruleAt lwAt
  ring

/-- **The identity at a call of kind KR.** r0, r1, fl: the three scalars of each of the two
units. -/
theorem alg_KR (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q n : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → E)
    (hseg : ∀ p ∈ c.pcs.toList, p.seg = Seg.rm ∨ p.seg = Seg.rd)
    (hpad : (tauN h q (t0N h q) : E) = 0) (pl : Seg → ℕ → E)
    (rule : ∀ s x, pl s x =
      ruleAt n c.pcs.toList pt s fun p => asC S cell x p.lam p.a (s == Seg.rd)) :
    kfKR (pl .rm 0) (pl .rm 1) (pl .rm 2) (lwAt n c.pcs.toList pt .rm) +
      kfKR (pl .rd 0) (pl .rd 1) (pl .rd 2) (lwAt n c.pcs.toList pt .rd) =
    Blocks.ext n (kvA S h cell q) pt := by
  rw [alg_pieces S h cell q n c hc ok pt, hpad, zero_mul, add_zero,
    sum_two (fun p : Pc => p.seg == Seg.rm) (fun p => p.seg == Seg.rd)]
  · rw [rule, rule, rule, rule, rule, rule]
    exact congrArg₂ (· + ·) (unit_KR S cell c.sh n _ pt .rm (Or.inl rfl)).symm
      (unit_KR S cell c.sh n _ pt .rd (Or.inr rfl)).symm
  · intro p hp
    rcases hseg p hp with h1 | h1 <;> rw [h1]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.kvA_eq
#print axioms OnBytes.Ends.A.alg_pieces
#print axioms OnBytes.Ends.A.alg_KR
