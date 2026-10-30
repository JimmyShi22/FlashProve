-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/AlgA3.lean: as OnBytes/Tie/Pv/Lookup/Ends/AlgA.lean,
for the segment wl and for a call of kind R16 that holds the segments wl and ix.

Definitions, statements and proofs, over any field E. A place of segment wl is (χ | g | i | n), the
half χ in front; its scalars stand at (g | i | n). "The port" is the Lean verifier under OnBytes/.
Main names:
  `hdW`, `denW`, `zoW`, `accW`, `rhL`: the components at (g | i | n): the query head; the
    denominator; the denominator times the output and the accumulator (both of degree two in the
    cells); the high parts of the two remainders. `key0`, `key1`: the key at χ = 0 and at χ = 1.
  `ruleW n b' ps pt F`: the rule value of a scalar of segment wl: as ruleAt, at the inner point
    without its first coordinate.
  `kfWL`: the term of segment wl in a key form, in its five scalars and zsl, written after the
    port's keyWL (OnBytes/Model/AttentionClaimsB.lean).
  `wl_low`, `wl_high`: under dh T G = 2^b', p.seg = wl and κ < 2^b': the piece's key at κ is key0,
    and at 2^b' + κ it is key1.
  `unit_WL`: under dh T G = 2^b', and p.b = 1 + b' for every piece p of wl (numbers alone): the
    weighted sum over the pieces of segment wl is kfWL at zsl := pt (n - (1 + b')), at the rule
    values of accW, zoW, denW and rhL, and at lwAt.
  `alg_R16`: under S.calls[q]? = some c; PcsOK n c.pcs.toList; every piece of c is of segment wl or
    ix; the call's padding row is 0 in E; dh T G = 2^b'; p.b = 1 + b' for every piece of wl; and the
    rules for ac, zo, zc, rh', rhp' and, at all k, ibs k: kfWL plus kfIX is ext n (kvA q) pt.
Limits: in alg_R16 the public value idLW is left as an extension (the rule value of κ ↦ the token's
number). That the port's forms have these values is not stated here. The premises on the shape and
the rules are shown of no shape and no proof.

-/
import OnBytes.Tie.Pv.Lookup.Ends.AlgA2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes.Model
open OnBytes.Attention (Seg ACall)

variable {E : Type} [Field E]

/-! ## The components at (g | i | n) -/

/-- The query head at place κ = (g | i | n) of the piece. -/
def hdW (S : Sh) (p : Pc) (κ : ℕ) : ℕ := κ / (S.dh * S.T) % S.G * S.HA + p.a

/-- ZC's term: the denominator. -/
def denW (S : Sh) (cell : NameA → E) (p : Pc) (κ : ℕ) : E :=
  den S cell p.lam (hdW S p κ) (κ / S.dh % S.T)

/-- ZO's term: the denominator times the output. Of degree two in the cells. -/
def zoW (S : Sh) (cell : NameA → E) (p : Pc) (κ : ℕ) : E :=
  denW S cell p κ * ten S cell S.atO p.lam (hdW S p κ * S.dh + κ % S.dh) (κ / S.dh % S.T)

/-- ACC's term: the accumulator. Of degree two in the cells. -/
def accW (S : Sh) (cell : NameA → E) (p : Pc) (κ : ℕ) : E :=
  acc S cell p.lam p.a (κ / (S.dh * S.T) % S.G) (κ / S.dh % S.T) (κ % S.dh)

/-- RH's and RHP's term. -/
def rhL (S : Sh) (cell : NameA → E) (second : Bool) (p : Pc) (κ : ℕ) : E :=
  if second then rhp S cell p.lam (hdW S p κ * S.dh + κ % S.dh) (κ / S.dh % S.T)
  else rh S cell p.lam (hdW S p κ * S.dh + κ % S.dh) (κ / S.dh % S.T)

/-- The key at χ = 0. -/
def key0 (S : Sh) (cell : NameA → E) (p : Pc) (κ : ℕ) : E :=
  2 * accW S cell p κ + denW S cell p κ - 2 * zoW S cell p κ - 65536 * (rhL S cell false p κ + 128)

/-- The key at χ = 1. -/
def key1 (S : Sh) (cell : NameA → E) (p : Pc) (κ : ℕ) : E :=
  2 * denW S cell p κ - 1 - (2 * accW S cell p κ + denW S cell p κ - 2 * zoW S cell p κ) -
    65536 * (rhL S cell true p κ + 128)

/-- The piece's key at a place of the lower half. -/
theorem wl_low (S : Sh) (cell : NameA → E) (sh b' : ℕ) (hsz : S.dh * S.T * S.G = 2 ^ b') (p : Pc)
    (hp : p.seg = Seg.wl) (κ : ℕ) (hκ : κ < 2 ^ b') : pcKey S cell sh p κ = key0 S cell p κ := by
  unfold pcKey
  rw [hp]
  have h0 : κ / (S.dh * S.T * S.G) = 0 := by rw [hsz]; exact Nat.div_eq_of_lt hκ
  simp only [segKey, h0, if_true, key0, accW, denW, zoW, rhL, hdW, Bool.false_eq_true, if_false]

/-- The piece's key at a place of the upper half. -/
theorem wl_high (S : Sh) (cell : NameA → E) (sh b' : ℕ) (hsz : S.dh * S.T * S.G = 2 ^ b') (p : Pc)
    (hp : p.seg = Seg.wl) (κ : ℕ) (hκ : κ < 2 ^ b') :
    pcKey S cell sh p (2 ^ b' + κ) = key1 S cell p κ := by
  have hpos : 0 < S.dh * S.T * S.G := by rw [hsz]; exact Nat.pos_of_ne_zero (by positivity)
  have hdT : 0 < S.dh * S.T := Nat.pos_of_mul_pos_right hpos |> fun _ =>
    Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hpos; exact absurd hpos (by omega)
  have hd : 0 < S.dh := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.zero_mul] at hdT; exact absurd hdT (by omega)
  have e1 : (2 ^ b' + κ) / (S.dh * S.T * S.G) = 1 := by
    rw [hsz, Nat.add_div_left _ (by rw [← hsz]; exact hpos), Nat.div_eq_of_lt hκ]
  have e2 : (2 ^ b' + κ) % S.dh = κ % S.dh := by
    rw [← hsz, Nat.mul_assoc, Nat.mul_add_mod]
  have e3 : (2 ^ b' + κ) / S.dh % S.T = κ / S.dh % S.T := by
    rw [← hsz, Nat.mul_assoc, Nat.mul_add_div hd, Nat.mul_add_mod]
  have e4 : (2 ^ b' + κ) / (S.dh * S.T) % S.G = κ / (S.dh * S.T) % S.G := by
    rw [← hsz, Nat.mul_add_div hdT, Nat.add_mod_left]
  unfold pcKey
  rw [hp]
  simp only [segKey, e1, e2, e3, e4, one_ne_zero, if_false, key1, accW, denW, zoW, rhL, hdW,
    if_true]

/-! ## Segment wl -/

/-- The rule value of a scalar of segment wl: at the inner point without its first coordinate. -/
def ruleW (n b' : ℕ) (ps : List Pc) (pt : ℕ → E) (F : Pc → ℕ → E) : E :=
  ((ofSeg ps .wl).map fun p => wpAt n p.off p.b pt *
    Blocks.ext b' (F p) (fun t => innAt n p.b pt (1 + t))).sum

/-- The term of segment wl in a key form (keyWL), in its five scalars and zsl. -/
def kfWL (zsl ac zo zc rh' rhp' lw : E) : E :=
  (1 - zsl) * ((2 * ac + zc - 2 * zo) - 65536 * (rh' + 128 * lw)) +
    zsl * (2 * zc - lw - (2 * ac + zc - 2 * zo) - 65536 * (rhp' + 128 * lw))

/-- **Segment wl.** -/
theorem unit_WL (S : Sh) (cell : NameA → E) (sh n b' : ℕ) (ps : List Pc) (pt : ℕ → E)
    (hsz : S.dh * S.T * S.G = 2 ^ b') (hb : ∀ p ∈ ofSeg ps .wl, p.b = 1 + b') :
    ((ofSeg ps .wl).map fun p => wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt)).sum =
    kfWL (pt (n - (1 + b'))) (ruleW n b' ps pt (accW S cell)) (ruleW n b' ps pt (zoW S cell))
      (ruleW n b' ps pt (denW S cell)) (ruleW n b' ps pt (rhL S cell false))
      (ruleW n b' ps pt (rhL S cell true)) (lwAt n ps pt .wl) := by
  have h1 : ∀ p ∈ ofSeg ps .wl, wpAt n p.off p.b pt *
      Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt) =
      (1 - pt (n - (1 + b'))) * (wpAt n p.off p.b pt *
        Blocks.ext b' (key0 S cell p) (fun t => innAt n p.b pt (1 + t))) +
      pt (n - (1 + b')) * (wpAt n p.off p.b pt *
        Blocks.ext b' (key1 S cell p) (fun t => innAt n p.b pt (1 + t))) := by
    intro p hp
    have hz : innAt n p.b pt 0 = pt (n - (1 + b')) := by
      unfold innAt
      rw [hb p hp, Nat.add_zero]
    have e : Blocks.ext p.b (pcKey S cell sh p) (innAt n p.b pt) =
        Blocks.ext (1 + b') (pcKey S cell sh p) (innAt n p.b pt) := by rw [hb p hp]
    rw [e, ext_top, hz,
      Blocks.ext_congr (fun κ hκ => wl_low S cell sh b' hsz p (seg_of_mem hp) κ hκ),
      Blocks.ext_congr (fun κ hκ => wl_high S cell sh b' hsz p (seg_of_mem hp) κ hκ)]
    ring
  have h2 : ∀ (l : List Pc) (a c : E) (F G : Pc → E),
      (l.map fun p => a * F p + c * G p).sum = a * (l.map F).sum + c * (l.map G).sum := by
    intro l a c F G
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  rw [List.map_congr_left h1, h2,
    unit_lin (ofSeg ps .wl) (fun p => wpAt n p.off p.b pt) (fun _ => b')
      (fun p t => innAt n p.b pt (1 + t)) (key0 S cell) (-(65536 * 128))
      [(2, accW S cell), (1, denW S cell), (-2, zoW S cell), (-65536, rhL S cell false)]
      (fun p _ κ => by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, key0]
        ring),
    unit_lin (ofSeg ps .wl) (fun p => wpAt n p.off p.b pt) (fun _ => b')
      (fun p t => innAt n p.b pt (1 + t)) (key1 S cell) (-1 - 65536 * 128)
      [(1, denW S cell), (-2, accW S cell), (2, zoW S cell), (-65536, rhL S cell true)]
      (fun p _ κ => by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, key1]
        ring)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold kfWL ruleW lwAt
  ring

/-- **The identity at a call of kind R16 that holds wl and ix.** -/
theorem alg_R16 (S : Sh) (h : Forest.Shape) (cell : NameA → E) (q n b' : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c) (ok : PcsOK n c.pcs.toList) (pt : ℕ → E)
    (hseg : ∀ p ∈ c.pcs.toList, p.seg = Seg.wl ∨ p.seg = Seg.ix)
    (hpad : (tauN h q (t0N h q) : E) = 0) (hsz : S.dh * S.T * S.G = 2 ^ b')
    (hb : ∀ p ∈ ofSeg c.pcs.toList .wl, p.b = 1 + b') (ac zo zc rh' rhp' : E) (ibs : ℕ → E)
    (rAC : ac = ruleW n b' c.pcs.toList pt (accW S cell))
    (rZO : zo = ruleW n b' c.pcs.toList pt (zoW S cell))
    (rZC : zc = ruleW n b' c.pcs.toList pt (denW S cell))
    (rRH : rh' = ruleW n b' c.pcs.toList pt (rhL S cell false))
    (rRHP : rhp' = ruleW n b' c.pcs.toList pt (rhL S cell true))
    (rIB : ∀ k, ibs k = ruleAt n c.pcs.toList pt .ix (ibX S cell k)) :
    kfWL (pt (n - (1 + b'))) ac zo zc rh' rhp' (lwAt n c.pcs.toList pt .wl) +
      kfIX S.cf.lt (ruleAt n c.pcs.toList pt .ix fun _ κ => ((κ % S.T : ℕ) : E)) ibs =
    Blocks.ext n (kvA S h cell q) pt := by
  have hib : ibs = fun k => ruleAt n c.pcs.toList pt .ix (ibX S cell k) := funext rIB
  rw [alg_pieces S h cell q n c hc ok pt, hpad, zero_mul, add_zero,
    sum_two (fun p : Pc => p.seg == Seg.wl) (fun p => p.seg == Seg.ix)]
  · rw [rAC, rZO, rZC, rRH, rRHP, hib]
    exact congrArg₂ (· + ·) (unit_WL S cell c.sh n b' _ pt hsz hb).symm
      (unit_IX S cell c.sh n _ pt).symm
  · intro p hp
    rcases hseg p hp with h1 | h1 <;> rw [h1]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.unit_WL
#print axioms OnBytes.Ends.A.alg_R16
