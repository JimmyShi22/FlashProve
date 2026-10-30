-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1PscOps.lean: the verifier's side of the first toy's private sum-check (Fmt/M1Psc.lean),
written over a structure of field operations on any type; at the format's field it is the functions
of Fmt/M1Psc.lean; and it commutes with every map that respects the operations.

Definitions that compute; theorems; tests (#guard). Core Lean, no Mathlib.

Why: Fmt/M1Psc.lean computes on triples of 64-bit words. A library that has the sum-check as a
protocol with theorems speaks of a field. To hold the one against the other: (1) the functions over
any carrier with operations (here); (2) at the format's operations they are the functions that the
decision runs (here); (3) a map from the words to a field that respects the operations carries the
one to the other (here: the laws "map_.."; that there is such a map is another file's matter); (4)
at a field's own operations they are the library's output (another folder's matter).

Main names:
  `FOps α`: Two products, because the format's code has two (the plain one, `Fld.mulE`, and a faster
    one, `Fld.mulEF`, proved equal in Fmt/FieldEFast.lean: `mulEF_eq`): so that (2) needs no theorem
    on the products. No law is asked.
  `opsOf f`: the format's operations on its cubic extension.
  `constXG`, `at3G`, `stepXG`, `runXG`, `constsXG`, `pscR0G`, `pscRKG`, `pscRG`, `leftOutG`: the
    claims, and the constants got back, round by round, on plain arguments (mu'; the pairs;
    (p_1, p_2); eps; gamma; beta).
  `eqStepG`, `pvG`, `bitsG`: the weights of a point.
  `maskUG`, `onMaskG`: the coefficients on the mask entries that are taken.
  `rowUG`, `rowE1G`, `rowE2G`: the three rows, each as (form on the main table, form on the mask
    row, target).
  `constX_at` .. `rowE2_at`, `pscBlock_at`: (2): each function of Fmt/M1Psc.lean or Fmt/M1Types.lean
    whose generic form is named above is the generic one at `opsOf f`; so are the three rows of
    `pscBlock`. By `rfl`, but for `runX_at` and `constsX_at` (recursion on the lists) and the four
    theorems that use them.
  `FOps.Hom A B φ`: φ respects the operations.
  `map_constX` .. `map_rowE2`: (3): under `FOps.Hom A B φ`, φ (on lists, arrays and rows: entry by
    entry) carries a generic function at A to the same function at B at the arguments under φ;
    `map_onMask` asks the like of its argument g.

Tests: the generic functions at another carrier (the integers modulo 101, as natural numbers), at
made-up values, the rows at one variable: a polynomial of three coefficients; the constant that the
round equation fixes; the weights of a point; the three rows' coefficients on the mask row, and of
row (U) also which entries of its main part are not 0, and its target.

Limits: this file does not say that the format's operations are a field's. It does not say anything
on a protocol. It has no theorem of the kind (3) on `constsXG` or `leftOutG`. This file proves
`FOps.Hom` of no map, so the map of (3) is not in it; no file of Fmt/ or Run/ proves `FOps.Hom` of a
map. No file of Fmt/ or Run/ takes step (4).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1Psc

set_option autoImplicit false

namespace Fmt.M1

/-- Operations of a field on a type; no law is asked -/
structure FOps (α : Type) where
  zero : α
  one  : α
  add  : α → α → α
  sub  : α → α → α
  mul  : α → α → α
  mulF : α → α → α
  neg  : α → α

/-- the format's operations -/
def opsOf (f : Fld) : FOps E := ⟨Fld.zeroE, Fld.oneE, f.addE, f.subE, f.mulE, f.mulEF, f.negE⟩

section
variable {α : Type} (A : FOps α)

def constXG (R zeta : α) (q : α × α) : α := A.sub R (A.mul zeta (A.add q.1 q.2))

def at3G (c0 c1 c2 x : α) : α := A.add c0 (A.add (A.mul c1 x) (A.mul c2 (A.mul x x)))

def stepXG (R zeta : α) (q : α × α) (gamma : α) : α := at3G A (constXG A R zeta q) q.1 q.2 gamma

def runXG : α → List α → List (α × α) → List α → α
  | R, z :: zs, q :: qs, g :: gs => runXG (stepXG A R z q g) zs qs gs
  | R, _, _, _ => R

def constsXG : α → List α → List (α × α) → List α → List α
  | R, z :: zs, q :: qs, g :: gs => constXG A R z q :: constsXG (stepXG A R z q g) zs qs gs
  | _, _, _, _ => []

def pscR0G (T mu eps : α) : α := A.add mu (A.mul eps T)

def pscRKG (T : α) (zeta : List α) (mu : α) (q : List (α × α)) (eps : α) (gamma : List α) : α :=
  runXG A (pscR0G A T mu eps) zeta q gamma

def pscRG (T : α) (zeta : List α) (mu : α) (q : List (α × α)) (p : α × α) (eps : α)
    (gamma : List α) (beta : α) : α :=
  at3G A (pscRKG A T zeta mu q eps gamma) p.1 p.2 beta

def leftOutG (T : α) (zeta : List α) (mu : α) (q : List (α × α)) (eps : α) (gamma : List α) :
    List α :=
  constsXG A (pscR0G A T mu eps) zeta q gamma ++ [pscRKG A T zeta mu q eps gamma]

def eqStepG (T : List α) (z : α) : List α := T.map (A.mulF (A.sub A.one z)) ++ T.map (A.mulF z)

def pvG (s : α) (z : List α) : Array α := (z.foldl (eqStepG A) [s]).toArray

def bitsG (b r : Nat) : List α := (List.range b).map fun t => if r.testBit t then A.one else A.zero

def maskUG (K : Nat) (gamma : List α) (beta : α) (t : Nat) : α :=
  if t < 2 * K then
    (if t % 2 = 0 then gamma.getD (t / 2) A.zero
      else A.mul (gamma.getD (t / 2) A.zero) (gamma.getD (t / 2) A.zero))
  else if t = 2 * K then A.one
  else if t = 2 * K + 1 then beta
  else if t = 2 * K + 2 then A.mul beta beta
  else A.zero

def onMaskG (lzk first : Nat) (g : Nat → α) : Array α :=
  Array.ofFn (n := lzk) fun i => if first ≤ i.val then g (i.val - first) else A.zero

/-- Row (U); R is the claim at the end. -/
def rowUG (K lzk : Nat) (gamma : List α) (beta eps R v1 v2 : α) (first : Nat) :
    Array α × Array α × α :=
  (pvG A (A.neg eps) (bitsG A 2 2 ++ gamma),
    onMaskG A lzk first (maskUG A K gamma beta),
    A.sub R (A.mul eps (A.mul v1 v2)))

/-- Row (E_1). -/
def rowE1G (K lzk : Nat) (gamma : List α) (beta v1 : α) (first : Nat) : Array α × Array α × α :=
  (pvG A A.one (bitsG A 2 0 ++ gamma),
    onMaskG A lzk first (fun t => if t = 2 * K + 3 then beta else A.zero),
    v1)

/-- Row (E_2). -/
def rowE2G (K lzk : Nat) (gamma : List α) (beta v2 : α) (first : Nat) : Array α × Array α × α :=
  (pvG A A.one (bitsG A 2 1 ++ gamma),
    onMaskG A lzk first (fun t => if t = 2 * K + 4 then beta else A.zero),
    v2)

end

/-! ## At the format's operations: the functions of Fmt/M1Psc.lean and Fmt/M1Types.lean -/

theorem constX_at (f : Fld) (R zeta : E) (q : E × E) :
    constX f R zeta q = constXG (opsOf f) R zeta q := rfl
theorem at3_at (f : Fld) (c0 c1 c2 x : E) : at3 f c0 c1 c2 x = at3G (opsOf f) c0 c1 c2 x := rfl
theorem stepX_at (f : Fld) (R zeta : E) (q : E × E) (gamma : E) :
    stepX f R zeta q gamma = stepXG (opsOf f) R zeta q gamma := rfl

theorem runX_at (f : Fld) :
    ∀ (R : E) (zs : List E) (qs : List (E × E)) (gs : List E),
      runX f R zs qs gs = runXG (opsOf f) R zs qs gs
  | R, z :: zs, q :: qs, g :: gs => runX_at f (stepX f R z q g) zs qs gs
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => rfl
  | _, _ :: _, _ :: _, [] => rfl

theorem constsX_at (f : Fld) :
    ∀ (R : E) (zs : List E) (qs : List (E × E)) (gs : List E),
      constsX f R zs qs gs = constsXG (opsOf f) R zs qs gs
  | R, z :: zs, q :: qs, g :: gs => congrArg (constX f R z q :: ·) (constsX_at f (stepX f R z q g) zs qs gs)
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => rfl
  | _, _ :: _, _ :: _, [] => rfl

theorem pscR0_at (f : Fld) (T : E) (m : PscMsg) (d : PscDraw) :
    pscR0 f T m d = pscR0G (opsOf f) T m.mu d.eps := rfl
theorem pscRK_at (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) :
    pscRK f T zeta m d = pscRKG (opsOf f) T zeta m.mu m.q d.eps d.gamma :=
  runX_at f _ _ _ _
theorem pscR_at (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) :
    pscR f T zeta m d = pscRG (opsOf f) T zeta m.mu m.q m.p d.eps d.gamma d.beta :=
  congrArg (fun x => at3 f x m.p.1 m.p.2 d.beta) (pscRK_at f T zeta m d)
theorem leftOut_at (f : Fld) (T : E) (zeta : List E) (m : PscMsg) (d : PscDraw) :
    leftOut f T zeta m d = leftOutG (opsOf f) T zeta m.mu m.q d.eps d.gamma := by
  unfold leftOut leftOutG
  rw [constsX_at, pscRK_at]
  rfl
theorem eqStep_at (f : Fld) (T : List E) (z : E) : eqStep f T z = eqStepG (opsOf f) T z := rfl
theorem pv_at (f : Fld) (s : E) (z : List E) : pv f s z = pvG (opsOf f) s z := rfl
theorem bitsE_at (f : Fld) (b r : Nat) : bitsE b r = bitsG (opsOf f) b r := rfl
theorem maskU_at (f : Fld) (K : Nat) (o : PscOut) (t : Nat) :
    maskU f K o t = maskUG (opsOf f) K o.gamma o.beta t := rfl
theorem onMask_at (f : Fld) (lzk first : Nat) (g : Nat → E) :
    onMask lzk first g = onMaskG (opsOf f) lzk first g := rfl

/-- The three rows, here and in the two theorems below. -/
theorem rowU_at (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat) :
    ((rowU f K lzk o first).c, (rowU f K lzk o first).d, (rowU f K lzk o first).t) =
      rowUG (opsOf f) K lzk o.gamma o.beta o.eps o.R o.v1 o.v2 first := rfl
theorem rowE1_at (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat) :
    ((rowE1 f K lzk o first).c, (rowE1 f K lzk o first).d, (rowE1 f K lzk o first).t) =
      rowE1G (opsOf f) K lzk o.gamma o.beta o.v1 first := rfl
theorem rowE2_at (f : Fld) (K lzk : Nat) (o : PscOut) (first : Nat) :
    ((rowE2 f K lzk o first).c, (rowE2 f K lzk o first).d, (rowE2 f K lzk o first).t) =
      rowE2G (opsOf f) K lzk o.gamma o.beta o.v2 first := rfl

/-- The block that the decision calls. -/
theorem pscBlock_at (f : Fld) (K lzk : Nat) (zeta : List E) (mu : E) (qs : List (E × E))
    (p v : E × E) (eps : E) (gamma : List E) (beta : E) :
    (pscBlock f K lzk zeta mu qs p v eps gamma beta).map (fun r => (r.c, r.d, r.t)) =
      [rowUG (opsOf f) K lzk gamma beta eps
            (pscRG (opsOf f) (opsOf f).zero zeta mu qs p eps gamma beta) v.1 v.2 0,
        rowE1G (opsOf f) K lzk gamma beta v.1 0, rowE2G (opsOf f) K lzk gamma beta v.2 0] := by
  have h := pscR_at f Fld.zeroE zeta ⟨mu, qs, p, v⟩ ⟨eps, gamma, beta⟩
  show [rowUG (opsOf f) K lzk gamma beta eps
          (pscR f Fld.zeroE zeta ⟨mu, qs, p, v⟩ ⟨eps, gamma, beta⟩) v.1 v.2 0,
      rowE1G (opsOf f) K lzk gamma beta v.1 0, rowE2G (opsOf f) K lzk gamma beta v.2 0] = _
  rw [h]
  rfl

/-! ## Maps that respect the operations -/

/-- φ respects the operations -/
structure FOps.Hom {α β : Type} (A : FOps α) (B : FOps β) (φ : α → β) : Prop where
  zero : φ A.zero = B.zero
  one  : φ A.one = B.one
  add  : ∀ x y, φ (A.add x y) = B.add (φ x) (φ y)
  sub  : ∀ x y, φ (A.sub x y) = B.sub (φ x) (φ y)
  mul  : ∀ x y, φ (A.mul x y) = B.mul (φ x) (φ y)
  mulF : ∀ x y, φ (A.mulF x y) = B.mulF (φ x) (φ y)
  neg  : ∀ x, φ (A.neg x) = B.neg (φ x)

section
variable {α β : Type} {A : FOps α} {B : FOps β} {φ : α → β} (h : FOps.Hom A B φ)
include h

/-- Under `h`, φ carries `constXG` at A to `constXG` at B; a pair is mapped entry by entry. -/
theorem map_constX (R zeta : α) (q : α × α) :
    φ (constXG A R zeta q) = constXG B (φ R) (φ zeta) (φ q.1, φ q.2) := by
  unfold constXG
  rw [h.sub, h.mul, h.add]

theorem map_at3 (c0 c1 c2 x : α) : φ (at3G A c0 c1 c2 x) = at3G B (φ c0) (φ c1) (φ c2) (φ x) := by
  unfold at3G
  rw [h.add, h.add, h.mul, h.mul, h.mul]

theorem map_stepX (R zeta : α) (q : α × α) (gamma : α) :
    φ (stepXG A R zeta q gamma) = stepXG B (φ R) (φ zeta) (φ q.1, φ q.2) (φ gamma) := by
  unfold stepXG
  rw [map_at3 h, map_constX h]

theorem map_runX :
    ∀ (R : α) (zs : List α) (qs : List (α × α)) (gs : List α),
      φ (runXG A R zs qs gs) = runXG B (φ R) (zs.map φ) (qs.map fun q => (φ q.1, φ q.2)) (gs.map φ)
  | R, z :: zs, q :: qs, g :: gs => by
      show φ (runXG A (stepXG A R z q g) zs qs gs) =
        runXG B (stepXG B (φ R) (φ z) (φ q.1, φ q.2) (φ g)) (zs.map φ)
          (qs.map fun q => (φ q.1, φ q.2)) (gs.map φ)
      rw [map_runX, map_stepX h]
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => rfl
  | _, _ :: _, _ :: _, [] => rfl

theorem map_pscR0 (T mu eps : α) : φ (pscR0G A T mu eps) = pscR0G B (φ T) (φ mu) (φ eps) := by
  unfold pscR0G
  rw [h.add, h.mul]

theorem map_pscRK (T : α) (zeta : List α) (mu : α) (q : List (α × α)) (eps : α) (gamma : List α) :
    φ (pscRKG A T zeta mu q eps gamma) =
      pscRKG B (φ T) (zeta.map φ) (φ mu) (q.map fun q => (φ q.1, φ q.2)) (φ eps) (gamma.map φ) := by
  unfold pscRKG
  rw [map_runX h, map_pscR0 h]

/-- The claim at the end. -/
theorem map_pscR (T : α) (zeta : List α) (mu : α) (q : List (α × α)) (p : α × α) (eps : α)
    (gamma : List α) (beta : α) :
    φ (pscRG A T zeta mu q p eps gamma beta) =
      pscRG B (φ T) (zeta.map φ) (φ mu) (q.map fun q => (φ q.1, φ q.2)) (φ p.1, φ p.2) (φ eps)
        (gamma.map φ) (φ beta) := by
  unfold pscRG
  rw [map_at3 h, map_pscRK h]

theorem map_eqStep (T : List α) (z : α) : (eqStepG A T z).map φ = eqStepG B (T.map φ) (φ z) := by
  unfold eqStepG
  rw [List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
  congr 1
  · refine List.map_congr_left fun x _ => ?_
    show φ (A.mulF (A.sub A.one z) x) = B.mulF (B.sub B.one (φ z)) (φ x)
    rw [h.mulF, h.sub, h.one]
  · refine List.map_congr_left fun x _ => ?_
    exact h.mulF z x

theorem map_eqFold :
    ∀ (z T : List α), (z.foldl (eqStepG A) T).map φ = (z.map φ).foldl (eqStepG B) (T.map φ)
  | [], _ => rfl
  | a :: z, T => by
      rw [List.foldl_cons, map_eqFold z, map_eqStep h]
      rfl

/-- The weights of a point. -/
theorem map_pv (s : α) (z : List α) : (pvG A s z).map φ = pvG B (φ s) (z.map φ) := by
  unfold pvG
  rw [List.map_toArray, map_eqFold h]
  rfl

theorem map_bits (b r : Nat) : (bitsG A b r).map φ = bitsG B b r := by
  unfold bitsG
  rw [List.map_map]
  refine List.map_congr_left fun t _ => ?_
  show φ (if r.testBit t then A.one else A.zero) = _
  split
  · exact h.one
  · exact h.zero

theorem map_getD (l : List α) (i : Nat) : φ (l.getD i A.zero) = (l.map φ).getD i B.zero := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact h.zero
  | some _ => rfl

theorem map_maskU (K : Nat) (gamma : List α) (beta : α) (t : Nat) :
    φ (maskUG A K gamma beta t) = maskUG B K (gamma.map φ) (φ beta) t := by
  unfold maskUG
  split
  · split
    · exact map_getD h _ _
    · rw [h.mul, map_getD h]
  · split
    · exact h.one
    · split
      · rfl
      · split
        · exact h.mul _ _
        · exact h.zero

theorem map_onMask (lzk first : Nat) (g : Nat → α) (g' : Nat → β) (hg : ∀ t, φ (g t) = g' t) :
    (onMaskG A lzk first g).map φ = onMaskG B lzk first g' := by
  unfold onMaskG
  rw [Array.map_ofFn]
  congr 1
  funext i
  show φ (if first ≤ i.val then g (i.val - first) else A.zero) = _
  split
  · exact hg _
  · exact h.zero

/-- a row, mapped -/
def mapRow (φ : α → β) (r : Array α × Array α × α) : Array β × Array β × β :=
  (r.1.map φ, r.2.1.map φ, φ r.2.2)

/-- The three rows, here and in the two theorems below. -/
theorem map_rowU (K lzk : Nat) (gamma : List α) (beta eps R v1 v2 : α) (first : Nat) :
    mapRow φ (rowUG A K lzk gamma beta eps R v1 v2 first) =
      rowUG B K lzk (gamma.map φ) (φ beta) (φ eps) (φ R) (φ v1) (φ v2) first := by
  unfold mapRow rowUG
  dsimp only
  rw [map_pv h, h.neg, List.map_append, map_bits h,
    map_onMask h lzk first _ _ (map_maskU h K gamma beta), h.sub, h.mul, h.mul]

theorem map_rowE1 (K lzk : Nat) (gamma : List α) (beta v1 : α) (first : Nat) :
    mapRow φ (rowE1G A K lzk gamma beta v1 first) =
      rowE1G B K lzk (gamma.map φ) (φ beta) (φ v1) first := by
  unfold mapRow rowE1G
  dsimp only
  rw [map_pv h, h.one, List.map_append, map_bits h, map_onMask h lzk first _ (fun t => if t = 2 * K + 3 then φ beta else B.zero) (fun t => by
    show φ (if t = 2 * K + 3 then beta else A.zero) = if t = 2 * K + 3 then φ beta else B.zero
    split
    · rfl
    · exact h.zero)]

theorem map_rowE2 (K lzk : Nat) (gamma : List α) (beta v2 : α) (first : Nat) :
    mapRow φ (rowE2G A K lzk gamma beta v2 first) =
      rowE2G B K lzk (gamma.map φ) (φ beta) (φ v2) first := by
  unfold mapRow rowE2G
  dsimp only
  rw [map_pv h, h.one, List.map_append, map_bits h, map_onMask h lzk first _ (fun t => if t = 2 * K + 4 then φ beta else B.zero) (fun t => by
    show φ (if t = 2 * K + 4 then beta else A.zero) = if t = 2 * K + 4 then φ beta else B.zero
    split
    · rfl
    · exact h.zero)]

end

/-! ## Tests at another carrier: the integers modulo 101 -/

namespace OpsT
def m101 : FOps Nat :=
  ⟨0, 1, fun a b => (a + b) % 101, fun a b => (a + 101 - b % 101) % 101, fun a b => a * b % 101,
    fun a b => a * b % 101, fun a => (101 - a % 101) % 101⟩
end OpsT

-- a polynomial of three coefficients; the constant that the round equation fixes:
-- under g ↦ (1 - ζ) g(0) + ζ g(1) the polynomial c0 + q1 X + q2 X² sums to c0 + ζ (q1 + q2)
#guard at3G OpsT.m101 3 5 7 2 == (3 + 10 + 28) % 101
#guard (let R := 40; let z := 9; let q := (5, 7); (constXG OpsT.m101 R z q + z * (q.1 + q.2)) % 101 == R)
-- the weights of a point: 2^n entries that sum to the factor in front
#guard (pvG OpsT.m101 6 [10, 20, 30]).size == 8 && (pvG OpsT.m101 6 [10, 20, 30]).foldl (· + ·) 0 % 101 == 6
-- at a corner of the cube: one entry
#guard pvG OpsT.m101 1 [1, 0] == #[0, 1, 0, 0]
-- row (U)'s main part stands on its own row of a table of four rows; the mask parts; (U)'s target
#guard (let r := rowUG OpsT.m101 1 8 [10] 3 2 50 4 5 0; (List.range 8).all fun j => (r.1.getD j 0 != 0) == (j % 4 == 2))
#guard (rowUG OpsT.m101 1 8 [10] 3 2 50 4 5 0).2.1 == #[10, 100, 1, 3, 9, 0, 0, 0] && (rowUG OpsT.m101 1 8 [10] 3 2 50 4 5 0).2.2 == (50 + 101 - 40) % 101
#guard (rowE1G OpsT.m101 1 8 [10] 3 4 0).2.1 == #[0, 0, 0, 0, 0, 3, 0, 0] && (rowE2G OpsT.m101 1 8 [10] 3 5 0).2.1 == #[0, 0, 0, 0, 0, 0, 3, 0]

end Fmt.M1
