-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/AgainMeans.lean: THEOREMS: WHAT A YES GIVES, for 22 of the 23 tests of
Johnson/Desc/First/TailClaims/Again.lean (the tests that the smallness test's two self tests call):
for each test x a theorem `x_iff : x … = true ↔ …`, whose right side is a proposition: ∧ for &&,
= for ==, ≤ and < for decide, ∀ for all, allBelow, allFrom and EqRun.all. (Not everywhere in plain
terms: readShapeHeld_iff keeps a Boolean filter, wants_iff an "if … != 0" in a value,
tieWeightsHeld_iff and readWeightsHeld_iff name the second computation's functions.) No block
imports this file. The 23rd, noneZero, is another file's. THEY ARE UNFOLDINGS OF THE TESTS' TEXT:
tools: they price no sent value and bound no chance.

How to read them. Each right side follows its test clause by clause, with the test's own `let`s.
Three propositions have names: `PieceFits n p` (pieceHeld), `Meets w x` (meets), and `eqAt z first
i`: the value of `verify-on-bytes`'s running product (EqRun) i indices behind `first`: by its text's
comment eq(z, first + i); NO THEOREM SAYS SO HERE OR IN THE LIBRARY: so where a test walks with
EqRun.all, its proposition speaks of `eqAt`, not of `eqPlainF`.

THEY ADD NO SECOND, INDEPENDENT EYE: a right side is its test read aloud. What they give: a law can
take a yes apart without unfolding Booleans; and a reader sees what is compared with what.

WHAT EACH TEST READS. plan: numbers of the plan and of the shapes made of it (tau, mz, lidb, NM,
mats, off, shp, gtTree, ix, tieObj, the calls z1 | z2 with their pieces, f9, the tables' sizes,
planClaimsF). drawn: challenges: the batching element F.theta, the drawn matrix cfF, the lookup's
points g.zx | zy | zb0 | zb1; and, inside bitFactor9, three more: the leaves' eps, the lookup's
alpha and its shift. own: what the verifier's own text has computed of drawn and plan values: g.e,
g.zk, rowX, loX, gamX, gamV, bitFactor9, nX4Laid, kappa, and THE LEDGER'S SUMS: the rows' weights
coef and L (L4, L5 are two such). sent: a value that a prover sent, read BY THE TEST's OWN BODY.
statement: a value of the request.
  test                plan   drawn            own                                  sent
  allFrom allBelow    -      -                -  (they read the test handed in)    PER CALLER (1)
  EqRun.allLoop all   -      the point z      -                                    -
  leE                 -      -                two elements (used to sort weights)  -
  neighboursDiffer    -      -                a list of weights                    -
  isPow2 meets        yes    -                -                                    -
  noneMeet wants      yes    -                -                                    -
  pieceHeld           yes    -                -                                    -
  forestHeld          yes    sizes of zy, zx  the size of e                        -
  callHeld            yes    -                the size of zk[q]                    -
  piecesTile          yes    -                ZZ's name, sizes; sizes of coef, L    -
  pointsHeld          yes    zy, zx           e, zk                                -
  pieceWeightsHeld    yes    zy[0]            kappa, zk, ZZ's coef and L            -
  tieShapeHeld        yes    -                sizes of rowX loX gamX gamV coef L   -
  tieWeightsHeld      yes    theta, cfF       loX gamX gamV, the tie's coef L, L5   -
  planesShapeHeld     yes    sizes of zb0 zb1 BZ's sizes; sizes of coef, L         -
  planesWeightsHeld   yes    theta, zb0, zb1  bitFactor9, BZ's coef and L          -
  readShapeHeld       yes    -                the size of L4; nX4Laid              -
  readWeightsHeld     yes    theta            L4; THE TABLES' WEIGHTS phi          - (2)
(1) AT selfUnits (SelfTests.lean) the test that allBelow is handed reads THE WHOLE WEIGHT OF AN
ENTRY OF U3, which at a layers' segment has scalars that a prover sent as factors of its lower terms
(the selector's shown values: OnBytes/Model/Tail.lean:1113-1120): a test on sent data at one remove.
(2) STATEMENT: at the head's segment three tables' weights read the request's covered positions.
SO ALL 22 READ NO VALUE THAT A PROVER SENT BY THEIR OWN BODIES, AS `verify-on-bytes` FILLS tl, F, g.
How that is known: BY READING, NO THEOREM: the arguments' types; the program's comments on the
fields (OnBytes/Model/Tail.lean:204-301, Look.lean:137-178); how `Forest.pad` fills zx, zy,
zb0, zb1 (points that its rounds return), e and zk (computed of zy, zx) (Look.lean:369-421); and for
the tables' weights `phi` (Look.lean:66-72), which readWeightsHeld reads through readWeightsAgain:
TRACED TO THEIR MAKERS IN TWO READINGS MADE APART: a table is made at three places and no
fourth (AttentionTables.placeAll, Layer.funsOf, HeadTables.tablesOf): every phi is made of drawn
points, challenges of rounds, plan numbers and, at the head, the request. readShapeHeld reads phi's
size alone. THE TYPES LET MORE IN: a Heard is a plain record that any code can build
(Look.lean:132-136): NO THEOREM TIES THE FILL; how the description's own texts fill phi and coef is
not read. planesWeightsHeld DOES NOT TEST bitFactor9: it stands in the adding and in the second
computation alike: any value passes.

Limits. Equivalences on what texts return. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.TailClaims.Again

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-! ## 0 The small ones -/

theorem isZeroE_iff (a : E) : isZeroE a = true ↔ a = zeroE :=
  ⟨fun h => by
    simp only [isZeroE, Bool.and_eq_true, beq_iff_eq] at h
    exact E.ext3 h.1.1 h.1.2 h.2, fun h => by subst h; rfl⟩

theorem notZeroE_iff (a : E) : (!isZeroE a) = true ↔ a ≠ zeroE := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, isZeroE_iff]

theorem allFrom_iff (p : Nat → Bool) : ∀ (count i : Nat),
    allFrom p count i = true ↔ ∀ j, i ≤ j → j < i + count → p j = true
  | 0, i => by
    simp only [allFrom, true_iff]
    intro j h1 h2
    omega
  | count + 1, i => by
    rw [allFrom, Bool.and_eq_true, allFrom_iff p count (i + 1)]
    constructor
    · rintro ⟨h0, h⟩ j h1 h2
      by_cases e : j = i
      · rw [e]; exact h0
      · exact h j (by omega) (by omega)
    · intro h
      exact ⟨h i (Nat.le_refl i) (by omega), fun j h1 h2 => h j (by omega) (by omega)⟩

theorem allBelow_iff (n : Nat) (p : Nat → Bool) : allBelow n p = true ↔ ∀ j < n, p j = true := by
  rw [allBelow, allFrom_iff]
  exact ⟨fun h j hj => h j (Nat.zero_le j) (by omega), fun h j _ hj => h j (by omega)⟩

theorem allFrom_upto_iff (p : Nat → Bool) (m i : Nat) :
    allFrom p (m - i) i = true ↔ ∀ j, i ≤ j → j < m → p j = true := by
  rw [allFrom_iff]
  exact ⟨fun h j h1 h2 => h j h1 (by omega), fun h j h1 h2 => h j h1 (by omega)⟩

theorem allFrom_zero_iff (p : Nat → Bool) (n : Nat) :
    allFrom p n 0 = true ↔ ∀ j < n, p j = true := allBelow_iff n p

theorem bnot_iff (b : Bool) : (!b) = true ↔ ¬ b = true := by
  cases b <;> simp

/-- The run i indices further on. -/
def stepsOn (r : EqRun) : Nat → EqRun
  | 0 => r
  | i + 1 => stepsOn r.next i

theorem EqRun.allLoop_iff (test : Nat → E → Bool) : ∀ (count done : Nat) (r : EqRun),
    EqRun.allLoop test count done r = true ↔
      ∀ i < count, test (done + i) (stepsOn r i).value = true
  | 0, _, _ => by
    simp only [EqRun.allLoop, true_iff]
    intro i h
    omega
  | count + 1, done, r => by
    rw [EqRun.allLoop, Bool.and_eq_true, EqRun.allLoop_iff test count (done + 1) r.next]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i =>
        have := h i (by omega)
        rwa [show done + 1 + i = done + (i + 1) by omega] at this
    · intro h
      refine ⟨h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rwa [show done + (i + 1) = done + 1 + i by omega] at this

/-- The value that the run from `first` has i indices further on: by `EqRun`'s own comment
eq(z, first + i); no theorem says so. -/
def eqAt (z : Array E) (first i : Nat) : E := (stepsOn (EqRun.start z first) i).value

theorem EqRun.all_iff (z : Array E) (first count : Nat) (test : Nat → E → Bool) :
    EqRun.all z first count test = true ↔ ∀ i < count, test i (eqAt z first i) = true := by
  rw [EqRun.all, EqRun.allLoop_iff]
  simp only [Nat.zero_add, eqAt]

theorem leE_iff (a b : E) :
    leE a b = true ↔
      a.c0 < b.c0 ∨ (a.c0 = b.c0 ∧ (a.c1 < b.c1 ∨ (a.c1 = b.c1 ∧ a.c2 ≤ b.c2))) := by
  simp only [leE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

theorem neighboursDiffer_iff : ∀ l : List E,
    neighboursDiffer l = true ↔ ∀ i a b, l[i]? = some a → l[i + 1]? = some b → a ≠ b
  | [] => by simp [neighboursDiffer]
  | [a] => by simp [neighboursDiffer]
  | a :: b :: t => by
    rw [neighboursDiffer, Bool.and_eq_true, bne_iff_ne, neighboursDiffer_iff (b :: t)]
    constructor
    · rintro ⟨h0, h⟩ i x y hx hy
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hy
        rw [← hx, ← hy]; exact h0
      | succ i => exact h i x y (by simpa using hx) (by simpa using hy)
    · intro h
      exact ⟨h 0 a b rfl rfl,
        fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy)⟩

/-! ## 1 The eight that read weights, points and their shapes -/

theorem pointsHeld_iff (tl : HTailF2) (g : Forest.Heard) :
    pointsHeld tl g = true ↔
      ∀ q ∈ [0, 1],
        g.e.getD q zeroE = callWeightAgain g q ∧
        ∀ i < tl.z1.call.n,
          (g.zk.getD q #[]).getD i zeroE =
            (if i < tl.z1.call.n - min tl.z1.call.n tl.lidb then g.zy.getD (1 + i) zeroE
             else g.zx.getD (i - (tl.z1.call.n - min tl.z1.call.n tl.lidb)) zeroE) := by
  simp only [pointsHeld, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_range]

theorem pieceWeightsHeld_iff (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) :
    pieceWeightsHeld tl F g kappa w = true ↔
      let p := (tl.zOf w.call).pieces.getD w.i {}
      let row := (F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}
      let cv := row.coef
      let L := row.L
      let zk := g.zk.getD w.call #[]
      let ka := mulE kappa (callWeightAgain g w.call)
      let mk := subE zeroE ka
      let cv0 := cv.getD w.r0 zeroE
      let L0 := L.getD w.c0 zeroE
      ka ≠ zeroE ∧ cv0 ≠ zeroE ∧ L0 ≠ zeroE ∧
        (∀ cc < w.Cp, mulE mk (eqAt zk p.off cc) ≠ zeroE ∧
          mulE cv0 (L.getD (w.c0 + cc) zeroE) = mulE mk (eqAt zk p.off cc)) ∧
        (∀ r < w.Rp, mulE mk (eqPlainF zk (p.off + r * p.CP)) ≠ zeroE ∧
          mulE (cv.getD (w.r0 + r) zeroE) L0 = mulE mk (eqPlainF zk (p.off + r * p.CP))) ∧
        mulE (cv.getD (w.r0 + w.Rp - 1) zeroE) (L.getD (w.c0 + w.Cp - 1) zeroE) =
          mulE mk (eqPlainF zk (p.off + (w.Rp - 1) * p.CP + (w.Cp - 1))) ∧
        (∀ r < w.r0, cv.getD r zeroE = zeroE) ∧
        (∀ r, w.r0 + w.Rp ≤ r → r < cv.size → cv.getD r zeroE = zeroE) ∧
        (∀ cc < w.c0, L.getD cc zeroE = zeroE) ∧
        ∀ cc, w.c0 + w.Cp ≤ cc → cc < L.size → L.getD cc zeroE = zeroE := by
  simp only [pieceWeightsHeld, Bool.and_eq_true, notZeroE_iff, isZeroE_iff, beq_iff_eq,
    EqRun.all_iff, List.all_eq_true, List.mem_range, allFrom_zero_iff, allFrom_upto_iff, and_assoc]

theorem tieShapeHeld_iff (tl : HTailF2) (F : Fork) (mu : Nat) :
    tieShapeHeld tl F mu = true ↔
      let s := tl.shp.getD mu {}
      let X := F.trees.getD (tl.gtTree.getD mu 0) {}
      let row := X.rows.getD 0 {}
      let mS2 := ((tl.mats.getD mu {}).m + 2) / 3
      X.kind = .symbols ∧ X.rows.size = 1 ∧ X.R = s.Rr ∧ X.K = s.Kc ∧
        mu < tl.tieObj.size ∧ mS2 = s.mS ∧ s.J = 1 ∧ s.R = mS2 ∧ s.Rr = mS2 ∧
        s.Rd = 0 ∧ s.k = (tl.mats.getD mu {}).k ∧ s.K1 = s.k ∧ s.Kc = s.k ∧
        (tl.rowX.getD mu #[]).size = mS2 ∧ (tl.loX.getD mu #[]).size = 1 ∧
        tl.tieObj.getD mu 0 < F.planClaimsF ∧ row.coef.size = s.Rr ∧ row.L.size = s.k ∧
        (tl.gamX.getD mu #[]).size = s.k ∧ (tl.gamV.getD mu #[]).size = s.k := by
  simp only [tieShapeHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem tieWeightsHeld_iff (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) :
    tieWeightsHeld tl F L5 mu = true ↔
      let s := tl.shp.getD mu {}
      let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
      let np2 := pow2Again tl.tau
      let ka := powE F.theta (F.planClaimsF + tl.firstAgain mu)
      let hi := powersAgain F.theta np2 s.mS
      let c0 := tl.off.getD mu 0
      let c1 := tl.mz + c0
      let before := (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0
      let xi2 := (Array.range tl.tau).map fun u => powE F.theta u
      (tl.loX.getD mu #[]).getD 0 zeroE = oneE ∧
        (∀ R < s.R, row.coef.getD R zeroE = hi.getD R zeroE ∧ row.coef.getD R zeroE ≠ zeroE) ∧
        (∀ i a b, (row.coef.toList.mergeSort leE)[i]? = some a →
          (row.coef.toList.mergeSort leE)[i + 1]? = some b → a ≠ b) ∧
        s.m ≤ 3 * s.mS ∧
        (∀ R < s.mS, ∀ i, 3 * R ≤ i → i < 3 * R + min 3 (s.m - 3 * R) →
          let x := mulE ka (hi.getD R zeroE)
          let xB := scaleE (fOfNat radb) x
          let xBB := scaleE (fOfNat radb) xB
          let v := if i % 3 = 0 then x else if i % 3 = 1 then xB else xBB
          v ≠ zeroE ∧ L5.getD (c0 + i) zeroE = v ∧
            L5.getD (c1 + i) zeroE = scaleNat v (2 ^ t2D0)) ∧
        ∀ c < s.k,
          let gam := sumAgain tl.cfF ((before + c) * tl.tau) xi2 tl.tau 0 zeroE
          (tl.gamX.getD mu #[]).getD c zeroE = gam ∧ (tl.gamV.getD mu #[]).getD c zeroE = gam ∧
            row.L.getD c zeroE = mulE (subE zeroE ka) gam := by
  simp only [tieWeightsHeld, Bool.and_eq_true, notZeroE_iff, beq_iff_eq, decide_eq_true_eq,
    allBelow_iff, allFrom_iff, neighboursDiffer_iff, and_assoc]

theorem planesShapeHeld_iff (tl : HTailF2) (F : Fork) (g : Forest.Heard) :
    planesShapeHeld tl F g = true ↔
      let B := F.trees.getD tl.ix.BZ {}
      let lKB := tl.f9.kT + tl.f9.cK
      B.rows.size = 3 ∧ B.R = 32 ∧ B.K = tl.bzColumns ∧ tl.f9.NC = 2 ∧ tl.f9.cK = 1 ∧
        B.K = 2 ^ lKB ∧
        (∀ r < 3, (B.rows.getD r {}).coef.size = 32 ∧ (B.rows.getD r {}).L.size = B.K) ∧
        g.zb0.size = 5 + lKB ∧ g.zb1.size = 5 + lKB := by
  simp only [planesShapeHeld, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc]

theorem planesWeightsHeld_iff (tl : HTailF2) (F : Fork) (g : Forest.Heard) (jo : Nat) :
    planesWeightsHeld tl F g jo = true ↔
      let B := F.trees.getD tl.ix.BZ {}
      let kp := t2fKappaByText F.theta (jo + 3)
      (∀ x ∈ (B.rows.getD 2 {}).coef, x = oneE) ∧
        (∀ e ∈ [0, 1],
          (∀ r < 32, (B.rows.getD e {}).coef.getD r zeroE = eqPlainF ((g.zb e).extract 0 5) r) ∧
          ∀ x < B.K, (B.rows.getD e {}).L.getD x zeroE =
            mulE (mulE (t2fKappaByText F.theta (jo + 1 + e))
              (if e = 0 then tl.bitFactor9 else subE zeroE oneE))
              (eqAt ((g.zb e).extract 5 (g.zb e).size) 0 x)) ∧
        ∀ x < B.K, (B.rows.getD 2 {}).L.getD x zeroE = scaleNat kp (2 ^ (x % 32)) := by
  simp only [planesWeightsHeld, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem, EqRun.all_iff, allBelow_iff, and_assoc]

theorem readShapeHeld_iff (tl : HTailF2) (L4 : Array E) :
    readShapeHeld tl L4 = true ↔
      let read := tl.funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)
      L4.size = 2 * tl.mz ∧
        (∀ Fn ∈ read, (tl.mats.getD Fn.mat {}).m ≠ 0 ∧ Fn.len ≠ 0 ∧
          (tl.mats.getD Fn.mat {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len) ∧
        read.foldl (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 = tl.nX4Laid ∧
        (List.range tl.NM).foldl (fun n mu => n + (tl.mats.getD mu {}).m) 0 = tl.mz := by
  simp only [readShapeHeld, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    Array.all_eq_true_iff_forall_mem, and_assoc]

theorem readWeightsHeld_iff (tl : HTailF2) (F : Fork) (L4 : Array E) :
    readWeightsHeld tl F L4 = true ↔
      ∀ x < 2 * tl.mz, L4.getD x zeroE = (tl.readWeightsAgain F).getD x zeroE := by
  simp only [readWeightsHeld, allBelow_iff, beq_iff_eq]

/-! ## 2 The pieces of the two calls, and the lookup's public numbers -/

theorem isPow2_iff (x : Nat) : isPow2 x = true ↔ ∃ k, x = 2 ^ k := by
  simp only [isPow2, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨Nat.log2 x, h.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Nat.ne_of_gt (Nat.two_pow_pos k), by rw [Nat.log2_two_pow]⟩

theorem wants_iff (tl : HTailF2) (x : Nat × List Want) :
    wants tl = some x ↔
      let rows1 := 2 ^ Nat.log2 tl.tau
      let rows2 := tl.tau - rows1
      let nbW := if rows2 != 0 then 2 else 1
      (rows2 = 0 ∨ ∃ k, rows2 = 2 ^ k) ∧
        x = (nbW, [0, 1].flatMap fun q =>
          { call := q, i := 0, row := q * nbW, r0 := 0, Rp := rows1, c0 := q * tl.mz,
            Cp := tl.mz } ::
            (if rows2 != 0 then
              [{ call := q, i := 1, row := q * nbW + 1, r0 := rows1, Rp := rows2, c0 := q * tl.mz,
                 Cp := tl.mz }]
            else [])) := by
  have key : ((tl.tau - 2 ^ Nat.log2 tl.tau != 0 &&
      !isPow2 (tl.tau - 2 ^ Nat.log2 tl.tau)) = true) ↔
      ¬ (tl.tau - 2 ^ Nat.log2 tl.tau = 0 ∨ ∃ k, tl.tau - 2 ^ Nat.log2 tl.tau = 2 ^ k) := by
    rw [Bool.and_eq_true, bne_iff_ne, bnot_iff, isPow2_iff, not_or]
  simp only [wants]
  split
  · next h => exact ⟨fun e => (by cases e), fun e => absurd e.1 (key.1 h)⟩
  · next h =>
    exact ⟨fun e => ⟨Classical.not_not.1 ((not_congr key).1 h), (Option.some.inj e).symm⟩,
      fun e => by rw [e.2]⟩

theorem forestHeld_iff (tl : HTailF2) (g : Forest.Heard) :
    forestHeld tl g = true ↔
      let h := tl.f9
      let n9 := tl.z1.call.n
      let dW := min n9 tl.lidb
      let io := n9 - dW
      tl.z2.call.n = n9 ∧ h.dT = dW ∧ h.kT = 10 ∧ h.NT = 2 ^ (io + 1) ∧ h.rK = io + 1 ∧
        h.iota = #[io, io] ∧ h.first = #[0, 2 ^ io] ∧ g.zy.size = io + 1 ∧ g.zx.size = dW ∧
        g.e.size = 2 := by
  simp only [forestHeld, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- One piece of a call with 2^n keys is well placed. -/
def PieceFits (n : Nat) (p : Piece) : Prop :=
  p.Rp ≠ 0 ∧ p.Cp ≠ 0 ∧ p.a ≤ 40 ∧ 2 ^ p.a = p.Rp ∧ p.r0 % p.Rp = 0 ∧ p.Cp ≤ p.CP ∧
    (∃ k, p.CP = 2 ^ k) ∧ p.b = p.a + clog2 p.CP ∧ p.b ≤ n ∧ p.off % 2 ^ p.b = 0 ∧
    p.off + 2 ^ p.b ≤ 2 ^ n

theorem pieceHeld_iff (n : Nat) (p : Piece) : pieceHeld n p = true ↔ PieceFits n p := by
  simp only [pieceHeld, PieceFits, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq,
    isPow2_iff, and_assoc]

theorem callHeld_iff (tl : HTailF2) (g : Forest.Heard) (nbW q : Nat) :
    callHeld tl g nbW q = true ↔
      let c := tl.zOf q
      let n := c.call.n
      let keys := c.pieces.foldl (fun s p => s + 2 ^ p.b) 0
      let a := c.pieces.getD 0 {}
      let b := c.pieces.getD 1 {}
      c.call.name = (if q = 0 then "R10z" else "R8d") ∧ c.call.fn = 0 ∧
        c.call.k = (if q = 0 then 10 else 8) ∧ c.call.kappa = 5 ∧ c.call.t0 = 0 ∧
        c.pieces.size = nbW ∧ 10 ≤ n ∧ n ≤ 44 ∧ (g.zk.getD q #[]).size = n ∧
        (∀ p ∈ c.pieces, PieceFits n p) ∧
        (nbW ≠ 2 ∨ ¬ (a.off < b.off + 2 ^ b.b ∧ b.off < a.off + 2 ^ a.b)) ∧
        n = max 10 (clog2 keys) ∧ c.call.iota = n - tl.lidb := by
  simp only [callHeld, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, bnot_iff,
    decide_eq_true_eq, Array.all_eq_true_iff_forall_mem, pieceHeld_iff, and_assoc]

/-- The rectangles of two expected pieces overlap. -/
def Meets (w x : Want) : Prop :=
  w.r0 < x.r0 + x.Rp ∧ x.r0 < w.r0 + w.Rp ∧ w.c0 < x.c0 + x.Cp ∧ x.c0 < w.c0 + w.Cp

theorem meets_iff (w x : Want) : meets w x = true ↔ Meets w x := by
  simp only [meets, Meets, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem noneMeet_iff : ∀ W : List Want,
    noneMeet W = true ↔ W.Pairwise fun w x => ¬ Meets w x
  | [] => by simp [noneMeet]
  | w :: t => by
    rw [noneMeet, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, noneMeet_iff t]
    simp only [bnot_iff, meets_iff]

theorem piecesTile_iff (tl : HTailF2) (F : Fork) (W : List Want) :
    piecesTile tl F W = true ↔
      let T := F.trees.getD tl.ix.ZZ {}
      T.name = "ZZ" ∧ T.R = tl.tau ∧ T.K = 2 * tl.mz ∧ (W.Pairwise fun w x => ¬ Meets w x) ∧
        (W.foldl (fun s w => s + w.Rp * w.Cp) 0) = T.R * T.K ∧
        ∀ w ∈ W,
          let p := (tl.zOf w.call).pieces.getD w.i {}
          let row := T.rows.getD w.row {}
          p.tree = tl.ix.ZZ ∧ p.row = w.row ∧ p.r0 = w.r0 ∧ p.Rp = w.Rp ∧ p.c0 = w.c0 ∧
            p.Cp = w.Cp ∧ w.r0 + w.Rp ≤ T.R ∧ w.c0 + w.Cp ≤ T.K ∧
            row.coef.size = T.R ∧ row.L.size = T.K := by
  simp only [piecesTile, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    noneMeet_iff, and_assoc]

end VerifiableInference.Desc.First.TailClaims

#print axioms VerifiableInference.Desc.First.TailClaims.isZeroE_iff
#print axioms VerifiableInference.Desc.First.TailClaims.notZeroE_iff
#print axioms VerifiableInference.Desc.First.TailClaims.allFrom_iff
#print axioms VerifiableInference.Desc.First.TailClaims.allBelow_iff
#print axioms VerifiableInference.Desc.First.TailClaims.allFrom_upto_iff
#print axioms VerifiableInference.Desc.First.TailClaims.allFrom_zero_iff
#print axioms VerifiableInference.Desc.First.TailClaims.bnot_iff
#print axioms VerifiableInference.Desc.First.TailClaims.EqRun.allLoop_iff
#print axioms VerifiableInference.Desc.First.TailClaims.EqRun.all_iff
#print axioms VerifiableInference.Desc.First.TailClaims.leE_iff
#print axioms VerifiableInference.Desc.First.TailClaims.neighboursDiffer_iff
#print axioms VerifiableInference.Desc.First.TailClaims.pointsHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.pieceWeightsHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.tieShapeHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.tieWeightsHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.planesShapeHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.planesWeightsHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.readShapeHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.readWeightsHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.isPow2_iff
#print axioms VerifiableInference.Desc.First.TailClaims.wants_iff
#print axioms VerifiableInference.Desc.First.TailClaims.forestHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.pieceHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.callHeld_iff
#print axioms VerifiableInference.Desc.First.TailClaims.meets_iff
#print axioms VerifiableInference.Desc.First.TailClaims.noneMeet_iff
#print axioms VerifiableInference.Desc.First.TailClaims.piecesTile_iff
