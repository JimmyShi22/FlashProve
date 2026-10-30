-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Bits.lean: the zero point and the test that all entries of the planes are bits.

It imports the library, Close.lean (for `ordC`, `ClPl`) and, under it,
Cb/Pv/Lookup/Blocks/E3Bit.lean (the test with an order of the variables: `ZeroCubeP`, `LkBitP`,
`ldZeroP_link`, `ldLkpBitP_*`), Cb/Pv/Lookup/Know/KnowAt.lean and Cb/Pv/Lookup/Know/LtK.lean. No
file of the port.

The two steps. Below, k := mu + d and q := the number of elements of E; the joints `Closed`, `Zero`
and `Bitten` are those of Letters.lean.
  Zero point. The prover sends nothing; the verifier draws ζ, mu + d elements, in one round. "All
  are bits" becomes: the extension of bit² − bit over all mu + d variables is 0 at ζ. At a corner
  of a dead plane the bit is the constant 0 (Idle.lean), so bit² − bit is 0 there for all entries.
  Test of the bits. A sumcheck on y² − y under the equality weights at ζ, target 0, variables bound
  from the highest down, degree 2 each, one further variable of degree 2, one shown value. It leaves
  two rows: on the hiding polynomial's coefficients; on the bits' extension at the end point.
Dead planes: `LkBitP` is used as it stands, with J := Option A.J and tAt := A.cell (`none` at a
dead plane); the entries are read by `ext0`; both rows are brought back to A.J by `Row.pull some`.

  `A.zeroK Ex`    the draw. Its error as a count: (mu + d) · q^(mu + d − 1) of q^(mu + d).
  `zero_know`     `Know` from `Closed` to `Zero`; no condition. The count is the library's
                  `ok_eqPt`.
  `A.Bt P`        the test's data, a value of `LkBitP`. `A.BT P`: the test's sumcheck.
  `bt_sum`        its sum claim at target 0 and the state (x, x.zt), at `ext0 μ`, is the third
                  clause of `Zero`.
  `A.rowU`, `A.rowV`   the two rows, on A.J. `rows_iff`: the output claim holds of `ext0 μ` exactly
                  if both rows hold of μ.
  `A.bitsK P SK`  the block: into the sumcheck's state, the letter's full sumcheck, back into the
                  flat state with the two rows appended.
  `bits_know`     `Know` from `Zero` to `Bitten`, under one condition on the letter: `SK.FullK` at
                  this sumcheck. `bits_lib`: the library's verifier meets it.
  `zero_errs`, `bits_errs`   errors and numbers of values as lists, by the library's readers (the
                  second at the library's verifier).
  `bt_vars_at`    place i of the list of variables weighs at coordinate k − 1 − i of ζ.
  `zero_pt`       coordinate t of the zero point is the t-th element drawn.
Not shown: an honest side; which of a round's coefficients is sent (that is the letter's).

-/
import Cb.Pv.KeyLookup.Close
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Finset

noncomputable section
namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-! ### the zero point -/

def zeroNx (x : A.XS) (ζ : Fin (A.mu + A.d) → E) : A.XS :=
  { x with zt := fun t => if h : t < A.mu + A.d then ζ ⟨t, h⟩ else 0 }

def zeroK (Ex : ExtSpec) : BkK A.XS A.XS Ex :=
  drawK (Fin (A.mu + A.d) → E) A.zeroNx Ex ((A.mu + A.d) * Fintype.card E ^ (A.mu + A.d - 1))

theorem zero_pt (x : A.XS) (ζ : Fin (A.mu + A.d) → E) (t : Fin (A.mu + A.d)) :
    (A.zeroNx x ζ).zt t = ζ t := dif_pos t.2

/-- bit² − bit, corner by corner. -/
def sq (μ : A.J → E) (c : Fin (A.mu + A.d) → Bool) : E :=
  ext0 μ (A.cell c) * (ext0 μ (A.cell c) - 1)

theorem sq_dead (μ : A.J → E) (c : Fin (A.mu + A.d) → Bool) (h : A.pl ≤ numLE c % 2 ^ A.mu) :
    A.sq μ c = 0 := by
  unfold sq
  rw [(A.cell_none_iff c).2 h, ext0_none, zero_mul]

theorem sq_zero_iff (μ : A.J → E) : A.sq μ = 0 ↔ A.Bts μ :=
  ⟨fun h => (A.bts_iff μ).2 fun c => congrFun h c, fun h => funext fun c => (A.bts_iff μ).1 h c⟩

/-- The third clause of `Zero`, in the reading of Idle.lean. -/
theorem zero_clause (μ : A.J → E) (zt : ℕ → E) :
    mleN (A.mu + A.d) (fun n => A.bitN μ n * (A.bitN μ n - 1)) zt =
      ∑ c, Alg.eqk (fun i : Fin (A.mu + A.d) => zt i) c * A.sq μ c := by
  unfold mleN Alg.mle sq
  refine Finset.sum_congr rfl fun c _ => ?_
  show Alg.eqk _ c * (A.bitN μ (numLE c) * (A.bitN μ (numLE c) - 1)) = _
  rw [A.bitN_cell]

/-- Knowledge soundness (`BkK.Know`): from `Closed` to `Zero`. -/
theorem zero_know (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    (A.zeroK Ex).Know (A.jt R0 msg Mu A.Closed) (A.jt R0 msg Mu A.Zero) := by
  refine knowAt_draw Kc M A.XS A.XS Ex Wp (Fin (A.mu + A.d) → E) A.zeroNx _ _ _
    (fun _ _ _ h => h) ?_
  intro x y m _
  by_cases hB : A.Bts (msg m)
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro β ⟨wp, h1, h2⟩
      exact h2 ⟨h1.1, ⟨⟨hB, h1.2.1.1⟩, h1.2.1.2⟩, h1.2.2.1⟩
  · have hv : A.sq (msg m) ≠ 0 := fun h => hB ((A.sq_zero_iff (msg m)).1 h)
    refine (cnt_mono fun β hβ => ?_).trans
      ((ok_eqPt E (Fin (A.mu + A.d)) (A.sq (msg m)) hv).trans (le_of_eq ?_))
    · obtain ⟨wp, h1, _⟩ := hβ
      have h3 := h1.2.2.2
      rw [A.zero_clause] at h3
      have hp : (fun i : Fin (A.mu + A.d) => (A.zeroNx x β).zt i) = β :=
        funext fun i => A.zero_pt x β i
      rw [hp] at h3
      exact h3
    · show Fintype.card (Fin (A.mu + A.d)) *
        Fintype.card E ^ (Fintype.card (Fin (A.mu + A.d)) - 1) = _
      rw [Fintype.card_fin]

theorem zero_errs (Ex : ExtSpec) :
    (A.zeroK Ex).e.toList = [(A.mu + A.d) * Fintype.card E ^ (A.mu + A.d - 1)] ∧
    (A.zeroK Ex).R.shape.chalList = [Fintype.card E ^ (A.mu + A.d)] := by
  refine ⟨rfl, ?_⟩
  show [Fintype.card (Fin (A.mu + A.d) → E)] = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ### the bits' sumcheck -/

/-- The test's data. -/
def Bt : LkBitP E :=
  { St := A.XS
    J := Option A.J
    k := A.mu + A.d
    tAt := A.cell
    wAt := fun i => some (P.wB i)
    cAt := some P.cB
    sg := ordC (A.mu + A.d) }

/-- the sumcheck -/
abbrev BT : PscOur E := (A.Bt P).zc.next

def bitsIn (x : A.XS) : E × (A.BT P).St := (0, (x, ((), fun i : Fin (A.mu + A.d) => x.zt i)))

/-- The sum claim at the target 0 is the third clause of `Zero`. -/
theorem bt_sum (x : A.XS) (μ : A.J → E) :
    (A.BT P).SumHolds (A.bitsIn P x) (ext0 μ) ↔
      mleN (A.mu + A.d) (fun n => A.bitN μ n * (A.bitN μ n - 1)) x.zt = 0 := by
  have hl := ldZeroP_link E (A.Bt P).zc x ((), fun i : Fin (A.mu + A.d) => x.zt i) (ext0 μ)
  have hr : ∑ i : Unit × (Fin (A.mu + A.d) → Bool),
        (A.Bt P).zc.toIn.ev.ze ((), fun i : Fin (A.mu + A.d) => x.zt i) i *
          (A.Bt P).zc.toIn.val x (ext0 μ) i =
      ∑ c, Alg.eqk (fun i : Fin (A.mu + A.d) => x.zt i) c * A.sq μ c := by
    rw [Fintype.sum_prod_type, Fintype.sum_unique]
    refine Finset.sum_congr rfl fun c _ => ?_
    show (1 * Alg.eqk (fun i : Fin (A.mu + A.d) => x.zt i) c) *
      (A.Bt P).zc.G x (ext0 μ) () (Alg.corner c) = _
    rw [LkBit.G_corner E (A.Bt P) x (ext0 μ) c, one_mul]
    rfl
  rw [A.zero_clause, ← hr]
  exact ⟨fun h => hl.symm.trans h, fun h => hl.trans h⟩

/-- The two rows, on A.J. -/
def rowU (o : (A.BT P).par.Out) : Row E A.J :=
  Row.pull some ⟨(A.BT P).par.slU (fun _ b => b.elim) o, (A.BT P).par.tU o⟩
def rowV (o : (A.BT P).par.Out) : Row E A.J :=
  Row.pull some ⟨(A.BT P).par.slE (A.Bt P).rowA () o, o.vals ()⟩

theorem rows_iff (o : (A.BT P).par.Out) (μ : A.J → E) :
    (A.BT P).par.OutHolds o (ext0 μ) ↔ (A.rowU P o).Holds μ ∧ (A.rowV P o).Holds μ :=
  (ldLkpBitP_rows E (A.Bt P) o (ext0 μ)).trans
    (and_congr
      (row_pull0 ⟨(A.BT P).par.slU (fun _ b => b.elim) o, (A.BT P).par.tU o⟩ μ).symm
      (row_pull0 ⟨(A.BT P).par.slE (A.Bt P).rowA () o, o.vals ()⟩ μ).symm)

def bitsOut (o : (A.BT P).par.Out) : A.XS :=
  let x : A.XS := o.st.1
  { x with rows := x.rows ++ [A.rowU P o, A.rowV P o] }

variable {Ex : ExtSpec}

/-- The block. -/
def bitsK (SK : PscLtK E Ex) : BkK A.XS A.XS Ex :=
  ((SK.full (A.BT P).par).preM (A.bitsIn P)).postM (A.bitsOut P)

/-- Knowledge soundness (`BkK.Know`): from `Zero` to `Bitten`. -/
theorem bits_know (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hL : SK.FullK M Wp Kc (A.BT P).par fun ms => ext0 (msg ms)) :
    (A.bitsK P SK).Know (A.jt R0 msg Mu A.Zero) (A.jt R0 msg Mu A.Bitten) := by
  let A0 : Rels Kc (A.BT P).St Ex (M × Wp) :=
    cj R0 msg (fun s => s.1.st) (fun s μ => A.Bitten s.1 μ ∧ Mu s.1.st μ) fun s μ => A.Bitten s.1 μ
  have g := SK.our_know M Wp Kc (A.BT P) (fun ms => ext0 (msg ms)) hL A0
  refine know_postM (A.bitsOut P) (know_preM (A.bitsIn P) (fun _ _ h => h) ?_ g)
    (fun _ _ h => h) ?_
  · intro x y w _ h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, (A.bt_sum P x _).1 h.2⟩
  · intro o y w _ h
    obtain ⟨hR, ⟨hn, hrows⟩, hc⟩ := h
    exact ⟨⟨hR, ⟨hn, fun r hr => hrows r (List.mem_append_left _ hr)⟩, hc⟩,
      (A.rows_iff P o _).2
        ⟨hrows _ (List.mem_append_right _ (List.mem_cons_self)),
          hrows _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))⟩⟩

/-- At the library's verifier the premise on the letter holds. -/
theorem bits_lib (Kc M Wp : Type) (msg : M → Option A.J → E) :
    (PscLtK.lib E Ex).FullK M Wp Kc (A.BT P).par msg :=
  PscLtK.lib_ourK M Wp Kc (A.BT P) msg (ldZeroP_vars E (A.Bt P).zc).1 (ldLkpBitP_degX E (A.Bt P))
    (ldLkpBitP_degY E (A.Bt P)) (ldZeroP_vars E (A.Bt P).zc).2

/-- At the library's verifier: errors and numbers of values, by the library's own readers. -/
theorem bits_errs :
    (A.bitsK P (PscLtK.lib E Ex)).e.toList = pscErrs (A.mu + A.d) 2 2 ∧
    (A.bitsK P (PscLtK.lib E Ex)).R.shape.chalList = pscVals (Fintype.card E) (A.mu + A.d) :=
  LdLkp.ll_psc (A.BT P) (A.mu + A.d) 2 rfl Ex Unit

/-- Which variable a round binds: place i weighs at coordinate k − 1 − i of the zero point. -/
theorem bt_vars_at (x : A.XS) :
    (A.BT P).vars (A.bitsIn P x).2 =
      List.ofFn fun i : Fin (A.mu + A.d) => (pfCube E 2).var (pdEq E 2 (x.zt i.rev)) :=
  ZeroCubeP.vars_at E (A.Bt P).zc (A.bitsIn P x).2

end Dat
end
end Lk6
