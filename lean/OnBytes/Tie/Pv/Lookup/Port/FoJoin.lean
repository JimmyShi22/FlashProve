-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean.
The lookup of a sub-proof: the end of its key side, as one affine form that must be 0.

A sub-proof's lookup serves several calls at once. Their key vectors are laid side by side into one
joint vector of 2^v keys, each key moved by its call's number times the shift θ (jointKey,
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean). A claim on that joint vector at a point is of the library's
type MCl (Cb/Ld/LdLkpTree.lean). The routine Forest.join of the Lean verifier under OnBytes/
(OnBytes/Model/Look.lean) takes from its caller, for each call c, an affine form KF c for "call c's
own key vector at call c's own point", and returns one affine form, which must be 0. joinK here is
written after that routine, fold for fold:
    the sum over the calls c of e_c (α - c θ - KF c), plus the sum over the trees y that hold only
      padding of eq(zy, y) (α - call 0's padding key), minus the form cEnd for the end of the key
      side.

Defines, in a commutative ring and on lists (computable):
  eK: the weight of a call's trees (after Forest.callWeight).
  padKeyK: a call's padding key, moved by the shift (after Forest.padKeyOf).
  joinK: the form (after Forest.join).
  rhoP: the point of a claim as a list, the top bit's coordinate first; zxOf, zyOf, zkOf: its cuts,
    by the functions of OnBytes/Tie/Pv/Lookup/Forest/FoPts.lean.
  KFokAt: what is asked of the caller's forms at a reading μ of the places: the value of KF c is the
    extension of call c's key vector at call c's point. It is a claim on μ, not an identity: where a
    caller's form names values that were sent and the key vector reads committed cells, it is what
    the caller's later rounds are to show.
  KFok: KFokAt under every reading: an identity.
  CEok: under every reading, the form cEnd reads α - the claim's target + the claim's form mf.
States:
  val_joinK: the value of joinK's form, as two sums less cEnd's value.
  eqN_top, ext_top: the lists' weights and extensions are the library's (Blocks.eqN, Blocks.ext) at
    the claim's point. eK_eq, zk_eq: a call's weight and point are eC and zkC of
    OnBytes/Tie/Pv/Lookup/Ends/Join.lean (zk_eq: under io h c ≤ h.rK).
  join_form: for every claim c : MCl and every reading μ: c holds of the joint key vector
    jointKey h (Kv μ) θ if and only if the form joinK, at the weights eK h (zyOf h c) and the point
    zyOf h c, is 0 at μ.
Premises of join_form: Prem h (seven clauses on the numbers of the shape;
OnBytes/Tie/Pv/Lookup/Ends/Join.lean); CEok; KFokAt, at the points zkOf h c, at the very reading μ
at which the claim is said.
By: the identity of the join (join_identity; mcl_join, OnBytes/Tie/Pv/Lookup/Ends/JoinClK.lean).
Does not say: that the caller's forms meet KFokAt (each caller's own matter); that the routine
Forest.join computes joinK (no theorem here); anything on rounds or masks' places.

-/
import Cb.Pv.Lookup.Forest.FoAff
import Cb.Pv.Lookup.Forest.FoEq
import OnBytes.Tie.Pv.Lookup.Forest.FoPts
import OnBytes.Tie.Pv.Lookup.Ends.JoinClK

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model OnBytes.Ends Cb.LdLkp

/-! ### Plain forms after the verifier's routines -/
section
variable {P K : Type} [CommRing K]

/-- After Forest.callWeight: the weight of call c's trees at the point zy of the trees' numbers. -/
def eK (h : Sh) (zy : List K) (c : ℕ) : K :=
  (List.range (h.rK - io h c)).foldl
    (fun e i => e * (if (fst h c / 2 ^ io h c / 2 ^ (h.rK - io h c - 1 - i)) % 2 = 1
        then zy.getD i 0 else 1 - zy.getD i 0)) 1

/-- After Forest.padKeyOf: the padding key of call c, moved by the shift. -/
def padKeyK (h : Sh) (θ : K) (c : ℕ) : K := ((OnBytes.Ends.tauN h c (t0Of h c) : ℕ) : K) +
    (c : K) * θ

/-- The form, after Forest.join. e c: the weight of call c; zy: the point of the trees' numbers;
KF c: the caller's form of call c's key vector; cEnd: the form for the end of the key side. -/
def joinK (h : Sh) (θ α : K) (e : ℕ → K) (zy : List K) (KF : ℕ → AffK P K)
    (cEnd : AffK P K) : AffK P K :=
  let onCalls := (List.range h.NC).foldl
    (fun (f : AffK P K) (c : ℕ) => AffK.addMul f (AffK.sub (AffK.ofConst (α - (c : K) * θ)) (KF c))
        (e c)) (AffK.ofConst 0)
  let empty := (List.range (2 ^ h.rK - h.NT)).foldl
    (fun s i => s + (eqTabK zy).getD (h.NT + i) 0 * (α - padKeyK h θ 0)) 0
  AffK.sub (AffK.add onCalls (AffK.ofConst empty)) cEnd

/-- What is asked of the caller's forms, at the reading μ. Kv μ c i: key number i of call c under
μ; zk c: call c's point. -/
def KFokAt (h : Sh) (Kv : (P → K) → ℕ → ℕ → K) (zk : ℕ → List K) (KF : ℕ → AffK P K)
    (μ : P → K) : Prop :=
  ∀ c < h.NC, AffK.val (KF c) μ = extL (Kv μ c) (zk c)

/-- The same under every reading: an identity. -/
def KFok (h : Sh) (Kv : (P → K) → ℕ → ℕ → K) (zk : ℕ → List K) (KF : ℕ → AffK P K) : Prop :=
  ∀ μ, ∀ c < h.NC, AffK.val (KF c) μ = extL (Kv μ c) (zk c)

theorem KFok_iff (h : Sh) (Kv : (P → K) → ℕ → ℕ → K) (zk : ℕ → List K) (KF : ℕ → AffK P K) :
    KFok h Kv zk KF ↔ ∀ μ, KFokAt h Kv zk KF μ := Iff.rfl

theorem foldl_addMul (g : ℕ → AffK P K) (e : ℕ → K) (μ : P → K) : ∀ (l : List ℕ) (f : AffK P K),
    AffK.val (l.foldl (fun f c => AffK.addMul f (g c) (e c)) f) μ = AffK.val f μ +
        (l.map fun c => e c * AffK.val (g c) μ).sum
  | [], f => by simp
  | c :: l, f => by
    rw [List.foldl_cons, foldl_addMul g e μ l, AffK.val_addMul, List.map_cons, List.sum_cons]
    ring

theorem foldl_add (F : ℕ → K) : ∀ (l : List ℕ) (s : K), l.foldl (fun s i => s + F i) s = s +
    (l.map F).sum
  | [], s => by simp
  | i :: l, s => by
    rw [List.foldl_cons, foldl_add F l, List.map_cons, List.sum_cons]
    ring

theorem foldl_mul (F : ℕ → K) : ∀ (l : List ℕ) (s : K), l.foldl (fun s i => s * F i) s = s *
    (l.map F).prod
  | [], s => by simp
  | i :: l, s => by
    rw [List.foldl_cons, foldl_mul F l, List.map_cons, List.prod_cons]
    ring

/-- The value of the join's form. -/
theorem val_joinK (h : Sh) (θ α : K) (e : ℕ → K) (zy : List K) (KF : ℕ → AffK P K) (cEnd : AffK P K)
    (μ : P → K) :
    AffK.val (joinK h θ α e zy KF cEnd) μ =
      ∑ c ∈ range h.NC, e c * (α - (c : K) * θ - AffK.val (KF c) μ) +
        ∑ i ∈ range (2 ^ h.rK - h.NT), (eqTabK zy).getD (h.NT + i) 0 * (α - padKeyK h θ 0) -
            AffK.val cEnd μ := by
  unfold joinK
  simp only [AffK.val_sub, AffK.val_add, AffK.val_ofConst, foldl_addMul, foldl_add, lsum, zero_add]

end

/-! ### A claim's point, as a list -/
section
variable {E : Type} [Field E]

/-- The first k coordinates of a point, as a list: the top bit's coordinate first. -/
def rhoP (k : ℕ) (pt : ℕ → E) : List E := (List.range k).map pt

omit [Field E] in
theorem range_succ_rev (n : ℕ) (q : ℕ → E) : ((List.range (n + 1)).map q).reverse =
    q n :: ((List.range n).map q).reverse := by
  rw [List.range_succ, List.map_append, List.reverse_append]
  rfl

/-- The list's weight, read from the top, is the library's, at every number. -/
theorem eqN_top (pt : ℕ → E) (off : ℕ) : ∀ (n X : ℕ),
    TwV.eqN ((List.range n).map fun i => pt (off + i)).reverse X = Blocks.eqN n off pt X
  | 0, _ => by simp [TwV.eqN, Blocks.eqN]
  | n + 1, X => by
    rw [range_succ_rev]
    show (if X % 2 = 1 then pt (off + n) else 1 - pt (off + n)) * TwV.eqN _ (X / 2) = _
    rw [eqN_top pt off n (X / 2)]
    unfold Blocks.eqN
    rw [Finset.prod_range_succ, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun t ht => ?_
      have h1 : n + 1 - 1 - t = (n - 1 - t) + 1 := by have := Finset.mem_range.mp ht; omega
      rw [h1, Nat.testBit_succ]
    · have h0 : n + 1 - 1 - n = 0 := by omega
      rw [h0, Nat.testBit_zero]
      simp

/-- The list's extension is the library's. -/
theorem ext_top (f : ℕ → E) (n : ℕ) (q : ℕ → E) : extL f ((List.range n).map q) =
    Blocks.ext n f q := by
  unfold extL Blocks.ext
  rw [lsum, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun X _ => ?_
  have := eqN_top q 0 n X
  simp only [Nat.zero_add] at this
  rw [this]

theorem lprod (f : ℕ → E) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, lprod f n, Finset.prod_range_succ]
    simp

variable (h : Sh) (pt : ℕ → E)

omit [Field E] in
/-- the two cuts of the point's list -/
theorem zx_rho : zx h.dT (rhoP (h.dT + h.rK) pt) = (List.range h.dT).map pt :=
  take_map_range pt (Nat.le_add_right _ _)
omit [Field E] in
theorem zy_rho : zy h.dT (rhoP (h.dT + h.rK) pt) = (List.range h.rK).map fun u => pt (h.dT + u) :=
  drop_map_range pt h.dT h.rK

/-- The table of weights at the trees' numbers' point is the library's weight. -/
theorem eqTab_top (y : ℕ) (hy : y < 2 ^ h.rK) :
    (eqTabK (zy h.dT (rhoP (h.dT + h.rK) pt))).getD y 0 = Blocks.eqN h.rK h.dT pt y := by
  rw [eqTabK_get, zy_rho, List.length_map, List.length_range, if_pos hy, eqN_top]

/-- A call's weight is the library's. -/
theorem eK_eq (c : ℕ) : eK h (zy h.dT (rhoP (h.dT + h.rK) pt)) c = eC h pt c := by
  unfold eK eC Blocks.eqN
  rw [foldl_mul, one_mul, lprod, zy_rho]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' : t < h.rK := by have := Finset.mem_range.mp ht; omega
  have hg : ((List.range h.rK).map fun u => pt (h.dT + u)).getD t 0 = pt (h.dT + t) := by
    rw [List.getD_eq_getElem _ _ (by simpa using ht')]
    simp
  rw [hg, Nat.testBit_eq_decide_div_mod_eq]
  show _ = if decide (fst h c / 2 ^ io h c / 2 ^ (h.rK - io h c - 1 - t) % 2 = 1) = true
      then _ else _
  simp only [decide_eq_true_eq]

omit [Field E] in
/-- A call's point is the library's. -/
theorem zk_eq (c : ℕ) (hio : io h c ≤ h.rK) :
    zk h.rK (io h c) (zx h.dT (rhoP (h.dT + h.rK) pt)) (zy h.dT (rhoP (h.dT + h.rK) pt)) =
      (List.range (io h c + h.dT)).map (zkC h pt c) := by
  unfold zk
  rw [zx_rho, zy_rho, List.range_add, List.map_append, List.map_map]
  have e : h.rK = (h.rK - io h c) + io h c := by omega
  congr 1
  · conv_lhs => rw [e]
    rw [Nat.add_sub_cancel, drop_map_range]
    refine List.map_congr_left fun u hu => ?_
    have hu' : u < io h c := List.mem_range.mp hu
    refine Eq.trans ?_ (if_pos (show u < iotaN h c from hu')).symm
    show pt (h.dT + (h.rK - io h c + u)) = pt (h.dT + h.rK - io h c + u)
    congr 1
    omega
  · refine List.map_congr_left fun u _ => ?_
    have hn : ¬ io h c + u < iotaN h c := by
      show ¬ io h c + u < io h c
      omega
    refine Eq.trans ?_ (if_neg hn).symm
    show pt u = pt (io h c + u - io h c)
    rw [Nat.add_sub_cancel_left]

end

/-! ### The join -/
section
variable {E N : Type} [Field E] [Fintype N]

/-- The form cEnd reads α less the claim's target plus the claim's form, under every reading of the
places. -/
def CEok (c : MCl E N) (α : E) (cEnd : AffK N E) : Prop :=
    ∀ μ, AffK.val cEnd μ = α - c.tg + ∑ i, c.mf i * μ i

/-- The three lists at a claim's point. -/
def zxOf (h : Sh) (c : MCl E N) : List E := zx h.dT (rhoP (h.dT + h.rK) c.pt)
def zyOf (h : Sh) (c : MCl E N) : List E := zy h.dT (rhoP (h.dT + h.rK) c.pt)
def zkOf (h : Sh) (c : MCl E N) (k : ℕ) : List E := zk h.rK (io h k) (zxOf h c) (zyOf h c)

/-- **The end of the key side.** A claim (MCl) on the joint key vector holds exactly if joinK's form
is 0. -/
theorem join_form {h : Sh} (hp : Prem h) (Kv : (N → E) → ℕ → ℕ → E) (θ α : E) (c : MCl E N)
    (KF : ℕ → AffK N E)
    (cEnd : AffK N E) (μ : N → E) (hKF : KFokAt h Kv (zkOf h c) KF μ) (hC : CEok c α cEnd) :
    c.Holds h.v (jointKey h (Kv μ) θ) μ ↔ AffK.val
        (joinK h θ α (eK h (zyOf h c)) (zyOf h c) KF cEnd) μ = 0 := by
  rw [mcl_join hp (Kv μ) θ α c μ rfl rfl, val_joinK, hC μ, sub_eq_zero]
  have hA : ∑ k ∈ range h.NC, eK h (zyOf h c) k * (α - (k : E) * θ - AffK.val (KF k) μ) =
      ∑ k ∈ range h.NC, eC h c.pt k * (α - (k : E) * θ -
          Blocks.ext (nN h k) (Kv μ k) (zkC h c.pt k)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < h.NC := Finset.mem_range.mp hk
    rw [hKF k hk']
    unfold zkOf zxOf zyOf
    rw [eK_eq, zk_eq h c.pt k (hp.le k hk'), ext_top, hp.n k hk', Nat.add_comm]
    rfl
  have hB : ∑ i ∈ range (2 ^ h.rK - h.NT), (eqTabK (zyOf h c)).getD (h.NT + i) 0 *
      (α - padKeyK h θ 0) =
      ∑ y ∈ Ico h.NT (2 ^ h.rK), Blocks.eqN h.rK h.dT c.pt y *
          (α - (OnBytes.Ends.tauN h 0 (t0N h 0) : E)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : h.NT + i < 2 ^ h.rK := by have := Finset.mem_range.mp hi; omega
    unfold zyOf
    rw [eqTab_top h c.pt _ hi']
    congr 2
    unfold padKeyK
    simp
    rfl
  rw [hA, hB]
  rfl

end
end Fo
