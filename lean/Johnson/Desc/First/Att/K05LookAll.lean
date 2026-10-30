-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LookAll.lean: the premises `LookAll` on the lookup's points
(Johnson/Desc/First/Att/K05Cap.lean), which stand in the statements on the kind K5, from two
records: one in the names of the lookup's heard record, one public.

Definitions, statements and proofs.
Main names:
  `KeyPtsAre ρ C z zk`: what the lookup's kind has to give: for each of the four calls q, the key
    point zk[q] has C.a q coordinates and, read, is the library's key point C.zC q z of the typed
    lookup's end point z.
  `K3Pts fs zx zy zk z`, `keyPts_of_k3`: the same in the names zx, zy, zk: zx has dT and zy rK
    coordinates; zk[q] is (the last iota_q coordinates of zy | zx); z is (zx | zy), read. Then
    `KeyPtsAre` at `Reading.gl` and C := `callsOf` fs, by `zk_eq_zC_of_fit`
    (Johnson/Road/Lane5ZkZc.lean), under the public test `CallsFit`.
  `UnitIs D C fam q u`: the public record on one unit: its call is q, of the size of the family's
    call; its inner point has the family's ℓ coordinates; it has nb pieces, and the weight of piece
    b at any key point is `eqAt` of the point's first a - ℓ coordinates at the block number nu0 + b.
  `eqAt_read`: `eqAt`, read, is `Blocks.eqN`, for any reading. (`readE_eqAt`,
    OnBytes/Tie/Pv/Lookup/Ends/PortA2.lean, has it for the function of that name in
    OnBytes/Model/AttentionShape.lean at one reading; the proof here follows that one.)
  `zC_same`, `inner_read`, `inner_size`, `weight_read`: a unit's inner point and weights, read, are
    `inn` and `wp`.
  `u4_eq`: the inner point of family 4 is that of family 3W without its first coordinate (y_g | y_i
    | y_n), by `inn_tail` (Inst/Model/Att/KeyFormsExt/Calls14.lean), where a piece is no longer than
    a tree.
  `lookPts_of`, `unitPtsM_of`, `unitPtsD_of`, `lookAll_of`: `LookAll` from `KeyPtsAre` and three
    `UnitIs`.
  `lookAll_of_k3`: from `K3Pts`, where the letters' calls are `callsOf` fs.
  `pcsSorted`, `weights_eq`, `unitOk`, `unitIs_of_ok`: `UnitIs` from a yes of a test on the unit's
    pieces.
Used: plain records, pure functions and lemmas on them alone; no routine in a context:
`LookAll`, `LookPts`, `UnitPtsM`, `UnitPtsD`, `weights`, `inner`, `eqAt`, `wp`, `inn`,
`zk_eq_zC_of_fit`, `callsFit_iota`, `callsOf`, `CallsFit`, `readV`, `foldl_mul_value`, `inn_tail`.
Limits: `K3Pts` and `KeyPtsAre` speak of four calls: where the lookup has fewer they cannot be met.
`UnitIs` is shown of no place by a theorem; `unitOk` is evaluated in no file of this tree. That a
record of the lookup's kind holds zk as `K3Pts` says, and that the typed lookup's end point is (zx |
zy), read, is not shown in this file or in what it imports. Nothing is claimed on soundness,
completeness or hiding.

-/
import Johnson.Road.Lane5ZkZc
import Johnson.Road.FormsKeysLook
import Inst.Model.Att.KeyFormsExt.Calls14
import Johnson.Desc.First.Att.K05Cap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes OnBytes.Model Cb.Pv.Att Inst.Model Inst.Model.AttSeg Finset

variable {K : Type} [Field K] {ρ : Reading K}

/-- **`eqAt`, read, is `Blocks.eqN`.** -/
theorem eqAt_read (z : Array E) (idx : ℕ) :
    ρ.val (eqAt z idx) = Blocks.eqN z.size 0 (fun t => ρ.val (z.getD t zeroE)) idx := by
  have h0 : eqAt z idx = (List.range z.size).foldl (fun p v => mulE p
      (if (idx >>> (z.size - 1 - v)) % 2 == 1 then z.getD v zeroE else subE oneE (z.getD v zeroE))) oneE := rfl
  rw [h0, OnBytes.Road.foldl_mul_value]
  unfold Blocks.eqN
  refine prod_congr rfl fun t _ => ?_
  have hb : ((idx >>> (z.size - 1 - t)) % 2 == 1) = idx.testBit (z.size - 1 - t) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, beq_eq_decide]
  rw [hb, Nat.zero_add]
  cases idx.testBit (z.size - 1 - t)
  · simp only [Bool.false_eq_true, if_false, ρ.sub, ρ.one]
  · simp only [if_true]

/-- **What the lookup's kind must give.** -/
structure KeyPtsAre (ρ : Reading K) (C : Calls) (z : ℕ → K) (zk : Array (Array E)) : Prop where
  size : ∀ q : Fin 4, (zk.getD q.1 #[]).size = C.a q
  read : ∀ (q : Fin 4) (i : ℕ), i < C.a q → ρ.val ((zk.getD q.1 #[]).getD i zeroE) = C.zC q z i

/-- **The public record on one unit.** -/
structure UnitIs (D : Dim) (C : Calls) (fam : Fam) (q : Fin 4) (u : UnitG) : Prop where
  call : u.call = q.1
  same : C.a q = C.a fam.call
  bits : u.bits = fam.l D
  le : fam.l D ≤ C.a q
  nPw : ∀ zkc : Array E, (weights u zkc).size = D.nb
  w : ∀ (zkc : Array E) (b : ℕ), b < D.nb →
    (weights u zkc).getD b zeroE = eqAt (zkc.extract 0 (C.a q - fam.l D)) (fam.nu0 D + b)

omit [Field K] in
/-- Calls of one size have one key point. -/
theorem zC_same (C : Calls) {q q' : Fin 4} (h : C.a q = C.a q') (z : ℕ → K) : C.zC q z = C.zC q' z := by
  funext t
  unfold Calls.zC Calls.e
  rw [h]

section Unit
variable {D : Dim} {C : Calls} {z : ℕ → K} {zk : Array (Array E)} {fam : Fam} {q : Fin 4} {u : UnitG}

/-- A unit's inner point, read, is the library's. -/
theorem inner_read (Kp : KeyPtsAre ρ C z zk) (U : UnitIs D C fam q u) (j : ℕ) (hj : j < fam.l D) :
    ρ.val ((inner u (zk.getD u.call #[])).getD j zeroE) = inn D C z fam j := by
  have hs := Kp.size q
  have hl := U.le
  rw [U.call]
  unfold inner
  rw [U.bits, hs, Array.getD_eq_getD_getElem?, Array.getElem?_extract, if_pos (by rw [hs]; omega),
    ← Array.getD_eq_getD_getElem?, Kp.read q _ (by omega), zC_same C U.same]
  unfold inn sh
  rw [← U.same]

theorem inner_size (Kp : KeyPtsAre ρ C z zk) (U : UnitIs D C fam q u) :
    (inner u (zk.getD u.call #[])).size = fam.l D := by
  have hs := Kp.size q
  have hl := U.le
  rw [U.call]
  unfold inner
  rw [U.bits, Array.size_extract, hs]
  omega

/-- A unit's weights, read, are the library's. -/
theorem weight_read (Kp : KeyPtsAre ρ C z zk) (U : UnitIs D C fam q u) (b : ℕ) (hb : b < D.nb) :
    ρ.val ((weights u (zk.getD u.call #[])).getD b zeroE) = wp D C z fam b := by
  have hs := Kp.size q
  have hl := U.le
  rw [U.w _ b hb, eqAt_read, U.call]
  have hz : ((zk.getD q.1 #[]).extract 0 (C.a q - fam.l D)).size = C.a q - fam.l D := by
    rw [Array.size_extract, hs]
    omega
  rw [hz]
  unfold wp Blocks.eqN
  rw [← U.same]
  refine prod_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have e : ρ.val (((zk.getD q.1 #[]).extract 0 (C.a q - fam.l D)).getD (0 + t) zeroE) =
      C.zC fam.call z (0 + t) := by
    rw [Nat.zero_add, Array.getD_eq_getD_getElem?, Array.getElem?_extract, if_pos (by rw [hs]; omega),
      Nat.zero_add, ← Array.getD_eq_getD_getElem?, Kp.read q _ (by omega), zC_same C U.same]
  beta_reduce
  rw [e]

end Unit

omit [Field K] in
/-- **The inner point of family 4 is (y_g | y_i | y_n)**, the inner point of family 3W without its
first coordinate, where a piece of either is no longer than a tree. -/
theorem u4_eq (D : Dim) (C : Calls) (z : ℕ → K) (hW : D.lW ≤ C.Dk) (a2 : C.Dk ≤ C.a 2) (a3 : C.Dk ≤ C.a 3) :
    u4 D C z = sh (uW D C z) 1 := by
  have e : D.lW = D.l4 + 1 := by
    unfold Dim.lW Dim.l4
    omega
  funext t
  show inn D C z .f4 t = inn D C z .w3 (1 + t)
  rw [KeyFormsExt.inn_tail D C z .f4 (show D.l4 ≤ C.Dk by omega) a3,
    KeyFormsExt.inn_tail D C z .w3 hW a2]
  show z (C.Dk - D.l4 + t) = z (C.Dk - D.lW + (1 + t))
  congr 1
  omega

section All
variable {D : Dim} {C : Calls} {z : ℕ → K} {zk : Array (Array E)}

/-- The premises on the list wl's unit. -/
theorem lookPts_of (Kp : KeyPtsAre ρ C z zk) {q : Fin 4} {u : UnitG} (U : UnitIs D C .w3 q u) :
    LookPts ρ D C z (weights u (zk.getD u.call #[])) (inner u (zk.getD u.call #[])) where
  nPw := U.nPw _
  nZ := by
    rw [inner_size Kp U]
    show 1 + D.lg + D.lT ≤ D.lW
    unfold Dim.lW
    omega
  hw := fun b hb => weight_read Kp U b hb
  hg := fun k hk => inner_read Kp U (1 + k) (by
    show 1 + k < D.lW
    unfold Dim.lW
    omega)
  hi := fun k hk => inner_read Kp U (1 + D.lg + k) (by
    show 1 + D.lg + k < D.lW
    unfold Dim.lW
    omega)
  hI := fun k hk => inner_read Kp U (1 + D.lg + k) (by
    show 1 + D.lg + k < D.lW
    unfold Dim.lW Dim.lT
    omega)

/-- The premises on the unit below the diagonal. -/
theorem unitPtsM_of (Kp : KeyPtsAre ρ C z zk) {q : Fin 4} {u : UnitG} (U : UnitIs D C .m1 q u) :
    UnitPtsM ρ D C z u (zk.getD u.call #[]) where
  nPw := U.nPw _
  hw := fun b hb => weight_read Kp U b hb
  hg := fun k hk => (inner_read Kp U k (by
    show k < D.lM
    unfold Dim.lM
    omega)).trans (by
      show inn D C z .m1 k = inn D C z .m1 (0 + k)
      rw [Nat.zero_add])
  hP := fun k hk => inner_read Kp U (D.lg + k) (by
    show D.lg + k < D.lM
    unfold Dim.lM
    omega)
  hs := fun k hk => inner_read Kp U (D.lg + D.lP + k) (by
    show D.lg + D.lP + k < D.lM
    unfold Dim.lM
    omega)

/-- The premises on the unit on the diagonal. -/
theorem unitPtsD_of (Kp : KeyPtsAre ρ C z zk) {q : Fin 4} {u : UnitG} (U : UnitIs D C .d1 q u) :
    UnitPtsD ρ D C z u (zk.getD u.call #[]) where
  nPw := U.nPw _
  hw := fun b hb => weight_read Kp U b hb
  hg := fun k hk => (inner_read Kp U k (by
    show k < D.lD
    unfold Dim.lD
    omega)).trans (by
      show inn D C z .d1 k = inn D C z .d1 (0 + k)
      rw [Nat.zero_add])
  hI := fun k hk => inner_read Kp U (D.lg + k) (by
    show D.lg + k < D.lD
    unfold Dim.lD
    omega)

end All

/-- **LookAll from the lookup's kind's record and three public records.** -/
theorem lookAll_of [Fintype K] {M0 X : Type} (P0 : OwnPar K M0 X) (S : Attention.Shape) (zk : Array (Array E))
    (u1 u2 : UnitG) (x0 : X) (Kp : KeyPtsAre ρ P0.C (P0.zOf x0) zk) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM u1) (UD : UnitIs P0.D P0.C .d1 qD u2) : LookAll P0 S zk u1 u2 ρ x0 :=
  ⟨fun wl hw => lookPts_of Kp (UW wl hw), unitPtsM_of Kp UM, unitPtsD_of Kp UD⟩

/-- **The same record in the names of the lookup's heard record**: zx · zy · zk. -/
structure K3Pts (fs : Model.Forest.Shape) (zx zy : Array E) (zk : Array (Array E)) (z : ℕ → Cb.Gl.E) : Prop where
  nx : zx.size = fs.dT
  ny : zy.size = fs.rK
  zk : ∀ q : Fin 4, zk.getD q.1 #[] = zy.extract (fs.rK - fs.iota.getD q.1 0) zy.size ++ zx
  z : z = OnBytes.Slice.readV (zx ++ zy)

theorem keyPts_of_k3 {S : Attention.Shape} {fs : Model.Forest.Shape} (hf : OnBytes.Road.L5.CallsFit S fs)
    {zx zy : Array E} {zk : Array (Array E)} {z : ℕ → Cb.Gl.E} (H : K3Pts fs zx zy zk z) :
    KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf fs) z zk where
  size := fun q => by
    obtain ⟨h1, h2⟩ := OnBytes.Road.L5.callsFit_iota hf q
    have h3 := hf.2.1 q
    have hDk : (OnBytes.Road.L5.callsOf fs).Dk = fs.dT := rfl
    have he : (OnBytes.Road.L5.callsOf fs).e q =
      (OnBytes.Road.L5.callsOf fs).a q - (OnBytes.Road.L5.callsOf fs).Dk := rfl
    rw [H.zk q, Array.size_append, Array.size_extract, H.nx, H.ny, h1]
    omega
  read := fun q i hi => by
    rw [H.zk q, H.z]
    exact OnBytes.Road.L5.zk_eq_zC_of_fit hf zx zy H.nx H.ny q i hi

/-- **LookAll from the lookup's heard record**, where the letters' calls are the library's numbers
of the lookup's shape. -/
theorem lookAll_of_k3 {M0 X : Type} (P0 : OwnPar Cb.Gl.E M0 X) (S : Attention.Shape) {fs : Model.Forest.Shape}
    (hf : OnBytes.Road.L5.CallsFit S fs) (hC : P0.C = OnBytes.Road.L5.callsOf fs) {zx zy : Array E}
    (zk : Array (Array E)) (u1 u2 : UnitG) (x0 : X) (H : K3Pts fs zx zy zk (P0.zOf x0)) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM u1) (UD : UnitIs P0.D P0.C .d1 qD u2) :
    LookAll P0 S zk u1 u2 Reading.gl x0 :=
  lookAll_of P0 S zk u1 u2 x0 (by rw [hC]; exact keyPts_of_k3 hf H) UW UM UD

/-! ### The public record, from a test on the unit's pieces -/

/-- The unit's pieces, by layer, then by head. -/
def pcsSorted (u : UnitG) : List Pc :=
  u.pcs.mergeSort fun x y => Decidable.decide (x.lam < y.lam) || (x.lam == y.lam && Decidable.decide (x.a ≤ y.a))

/-- The weights are made of the sorted pieces, one by one. -/
theorem weights_eq (u : UnitG) (zkc : Array E) :
    weights u zkc = ((pcsSorted u).map fun pc => eqAt (zkc.extract 0 (u.n - pc.b)) (pc.off >>> pc.b)).toArray := by
  unfold weights pcsSorted
  rw [← List.map_mergeSort (f := fun pc : Pc => (pc.lam, pc.a, eqAt (zkc.extract 0 (u.n - pc.b)) (pc.off >>> pc.b)))
    (r := fun x y => Decidable.decide (x.lam < y.lam) || (x.lam == y.lam && Decidable.decide (x.a ≤ y.a))) (fun _ _ _ _ => rfl)]
  simp [List.map_map, Function.comp_def]

/-- **The test**: no challenge in it. -/
def unitOk (D : Dim) (C : Calls) (fam : Fam) (q : Fin 4) (u : UnitG) : Bool :=
  u.call == q.1 && C.a q == C.a fam.call && u.bits == fam.l D && Decidable.decide (fam.l D ≤ C.a q) &&
    ((pcsSorted u).map fun pc => (u.n - pc.b, pc.off >>> pc.b)) ==
      (List.range D.nb).map fun b => (C.a q - fam.l D, fam.nu0 D + b)

theorem unitIs_of_ok {D : Dim} {C : Calls} {fam : Fam} {q : Fin 4} {u : UnitG} (h : unitOk D C fam q u = true) :
    UnitIs D C fam q u := by
  unfold unitOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hlen : (pcsSorted u).length = D.nb := by
    have := congrArg List.length h5
    simpa using this
  refine ⟨h1, h2, h3, h4, fun zkc => by rw [weights_eq]; simp [hlen], fun zkc b hb => ?_⟩
  have hb' : b < (pcsSorted u).length := by rw [hlen]; exact hb
  have e := congrArg (fun l => l[b]?) h5
  simp only [List.getElem?_map, List.getElem?_range hb, List.getElem?_eq_getElem hb', Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at e
  rw [weights_eq]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hb', Option.map_some, Option.getD_some]
  rw [e.1, e.2]

end VerifiableInference.Desc.First.Att.P
