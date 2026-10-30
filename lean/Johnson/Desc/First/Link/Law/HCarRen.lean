-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarRen.lean: `hCar_lay` (HCarLay.lean) WHERE THE CLOSING's FILES TYPE
THE GROUP OVER ANOTHER LIST THAN THE CODE SWITCH's TYPED ROW DOES. For the first link: there the
row's list has six messages, one of them no member of the group; the closing's files type the
group over the five members' list. HCarLay.lean's three theorems with «r.cs = cs · r.lo = lo · kb ↔
r.kept» out and ONE sentence on numbers in: at every number n the two lists' messages number n have
as many kept rows (`keptRowsAt`, KeptEquiv.lean). By `keptEquiv_rows` and `carryAt_renamed`
(CarryRenamed.lean). Theorems.

  `carryAt_ren`, `carryAt_behind_ren`, `hCar_ren`: as `carryAt_lay`, `carryAt_behind_lay`,
    `hCar_lay`; what is asked of the row r is: s is the stage of r.g at some number of draws ·
    (∀ n, keptRowsAt r.lo r.mem r.kp n = keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) ·
    r.rad ≤ e. NOTHING ELSE TIES cs AND lo TO THE ROW BUT `FrontFitsAt`.
Limits. Those of HCarOf.lean: EVERY PREMISE STANDS; NONE IS SHOWN AT A VALUE. A kept member must
bear the SAME number in both lists. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HCarLay
import Johnson.Desc.First.Link.Law.CarryRenamed
import Johnson.Desc.First.Link.Law.KeptEquiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (wordsOf)
open VerifiableInference.Desc.First.K2Caller (SwRow carryRow plainD plainR carryAtZ carryAtZ_iff
  doorZ)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt groupLayK layAt sizesM sizesZ)

/-- **AT A TYPED GROUP OVER ANOTHER LIST THAN THE ROW's.** -/
theorem carryAt_ren (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (r : SwRow) (H : r.OK)
    (t₀ : ℕ) (hs : s = stageOf r.g t₀)
    (hk : ∀ n, keptRowsAt r.lo r.mem r.kp n =
      keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) (he : r.rad ≤ e)
    {Xi : Type} (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ) (y : Strs) (p : First.K2.P2)
    (t : First.S) (orc : Strs → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (no ix : {i // memMain lo i} → ℕ) (z : (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.Word)
    (N : SlotNames (groupLayK cs lo s e kb hM hZ))
    (hF : ∀ fx W₀, First.K2.frontAt p t = some fx → First.K2.frameAt fx = some W₀ →
      FrontFitsAt cs lo (memMain lo) s e
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        hM hZ (fun a => kb a.1 = true) r.kept G
        seat y p t (orc y) no ix z N fx W₀)
    (hC : carryRow r H p orc smp t y) :
    ∃ fx W₀, First.K2.frontAt p t = some fx ∧ First.K2.frameAt fx = some W₀ ∧
      CarryAt (groupLayK cs lo s e kb hM hZ) N fx.f.rows
        (foldedAt (groupLayK cs lo s e kb hM hZ).Sh.par
          (readP (s.h + s.g) fx.f.rows.gamma)
          ((groupLayK cs lo s e kb hM hZ).Sh.rho.wd
            ((groupLayK cs lo s e kb hM hZ).G.word (wordsOf G cs lo seat y))) z) := by
  subst hs
  obtain ⟨φ, hφ⟩ : ∃ φ : (plainR r H).Kp ≃ (groupLayK cs lo (stageOf r.g t₀) e kb hM hZ).Kp,
      ∀ κ, (φ κ).1.1.1.val = κ.1.1.1.val ∧ (φ κ).2.val = κ.2.val :=
    keptEquiv_rows _ _ _ _ _ _ _ _ _ _ cs lo (memMain lo) (stageOf r.g t₀) e _ _ hM hZ
      (fun a => kb a.1 = true) hk
  exact carryAt_renamed r H cs lo (memMain lo) t₀ e _ _ hM hZ (fun a => kb a.1 = true) φ hφ G seat
    y p t orc smp no ix z N he hF hC

/-- **FROM THE ITEM «carry» AT THE STATE BEHIND TO CarryAt.** -/
theorem carryAt_behind_ren (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {Pz Wt : Type} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (a' : Pz × First.S) (y : Strs) (w : Wt) {Xi : Type}
    (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ) (no ix : {i // memMain lo i} → ℕ)
    (zw : (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.Word)
    (N : SlotNames (groupLayK cs lo s e kb hM hZ)) (rows : SingleRows)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → (∃ t₀, s = stageOf r.g t₀) ∧
      (∀ n, keptRowsAt r.lo r.mem r.kp n =
        keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) ∧ r.rad ≤ e)
    (hF : ∀ r t fx W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m a'.2 = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx → First.K2.frameAt fx = some W₀ →
      fx.f.rows = rows ∧
      FrontFitsAt cs lo (memMain lo) s e
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        hM hZ (fun a => kb a.1 = true) r.kept G
        seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) no ix zw N fx W₀)
    (hC : carryAtZ Z lay m a' y w) :
    CarryAt (groupLayK cs lo s e kb hM hZ) N rows
      (foldedAt (groupLayK cs lo s e kb hM hZ).Sh.par
        (readP (s.h + s.g) rows.gamma)
        ((groupLayK cs lo s e kb hM hZ).Sh.rho.wd
          ((groupLayK cs lo s e kb hM hZ).G.word (wordsOf G cs lo seat y))) zw) := by
  obtain ⟨r, t, h1, h2, hok, h3⟩ := (carryAtZ_iff Z lay m a' y w).1 hC
  obtain ⟨⟨t₀, e3⟩, e4, e5⟩ := hr r h1
  obtain ⟨fx, W₀, g1, g2, g3⟩ := carryAt_ren cs lo s e kb hM hZ r (r.ok_says hok) t₀ e3 e4 e5 G
    seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) _ no ix zw N
    (fun fx W₀ k1 k2 => (hF r t fx W₀ h1 h2 k1 k2).2) h3
  rw [(hF r t fx W₀ h1 h2 g1 g2).1] at g3
  exact g3

section AtFa
open OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb.Pv
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc.First.Close (CarriedAt faK10 SbV slV ZV)

/-- **hCar AT THE CONCRETE fa, AT A GROUP TYPED OVER ANOTHER LIST THAN THE ROW's.** -/
theorem hCar_ren (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {Xi : Type} (G : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ) (N : SlotNames (groupLayK cs lo s e kb hM hZ))
    (keep : (sigOf cs lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
    (pull : ((groupLayK cs lo s e kb hM hZ).Sh.Cin.J → GE) →
      (groupLayK cs lo s e kb hM hZ).G.C.J → GE) (n : ℕ)
    (num : (groupLayK cs lo s e kb hM hZ).G.Row B ≃ Fin n)
    (fx : Fin (((groupLayK cs lo s e kb hM hZ).Sh.fold (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
      (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).Msg × Wp))
    (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
    (w₁ : LdBrW (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
      (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
      (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE)) {Pz Wt : Type}
    (smp : Pz × First.S → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
    (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (z : Pz) (a : First.S × F.E.Str) (s' : First.S) (y : Strs) (w : Wt)
    (no ix : {i // memMain lo i} → ℕ)
    (mW : First.S × F.E.Str → (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.nat.Str)
    (rows : SingleRows)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → (∃ t₀, s = stageOf r.g t₀) ∧
      (∀ n, keptRowsAt r.lo r.mem r.kp n =
        keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n) ∧ r.rad ≤ e)
    (hF : ∀ r t fx' W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m s' = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' → First.K2.frameAt fx' = some W₀ →
      fx'.f.rows = rows ∧
      FrontFitsAt cs lo (memMain lo) s e
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        hM hZ (fun a => kb a.1 = true) r.kept G
        seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) no ix (mW a) N fx'
        W₀)
    (hy : ∀ i x, y.col (seat i).1 x = (strsOf F a.2).col (seat i).1 x)
    (hC : carryAtZ Z lay m (z, s') y w)
    (h2 : ∃ (zz : (ZV (groupLayK cs lo s e kb hM hZ) n num).D)
      (v : ((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
        (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
        (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).Wit × Wp),
      (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
        (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
        (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp).over A₀).relR
        ((batX ((groupLayK cs lo s e kb hM hZ).foldCaller keep
            (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
            (ZV (groupLayK cs lo s e kb hM hZ) n num) fx A₀ bC bZ w₀ w₁)
          (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ) N keep pull n num fx A₀ bC
            bZ w₀ w₁ L smp σ₀ st₀ e₀
            mW z a).1 zz).2,
          ((ldBrG (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
            (SbV (groupLayK cs lo s e kb hM hZ) B) (slV (groupLayK cs lo s e kb hM hZ) pull)
            (ZV (groupLayK cs lo s e kb hM hZ) n num)).kp E₀).map
            (e₀, wordsOf G cs lo seat (strsOf F a.2))).2) v) :
    CarriedAt (groupLayK cs lo s e kb hM hZ) N keep (SbV (groupLayK cs lo s e kb hM hZ) B)
      (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e kb hM hZ) n num) fx
      A₀ bC bZ w₀ w₁ L
      (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ) N keep pull n num fx A₀ bC bZ
        w₀ w₁ L smp σ₀ st₀ e₀
        mW z a) rows := by
  have h1 := carryAt_behind_ren cs lo s e kb hM hZ Z lay m (z, s') y w G seat no ix (mW a) N rows
    hr hF hC
  rw [wordsOf_congr G cs lo seat hy] at h1
  exact carriedAt_of _ N keep _ _ _ fx A₀ bC bZ w₀ w₁ L _ rows h1 h2

end AtFa

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_ren
#print axioms VerifiableInference.Desc.LinkJoin.carryAt_behind_ren
#print axioms VerifiableInference.Desc.LinkJoin.hCar_ren
