-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
(Over CarryAtFull.lean and HCarOf.lean, in which the fresh mask's word is a letter.)
Johnson/Desc/First/Link/Law/HCarLay.lean: `hCar_of` (HCarOf.lean) GENERAL IN THE LIST, THE CODES,
THE STAGE AND THE RADIUS: at the typed group of any list at the program's own layout
(`groupLayK cs lo s e kb hM hZ`, Johnson/Desc/First/Close/Law/CubeOfShapes.lean). HCarOf.lean's
three theorems with the full size's letters taken out: that the list is a written one and the
group's sizes a written front's was spent there through the group's type alone. Theorems. No other
file turns.

  `carryAt_lay`, `carryAt_behind_lay`, `hCar_lay`: as `carryAt_full` (CarryAtFull.lean),
    `carryAt_behind`, `hCar_of`; the row's public equations are now: r.cs = cs · r.lo = lo · s is
    the stage of r.g at some number of draws · (kb i = true ↔ i ∈ r.kept) · r.rad ≤ e.
Limits. Those of HCarOf.lean: EVERY PREMISE STANDS; NONE IS SHOWN AT A VALUE. r.lo = lo ties the
closing's list to the switch's typed row's own list: where the two kinds' files type one link over
two lists the premise cannot be met. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HCarOf
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (wordsOf)
open VerifiableInference.Desc.First.K2Caller (SwRow carryRow plainD carryAtZ carryAtZ_iff doorZ)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt groupLayK layAt sizesM sizesZ)

/-- **AT THE TYPED GROUP OF ANY LIST AT THE PROGRAM's OWN LAYOUT.** -/
theorem carryAt_lay (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    (r : SwRow) (H : r.OK)
    (hcs : r.cs = cs) (hl : r.lo = lo) (t₀ : ℕ) (hs : s = stageOf r.g t₀)
    (hkb : ∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) (he : r.rad ≤ e)
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
  obtain ⟨set, cs', lo', g', rad', l', o', roots', kept', rider'⟩ := r
  dsimp only at hcs hl hs
  subst hcs hl hs
  exact carryAt_kp _ H t₀ e _ _ _ _ (fun a => kb a.1 = true) (fun a => hkb a.1) G seat y p
    t orc smp no ix z N he hF hC

/-- **FROM THE ITEM «carry» AT THE STATE BEHIND TO CarryAt.** -/
theorem carryAt_behind_lay (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {Pz Wt : Type} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (a' : Pz × First.S) (y : Strs) (w : Wt) {Xi : Type}
    (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ) (no ix : {i // memMain lo i} → ℕ)
    (zw : (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.Word)
    (N : SlotNames (groupLayK cs lo s e kb hM hZ)) (rows : SingleRows)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → r.cs = cs ∧ r.lo = lo ∧
      (∃ t₀, s = stageOf r.g t₀) ∧ (∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) ∧
      r.rad ≤ e)
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
  obtain ⟨e1, e2, ⟨t₀, e3⟩, e4, e5⟩ := hr r h1
  obtain ⟨fx, W₀, g1, g2, g3⟩ := carryAt_lay cs lo s e kb hM hZ r (r.ok_says hok) e1 e2 t₀ e3 e4
    e5 G
    seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) _ no ix zw N
    (fun fx W₀ k1 k2 => (hF r t fx W₀ h1 h2 k1 k2).2) h3
  rw [(hF r t fx W₀ h1 h2 g1 g2).1] at g3
  exact g3

section AtFa
open OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb.Pv
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc.First.Close (CarriedAt faK10 SbV slV ZV)

/-- **hCar AT THE CONCRETE fa, GENERAL IN THE LIST.** -/
theorem hCar_lay (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
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
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → r.cs = cs ∧ r.lo = lo ∧
      (∃ t₀, s = stageOf r.g t₀) ∧ (∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) ∧
      r.rad ≤ e)
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
  have h1 := carryAt_behind_lay cs lo s e kb hM hZ Z lay m (z, s') y w G seat no ix (mW a) N rows
    hr hF hC
  rw [wordsOf_congr G cs lo seat hy] at h1
  exact carriedAt_of _ N keep _ _ _ fx A₀ bC bZ w₀ w₁ L _ rows h1 h2

end AtFa

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carryAt_lay
#print axioms VerifiableInference.Desc.LinkJoin.carryAt_behind_lay
#print axioms VerifiableInference.Desc.LinkJoin.hCar_lay
