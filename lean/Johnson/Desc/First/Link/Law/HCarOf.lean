-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarOf.lean: **K10's LAW's PREMISE hCar (`CarriedAt … (fa
a) rows`: Johnson/Desc/First/Close/Law/RowsAtK10.lean, Leads.lean) AT THE CONCRETE fa (`faK10`,
FaK10.lean) AND THE CLOSING's GROUP AT THE FULL SIZE, FROM THE TABLE's ITEM «carry» AS THE CLOSED
CONSTANT HAS IT (`K2Caller.carryAtZ`, Johnson/Top/H0/K2Caller/CarryClosed.lean) AT THE STATE
BEHIND**, under named premises; the second half of `CarriedAt` stays a premise. Theorems. It changes
no other file.

faK10's letter mW (the fresh mask's word) is a letter here too:
`FrontFitsAt` asks ONE clause of mW a (`fresh`, CarryAtFull.lean).

Who pays `fresh`: OpenWordFront.lean's `mWRaw_fresh` (off the raw columns) or `mWAt_fresh`.
  `wordsOf_congr`, `mWAt_congr`: the table's words and the term mWAt read of the strings the columns
    of the seats' trees alone.
  `carryAt_behind`: from carryAtZ Z lay m (z, s') y w: the row, the way in, the front and its frame
    are there (`carryAtZ_iff`); with `carryAt_full` (CarryAtFull.lean): CarryAt of the claim `rows`,
    where every such front carries `rows`.
  `hCar_of`: **carryAtZ Z lay m (z, s') y w · the row's five public equations · FrontFitsAt (at the
    word mW a) and fx.f.rows = rows at every row, way in, front and frame · the strings in front
    and behind agree on the members' seats' trees · the second half ⊢ CarriedAt RF N keep … L (faK10
    … mW z a) rows**, RF := groupFullLayK lo hlo gs hgs kb; general in mW.
Limits. EVERY PREMISE STANDS; NONE IS SHOWN AT A VALUE: the row's equations · FrontFitsAt (15
clauses) · «the front carries rows» · «the seats' trees stay» · THE SECOND HALF OF CarriedAt.
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.CarryAtFull
import Johnson.Desc.First.Link.Law.CarriedFirst
import Johnson.Desc.First.Close.Law.FaK10
import Johnson.Top.H0.K2Caller.CarryClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Iop IOR Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (wordsOf wordAt rowAt)
open VerifiableInference.Desc.First.K2Caller (SwRow carryAtZ carryAtZ_iff doorZ)
open VerifiableInference.Desc.First.Close (CarryAt SlotNames foldedAt groupFullLayK layAt sizesM
  sizesZ)

theorem wordsOf_congr {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {y y' : Strs}
    (h : ∀ i x, y.col (seat i).1 x = y'.col (seat i).1 x) :
    wordsOf G cs l seat y = wordsOf G cs l seat y' := by
  funext i pN
  have e : ∀ x, wordOf G y (seat i).1 (seat i).2 x = wordOf G y' (seat i).1 (seat i).2 x :=
    fun x => by
      unfold wordOf
      rw [h i x]
  rcases pN with x | x
  · funext r
    simp only [Sound.wordsOf, Sound.wordAt, e]
  · funext r
    simp only [Sound.wordsOf, Sound.wordAt, e]

theorem mWAt_congr (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
    (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
    (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
    (kp : {i // mem i} → Prop) [DecidablePred kp] {Xi : Type} (G : FileDescription Xi) {y y' : Strs}
    (seatF : ℕ × ℕ) (aF : ℕ) (h : ∀ x, y.col seatF.1 x = y'.col seatF.1 x) :
    mWAt cs l mem s e oM oZ hM hZ kp G y seatF aF =
      mWAt cs l mem s e oM oZ hM hZ kp G y' seatF aF := by
  unfold mWAt wordOf
  simp only [h]

/-- **FROM THE ITEM «carry» AT THE STATE BEHIND TO CarryAt.** -/
theorem carryAt_behind (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
    (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool) {Pz Wt : Type} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (a' : Pz × First.S) (y : Strs) (w : Wt) {Xi : Type}
    (G : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ) (no ix : {i // memMain lo i} → ℕ)
    (zw : (groupFullLayK lo hlo gs hgs kb).Sh.par.Cw.Word)
    (N : SlotNames (groupFullLayK lo hlo gs hgs kb)) (rows : SingleRows)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → r.cs = codesFull2 ∧ r.lo = lo ∧ r.g = gs ∧
      (∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) ∧ r.rad ≤ radFull)
    (hF : ∀ r t fx W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m a'.2 = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx → First.K2.frameAt fx = some W₀ →
      fx.f.rows = rows ∧
      FrontFitsAt codesFull2 lo (memMain lo) (stageOf gs 219) radFull
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        (hMFull lo hlo gs hgs 219) (hZFull lo hlo gs hgs 219) (fun a => kb a.1 = true) r.kept G
        seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) no ix zw N fx W₀)
    (hC : carryAtZ Z lay m a' y w) :
    CarryAt (groupFullLayK lo hlo gs hgs kb) N rows
      (foldedAt (groupFullLayK lo hlo gs hgs kb).Sh.par
        (readP ((stageOf gs 219).h + (stageOf gs 219).g) rows.gamma)
        ((groupFullLayK lo hlo gs hgs kb).Sh.rho.wd
          ((groupFullLayK lo hlo gs hgs kb).G.word (wordsOf G codesFull2 lo seat y))) zw) := by
  obtain ⟨r, t, h1, h2, hok, h3⟩ := (carryAtZ_iff Z lay m a' y w).1 hC
  obtain ⟨e1, e2, e3, e4, e5⟩ := hr r h1
  obtain ⟨fx, W₀, g1, g2, g3⟩ := carryAt_full lo hlo gs hgs kb r (r.ok_says hok) e1 e2 e3 e4 e5 G
    seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) _ no ix zw N
    (fun fx W₀ k1 k2 => (hF r t fx W₀ h1 h2 k1 k2).2) h3
  rw [(hF r t fx W₀ h1 h2 g1 g2).1] at g3
  exact g3

section AtFa
open OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb.Pv
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc.First.Close (CarriedAt faK10 SbV slV ZV)

/-- **hCar AT THE CONCRETE fa.** -/
theorem hCar_of (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
    (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool) {Xi : Type} (G : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ) (N : SlotNames (groupFullLayK lo hlo gs hgs kb))
    (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
    (pull : ((groupFullLayK lo hlo gs hgs kb).Sh.Cin.J → GE) →
      (groupFullLayK lo hlo gs hgs kb).G.C.J → GE) (n : ℕ)
    (num : (groupFullLayK lo hlo gs hgs kb).G.Row B ≃ Fin n)
    (fx : Fin (((groupFullLayK lo hlo gs hgs kb).Sh.fold (SbV (groupFullLayK lo hlo gs hgs kb) B)
      (slV (groupFullLayK lo hlo gs hgs kb) pull)
      (ZV (groupFullLayK lo hlo gs hgs kb) n num)).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep
      (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
      (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp).Msg × Wp))
    (bC bZ : ℕ) (w₀ : (sigOf codesFull2 lo).Wit × Wp)
    (w₁ : LdBrW (groupFullLayK lo hlo gs hgs kb).G ((groupFullLayK lo hlo gs hgs kb).sizeB keep
      (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
      (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp Wp)
    (L : List (BatFoldCaller GE)) {Pz Wt : Type}
    (smp : Pz × First.S → (i : Fin lo.length) → Option ((sigOf codesFull2 lo).om i).Smp)
    (σ₀ : (sigOf codesFull2 lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame} (Z : ProofFile.Pub)
    (lay : ByteArray) (m : ℕ) (z : Pz) (a : First.S × F.E.Str) (s' : First.S) (y : Strs) (w : Wt)
    (no ix : {i // memMain lo i} → ℕ)
    (mW : First.S × F.E.Str → (groupFullLayK lo hlo gs hgs kb).Sh.par.Cw.nat.Str)
    (rows : SingleRows)
    (hr : ∀ r, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → r.cs = codesFull2 ∧ r.lo = lo ∧ r.g = gs ∧
      (∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) ∧ r.rad ≤ radFull)
    (hF : ∀ r t fx' W₀, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r → doorZ Z m s' = some t →
      First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' → First.K2.frameAt fx' = some W₀ →
      fx'.f.rows = rows ∧
      FrontFitsAt codesFull2 lo (memMain lo) (stageOf gs 219) radFull
        (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
        (hMFull lo hlo gs hgs 219) (hZFull lo hlo gs hgs 219) (fun a => kb a.1 = true) r.kept G
        seat y (ProofFile.pAtK2 Z m) t (First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) no ix (mW a) N fx'
        W₀)
    (hy : ∀ i x, y.col (seat i).1 x = (strsOf F a.2).col (seat i).1 x)
    (hC : carryAtZ Z lay m (z, s') y w)
    (h2 : ∃ (zz : (ZV (groupFullLayK lo hlo gs hgs kb) n num).D)
      (v : ((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep
        (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
        (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp).Wit × Wp),
      (((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep
        (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
        (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp).over A₀).relR
        ((batX ((groupFullLayK lo hlo gs hgs kb).foldCaller keep
            (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
            (ZV (groupFullLayK lo hlo gs hgs kb) n num) fx A₀ bC bZ w₀ w₁)
          (faK10 G codesFull2 lo seat (groupFullLayK lo hlo gs hgs kb) N keep pull n num fx A₀ bC
            bZ w₀ w₁ L smp σ₀ st₀ e₀
            mW z a).1 zz).2,
          ((ldBrG (groupFullLayK lo hlo gs hgs kb).G ((groupFullLayK lo hlo gs hgs kb).sizeB keep
            (SbV (groupFullLayK lo hlo gs hgs kb) B) (slV (groupFullLayK lo hlo gs hgs kb) pull)
            (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp E₀).map
            (e₀, wordsOf G codesFull2 lo seat (strsOf F a.2))).2) v) :
    CarriedAt (groupFullLayK lo hlo gs hgs kb) N keep (SbV (groupFullLayK lo hlo gs hgs kb) B)
      (slV (groupFullLayK lo hlo gs hgs kb) pull) (ZV (groupFullLayK lo hlo gs hgs kb) n num) fx
      A₀ bC bZ w₀ w₁ L
      (faK10 G codesFull2 lo seat (groupFullLayK lo hlo gs hgs kb) N keep pull n num fx A₀ bC bZ
        w₀ w₁ L smp σ₀ st₀ e₀
        mW z a) rows := by
  have h1 := carryAt_behind lo hlo gs hgs kb Z lay m (z, s') y w G seat no ix (mW a) N rows hr hF
    hC
  rw [wordsOf_congr G codesFull2 lo seat hy] at h1
  exact carriedAt_of _ N keep _ _ _ fx A₀ bC bZ w₀ w₁ L _ rows h1 h2

end AtFa

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hCar_of
#print axioms VerifiableInference.Desc.LinkJoin.wordsOf_congr
#print axioms VerifiableInference.Desc.LinkJoin.mWAt_congr
#print axioms VerifiableInference.Desc.LinkJoin.carryAt_behind
