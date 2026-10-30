-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GroupSub.lean (kind K10): THE TYPED GROUP, THE TYPED STAGE's PREMISES
AND K10's LAW AT THE MAKER's PIECE, AT ANY LIST WHOSE ENTRIES STAND ON THE WRITTEN LISTS OF THE FULL
SIZE: not at the 26 written lists alone. Definitions, statements and proofs.

Why. `k10_law_full_lay` (KindK10LawLay.lean, beside this file) stands at a list lo ∈ `linksFullLit`.
At link 0 the written list has six messages, the group five: the index masks' message has no main
row; it is in the signature `sigOf codesFull2 lo` and no member. The proved batching hands on every
message that is no member (`Cb.Pv.Bat.Size.kp`), so what stands behind the closing (`CarriedAt`,
Leads.lean) asks a witness for that message's word: which the table's relation behind the closing
does not hold, and by the table's own text need not. At the list WITHOUT that message every message
is a member. That list is on no written list.
What makes it light. The payers of the typed stage's premises (GroupFull.lean, AtFull.lean,
Corners.lean) spend "lo is a written list" entry by entry alone: `links_fit` and `tablesFull_ok`
(Johnson/G/) speak of every entry of every written list.
  `Written lo`: every entry of lo stands on a written list. `written_of_mem`: a written list is so.
    `written_filter`: a part of such a list is so.
  `hMSub`, `hZSub`, `sub_fit`, `sub_len`: the entries' codes are the stage's; each fits.
    `groupSubAt`: the group at any corners and any kept members; `groupSub`: at the program's own
    layout for the flags kb; `groupSub_eq`: it IS `groupLayK` (CubeOfShapes.lean) at the full size's
    letters: by definition.
  `sub_stage`, `sub_radius_eq`, `sub_inJ`, `sub_counts`, `sub_radius`, `sub_fits`, `sub_fix`,
    `sub_pulls`, `sub_good`, `sub_good_of_corners`: the likes of GroupFull.lean's, AtFull.lean's and
    Corners.lean's.
  `k10_law_sub`: `k10_law_full_lay`'s end at `groupSub`, from the test on the corners (`Corners`) in
    place of "gs.k = kLay lo kb".
Limits. hQ is a premise, as there. `Corners` at a list that is not written is a premise: a closed
test. Nothing is said of link 0's five-list here. This file rests, through GroupFull.lean, on the
files under ThirdParty/ (lean/LIMITS.md, L15). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.KindK10LawLay
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- Every entry of the list stands on a written list of the full size. -/
def Written (lo : List (OracleShape × ℕ)) : Prop := ∀ x ∈ lo, ∃ l ∈ linksFullLit, x ∈ l

theorem written_of_mem {lo : List (OracleShape × ℕ)} (h : lo ∈ linksFullLit) : Written lo :=
  fun _ hx => ⟨lo, h, hx⟩

theorem written_filter {lo : List (OracleShape × ℕ)} (h : Written lo)
    (p : OracleShape × ℕ → Bool) : Written (lo.filter p) :=
  fun x hx => h x (List.mem_filter.1 hx).1

section
variable (lo : List (OracleShape × ℕ)) (hen : Written lo) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

include hen hgs in
theorem hMSub : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
    cMain codesFull2 (lo.get i).1 = (stageOf gs 219).C := fun i k _ => by
  obtain ⟨l, hl, hx⟩ := hen _ (List.get_mem lo i)
  exact ((tablesFull_ok gs hgs).2 l hl (lo.get i) hx k).1

include hen hgs in
theorem hZSub : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
    cMask codesFull2 (lo.get i).1 = (stageOf gs 219).Z := fun i k => by
  obtain ⟨l, hl, hx⟩ := hen _ (List.get_mem lo i)
  exact ((tablesFull_ok gs hgs).2 l hl (lo.get i) hx k).2

include hen in
theorem sub_fit (i : Fin lo.length) :
    MemberFits codesFull2 logFull radFull distFull (lo.get i).1 (lo.get i).2 := by
  obtain ⟨l, hl, hx⟩ := hen _ (List.get_mem lo i)
  exact links_fit l hl (lo.get i) hx

/-- The group's data at such a list. -/
noncomputable abbrev rowsAtSub : Rows (sigOf codesFull2 lo) :=
  rowsPort codesFull2 lo (memMain lo) (stageOf gs 219) radFull oM oZ (hMSub lo hen gs hgs)
    (hZSub lo hen gs hgs)

/-- The group at any corners, whole members kept. -/
noncomputable abbrev groupSubAt : RowsK (sigOf codesFull2 lo) :=
  (rowsAtSub lo hen gs hgs oM oZ).keep kp

theorem sub_stage : (placeFull gs.k).s = (groupSubAt lo hen gs hgs oM oZ kp).s :=
  (frontFull_place gs hgs).2

theorem sub_radius_eq : (placeFull gs.k).e = (groupSubAt lo hen gs hgs oM oZ kp).e := rfl

theorem sub_inJ : InJ (groupSubAt lo hen gs hgs oM oZ kp).s (groupSubAt lo hen gs hgs oM oZ kp).e :=
  place_inJ _ _ (placeFull_good gs hgs) (sub_stage lo hen gs hgs oM oZ kp)
    (sub_radius_eq lo hen gs hgs oM oZ kp)

theorem sub_counts : CountsAt (groupSubAt lo hen gs hgs oM oZ kp).s
    (groupSubAt lo hen gs hgs oM oZ kp).e (placeFull gs.k).bC (placeFull gs.k).bZ :=
  place_counts _ _ (placeFull_good gs hgs) (sub_stage lo hen gs hgs oM oZ kp)
    (sub_radius_eq lo hen gs hgs oM oZ kp)

theorem sub_radius : (groupSubAt lo hen gs hgs oM oZ kp).G.e <
    (groupSubAt lo hen gs hgs oM oZ kp).s.d :=
  place_radius _ _ (placeFull_good gs hgs) (sub_stage lo hen gs hgs oM oZ kp)
    (sub_radius_eq lo hen gs hgs oM oZ kp)

include hen hgs in
theorem sub_len (i : Fin lo.length) : aOf codesFull2 (lo.get i).1 ≤ (stageOf gs 219).C.a := by
  show aOf codesFull2 (lo.get i).1 ≤ (stageOf gs 0).C.a
  rw [(tablesFull_ok gs hgs).1]
  exact (sub_fit lo hen i).le

theorem sub_fits : (groupSubAt lo hen gs hgs oM oZ kp).G.Fits :=
  rowsPort_fits codesFull2 lo (memMain lo) (stageOf gs 219) radFull oM oZ _ _
    (fun i _ => sub_len lo hen gs hgs i)
    (fun i _ => by
      show radFull ≤ 2 ^ ((stageOf gs 0).C.a - _) * _ + (2 ^ ((stageOf gs 0).C.a - _) - 1)
      rw [(tablesFull_ok gs hgs).1]
      exact (sub_fit lo hen i).near)

theorem sub_fix (a) : ((groupSubAt lo hen gs hgs oM oZ kp).view a).Fix
    (groupSubAt lo hen gs hgs oM oZ kp).G.e :=
  membPort_fix codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219) (oM a.1) (oZ a.1)
    (hMSub lo hen gs hgs a.1 a.2) (hZSub lo hen gs hgs a.1 a.2)
    (sub_len lo hen gs hgs a.1) _

theorem sub_pulls : Pulls (groupSubAt lo hen gs hgs oM oZ kp)
    (pullOf (groupSubAt lo hen gs hgs oM oZ kp)) :=
  pulls_keep (rowsAtSub lo hen gs hgs oM oZ) kp fun a =>
    membPort_onto codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219) (oM a.1) (oZ a.1)
      (hMSub lo hen gs hgs a.1 a.2) (hZSub lo hen gs hgs a.1 a.2)

/-- The group's data are in order, from four conditions on where the rows stand. -/
theorem sub_good
    (fitM : ∀ r, ¬ kp r.1 → (rowsAtSub lo hen gs hgs oM oZ).atM r <
      2 ^ ((stageOf gs 219).h + (stageOf gs 219).g))
    (injM : ∀ r r', ¬ kp r.1 → ¬ kp r'.1 → (rowsAtSub lo hen gs hgs oM oZ).atM r =
      (rowsAtSub lo hen gs hgs oM oZ).atM r' → r = r')
    (fitZ : ∀ r, (rowsAtSub lo hen gs hgs oM oZ).atZ r < 2 ^ (stageOf gs 219).h)
    (injZ : Function.Injective (rowsAtSub lo hen gs hgs oM oZ).atZ) :
    (groupSubAt lo hen gs hgs oM oZ kp).Good :=
  Rows.keep_good _ kp
    { sized := by
        have h := (Johnson.Bridge.FoldedPlace.stageJ (placeFull_good gs hgs)).sized
        rw [(frontFull_place gs hgs).2] at h
        exact h
      view := fun a => membPort_laws codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219)
        (oM a.1) (oZ a.1) (hMSub lo hen gs hgs a.1 a.2) (hZSub lo hen gs hgs a.1 a.2)
        (sub_len lo hen gs hgs a.1)
      fitM := fitM
      injM := injM
      fitZ := fitZ
      injZ := injZ
      one := by
        show 1 ≤ (stageOf gs 219).h + (stageOf gs 219).g
        rw [← (frontFull_place gs hgs).2]
        show 1 ≤ 0 + gs.k
        rcases (frontFull_place gs hgs).1 with h | h <;> omega }

end

section
variable (lo : List (OracleShape × ℕ)) (hen : Written lo) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ) (kb : Fin lo.length → Bool)

/-- **The group's data are in order at every layout that passes the test on the corners.** -/
theorem sub_good_of_corners (h : Corners lo gs.k oM oZ kb) :
    (groupSubAt lo hen gs hgs oM oZ fun a => kb a.1 = true).Good := by
  obtain ⟨c1, c2, c3, c4⟩ := h
  have e : (stageOf gs 219).h + (stageOf gs 219).g = gs.k := by
    rw [← (frontFull_place gs hgs).2]
    show 0 + gs.k = gs.k
    omega
  have e0 : (stageOf gs 219).h = 0 := by
    rw [← (frontFull_place gs hgs).2]
    rfl
  refine sub_good lo hen gs hgs _ _ _ (fun r hr => ?_) (fun r r' hr hr' k => ?_) (fun r => ?_)
    fun r r' k => ?_
  · rw [e]
    have h1 := c1 r.1.1 r.1.2 (by simpa using hr)
    have h2 : r.2.val < (lo.get r.1.1).1.mainRows := r.2.isLt
    show oM r.1.1 + r.2.val < 2 ^ gs.k
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.mainRows)
      (fun a => oM a.1) (fun a => kb a.1 = false)
      (fun a b ha hb hab => c2 a.1 b.1 a.2 b.2 ha hb fun q => hab (Subtype.ext q)) r r'
      (by simpa using hr) (by simpa using hr') k
  · rw [e0]
    have h1 := c3 r.1.1 r.1.2
    have h2 : r.2.val < (lo.get r.1.1).1.maskRows := r.2.isLt
    show oZ r.1.1 + r.2.val < 2 ^ 0
    omega
  · exact apart_inj_on (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.maskRows)
      (fun a => oZ a.1) (fun _ => True)
      (fun a b _ _ hab => c4 a.1 b.1 a.2 b.2 fun q => hab (Subtype.ext q)) r r' trivial trivial k

/-- The group at the program's own layout for the flags kb. -/
noncomputable abbrev groupSub : RowsK (sigOf codesFull2 lo) :=
  groupSubAt lo hen gs hgs (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
    fun a => kb a.1 = true

/-- It is `groupLayK` at the full size's letters. -/
theorem groupSub_eq : groupSub lo hen gs hgs kb =
    groupLayK codesFull2 lo (stageOf gs 219) radFull kb (hMSub lo hen gs hgs)
      (hZSub lo hen gs hgs) := rfl

end

variable (lo : List (OracleShape × ℕ)) (hen : Written lo) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupSub lo hen gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupSub lo hen gs hgs kb).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupSub lo hen gs hgs kb).sizeB keep
    (SbV (groupSub lo hen gs hgs kb) B)
    (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
    (ZV (groupSub lo hen gs hgs kb) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSub lo hen gs hgs kb).G ((groupSub lo hen gs hgs kb).sizeB keep
    (SbV (groupSub lo hen gs hgs kb) B)
    (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
    (ZV (groupSub lo hen gs hgs kb) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the real group. -/
local notation "CK" => (groupSub lo hen gs hgs kb).foldCaller keep
  (SbV (groupSub lo hen gs hgs kb) B)
  (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
  (ZV (groupSub lo hen gs hgs kb) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁

/-- **THE LAW AT THE MAKER's PIECE, AT A LIST OF WRITTEN ENTRIES.** -/
theorem k10_law_sub
    (hC : Corners lo gs.k (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
      kb) (N : SlotNames RF)
    {Pz : Type} (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd (CK) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd (CK) dB dE dR (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1 Cl)
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ) (x : Rest (ckP .two) F (Pz × S1) W (dB :: dE :: List.replicate (Yc (CK)).k dR))
    (hcap : x.err = Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR)))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → W → W)
    (fa : Pz → S1 × F.E.Str → ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str)
    {na nb : String} (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n))
    (Rin Rout : (Pz × S1) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base dB dE dR (Yc (CK)).k
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc (CK)).k dR)))).ior.red.out a τ = some a' →
      K10EndS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR))) (fa z) a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) [] x).withMap e).ext
          ((z, a.1), a.2) τ w)) :
    ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) [] x).withMap e).GoodIn
      (fun a => K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  k10_law_withMap RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁
    L dB dE dR ρ hρ (caller_step RF keep _ _ _ A₀ _ _ w₀ w₁)
    (caller_pick RF keep _ _ _ A₀ _ _ w₀ w₁) (sub_fits lo hen gs hgs _ _ _)
    (sub_good_of_corners lo hen gs hgs _ _ kb hC)
    (sub_inJ lo hen gs hgs _ _ _) (sub_counts lo hen gs hgs _ _ _)
    (sub_radius lo hen gs hgs _ _ _) (sub_fix lo hen gs hgs _ _ _)
    (sub_pulls lo hen gs hgs _ _ _) pS Pr b H base x hcap e fa (placeFull gs.k)
    (placeFull_paid gs hgs) (sub_stage lo hen gs hgs _ _ _)
    (sub_radius_eq lo hen gs hgs _ _ _) le_rfl le_rfl iE iR (batFull gs.k n)
    (batFull_paid gs.k n hn57) (sub_stage lo hen gs hgs _ _ _)
    (sub_radius_eq lo hen gs hgs _ _ _) le_rfl iB Rin Rout hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.written_of_mem
#print axioms VerifiableInference.Desc.First.Close.written_filter
#print axioms VerifiableInference.Desc.First.Close.hMSub
#print axioms VerifiableInference.Desc.First.Close.hZSub
#print axioms VerifiableInference.Desc.First.Close.sub_fit
#print axioms VerifiableInference.Desc.First.Close.sub_stage
#print axioms VerifiableInference.Desc.First.Close.sub_radius_eq
#print axioms VerifiableInference.Desc.First.Close.sub_inJ
#print axioms VerifiableInference.Desc.First.Close.sub_counts
#print axioms VerifiableInference.Desc.First.Close.sub_radius
#print axioms VerifiableInference.Desc.First.Close.sub_len
#print axioms VerifiableInference.Desc.First.Close.sub_fits
#print axioms VerifiableInference.Desc.First.Close.sub_fix
#print axioms VerifiableInference.Desc.First.Close.sub_pulls
#print axioms VerifiableInference.Desc.First.Close.sub_good
#print axioms VerifiableInference.Desc.First.Close.sub_good_of_corners
#print axioms VerifiableInference.Desc.First.Close.groupSub_eq
#print axioms VerifiableInference.Desc.First.Close.k10_law_sub
