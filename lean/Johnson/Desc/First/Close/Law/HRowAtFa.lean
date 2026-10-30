-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/HRowAtFa.lean (kind K10): THE PREMISE hRow OF k10_hQ_beside
(HQBeside.lean, beside this file), IN ITS VERY FORM, AT THE CONCRETE fa (`faK10`), THE WRITTEN
LIST's
TYPED GROUP AND A MEANING WHOSE LETTER "row" IS THE RULED LAYER's. An assembly: k10_rows_at_cube
(RowsAtCube.lean) with wordsAre_of_pins (WordsAtFa.lean) in hW's place. A structure, a
statement and its proof.

What is said.
  `RowAsks .. z a`: WHAT THE ROWS' PART ASKS OF THE STATEMENT IN FRONT, eleven named fields: the
    statement is in order · the public ties (CubeFits, NamesFit) at the begun statement · the slots'
    names lie within the tables · the frame's group is the table's number · the promise's rowsHeld
    and membersHeld at the open set O · no two messages have one place in the book · the codes · the
    book places message no i at the plan's seat of member i · ShapesAre.
  `k10_hRow`: **hRow, IN ITS VERY FORM**: every item "row m c" that the closing's row closes holds
in
    front at the extractor's value.

PREMISES, by sort.
  on letters: hR (R is the written list's typed group) · hg (R.Good) · hPr (the place's k is the
    stage's) · hrow (the meaning's letter "row" is rowSays Nu (wordsAtFirst arr): at the composed
    meaning by definition) · hO (what the row closes of rows is open in O) · hP (a moment's samples
    are open only with that moment's pin).
  on the statement in front, under X: hX : RowAsks.
  across the step, under X, the law's condition, its end and the relation behind: hCar (CarriedAt:
    left to other files of K10's) · hpin (every member with a main row is pinned in front at the
    extractor's value: at a kept member: `pin_kept_behind`, PinKeptBack.lean; the whole: `k10_hpin`,
    HpinAtTable.lean, with a letter smpD inside fa, which spends hCar's like (`CarriedAt`, with smpD
    inside fa) and hV (`SameVal`): each under its own premises).

Limits. BOOK-KEEPING: NO PREMISE IS DISCHARGED THAT THE TWO THEOREMS ASK; they are gathered and
named.
NOTHING IS SHOWN OF ANY STATE. Nothing on the pins' part hPin. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.WordsAtFa
import Johnson.Desc.First.Close.Law.RowsAtCube
import Johnson.Desc.First.Close.Law.HQBeside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open OnBytes.Means (InOrder tableSize)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowsHeld membersHeld PlacesApart
  rowSays wordsAtFirst)

variable {Xi : Type} (Gd : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (s : Sg) (e' : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))

local notation "S1" => VerifiableInference.Desc.First.S

/-- The typed stage's caller. -/
local notation "cK10" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

/-- **WHAT THE ROWS' PART ASKS OF THE STATEMENT IN FRONT.** -/
structure RowAsks (Nu : Numbers) (m : ℕ) (O : List Item) (no : Fin lo.length → ℕ) (a : S1) :
    Prop where
  inOrder : InOrder (rdK a).2.2
  ties : ∀ G lay, (rdK a).2.2.groups[(rdK a).2.1.group]? = some G →
    (begun (rdK a).2.2 (rdK a).2.1.group G).layout (rdK a).2.1.group = some lay →
    CubeFits R (begun (rdK a).2.2 (rdK a).2.1.group G) lay (fun b => no b.1) ∧
      NamesFit R N (begun (rdK a).2.2 (rdK a).2.1.group G) lay fun b => no b.1
  names : ∀ G, (rdK a).2.2.groups[(rdK a).2.1.group]? = some G → ∀ q x,
    N.orc q < (begun (rdK a).2.2 (rdK a).2.1.group G).oracles.size ∧
      N.idx q x < tableSize (begun (rdK a).2.2 (rdK a).2.1.group G) (N.orc q) .main
  grp : (rdK a).2.1.group = Nu.groupAt m
  rows : rowsHeld Nu O a = true
  members : membersHeld Nu O a = true
  apart : PlacesApart a
  codes : a.st.codes = cs
  seats : ∀ i, memMain lo i → seatBy noFirst a.book (no i) = some (seat i)
  shapes : ∀ Gr, (rdK a).2.2.groups[(rdK a).2.1.group]? = some Gr →
    ShapesAre (rdK a).2.2 Gr lo kb no

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **hRow OF k10_hQ_beside, IN ITS VERY FORM.** -/
theorem k10_hRow (hR : R = groupLayK cs lo s e' kb hM hZ) (hg : R.Good) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (hPr : Pr.k = R.s.h + R.s.g) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (X : (Pz × S1) × F.E.Str → Prop) (O : List Item) (no : Fin lo.length → ℕ)
    (hrow : Mg.row = rowSays Nu (wordsAtFirst arr))
    (hO : ∀ c, insQ links ps k (Item.row m c) → Item.row m c ∈ O)
    (hP : ∀ t, Item.row m (.sample t) ∈ O → t < 3 ∧ Item.pin m t ∈ O)
    (hX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → RowAsks cs lo seat kb R N Nu m O no a.1)
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L
          (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a) (rdBK a'.1).1.rows)
    (hpin : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ i, memMain lo i → PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1)
          (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)) :
    ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ c, insQ links ps k (Item.row m c) →
          Mg.row m c (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w) := by
  intro z a a' hx hon hend w hw c hc
  have A := hX z a hx
  rw [hrow]
  exact k10_rows_at_cube R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base _ _ _ a a' hend
    hPr A.inOrder hg (fun b => no b.1) A.ties A.names (hCar z a a' hx hon hend w hw) (fun _ => 0)
    Nu (wordsAtFirst arr) z (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)
    (wordsAre_of_pins Gd cs lo seat s e' kb hM hZ R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀
      st₀ e₀ mW hR arr z a no (fun _ => 0) _ A.codes A.seats A.shapes
      (hpin z a a' hx hon hend w hw))
    m A.grp O A.rows A.members A.apart hP c (hO c hc)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_hRow
