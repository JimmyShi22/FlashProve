-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsIdn.lean: THE ROAD's SENTENCE ON THE IDENTITIES (the letter idn of
Johnson/Road/K4/CloseFill.lean's filling: all identities of every norm at every position, at the
value's cells) GIVES, IN A GROUP THAT IS NOT THE FIRST, THE TWO CLAUSES `NormField` AND `EmbField`
(Johnson/Road/Rows/LayerTop.lean) AT THE INTEGERS OF "WHAT THE PROVER HIDES" (`Meaning.mgOf` of
`Meaning.ownOf`, Johnson/Goal/Meaning/HidOwn.lean, at the symbols that `Meaning.symAt` reads in the
messages as each segment reads them), at the filled pinned part. Theorems. No draw, no count.

CALLED: `sym_one` (Johnson/Road/K4/K4PinsSym.lean) · `Meaning.cell_ownAt`
(Johnson/Goal/Meaning/HidBase.lean: the cast of an entry of a witness's list IS `cellValS` of its
symbols at that cell, by the make: no premise on the packing) · `Plan4K.cells_eq`
(Johnson/Road/K4/ValueSeat.lean).

  `mats_raw`: under `Covers` the value's matrices are `PinPlan.raw`.
  `own_cast`: the casts of a witness's list, at all numbers: `cellValS` of its symbols inside the
    sizes, 0 outside.
  **`raw_own`**: THE FIRST HALF: under `SitsIn`, `SymsOne` at segment k, and "tl's size is s k":
    `PinPlan.raw tl` at the pinned part of w is the cast of segment k's own list.
  `ownW`: each segment's own list off a witness (the term that the table's authors' filling lays
    under `Meaning.hidOf`).
  `SeamIs`: THE SECOND HALF, AT A WITNESS, CELL BY CELL: the stream that comes into group g, as
    segment 2 g's own list has it (a kept copy), is the stream that goes out of group g - 1, as
    segment 2 (g - 1)'s own list has it (the owner's).
  `SeamFit`, **`seam_of_fit`**: `SeamIs` HOLDS OF EVERY WITNESS under conditions on public letters
    alone: the two entries have one size, radix and shift (`Meaning.sizeAt`: a Bool) · the two
    segments' seats name one message, row and place (`Meaning.SeatAt`) · every tenant of every group
    is a member's seat (`GroupsSeated`) · at each seat so named either group has just one tenant
    with that number (`namedOnce`: a Bool) and the place is no pad's place of either segment's own
    copy (`OffPad`). By `readAt_agree` (Johnson/Desc/Sound/ReadAt.lean), `Meaning.agreeAt_of_seat`,
    `Meaning.sameArrF` (Johnson/Goal/Meaning/HidFamily.lean), `Meaning.mzTot_same`
      (Johnson/Goal/Meaning/HidWord.lean).
  `mg_own`: under `SeamIs` the list of group g of "what the prover hides" is segment 2 g's own.
  `norm_of_idn`: the road's sentence gives `NormField` at any integers whose casts are the value's
    matrices.
  (`EmbField` holds for nothing in a group that is not the first: the library's `embField_later`,
    Johnson/Road/Rows/LayerDict.lean, called.)
  **`idn_fields`**: `NormField … (mgOf y (ownW …) p.g) Wi xx ∧ EmbField … `, at every Wi and xx,
    from: the road's sentence `plan.Idn (partOf … w)` · p.g ≠ 0 · "the section's table of scales is
    the public parameters'" · a group has four layers · `Covers` · `SitsIn` · `SymsOne` at segment 2
    p.g · "tl's size is s (2 p.g)" · `SeamFit`.

OBJECT: none of its own. USER: none yet; meant: whoever pays the line idn of `K4Lines`
(Johnson/Road/K4/CloseAtTable.lean) at a meaning whose field constr holds these two clauses at
every index that the decoded matrix holds. LETTERS, filled by nobody: those of K4PinsSym.lean; the
sizes s and the seats seat of all segments; the seat's letters.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE, AND WHO COULD PAY IT: `SymsOne`,
`SitsIn`, `Covers`, "tl's size is s (2 p.g)", `SeamFit`: runs on the plan: NONE HAS RUN. WHETHER THE
REAL PLAN MEETS `OffPad` AT THE SEAM IS NOT KNOWN TO US (the authors of `readAt` name it as owed).
THE FIRST GROUP IS NOT COVERED: there the identity on the embedding reads the request's tokens and
the committed matrix. ctx (the four items that K4's row reads) IS NOT SPENT: both sides read the
witness. That the table's item constr m idn says these two clauses at m = 2 p.g is its filler's
word. The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsSym
import Johnson.Road.K4.K4PinsPlanes
import Johnson.Goal.Meaning.HidBase
import Johnson.Goal.Meaning.HidFamily
import Johnson.Road.Rows.LayerDict

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Model.Verify (Public layerShape)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.Rows.Norms (castM NormField EmbField)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls cellJ szOf)
open VerifiableInference.Desc.Sound (Mem MsgT)
open Cb.Pv.Tail (Size cellValS)
open Inst.Model (Scl Mat)
open Inst.Model.FFSeg (Dim)

/-! ## 1 The value's matrices -/

/-- Under `Covers` the value's matrices are `PinPlan.raw`. -/
theorem mats_raw [scl : Scl] {Cells : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (hC : Covers tl nM nR nC) (X : Public)
    (p : Par) (hg : p.g < 12) (t : PinM Cells) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).mats t = A.raw tl t := by
  funext a r c
  show (if a < nM ∧ r < nR ∧ c < nC then A.raw tl t a r c else 0) = _
  by_cases hb : a < nM ∧ r < nR ∧ c < nC
  · rw [if_pos hb]
  · rw [if_neg hb]
    have e : cellJ (szOf tl) a r c = none := by
      cases hc : cellJ (szOf tl) a r c with
      | none => rfl
      | some j => exact absurd (hC a r c (by rw [hc]; rfl)) hb
    unfold PinPlan.raw
    rw [e]
    rfl

/-! ## 2 The first half: one segment's own list -/

/-- The casts of a witness's list, at all numbers. -/
theorem own_cast (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msg : Meaning.Msgs) (k a r c : ℕ) :
    ((Meaning.ownAt s seat msg k a r c : ℤ) : Cb.Gl.E) =
      ((cellJ (s k) a r c).map (cellValS (Meaning.symAt (s k) (seat k) msg))).getD 0 := by
  unfold cellJ
  by_cases h : a < (s k).NM ∧ c < (s k).k a ∧ r < (s k).m a
  · rw [dif_pos h]
    exact Meaning.cell_ownAt h.1 h.2.1 h.2.2
  · rw [dif_neg h]
    have e : Meaning.ownAt s seat msg k a r c = 0 := by
      unfold Meaning.ownAt Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
      by_cases h1 : a < (s k).NM
      · rw [dif_pos h1]
        by_cases h2 : c < (s k).k a
        · rw [dif_pos h2]
          by_cases h3 : r < (s k).m a
          · exact absurd ⟨h1, h2, h3⟩ h
          · rw [dif_neg h3]
        · rw [dif_neg h2]
      · rw [dif_neg h1]
    rw [e]
    exact Int.cast_zero

section
variable {Cells Tok : Type} (A : PinPlan Cells) (tl : HTailF2) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (N : Numbers) (m : ℕ) (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **THE FIRST HALF: the value's raw matrices are the casts of segment k's own list**, under
`SitsIn`, `SymsOne` at segment k, and "tl's size is s k". -/
theorem raw_own (k : ℕ) (hσ : szOf tl = s k)
    (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m)
    (h1 : SymsOne A tl arr N k (s k) (seat k)) (w : Wit Cells Tok MsgT) :
    A.raw tl (partOf A.D.codes arr ms N m w) =
      castM (Meaning.ownAt s seat (VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w)
        k) := by
  funext a r c
  show _ = ((Meaning.ownAt s seat _ k a r c : ℤ) : Cb.Gl.E)
  rw [own_cast]
  have gen : ∀ σ : Size, σ = s k →
      ((cellJ σ a r c).map (cellValS fun (μ : Fin σ.NM) (i : Fin (Alg.symRows (σ.m μ)))
        (c' : Fin (σ.k μ)) =>
          symU A tl (partOf A.D.codes arr ms N m w) μ.val i.val c'.val)).getD 0 =
      ((cellJ (s k) a r c).map (cellValS (Meaning.symAt (s k) (seat k)
        (VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w)))).getD 0 := by
    intro σ e
    subst e
    have es : (fun (μ : Fin (s k).NM) (i : Fin (Alg.symRows ((s k).m μ)))
        (c' : Fin ((s k).k μ)) =>
          symU A tl (partOf A.D.codes arr ms N m w) μ.val i.val c'.val) =
        Meaning.symAt (s k) (seat k)
          (VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w) :=
      funext fun μ => funext fun i => funext fun c' =>
        sym_one A tl arr ms N m k (s k) (seat k) hs h1 w μ i c'
    rw [es]
  exact gen (szOf tl) hσ

/-! ## 3 The second half: the seam -/

/-- Each segment's own list, off a witness. -/
def ownW (cs : OnBytes.Codes) (w : Wit Cells Tok MsgT) : ℕ → Mats ℤ :=
  Meaning.ownOf s fun k =>
    Meaning.symAt (s k) (seat k) (VerifiableInference.Desc.Sound.readAt cs arr ms N k w)

/-- **THE SECOND HALF, cell by cell**: the kept copy against the owner's array. -/
def SeamIs (cs : OnBytes.Codes) (y : Lay) (g : ℕ) (w : Wit Cells Tok MsgT) : Prop :=
  ∀ r c, ownW arr ms N s seat cs w (2 * (g - 1)) (matIx y).iXO r c =
    ownW arr ms N s seat cs w (2 * g) (matIx y).iXI r c

/-- Under `SeamIs` the list of group g of "what the prover hides" is segment 2 g's own. -/
theorem mg_own (cs : OnBytes.Codes) (y : Lay) (g : ℕ) (w : Wit Cells Tok MsgT)
    (h : SeamIs arr ms N s seat cs y g w) :
    Meaning.mgOf y (ownW arr ms N s seat cs w) g = ownW arr ms N s seat cs w (2 * g) := by
  funext a
  unfold Meaning.mgOf
  by_cases ha : a = (matIx y).iXI ∧ 0 < g
  · rw [if_pos ha, ha.1]
    exact funext fun r => funext fun c => h r c
  · rw [if_neg ha]

end

/-! ## 4 The second half, from conditions on public letters -/

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (s : ℕ → Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **Conditions on public letters alone**, at the pair (the stream that comes into group g, in
segment 2 g · the stream that goes out of group g - 1, in segment 2 (g - 1)). -/
structure SeamFit (cs : OnBytes.Codes) (y : Lay) (g : ℕ) : Prop where
  /-- both are entries of their lists, of one size, radix and shift: a Bool -/
  sizes : Meaning.sizeAt (s (2 * g)) (s (2 * (g - 1))) (matIx y).iXI (matIx y).iXO = true
  /-- the two segments' seats name one message, row and place -/
  seats : Meaning.SeatAt (s (2 * g)) (s (2 * (g - 1))) (seat (2 * g)) (seat (2 * (g - 1)))
    (matIx y).iXI (matIx y).iXO
  /-- every tenant of every group is a member's seat -/
  seated : VerifiableInference.Desc.Sound.GroupsSeated ms N
  /-- at each seat so named: either group has just one tenant with that number, and the place is no
  pad's place of either segment's own copy -/
  each : ∀ (h : (matIx y).iXI < (s (2 * g)).NM), ∀ i < Alg.symRows ((s (2 * g)).m (matIx y).iXI),
    ∀ c < (s (2 * g)).k (matIx y).iXI,
      VerifiableInference.Desc.Sound.namedOnce arr N (2 * g)
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).1 = true ∧
      VerifiableInference.Desc.Sound.namedOnce arr N (2 * (g - 1))
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).1 = true ∧
      VerifiableInference.Desc.Sound.OffPad cs arr ms N (2 * g)
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).1 (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).2.1
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).2.2 ∧
      VerifiableInference.Desc.Sound.OffPad cs arr ms N (2 * (g - 1))
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).1 (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).2.1
        (seat (2 * g) ⟨(matIx y).iXI, h⟩ i c).2.2

/-- **THE SECOND HALF HOLDS OF EVERY WITNESS**, under `SeamFit`. -/
theorem seam_of_fit (cs : OnBytes.Codes) (y : Lay) (g : ℕ) (F : SeamFit arr ms N s seat cs y g)
    (w : Wit Cells Tok MsgT) : SeamIs arr ms N s seat cs y g w := fun r c =>
  (Meaning.mzTot_same (Meaning.sameArrF F.sizes (Meaning.agreeAt_of_seat F.seats
    fun h i hi c' hc' =>
      VerifiableInference.Desc.Sound.readAt_agree cs arr ms N (2 * g) (2 * (g - 1)) _ _ _ w
        (F.each h i hi c' hc').1 (F.each h i hi c' hc').2.1 F.seated (F.each h i hi c' hc').2.2.1
        (F.each h i hi c' hc').2.2.2)) r c).symm

end

/-! ## 5 The two clauses -/

/-- **The road's sentence gives `NormField`**, at any integers whose casts are the value's matrices,
where the section's table of scales is the public parameters' and a group has four layers. -/
theorem norm_of_idn [scl : Scl] {M : Type} (U : RefSeat M VerifiableInference.Desc.First.S)
    (X : Public) (p : Par) (hg : p.g < 12) (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4)
    (t : M) (Mz : Mats ℤ) (hM : (U.atRec X p hg).mats t = castM Mz)
    (hI : (U.atRec X p hg).plan.Idn t) (Wi : Mat) (xx : Cm.Seg.XI) :
    NormField (layerShape X.P) X.layers.sc U.y p.g Mz Wi xx := by
  have hsc : scl = sclOf (layerShape X.P) X.layers.sc p.g 4 := by
    rw [hscl, ← hlam]
  intro k ν i hv
  obtain ⟨_, hν, hi⟩ := hv
  have h0 := hI (k, ⟨ν, hν⟩) i hi
  rw [Plan4K.cells_eq _ t (fun _ _ _ hb => if_neg hb), hM] at h0
  subst hsc
  exact h0

/-- **THE ROAD's SENTENCE ON THE IDENTITIES GIVES THE TWO CLAUSES AT "WHAT THE PROVER HIDES"**, in a
group that is not the first: from "the section's table of scales is the public parameters'", a group
  has four
layers, `Covers`, `SitsIn`, "tl's size is s (2 p.g)", `SymsOne` at segment 2 p.g, and `SeamFit`:
EVERY ONE OF THESE BUT THE FIRST A CONDITION ON PUBLIC LETTERS. -/
theorem idn_fields [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
    (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4) (hg0 : p.g ≠ 0)
    (hC : Covers tl nM nR nC) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)
    (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hσ : szOf tl = s (2 * p.g))
    (h1 : SymsOne A tl arr N (2 * p.g) (s (2 * p.g)) (seat (2 * p.g))) (w : Wit Cells Tok MsgT)
    (F : SeamFit arr ms N s seat A.D.codes y p.g)
    (hI : ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.Idn
      (partOf A.D.codes arr ms N m w)) (Wi : Mat) (xx : Cm.Seg.XI) :
    NormField (layerShape X.P) X.layers.sc y p.g
        (Meaning.mgOf y (ownW arr ms N s seat A.D.codes w) p.g) Wi xx ∧
      EmbField (layerShape X.P) X.layers.sc y p.g
        (Meaning.mgOf y (ownW arr ms N s seat A.D.codes w) p.g) Wi xx := by
  refine ⟨norm_of_idn (A.seatN n N tl y nM nR nC n0 ns nx v7) X p hg hscl hlam _ _ ?_ hI Wi xx,
    OnBytes.Road.Rows.Norms.embField_later _ _ _ _ _ _ _ hg0⟩
  rw [mats_raw A n N tl y nM nR nC n0 ns nx v7 hC X p hg,
    raw_own A tl arr ms N m s seat (2 * p.g) hσ hs h1 w,
    mg_own arr ms N s seat A.D.codes y p.g w (seam_of_fit arr ms N s seat A.D.codes y p.g F w)]
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.mats_raw
#print axioms OnBytes.Road.K4.own_cast
#print axioms OnBytes.Road.K4.raw_own
#print axioms OnBytes.Road.K4.mg_own
#print axioms OnBytes.Road.K4.seam_of_fit
#print axioms OnBytes.Road.K4.norm_of_idn
#print axioms OnBytes.Road.K4.idn_fields
