-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsAtWide.lean: SEVEN OF THE TEN FIELDS THAT THE ASSEMBLY OF K4's LAW LEAVES AT A
LATER GROUP (its structure `K4LaterAt`), OR THEIR PARTS, AT THE DATA OFF THE WIDER MEANING's OWN
PARAMETERS (`k4DataWide 𝔇 E Mg₀`, Johnson/Road/K4/K4MeansAtWide.lean; `MgData`,
Johnson/Desc/Sound/MgAll.lean; `WideData`, Johnson/Desc/Sound/MgWide.lean): WHAT HOLDS BY THE MAKE
OF THAT TERM, WHAT AT A NAMED EQUATION ON ONE OF ITS PARAMETERS; AND A TEST WITH CODE FOR THE TIES
OF THE INDEX MASKS' MESSAGE. By unfolding, and calls. No draw, no count.

  `group_at`: X.p4 = true → 2 * g / stepOf X = g.
  **`ties_wide`**: `MeansTies (k4DataWide 𝔇 E Mg₀) p m xL sz seat Stored.entries`, from `WorthTies`
    and the equation on what 𝔇.H reads off a witness: its fields sent, arr, msg hold BY THE MAKE:
    the term's data for the lookup bear the term's own codes and arr; its oracle message for the
    committed table is fixed (`k3StoredAt`).
  `nr_wide`, `nc_wide`, `encIs_wide`: there the lookup's numbers of rows and columns are the term's;
    the value's reader of the committed matrix is `rcQ`.
  `rides_wide`: `RecRides`, from 𝔇.smp = `smpNamed 𝔇.cs seats` and "the decoder does not read the
    verifier's state".
  `m0_wide`, `lk_wide`: the layout's numbers of rows and column bits are the reference ones, from
    𝔇.d1.lay = X.layers.wsLay, `RefPub` and the group's plan: `m0_ref`,
    `lk_ref` (Johnson/Road/K4/WsLayRef.lean), called.
  `rwMat_wide`: the reader of the pile of pending rows has the matrix off the witness's cells, from
    𝔇.mat13 = `matOfCells nR kCol`.
  `indexTieB`, **`indexTie_of_B`**: THE TEST: the list of shapes has a shape sh at the index masks'
    number · the list of seats has `N.index` there · a member of ms sits at `N.index` and has the
    shape sh · sh has a mask row · n entries fit its mask rows. A yes gives these, and `IndexFit` at
    `posFree sh.maskRows` (Johnson/Road/K4/K4PinsIndexAt.lean). `indexTieB_nil`: it can fail.

STANDS OVER MgAll.lean · MgWide.lean · K3LettersAt | K3StoredThree · SmpNamed.lean · MatOfCells.lean
· K4MeansAtWide.lean · WsLayRef.lean, which stand in this tree.

OBJECT: `k4DataWide 𝔇 E Mg₀`. USER: Johnson/Road/K4/K4PinsLaterAtWide.lean; meant: the assembly of
K4's law at the wider meaning. LETTERS: 𝔇, E, Mg₀, p, m, xL, sz, seat, z, seats, g, hp: free.

Limits. K04_law IS NOT PROVED BY THIS. EVERY NAMED EQUATION ON A PARAMETER, `WorthTies`, `RefPub`,
`NoRec` STAY PREMISES: that the wider meaning is laid at parameters that meet them is its authors'
word. BY ITS AUTHORS' OWN WARNING THE WIDER MEANING IS ONE SIDE OF A BRIDGE: a law shown at it
counts only when the bridge to the meaning that counts is paid. `indexTieB` IS EVALUATED NOWHERE IN
THIS FILE; at the written values Lean's kernel decides it at the twelve groups (`indexTie_written`,
Johnson/Road/K4/K4PinsWrittenNext.lean). IT WILL TURN WHEN `MgData`, `WideData` OR `k4DataWide`
TURNS.
-/
import Johnson.Road.K4.K4MeansAtWide
import Johnson.Road.K4.K4PinsOfMeans
import Johnson.Road.K4.K4PinsConduit
import Johnson.Road.K4.K4PinsIndexAt
import Johnson.Road.K4.WsLayRef
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.K13.Law.MatOfCells
import Johnson.Desc.First.Look.K3CallerLayTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.First.Look (stepOf Stored.entries Stored.NoRec)
open VerifiableInference.Desc.Sound (MsgT Mem seatOf MgData WideData smpNamed smpNamed_same)
open VerifiableInference.Desc.K13.Law (matOfCells)
open Inst.Model.Layout (kRef hRef)
open Cb.Pv.Tail (Size)

/-- Where attention has a link of its own, segment 2 g is group g's. -/
theorem group_at {X : Public} (h4 : X.p4 = true) (g : ℕ) : 2 * g / stepOf X = g := by
  unfold stepOf
  rw [h4, if_pos rfl]
  exact Nat.mul_div_cancel_left g (by decide : 0 < 2)

/-! ## The test on the index masks' message -/

/-- **The test.** M: the list of shapes. places: the list of seats. n: how many entries are read. -/
def indexTieB (cs : OnBytes.Codes) (M : List OnBytes.OracleShape) (places : List (ℕ × ℕ))
    (ms : List Mem) (N : Numbers) (n : ℕ) : Bool :=
  match M[N.indexNo]?, ms.find? fun y => decide (seatOf y = N.index) with
  | some sh, some u =>
    decide (places[N.indexNo]? = some N.index) && decide ((u.1.l.get u.2).1 = sh) &&
      decide (0 < sh.maskRows) && decide (n ≤ sh.maskRows * (pMask cs sh).ell)
  | _, _ => false

/-- **A yes gives the ties, and `IndexFit` at the free entries.** -/
theorem indexTie_of_B {cs : OnBytes.Codes} {M : List OnBytes.OracleShape}
    {places : List (ℕ × ℕ)} {ms : List Mem} {N : Numbers} {n : ℕ}
    (h : indexTieB cs M places ms N n = true) :
    ∃ sh u, M[N.indexNo]? = some sh ∧ places[N.indexNo]? = some N.index ∧
      memAt ms N.index = some u ∧ (u.1.l.get u.2).1 = sh ∧ seatOf u = N.index ∧
      IndexFit cs (posFree sh.maskRows) ms N n := by
  unfold indexTieB at h
  split at h
  · rename_i sh u hM hu
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hs : decide (seatOf u = N.index) = true :=
      List.find?_some (p := fun y => decide (seatOf y = N.index)) hu
    exact ⟨sh, u, hM, h1, hu, h2, of_decide_eq_true hs,
      indexFit_free hu (by rw [h2]) h3 (by rw [h2]; exact h4)⟩
  · cases h

/-- **The test can fail**: no member, no yes. -/
theorem indexTieB_nil (cs : OnBytes.Codes) (M : List OnBytes.OracleShape)
    (places : List (ℕ × ℕ)) (N : Numbers) (n : ℕ) : indexTieB cs M places [] N n = false := by
  unfold indexTieB
  cases M[N.indexNo]? <;> rfl

/-! ## At the wider meaning's own parameters -/

noncomputable section

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg₀ : Meaning P (Wit (CellsK rows cols) Tok MsgT))

/-- There the lookup's number of rows is the term's. -/
theorem nr_wide : (k4DataWide 𝔇 E Mg₀).L3.nr = rows := rfl

/-- There the lookup's number of columns is the term's. -/
theorem nc_wide : (k4DataWide 𝔇 E Mg₀).L3.nc = cols := rfl

/-- **`MeansTies` at the term**: three of its five fields by the make. -/
theorem ties_wide {p : Par} {m : ℕ} {xL : VerifiableInference.Desc.First.Look.Place}
    {sz : ℕ → Size} {seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    (hW : WorthTies X (k4DataWide 𝔇 E Mg₀).L3 p m xL)
    (hH : ∀ w, (𝔇.H.hid w).MG p.g =
      _root_.Meaning.mgOf X.y (ownW 𝔇.arr 𝔇.ms 𝔇.N sz seat 𝔇.cs w) p.g) :
    MeansTies (k4DataWide 𝔇 E Mg₀) p m xL sz seat Stored.entries :=
  ⟨rfl, rfl, hW, rfl, hH⟩

/-- The tie of the two readers of the committed matrix. -/
theorem encIs_wide :
    cutW (oW := (k4DataWide 𝔇 E Mg₀).L3.oW) Stored.entries (k4DataWide 𝔇 E Mg₀).L3.wOf rows cols =
      rcQ rows cols := encIs_conduit

/-- **`RecRides` at the term's parameters.** -/
theorem rides_wide (z : P) {seats : List (ℕ × ℕ)} (hsmp : 𝔇.smp = smpNamed 𝔇.cs seats)
    (hN : Stored.NoRec 𝔇.decT) :
    RecRides (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).smp
      (k4DataWide 𝔇 E Mg₀).decT z :=
  recRides_of_noRec 𝔇.cs 𝔇.smp hN z fun s s' r sd i => by
    rw [hsmp]
    exact smpNamed_same 𝔇.cs seats (z, s) (z, s') r.st sd i

/-- The layout's number of rows is the reference's. -/
theorem m0_wide {g : ℕ} {hp : HPlan2} (hl : 𝔇.d1.lay = X.layers.wsLay) (B : RefPub X g)
    (hG : X.G[g]? = some hp) : hRef = (k4DataWide 𝔇 E Mg₀).d1.lay.m0 := by
  show hRef = 𝔇.d1.lay.m0
  rw [hl]
  exact m0_ref B hG

/-- The layout's number of column bits is the reference's. -/
theorem lk_wide {g : ℕ} {hp : HPlan2} (hl : 𝔇.d1.lay = X.layers.wsLay) (B : RefPub X g)
    (hG : X.G[g]? = some hp) : kRef = (k4DataWide 𝔇 E Mg₀).d1.lay.lk := by
  show kRef = 𝔇.d1.lay.lk
  rw [hl]
  exact lk_ref B hG

/-- The reader of the pile of pending rows has the matrix off the witness's cells. -/
theorem rwMat_wide (hm : 𝔇.mat13 = matOfCells nR 𝔇.P13.lin.kCol) (a) (w) :
    ((k4DataWide 𝔇 E Mg₀).rw13 a w).mat = matOfCells nR 𝔇.P13.lin.kCol w.cells := by
  show 𝔇.mat13 w.cells = _
  rw [hm]

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.group_at
#print axioms OnBytes.Road.K4.indexTie_of_B
#print axioms OnBytes.Road.K4.indexTieB_nil
#print axioms OnBytes.Road.K4.nr_wide
#print axioms OnBytes.Road.K4.nc_wide
#print axioms OnBytes.Road.K4.ties_wide
#print axioms OnBytes.Road.K4.encIs_wide
#print axioms OnBytes.Road.K4.rides_wide
#print axioms OnBytes.Road.K4.m0_wide
#print axioms OnBytes.Road.K4.lk_wide
#print axioms OnBytes.Road.K4.rwMat_wide
