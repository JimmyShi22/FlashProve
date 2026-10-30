-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Places.lean: the places, that is the entries of the coins that a finite type
of random values fills, and the statement that the explicit shift of the coins is 0 outside them
under the public premises on sizes.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file defines. The coins of the prover's algorithm (LCoins) are functions on all natural
numbers and all sizes. The algorithm reads them at finitely many entries (by inspection, not
proved). A finite type of random values fills finitely many entries, the places, and puts 0 at every
other. So a shift of the coins can be carried down to such a type only if it is 0 at those other
entries too. InPlaces P S C says that the coins C are 0 outside the places, at parameters P and
sizes S.
  InPlaces        the places of all coins: both pads; the members' rows' tails, at rows below R and
                  entries below the main code's tail length; the tail of the row beside the two
                  folded rows, below the mask code's tail length; the first fold's coefficients, at
                  the first stage's sizes only; and InBody for the stages.
  InBody          the same along the stages, by the recursion of shB
                  (Johnson/LinkSim/AtText/ShiftDefs.lean). After the last switch all coins are 0.
  InSwitch        the places of one switch's coins, from stage sizes s to s'. At every switch:
                  the free entries of the new mask table, from carriedN s on, up to the table's
                  end; and, inside the new sizes, the tails of the new main rows and of the
                  carried mask rows. Of the structure of coins given to the switch (PS), the two
                  table fields tabM and tabZ are 0 (the algorithm overwrites them). Where a fold
                  follows: the fresh rows' tails inside the sizes, and the next fold's
                  coefficients at the next stage's sizes only; no fresh table and no masking
                  word. At the last switch: row 0 of the fresh table and of its tails, and the
                  masking word's main row and its tail, inside the sizes; no coefficients.
  carriedN s      how many entries of the new mask table hold what the fold leaves: two folded
                  mask messages and three folded tails.
  Spec.shiftInPlaces   Statement only; proved as shiftInPlaces in PlacesProof.lean. Under the
                  public premises on sizes (Sizes, Johnson/LinkSim/AtText/SpecShift.lean), the
                  explicit shift of the coins (shC) is 0 outside the places. This holds for all
                  data Xd, whose contribution the shift compensates, and all data Xr, coins C and
                  verifier challenges D of the run along which the shift is computed.

How it fits. Johnson/LinkSim/AtText/CoinsPlaces.lean proves that the image of LinkK is 0 outside the
places and, where P has a stage, contains every value of the coins that is. CoinsDown.lean then
carries a shift of the coins that is 0 outside the places down to LinkK.

Limits.
- At a plan without a stage, InPlaces constrains none of the stages' coins, because its condition on
  them speaks of a first stage. The public premises on sizes (Sizes,
  Johnson/LinkSim/AtText/SpecShift.lean) require one.
- At the last switch, InSwitch does not ask that the last stage have one main row and one mask row.
  It lets the tails of all rows inside the sizes be free, while the explicit shift of the coins puts
  values in row 0 alone. The two agree where the last stage has no row variable, which the public
  premises on sizes require.

Notes.
- No proof here: Spec.shiftInPlaces is proved in PlacesProof.lean.
- That a given finite type's image is InPlaces is not said here (of LinkK it is proved in
  CoinsPlaces.lean).

Sources.
- The places follow, field by field, a finite type of the link's prover's random values of this
  library (Johnson/Prover/Link/LinkCoin.lean; not imported here).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecStage

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- The entries of a new mask table that hold what the fold leaves. -/
def carriedN (s : Sg) : ℕ := 2 * s.Z.l + s.C.r + 2 * s.Z.r

/-- The places of one switch's coins. s: the sizes before the switch; s': after it. -/
structure InSwitch (s s' : Sg) (last : Bool) (fr : ℕ → GE) (new : PS)
    (W : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) : Prop where
  fr : ∀ i, ¬(carriedN s ≤ i ∧ i < 2 ^ s'.h * s'.Z.l) → fr i = 0
  tabM : ∀ i, new.tabM i = 0
  tabZ : ∀ i, new.tabZ i = 0
  tM : ∀ b q, ¬(b < 2 ^ (s'.h + s'.g) ∧ q < s'.C.r) → new.tM b q = 0
  tZ : ∀ b q, ¬(b < 2 ^ s'.h ∧ q < s'.Z.r) → new.tZ b q = 0
  fT : ∀ b q, ¬((if last then b = 0 else b < 2 ^ s'.h) ∧ q < s'.Z.r) → new.fT b q = 0
  fM : ∀ b i, ¬(last = true ∧ b = 0 ∧ i < s'.Z.l) → new.fM b i = 0
  sM : ∀ i, ¬(last = true ∧ i < s'.C.l) → new.sM i = 0
  sT : ∀ q, ¬(last = true ∧ q < s'.C.r) → new.sT q = 0
  W : ∀ σ, ¬(last = false ∧ σ = s') → W σ = 0

/-- Along the stages, from the switch number j on. -/
def InBody : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ → BCoins → Prop
  | _, [], j, K =>
    (∀ i, j ≤ i → K.fr i = 0 ∧ K.new i = zPS) ∧ ∀ σ i, j < i → K.W σ i = 0
  | cur, next :: rest, j, K =>
    InSwitch (sgOf cur) (sgOf next) rest.isEmpty (K.fr j) (K.new j) (fun σ => K.W σ (j + 1)) ∧
      InBody next rest (j + 1) K

/-- The coins C are 0 outside the places, at parameters P and sizes S. -/
structure InPlaces (P : P15) (S : Sz) (C : LCoins) : Prop where
  tN : ∀ a i q, ¬(i < S.P.R ∧ q < S.P.C.r) → C.tN a i q = 0
  psi : ∀ q, S.P.Z.r ≤ q → C.ψN q = 0
  W0 : ∀ σ, σ ≠ sg0 P → C.body.W σ 0 = 0
  body : ∀ first rest, (p12Of P).nums.stages = first :: rest → InBody first rest 0 C.body

/-- Statement only; proved as shiftInPlaces in PlacesProof.lean. Under Sizes, the shift of the coins
is 0 outside the places. -/
def Spec.shiftInPlaces : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (Xd Xr : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn), Sizes P S t D →
    InPlaces P S (shC P S t Xd Xr C D)

end OnBytes.LinkSim.AtText
