-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Condition.lean: THE ROWS «K06_condition» AND «K07_condition»: premises ON PUBLIC NUMBERS ALONE that the laws on the output
head's own rounds (K6) and on the next token (K7) ask, AS ONE STRUCTURE WITH NAMED FIELDS, and that it holds at two written records. Law/K06ConditionSpends.lean
SPENDS it: from it the laws' own premises, under the laws' own names.

Among its fields: admitted · numbers · pad · blocks · table · work · once · reads.
WHAT IT DOES NOT SHOW. NOTHING OF SOUNDNESS. **THAT NO PREMISE IS MISSED IS NOT SHOWN**: the fields were gathered by reading the laws' closed statements, by two searches of their files' binders, and
by further finds. THAT THE TWO WRITTEN RECORDS ARE THOSE OF THE FILES THAT SHIP: they were typed by program off a print of the program's own reader (OnBytes.Model.Verify: Public.hS;
borderOf; the setting's work and instances; the plan's array of reads) at another build's two stored sets of public files (made-up weights), and held against that reader by a
sheet: runs, no theorem; no test here reads a file. Premises on the REQUEST (Request.ok), on the heard token (y < V), on the carried record (WellLaid, PointsOk), on the transcript (Canonical,
NoBad), on the cells and on the public TABLE of exponentials (TableOk) are no numbers of the plan: NOT HERE.
THE FIELDS, EACH WITH WHO ASKS IT. «the kind»: HeadOk.lean's planOk. «the program»: OnBytes/Model/HeadLayout.lean's admitted and numbers, which its layout runs before any head's plan is made.
  ok        (parOf h work).ok = true: the kind's own tests on the plan: K06_law (Law/RowRides.lean) · K06BackStatement. It reads sT, the sizes and the policy: NOT the letter work (ok_any).
  admitted  the program's tests on the shape (4 ≤ lt ≤ 16 · 1 ≤ d ≤ 2^20 · lt < la ≤ 16 · XL is 4 or 5 · 2 ≤ V ≤ 2^24 · lPd = ceilLog2 d · S2 ∣ d · …): asked by nobody's law by name: IT PAYS
            features, point, rows and index's second half at once: these four are tested by the program, though not by the kind.
  numbers   numbers h returns: a premise of Law/ReadsFit.lean readLen_fits and Law/ReadsFitNorm.lean readLenN_fits · wideLenN_fits.
  features  0 < d: RowRidesStatement's hasFeatures, unfolded.      point  0 < lt: Law/K06Rounds.lean · Law/K06Below.lean.      rows  h.lt ≤ h.la: readLen_fits.
  block     ls ≤ lPd: the normalization's laws (Law/NormRule.lean and four more). NEITHER THE KIND NOR admitted TESTS IT.
  pad       h.lPd = lPd: the planner's record takes the FIELD h.lPd (OnBytes/Model/HeadRounds.lean: own); the kind's lPd is clog2 d (Norm.lean): without this Law/HeadPrices.lean's recOf is not the plan's record.
  limbs     h.XL = 5: readLen_fits. THE PROGRAM LETS 4 BY; the kind's text has five limbs written in.
  blocks    S2 ∣ d: the normalization's laws.      table  S2 ∣ JVa: K06OutAtLookupStatement. Both stand in the kind's planOk too.
  keys      every key's length is below 2 ^ 41: K06OutAtLookupStatement.
  index     lt + lPd ≤ 63 and h.la ≤ 63: Law/EqOne.lean eq_eq_eqOne asks z.size ≤ 63 of whichever point it is spent at (no law of ours calls it).
  stream    5 d / S2 ≤ kxb (mxb / 2 ^ la): StreamFits, unfolded: on the LAYERS' layout's numbers. NO TEST OF THE KIND's ASKS IT.
  origin    b.off = 0 and b.cnt * b.J = h.d: no theorem's premise but the text's meaning's (Law/ReadsFitNorm.lean stream_at_zero). The program's own test asks less.
  work      work + 66 ≤ 128: Law/K06Below.lean.      once  inst = 1: Law/K06Rounds.lean's prices stand before the planner's factor «instances».
  reads     the plan names an array of reads: else Head.blockOf W l is none and K06_law speaks of no block.
  K06Full   BESIDE, FOR THE TIE TO THE LIBRARY's REFERENCE MODEL ALONE (Law/HeadScopeAt.lean headScope_of_full): h.digSh = 8 (the kind lets 7 by). Stated at the full-size record.
  k06Cond_bites   the structure says no at three turned records.      K07Cond   2 ≤ h.V: the next token's kind's one test on the plan.

-/
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Cond

open OnBytes.Model.Head (Shape Border)
open Norm (lt ls d lPd S2)

/-- **PREMISES ON PUBLIC NUMBERS ALONE THAT OUR LAWS ON K6 ASK.** h: the head's shape. b: what the head reads of the layers' layout. work, inst: the setting's bits of work in front of a field's challenge in a
request's own rounds, and its number of instances. reads: the number of the plan's array of reads. -/
structure K06Cond (h : Shape) (b : Border) (work inst : Nat) (reads : Option Nat) : Prop where
  ok : (parOf h work).ok = true
  admitted : OnBytes.Model.Head.admitted h = true
  numbers : (OnBytes.Model.Head.numbers h).toOption.isSome = true
  features : letI := sizesOf h; 0 < d
  point : letI := sizesOf h; 0 < lt
  rows : h.lt ≤ h.la
  block : letI := sizesOf h; ls ≤ lPd
  pad : letI := sizesOf h; h.lPd = lPd
  limbs : h.XL = 5
  blocks : letI := sizesOf h; S2 ∣ d
  table : letI := sizesOf h; S2 ∣ JVa
  keys : letI := sizesOf h; ∀ k : PlaceKey, lenOf k < 2 ^ 41
  index : letI := sizesOf h; lt + lPd ≤ 63 ∧ h.la ≤ 63
  stream : 5 * h.d / h.S2 ≤ 1 * (b.kxb * (b.mxb / 2 ^ h.la))
  origin : b.off = 0 ∧ b.cnt * b.J = h.d
  work : work + 66 ≤ 128
  once : inst = 1
  reads : reads.isSome = true

/-- The kind's tests on the plan do not read the letter work. -/
theorem ok_any (h : Shape) (w w' : Nat) : (parOf h w).ok = (parOf h w').ok := rfl

/-- Beside it, for the tie to the library's reference model alone. -/
def K06Full (h : Shape) : Prop := h.digSh = 8

/-- The next token's. -/
def K07Cond (h : Shape) : Prop := 2 ≤ h.V

/-- The head's public numbers at a stored SMALL set of another build than the shipped one, as the program's reader printed them. -/
def hSmall : Shape :=
  { lt := 6,
    la := 8,
    d := 512,
    lPd := 9,
    V := 512,
    MF := 43,
    KF := 30,
    epsF := 1,
    toksrc := 1,
    wbEmb := 21,
    wbHead := 13,
    clipC := 256,
    theta := 256,
    cap := 0,
    logS := 16,
    digSh := 8,
    tabS := 4,
    famF := 24,
    lmhf := 14,
    NHf := 1,
    lmhd := 12,
    lmhr := 12,
    lmbH := 13,
    iotaH := [0, 0, 0, 0, 0, 0],
    nmin := 20,
    NMINH := 0,
    LIDB := 24,
    XL := 5,
    polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"],
                  ["R16b", "R16", "HD1"],
                  ["R8", "R8", "ROW", "HD2"],
                  ["FEa", "FE", "HE0"],
                  ["FEb", "FE", "HE1"],
                  ["FC", "FC", "CNF"]] }

/-- The same at a stored FULL-SIZE set of another build than the one that ships. -/
def hFull : Shape :=
  { lt := 10,
    la := 16,
    d := 5120,
    lPd := 13,
    V := 202048,
    MF := 44,
    KF := 30,
    epsF := 53687,
    toksrc := 1,
    wbEmb := 21,
    wbHead := 13,
    clipC := 256,
    theta := 256,
    cap := 0,
    logS := 15,
    digSh := 8,
    tabS := 4,
    famF := 24,
    lmhf := 16,
    NHf := 4,
    lmhd := 14,
    lmhr := 13,
    lmbH := 15,
    iotaH := [1, 1, 1, 0, 0, 0],
    nmin := 20,
    NMINH := 27,
    LIDB := 28,
    XL := 5,
    polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"],
                  ["R16b", "R16", "HD1"],
                  ["R8", "R8", "ROW", "HD2"],
                  ["FEa", "FE", "HE0"],
                  ["FEb", "FE", "HE1"],
                  ["FC", "FC", "CNF"]] }

/-- What the head needs to know of the layers' layout (OnBytes.Model.Verify.borderOf), as printed at the two sets. -/
def bSmall : Border := { mxb := 8192, kxb := 20, off := 0, nl := 5, cnt := 1, J := 512 }
@[inherit_doc bSmall] def bFull : Border := { mxb := 65536, kxb := 400, off := 0, nl := 5, cnt := 1, J := 5120 }

/-- The bits of work, the instances and the array of reads, as printed: the same at the two sets. -/
def workAt : Nat := 0
@[inherit_doc workAt] def instAt : Nat := 1
@[inherit_doc workAt] def readsAt : Option Nat := some 0

theorem keys_small : letI := sizesOf hSmall; ∀ k : PlaceKey, lenOf k < 2 ^ 41 := by
  intro k
  rcases k with a | b
  · cases a <;> decide
  · cases b <;> decide

theorem keys_full : letI := sizesOf hFull; ∀ k : PlaceKey, lenOf k < 2 ^ 41 := by
  intro k
  rcases k with a | b
  · cases a <;> decide
  · cases b <;> decide

theorem k06Cond_small : K06Cond hSmall bSmall workAt instAt readsAt where
  ok := by decide
  admitted := by decide
  numbers := by decide
  features := by decide
  point := by decide
  rows := by decide
  block := by decide
  pad := by decide
  limbs := rfl
  blocks := by decide
  table := by decide
  keys := keys_small
  index := by decide
  stream := by decide
  origin := by decide
  work := by decide
  once := rfl
  reads := rfl

theorem k06Cond_full : K06Cond hFull bFull workAt instAt readsAt where
  ok := by decide
  admitted := by decide
  numbers := by decide
  features := by decide
  point := by decide
  rows := by decide
  block := by decide
  pad := by decide
  limbs := rfl
  blocks := by decide
  table := by decide
  keys := keys_full
  index := by decide
  stream := by decide
  origin := by decide
  work := by decide
  once := rfl
  reads := rfl

theorem k06Full_full : K06Full hFull := rfl

theorem k07Cond_small : K07Cond hSmall := by unfold K07Cond; decide
theorem k07Cond_full : K07Cond hFull := by unfold K07Cond; decide

/-- The structure can say no: at the small record with no feature; with four limbs; with the stream's tensor one feature off. -/
theorem k06Cond_bites :
    ¬ K06Cond { hSmall with d := 0 } bSmall workAt instAt readsAt ∧
      ¬ K06Cond { hSmall with XL := 4 } bSmall workAt instAt readsAt ∧
      ¬ K06Cond hSmall { bSmall with off := 1 } workAt instAt readsAt :=
  ⟨fun C => absurd C.features (by decide), fun C => absurd C.limbs (by decide),
    fun C => absurd C.origin.1 (by decide)⟩

/-- **The rows, as closed propositions.** -/
def K06Condition : Prop :=
  K06Cond hSmall bSmall workAt instAt readsAt ∧ K06Cond hFull bFull workAt instAt readsAt ∧ K06Full hFull
@[inherit_doc K06Condition] def K07Condition : Prop := K07Cond hSmall ∧ K07Cond hFull

theorem k06Condition : K06Condition := ⟨k06Cond_small, k06Cond_full, k06Full_full⟩
theorem k07Condition : K07Condition := ⟨k07Cond_small, k07Cond_full⟩

end VerifiableInference.Desc.Kinds.Head.Law.Cond

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.k06Condition
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.k07Condition
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.k06Cond_bites
