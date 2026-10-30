-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/KeysCongr.lean: CONDITIONAL.

What is here. THE LOOKUP's SENTENCE ON THE KEYS (`K3Keys`, Johnson/Top/H/K3RowOut.lean) READS ITS
READING ν OF THE LOOKUP's PLACES AT MASK ENTRIES ALONE, ALL OF THEM BELOW (THE LOOKUP's FIRST SLOT +
ITS NUMBER OF MASK ENTRIES). It reads no cell. So it holds of a second reading that agrees with the
first at every mask entry below that sum (`keys_congr`), and so does the same sentence at all rounds
for which the heard structure stands (`outKeys_congr`). Why that is so: the sentence says that the
join's form has the value 0 (`claimJoin`, OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean); the calls'
forms in it are constants; by the library's `val_joinK` (Port/FoJoin.lean) the reading is left in
the value of one form, the one for the end of the key side; that form's places are fields of the
public numbers' ledgers of the key levels and of the first tie (`numsF`, Forest/FoV.lean), each the
first slot plus a clamped place of the library's ledger of mask entries; and the library has each
such place below the number of mask entries (`Fo.Slots.pKeyC_lt`, `Fo.Slots.pTieC_lt`,
Ends/FoSlotNums.lean). What it is for: a caller whose mask row goes on behind the lookup's entries
may take its own row as ν's masks. General in the ring, the shape and the key vectors Kv; it imports
nothing of the honest side. The forms' lemmas are those of Johnson/Road/K4/W/PlanesCongr.lean,
section 2.

  `onLt_fK`, `cEndF_lt`   the form for the end of the key side names mask entries below the sum.
  `claimJoin_readings`   the join's value at two readings that agree there.
  `keys_congr`   **the sentence on the keys at a second reading.**
  `outKeys_congr`   **the same at all rounds for which the heard structure stands.**

Not shown here. THAT THE SENTENCE HOLDS OF ANY READING: P and H are hypotheses. hm: the two readings
agree at every mask entry below the sum, THOSE BELOW THE LOOKUP's FIRST SLOT AMONG THEM: a
hypothesis; that the sentence reads none below the first slot is not shown. THE KEY VECTORS Kv ARE
ONE AND THE SAME ON BOTH SIDES: where a caller's key vectors hang on its reading, that they are
unchanged is the caller's to show. Nothing is said of the lookup's other sentences (its rows:
nowhere; its planes: Johnson/Road/K4/W/PlanesCongr.lean). No example is written here; tests with
code at one small synthetic lookup: Johnson/Road/K4/W/KeysCongrTest.lean. Nothing on soundness, on
completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, none whose name begins Cb.Bridge, and
none whose name holds RecCompile. It imports nothing of the honest side
(Johnson/Desc/ProofFile/Honest/).
-/
import Johnson.Road.K4.W.PlanesCongr
import OnBytes.Tie.Pv.Lookup.Ends.FoSlotNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.W
open TwV (Nums Trace Rounds)
open _root_.Fo (Pl claimJoin endsOf AffK val_joinK)
open VerifiableInference.OnPublicFiles (K3Keys K3OutKeys)

section
variable {K : Type} [CommRing K] {n : ℕ}

/-- CONDITIONAL: on hT. The form with which the key side is entered. -/
theorem onLt_fK (N : Nums Pl K) (hT : ∀ l, LedLt n (N.ledTie l)) (t : Trace K) :
    OnLt n (TwV.fK N t) := by
  intro pc hpc
  unfold TwV.fK at hpc
  rw [List.mem_singleton.mp hpc]
  exact (hT 0).sh 0

/-- The form for the end of the key side names mask entries alone, each below the first slot plus
the lookup's number of mask entries. -/
theorem cEndF_lt (h : FoNums.Sh) (lm first : ℕ) (rs : Rounds K) :
    OnLt (first + FoNums.nMasks h) (endsOf h lm first rs).cEndF :=
  onLt_scale _ (onLt_incTop _
    (fun l => ledF_lt first (FoNums.nMasks h) _ (_root_.Fo.Slots.pKeyC_lt (FoNums.S h) l))
    (onLt_fK _
      (fun l => ledF_lt first (FoNums.nMasks h) _ (_root_.Fo.Slots.pTieC_lt (FoNums.S h) l)) _) _)

/-- CONDITIONAL: on hm. **The join's value at two readings** that agree at the mask entries below
that sum. kf: the calls' key vectors at their points. -/
theorem claimJoin_readings (h : FoNums.Sh) (lm first : ℕ) {ν ν' : Pl → K}
    (hm : ∀ j, j < first + FoNums.nMasks h → ν (.mask j) = ν' (.mask j)) (rs : Rounds K)
    (kf : ℕ → K) : claimJoin h lm first rs ν kf = claimJoin h lm first rs ν' kf := by
  have e : AffK.val ((endsOf h lm first rs).cEndF, (endsOf h lm first rs).cEndC) ν =
      AffK.val ((endsOf h lm first rs).cEndF, (endsOf h lm first rs).cEndC) ν' :=
    congrArg (· + (endsOf h lm first rs).cEndC) (valS_congr (cEndF_lt h lm first rs) hm)
  unfold claimJoin
  rw [val_joinK, val_joinK, e]
  simp only [AffK.val_ofConst]

/-- CONDITIONAL: on hm and P. **THE SENTENCE ON THE KEYS AT A SECOND READING** that agrees with the
first at the mask entries below that sum. -/
theorem keys_congr (h : FoNums.Sh) (lm first : ℕ) {ν ν' : Pl → K}
    (hm : ∀ j, j < first + FoNums.nMasks h → ν (.mask j) = ν' (.mask j)) (Kv : ℕ → ℕ → K)
    (rs : Rounds K) (P : K3Keys h lm first ν Kv rs) : K3Keys h lm first ν' Kv rs := by
  unfold K3Keys at P ⊢
  rw [← claimJoin_readings h lm first hm rs]
  exact P

/-- CONDITIONAL: on hm and H. **THE SAME AT ALL ROUNDS FOR WHICH THE HEARD STRUCTURE STANDS.** -/
theorem outKeys_congr (h : FoNums.Sh) (lm first : ℕ) {ν ν' : Pl → K}
    (hm : ∀ j, j < first + FoNums.nMasks h → ν (.mask j) = ν' (.mask j)) (Kv : ℕ → ℕ → K)
    (ρ : OnBytes.Model.Reading K) (g : OnBytes.Model.Forest.Heard) (F' : OnBytes.Model.Fork)
    (H : K3OutKeys h lm first ν Kv ρ g F') : K3OutKeys h lm first ν' Kv ρ g F' :=
  fun rs hI => keys_congr h lm first hm Kv rs (H rs hI)

end

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.onLt_fK
#print axioms OnBytes.Road.K4.W.cEndF_lt
#print axioms OnBytes.Road.K4.W.claimJoin_readings
#print axioms OnBytes.Road.K4.W.keys_congr
#print axioms OnBytes.Road.K4.W.outKeys_congr
