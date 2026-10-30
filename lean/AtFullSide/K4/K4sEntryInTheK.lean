-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/K4sEntryInTheK.lean: the entry has no premise; the share is CONDITIONAL on the binders named.

What is here. WHAT THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) HAND IN FOR THE ROWS OF RECORD (E2E/TheKOfRecord.lean: `LotEntry`, `TheThirteen`, `theK`), AND K4's SHARE OF THE ONE THEOREM ON ZERO KNOWLEDGE AT THESE ROWS, with the premise "K4's lot is among the rows' lots" turned into one equation on the entries: the field k4 of the thirteen is `k4Entry` (hE). Three fields laid and two calls; nothing new
is shown.

  `k4Entry`              the entry: the lot `k4BaseSlot` · a lot of the base filling bears its name (`k4_named_base`) · that lot has its sides (`k4_fit_at_name`), at every public part and ground
  `k4_lot_in_theK`       at every thirteen entries whose field k4 is `k4Entry`: K4's lot is among the lots of `theK` (`mem_theK`)
  **`k4_share_at_theK`**   there: `KindShare A (theGOfReturn made h T (theK E apart R)) H Rel Th .K4`, at every H, Rel and family of invariants Th (`k4_kind_share`, AtFullSide/K4/K4sRowsOfT3.lean): of the lot hE alone is asked

Limits. The twelve other entries, apart and the later chains' rows R are letters: no value of `TheThirteen` is shown here. Those of `k4_kind_share`: the spender's half; fresh true and empty; no joint law; On and bud are True at K4's rows. One kind of the theorem's "for every kind". This file proves zero knowledge of nothing.
No property is claimed.
-/
import AtFullSide.K4.K4sRowsOfT3
import E2E.TheKOfRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K4
open ProofFile.Honest ProofFile.Honest.K4 ProofFile.Honest.K4.ExactFresh
open ProofFile.Honest.Term (baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows LotEntry TheThirteen LaterRows theK mem_theK)

/-- **K4's ENTRY FOR THE ROWS OF RECORD.** -/
def k4Entry (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    LotEntry (baseFilling files) Z Gr where
  slot := k4BaseSlot
  named := k4_named_base files
  fit := fun L hL hn => k4_fit_at_name files Z Gr L hL hn

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL on hE. **K4's lot is among the lots of the rows of record.** -/
theorem k4_lot_in_theK {Z : ProofFile.Pub} {Gr : ProofFile.Ground} (E : TheThirteen (baseFilling files) Z Gr)
    (hE : E.k4 = k4Entry files Z Gr) (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows (baseFilling files) Z Gr) : k4BaseSlot ∈ (theK E apart R).lots := by
  have hm : E.k4 ∈ E.entries := by
    unfold TheThirteen.entries
    simp
  have hs := mem_theK hm apart R
  rw [hE] at hs
  exact hs

/-- CONDITIONAL on the binders and hE. **K4's SHARE AT THE ROWS OF RECORD**: of the lot hE alone is asked. -/
theorem k4_share_at_theK (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T₀ : ThreadParts A Wt) (E : TheThirteen (baseFilling files) A.Z A.G)
    (hE : E.k4 = k4Entry files A.Z A.G) (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows (baseFilling files) A.Z A.G)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R',
      ready A.F A.B ((theGOfReturn made h T₀ (theK E apart R)).prover H) w₀ rc x k = .ok R' →
      ThreadsP A.F A.B ((theGOfReturn made h T₀ (theK E apart R)).prover H) w₀ rc x k R') :
    KindShare A (theGOfReturn made h T₀ (theK E apart R)) H Rel Th .K4 :=
  k4_kind_share made h T₀ (theK E apart R) (k4_lot_in_theK E hE apart R) H Rel Th

end AtFullSide.K4

#print axioms AtFullSide.K4.k4Entry
#print axioms AtFullSide.K4.k4_lot_in_theK
#print axioms AtFullSide.K4.k4_share_at_theK
