-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EntriesForTheK.lean: the members' batching (kind K13), toward zero knowledge: what
the kind hands in for the rows that the kinds lay (`LotEntry`, E2E/TheKOfRecord.lean), and what
follows at these rows. An entry is a lot with its simulators, that a lot of the filling bears its
name, and that it has that lot's sides. Three entries are made here, at the base filling, at every
public part and ground: the kind's own; and the two of the kind K1, whose first lot holds the part
whose coins this kind's second part spends. Three definitions; statements with their proofs, by
calls.

  `k13EntryAtBase`   the kind's own lot `k13LotAtBase`
  `k1EntryAtBase`, `wEntryAtBase`   the kind K1's two lots with their simulators (`K1.Sim.lotS`,
     `K1.Sim.wS`): the first segment's opening with each link's reads and digits; the sending of W
  `three_names_apart`   the three lots' names differ
  `k13_laid_at_theK`, `k1_laid_at_theK`, `w_laid_at_theK`   where the thirteen entries hold these
     three in their fields, the three lots are among the lots of `theK`
  `k13Share_at_theK`, `k13Stands_at_theK`, `ownerFresh_at_theK`   so at these rows, where the
     thirteen hold these entries, no premise "the lot is among the lots" is left: the kind's record
     of three shares; its row stands with a side at member 355; the owner's condition fresh at the
     kind's address

Limits.
  * The ten other entries, that the thirteen names differ, and the later chains' rows are arguments.
  * The two lots of the kind K1 and their simulators are that kind's; here only their names and
    sides are held against the filling's.
  * All limits of the statements called (Johnson/Desc/ProofFile/Honest/K13/Term/).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheKOfRecord
import Johnson.Desc.ProofFile.Honest.K13.Term.OwnerAtTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K13
open ProofFile.Honest ProofFile.Honest.K13
open ProofFile.Honest.Term (matrixInput baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (LotEntry TheThirteen LaterRows theK mem_theK)
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.AtFiles

/-- **The kind's own entry.** -/
def k13EntryAtBase (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    LotEntry (baseFilling files) Zq G where
  slot := k13LotAtBase Zq
  named := List.any_eq_true.2 ⟨_, k13FillLot_mem matrixInput _ _ openHonest, by rfl⟩
  fit := fun L hL hn => by
    rw [k13_slot_by_name L hL hn]
    exact k13SLot_halves _ _ Zq G

/-- **The entry of the kind K1's first lot.** -/
def k1EntryAtBase (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    LotEntry (baseFilling files) Zq G where
  slot := k1LotAtBase
  named := by rfl
  fit := fun L hL hn => by
    rw [(k1_slots_by_name L hL).1 hn]
    exact congrFun (congrFun (congrArg HLot.halves
      (K1.Sim.lotS_toHLot_base matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
        openHonest)) Zq) G

/-- **The entry of the kind K1's second lot**, the sending of W. -/
def wEntryAtBase (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    LotEntry (baseFilling files) Zq G where
  slot := wLotAtBase
  named := by rfl
  fit := fun L hL hn => by
    rw [(k1_slots_by_name L hL).2 hn]
    exact congrFun (congrFun (congrArg HLot.halves
      (K1.Sim.wS_toHLot_base matrixInput OnBytes.secondHashFunction openHonest)) Zq) G

/-- The three lots' names differ. -/
theorem three_names_apart (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    [(k13EntryAtBase files Zq G).slot.name, (k1EntryAtBase files Zq G).slot.name,
      (wEntryAtBase files Zq G).slot.name].Nodup := by
  show ["K13: the members' batching", k1LotAtBase.name, wLotAtBase.name].Nodup
  decide

section
variable {files : VerifierAndGoals.PublicFiles} {Zq : ProofFile.Pub} {G : ProofFile.Ground}
  (E : TheThirteen (baseFilling files) Zq G) (apart : (E.entries.map (·.slot.name)).Nodup)
  (R : LaterRows (baseFilling files) Zq G)

/-- Where the thirteen hold the kind's entry, its lot is among the lots of the rows of record. -/
theorem k13_laid_at_theK (e : E.k13 = k13EntryAtBase files Zq G) :
    k13LotAtBase Zq ∈ (theK E apart R).lots := by
  have q := mem_theK (E := E) (e := E.k13) (by simp [TheThirteen.entries]) apart R
  rw [e] at q
  exact q

/-- The same of the kind K1's first lot. -/
theorem k1_laid_at_theK (e : E.k1 = k1EntryAtBase files Zq G) :
    k1LotAtBase ∈ (theK E apart R).lots := by
  have q := mem_theK (E := E) (e := E.k1) (by simp [TheThirteen.entries]) apart R
  rw [e] at q
  exact q

/-- The same of the kind K1's second lot. -/
theorem w_laid_at_theK (e : E.w = wEntryAtBase files Zq G) :
    wLotAtBase ∈ (theK E apart R).lots := by
  have q := mem_theK (E := E) (e := E.w) (by simp [TheThirteen.entries]) apart R
  rw [e] at q
  exact q

end

section
variable {Wt : Type} {files : VerifierAndGoals.PublicFiles} {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
  (T : ThreadParts returned Wt) (E : TheThirteen (baseFilling files) returned.Z returned.G)
  (apart : (E.entries.map (·.slot.name)).Nodup)
  (R : LaterRows (baseFilling files) returned.Z returned.G)

/-- **The kind's record of three shares, at the rows of record.** -/
theorem k13Share_at_theK (e : E.k13 = k13EntryAtBase files returned.Z returned.G)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R',
      ready returned.F returned.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k =
        .ok R' →
      ThreadsP returned.F returned.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k
        R') :
    KindShare returned (theGOfReturn made h T (theK E apart R)) H Rel Th .K13 :=
  k13Share_at_theGOfReturn made h T (theK E apart R) (k13_laid_at_theK E apart R e) H Rel Th

/-- **The kind's row stands there, with a side at member 355.** -/
theorem k13Stands_at_theK (e : E.k13 = k13EntryAtBase files returned.Z returned.G) :
    K13Stands (theGOfReturn made h T (theK E apart R))
      ((k13LotAtBase returned.Z).rows returned.Z returned.G) :=
  k13Stands_at_theGOfReturn made h T (theK E apart R) (k13_laid_at_theK E apart R e)

/-- **The owner's condition fresh at the kind's address, at the rows of record.** -/
theorem ownerFresh_at_theK (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (e₁ : E.k1 = k1EntryAtBase files returned.Z returned.G)
    (eW : E.w = wEntryAtBase files returned.Z returned.G) :
    OwnerFreshAtK13 (theGOfReturn made h T (theK E apart R)) :=
  ownerFreshAtK13_at_theGOfReturn scope live made h T (theK E apart R)
    (k1_laid_at_theK E apart R e₁) (w_laid_at_theK E apart R eW)

end

end AtFullSide.K13

#print axioms AtFullSide.K13.k13EntryAtBase
#print axioms AtFullSide.K13.k1EntryAtBase
#print axioms AtFullSide.K13.wEntryAtBase
#print axioms AtFullSide.K13.three_names_apart
#print axioms AtFullSide.K13.k13_laid_at_theK
#print axioms AtFullSide.K13.k1_laid_at_theK
#print axioms AtFullSide.K13.w_laid_at_theK
#print axioms AtFullSide.K13.k13Share_at_theK
#print axioms AtFullSide.K13.k13Stands_at_theK
#print axioms AtFullSide.K13.ownerFresh_at_theK
