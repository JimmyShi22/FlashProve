-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastAll.lean: what the file's rule asks of the key file's last chain, joined, at the thread `threadOwn` (the last thread
at the letters of this work: riders true of all, `keptOwn`) and the letter `saidOwn`.

  `threadOwn`, `saidOwn`.
  `last_members`: `OwesS`, `SaidNext` at every border, `YesS` at every letter for a fall.

Left as premises, each named: `hP` (`playsS_own` pays it from `RunPlays`, `listed`, `laid`); `hE` (`exchangeS_first₃` pays it
from the rows in front and (Dot)); `hR` (riders past the pins); `hasks`, the value ties `hpl`, `hms`, `htr`, `hhalf` of
`acceptedS_own`; `hfit`, `hd` of `third_shaped`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastTerm
import E2E.KeyLastMembers
import E2E.KeyLastOwes
import E2E.KeyLastShaped
import E2E.KeyLastValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (proverSideOfProximityTest firstPart restPart opened_of_played)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁)
open AtPublicFiles.KeyLay (pWK jobKWAt)
open AtPublicFiles.AtFiles (KeySourced accepted_third₀ accepted_third₁ accepted_third₃)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKWFull)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type} {Z : VerifierAndGoals.PublicFiles}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)

/-- **The last thread at this work's letters.** -/
abbrev threadOwn :=
  threadFull Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd
    (fun _ _ _ => True) keptOwn w dfltT dfltM

/-- **What is said of the run on it.** -/
abbrev saidOwn :=
  saidKey (descriptionFromSource Xs Nr Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
    (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM)

variable {Wd : Type} (JI JW : ProofFile.Honest.K1.SendJob Wd X) (A : ProofFile.Honest.K14.SendPub)
  (lift : Local W₀ Rc Xi Unit → Wd) (ask : Local W₀ Rc Xi Unit → ProofFile.Honest.K14.Ask)

/-- **The last chain's part of the debts at the members.** -/
theorem last_members (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : ∀ v, (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hdM : dfltM.opened.isSome = true)
    (hpl : pWK Pl = piKWFull)
    (hms : (jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape) = msKW)
    (htr : (jobKWAt Xs Nr Pl JI JW A lift ask).trees = ProofFile.Honest.K12.AtProof.treesW piKWFull)
    (hhalf : ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM).hs.find? fun g => g.place == (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place) =
      some (proverSideOfProximityTest (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X).needsField)
    (hP : PlaysS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) 2)
    (hE : ExchangeS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) 0)
    (hR : ∀ b, b < 4 → RidesPast (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) b)
    (hasks : ∀ k st m E
      (c : RowCoins [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest]),
      ThrS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) 2 k st m E →
      lendRow Bk (Bk.rowsOf 2) (k.look 2) (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place
        [(firstPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest] 0 = .ok c →
      OwnAsks (jobKWAt Xs Nr Pl JI JW A lift ask) m E c)
    (fl : Nat → S₃ → List Fmt.Drawn → Option String) :
    OwesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) ∧ (∀ b, SaidNext (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) b) ∧
      YesS (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) (saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) fl := by
  have hZ := third_shaped Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML
    (tableKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd
      (fun _ _ _ => True) keptOwn w dfltT dfltM) n₁ n₂ Vd (fun _ _ _ => True) keptOwn w hs scope hfit hd
    (fun _ _ _ => true)
  have hfun : ∀ k v h s s', (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM).begun k v h s →
      (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM).begun k v h s' → s = s' := fun k v h s s' a b =>
    Except.ok.inj ((show (descriptionFromSource Xs Nr Pl).start₃ _ _ _ = .ok s from a).symm.trans b)
  refine ⟨owes_last _ _ hs scope rfl hP
      (fun b hb => behind_all Xs Nr Pl K _ Nm _ _ _ _ _ _ n₁ n₂ Vd w hs scope b hb) hE
      (by show (LastRows.rows 1).owes = []; decide) (by show (LastRows.rows 2).owes = []; decide)
      (by show (LastRows.rows 3).owes = []; decide) hR,
    saidNext_key (descriptionFromSource Xs Nr Pl) (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM)
      (startKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ dfltM)
      (fun blk h => by
        have h' : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[0]? = some blk := h
        obtain rfl := Option.some.inj h'
        rfl)
      (fun blk h => by
        have h' : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[1]? = some blk := h
        obtain rfl := Option.some.inj h'
        rfl),
    yes_last _ _ hs scope rfl fl fun b hb => ?_⟩
  match b, hb with
  | 0, _ => exact acceptedS_of _ _ (accepted_third₀ rfl hs scope hZ (values_first₃ hs scope rfl hZ fl))
  | 1, _ => exact acceptedS_of _ _ (accepted_third₁ rfl hs scope hZ)
  | 2, _ =>
    exact acceptedS_own (Said := saidOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML n₁ n₂ Vd w dfltT dfltM) JI JW A lift ask hs scope rfl rfl
      hfun hZ hpl hms htr hhalf (fun _ _ h => h.1)
      (fun _ _ _ _ hT => opened_of_played (startBy_opened dfltM hdM) (hT.2.2 (Nat.le_refl 2))) hasks fl
  | 3, _ => exact acceptedS_of _ _ (accepted_third₃ rfl hs scope hZ)
  | _ + 4, h => exact absurd h (by omega)

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.last_members
