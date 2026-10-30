-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyExact.lean: the key rung, twin of E2E/BridgeExact.lean at the key file: from the rows' rule Owed at the key file to OneExact at offlineProverWithEncodedTable.

Nothing here proves zero knowledge of the protocol. Owed at the key file is a premise, and no member of it is known at any description
of the protocol. It says what the key file's rows must meet; the prover is a letter.
-/
import E2E.BridgeExact
import E2E.KeyBridgeFilled
import E2E.BridgeNoStop
import E2E.BridgeDebts
import Johnson.Desc.ProofFile.Honest.Law.SharesNoHid

set_option autoImplicit false
set_option maxRecDepth 20000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Stops
open VerifiableInference.Desc (FileDescription Block)
open ProofFile.Honest

section Parts
variable {S Cl V W X : Type}

/-- No part of these lists has a second stop that fires. -/
def NoHid (hs : List (Placed V W X)) : Prop := ∀ h ∈ hs, ∀ p ∈ h.parts, ∀ u f o, p.hid u f o = none

theorem rowStopAt_not_hid (v : Option V) :
    ∀ (ps : List (Part V W X)), (∀ p ∈ ps, ∀ u f o, p.hid u f o = none) → ∀ loc ds,
      rowStopAt v ps loc ds ≠ some .hid
  | [], _, _, _ => by
    show (none : Option Why) ≠ some .hid
    simp
  | p :: ps, h, loc, ds => by
    show ((p.stopAt v loc (ds.take p.moves.length)).or
      (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))) ≠ some .hid
    have h1 := stopAt_not_hid p v loc (ds.take p.moves.length)
      fun u j => h p (List.mem_cons_self ..) u _ _
    have h2 := rowStopAt_not_hid v ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (loc ++ ds.take p.moves.length) (ds.drop p.moves.length)
    cases e : p.stopAt v loc (ds.take p.moves.length) with
    | none => exact h2
    | some a =>
      intro hh
      have ha : some a = some Why.hid := hh
      exact h1 (e.trans ha)

theorem chainStopAt_not_hid (v : Option V) {hs : List (Placed V W X)} (h : NoHid hs) :
    ∀ (bs : List (Block S Cl)) loc ds, chainStopAt v bs hs loc ds ≠ some .hid
  | [], _, _ => by
    show (none : Option Why) ≠ some .hid
    simp
  | b :: bs, loc, ds => by
    show (((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v bs hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length))) ≠ some .hid
    have h2 := chainStopAt_not_hid v h bs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length)
    cases e : hs.find? (fun g => g.place == b.place) with
    | none => exact h2
    | some g =>
      have h1 := rowStopAt_not_hid v g.parts (h g (List.mem_of_find?_eq_some e)) loc
        (ds.take b.rounds.length)
      show ((rowStopAt v g.parts loc (ds.take b.rounds.length)).or _) ≠ some .hid
      cases e' : rowStopAt v g.parts loc (ds.take b.rounds.length) with
      | none => exact h2
      | some a =>
        intro hh
        have ha : some a = some Why.hid := hh
        exact h1 (e'.trans ha)

end Parts

section File
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **No second stop**: no part of the first and the last chain has a second stop that fires. First stops are free. -/
def NoSecondStop (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop := NoHid H.first ∧ NoHid H.second

theorem hidB_false_of_quiet (F : FileDescription Xi) {H : Prover W₀ Rc Xi Ky Tr X₀ X} (h : NoSecondStop H)
    (w₀ : W₀) (rc : Rc) (x : Xi) (ds : List Fmt.Drawn × List Fmt.Drawn) :
    hidB F H w₀ rc x ds = false := by
  unfold hidB
  cases H.trace w₀ x with
  | none => rfl
  | some tr =>
    have h1 := chainStopAt_not_hid (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) h.1
      F.first.blocksInOrder [] ds.1
    have h2 := chainStopAt_not_hid (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) h.2
      F.second.blocksInOrder ds.1 ds.2
    show (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first []
        ds.1 == some .hid ||
      chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second ds.1
        ds.2 == some .hid) = false
    rw [Bool.or_eq_false_iff]
    exact ⟨by simpa using h1, by simpa using h2⟩

end File

section Side
open Iop
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK SgX)
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts)
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **With no second stop the private stops are empty.** -/
theorem hid_empty_of_quiet (h : NoSecondStop H) (w : W₀ × Rc × Sd) (x : Xi) :
    (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ a =>
    Bool.false_ne_true ((hidB_false_of_quiet F h _ _ _ _).symm.trans a)

end Side

end AtPublicFiles.Stops

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀ relationsAndEncodingOfClaims RecFull ansL)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed relAt honestBatchProverOfFile simOne TiedAt Committer batchOf)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

local instance (priority := high) keyExactPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) keyExactOfInhabited {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts)
  [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃] (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  (shT : TableKey → Fx.S₂)

/-- D1: the answers as they are read off a key file's instance. -/
def ansKey (x : KeyInst) : List OnBytes.E := x.key.record.toList

theorem ansKey_along (a : XF × RecFull) : ansKey (keyInstanceOfOutOfDomainSample a.2) = ansL a.2 := by
  unfold ansKey ansL
  rfl

/-- The map that writes a key file's instance at an object's instance. -/
abbrev wrK : XF × RecFull → KeyInst := fun a => keyInstanceOfOutOfDomainSample a.2

/-- D2: the committer's structure at the key file. -/
def cmKey : Committer (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed XF KeyInst TableKey :=
  cmAt (AZ Z) PadZ (holdZ Z) wrK (fun x : KeyInst => x.key) keyAt fun _ => rfl

/-- S1: the six equations at the key file. -/
theorem tiedAt_key (hst : ∀ a : XF × RecFull, Fx.start₂ (Fx.pub (keyInstanceOfOutOfDomainSample a.2)) = shT (keyInstanceOfOutOfDomainSample a.2).key) :
    TiedAt (ansAt (AZ Z) PadZ (holdZ Z)) wrK (cmKey Z) keyAt 0
      ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) Fx shT
      (frontAt (Xi := KeyInst) (R₂ := Q₂) (R₃ := Q₃) (AZ Z) PadZ (holdZ Z))
      (joinAt (AZ Z) PadZ (holdZ Z) val₂)
      (seamAt (Xi := KeyInst) (R₂ := Q₂) (AZ Z) PadZ (holdZ Z) val₃) (pubAt val₂ val₃ ansKey) :=
  tiedAt_cmAt (AZ Z) PadZ (holdZ Z) wrK (fun x : KeyInst => x.key) keyAt (fun _ => rfl) val₂ val₃ 0
    (dataAtFiles flashProveData Z).DK Fx shT ansKey ansKey_along hst

variable (GK : Sides Fx BT (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) TableKey TrT X₀T XT)
  (HK : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)

/-- D3: the prover of the key file's rows, at the committer's structure at the first item. -/
abbrev provK : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT :=
  GK.prover ((cmKey Z).proverAt 0 HK)

/-- The key file's rounds' data at Z. -/
abbrev DKz : WholeD := (dataAtFiles flashProveData Z).DK.at frS.P.T.a

/-- D4: the offline simulator, made of the description, the book, the rows' simulators T and the public stops. -/
def simKey (T : ProofFile.Honest.Sims KeyInst TableKey) : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z) := fun x ρ a =>
  (simOne (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
      ByteArray.empty Fx silKey BT T (fun k : KeyInst => k.key) (pubAt val₂ val₃ ansKey 0)
      (honestBatchProverOfFile (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
        ByteArray.empty Fx silKey BT (provK Z Fx BT GK HK)
        (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) shT
        (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)).one.Bad
      (keyInstanceOfOutOfDomainSample x) ρ a).map (Option.map (viewRe keyInstanceOfOutOfDomainSample _))

/-- The answers of a written key. -/
theorem ansKey_inst (rec : RecFull) : ansKey (keyInstanceOfOutOfDomainSample rec) = ansL rec := by
  unfold ansKey ansL
  rfl

/-- D5: the relation: a sample is the honest one, and the rows' range holds of the index. -/
def TiedKey (Rq : FullSizeMatrix → XF → Prop) (x₀ : XF) : AtPublicFiles.KeyBridge.TiedT (protocolAtFiles Z) :=
  fun w x => x = (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2 ∧ Rq w.1 x₀

/-- S3: offlineProverWithEncodedTable's table is the committer's string. -/
theorem tableOf_is :
    tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK =
      (cmKey Z).ext (DKz Z).a := by
  funext w
  exact (ext_cmAt (AZ Z) PadZ (holdZ Z) wrK (fun x : KeyInst => x.key) keyAt (fun _ => rfl) w).symm

/-- S2: offlineProverWithEncodedTable's seam is the committer's. -/
theorem keySeam_is :
    keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃ = fun q2 q3 =>
      (cmKey Z).seam (frontAt (AZ Z) PadZ (holdZ Z) 0 q2 q3) (joinAt (AZ Z) PadZ (holdZ Z) val₂ q2)
        (seamAt (AZ Z) PadZ (holdZ Z) val₃ q2 q3) := by
  funext q2 q3
  have hf : (fun i r e (_ : KeyInst) =>
      (⟨(keyInstanceOfOutOfDomainSample (sampleOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) i r e)).key.record.toList, 0⟩ :
        OnBytes.Maker.FrontMsg (List OnBytes.E))) =
      frontAt (AZ Z) PadZ (holdZ Z) 0 q2 q3 := by
    funext i r e x
    exact congrArg (fun l => (⟨l, 0⟩ : OnBytes.Maker.FrontMsg (List OnBytes.E))) (ansKey_inst _)
  have hj : (fun i r e =>
      (⟨(keyInstanceOfOutOfDomainSample (sampleOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) i r e)).key.record.toList,
        val₂ q2⟩ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)) =
      joinAt (AZ Z) PadZ (holdZ Z) val₂ q2 := by
    funext i r e
    exact congrArg (fun l => (⟨l, val₂ q2⟩ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray))
      (ansKey_inst _)
  show ProofFile.Honest.KeyAndJoiningRoundMessages.mk _ _ _ _ = ProofFile.Honest.KeyAndJoiningRoundMessages.mk _ _ _ _
  rw [hf, hj]
  rfl

section Letters
variable {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : R₂ → R₃ → ProofFile.Honest.KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst Ky
    (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → Fx.S₂)
  (ext : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
    (Iop.oneExternalString (2 ^ ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- offlineProverWithEncodedTable's output is the side's, its views read at the object. In letters for the prover and the seam: so Lean unfolds nothing of them. -/
theorem keyHonestObj_exact (P : (filesAt Z).Provers)
    (sim : KeyInst → (ρ : Rho (batchOf (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey).loc.shape) → _ →
      PMF (Option (DView (batchOf (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey).loc)))
    (w : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : RecFull) (ρ)
    (h : (offlineBatchProver (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK Fx
        (dataAtFiles flashProveData Z).G.rec₀ B H J sh ext).one.output w (keyInstanceOfOutOfDomainSample x) ρ =
      sim (keyInstanceOfOutOfDomainSample x) ρ ((batchOf (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
                                 (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey).loc.extAns (keyInstanceOfOutOfDomainSample x) ρ (ext w))) :
    (offlineProverInThreeProtocols Z Fx B H J sh ext P).output w x ρ =
      (sim (keyInstanceOfOutOfDomainSample x) ρ ((batchOf (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
                                 (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey).loc.extAns (keyInstanceOfOutOfDomainSample x) ρ (ext w))).map
        (Option.map (viewRe keyInstanceOfOutOfDomainSample _)) :=
  AtPublicFiles.Along.exact_re (offlineBatchProver (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK Fx
                (dataAtFiles flashProveData Z).G.rec₀ B H J sh ext).one keyInstanceOfOutOfDomainSample _ id sim w x ρ h

end Letters

/-- **S4, THE RUNG: from the rows' rule at the key file to OneExact at offlineProverWithEncodedTable.** Rq: the range of the rows. -/
theorem oneExact_keyZ_of_owedAt (Rq : FullSizeMatrix → XF → Prop) (x₀ : XF)
    (hst : ∀ a : XF × RecFull, Fx.start₂ (Fx.pub (keyInstanceOfOutOfDomainSample a.2)) = shT (keyInstanceOfOutOfDomainSample a.2).key)
    (hit : AtPublicFiles.AtZero.ItemsZero Fx) (hD : ProofFile.Honest.DataFits Fx (DKz Z))
    (hdue : ∀ ρ, (ProofFile.Honest.drawsAt (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty ρ).due Fx = true)
    (hO : Owed Fx BT ((cmKey Z).proverAt 0 HK) GK.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) Rq wrK))
    (hE : GK.owns = true) :
    AtPublicFiles.KeyBridge.OneExact (offlineProverWithEncodedTable Z Fx BT (provK Z Fx BT GK HK) val₂ val₃ shT)
      (simKey Z Fx BT val₂ val₃ shT GK HK GK.sims) (TiedKey Z Rq x₀) := by
  intro w x hx ρ hρ
  obtain ⟨rfl, hq⟩ := hx
  have step : ∀ (J : Q₂ → Q₃ → ProofFile.Honest.KeyAndJoiningRoundMessages (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed KeyInst TableKey
        (OnBytes.Maker.FrontMsg (List OnBytes.E)) (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
      (e : (Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed →
        (Iop.oneExternalString (2 ^ (DKz Z).a) _root_.Run.PQ.SgX).Str),
      J = (fun q2 q3 => (cmKey Z).seam (frontAt (AZ Z) PadZ (holdZ Z) 0 q2 q3)
        (joinAt (AZ Z) PadZ (holdZ Z) val₂ q2) (seamAt (AZ Z) PadZ (holdZ Z) val₃ q2 q3)) →
      e = (cmKey Z).ext (DKz Z).a →
      ρ ∉ (honestBatchProverOfFile (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
        ByteArray.empty Fx silKey BT (provK Z Fx BT GK HK) J shT e).one.Hid w
          (keyInstanceOfOutOfDomainSample ((protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) →
      (honestBatchProverOfFile (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
        ByteArray.empty Fx silKey BT (provK Z Fx BT GK HK) J shT e).one.output w
          (keyInstanceOfOutOfDomainSample ((protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) ρ =
      simOne (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
        ByteArray.empty Fx silKey BT GK.sims (fun k : KeyInst => k.key) (pubAt val₂ val₃ ansKey 0)
        (honestBatchProverOfFile (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
          ByteArray.empty Fx silKey BT (provK Z Fx BT GK HK) J shT e).one.Bad
        (keyInstanceOfOutOfDomainSample ((protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) ρ
        ((batchOf (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀) (join₀ (dataAtFiles flashProveData Z).G.rec₀)
          ByteArray.empty Fx silKey).loc.extAns (keyInstanceOfOutOfDomainSample ((protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) ρ (e w)) := by
    intro J e hJ he hρ'
    subst hJ
    subst he
    exact ProofFile.Honest.one_exact_atItem_mute (tiedAt_key Z Fx (Q₂ := Q₂) (Q₃ := Q₃) val₂ val₃ shT hst)
      hit hO hE hD w (x₀, (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)
      (by
        rw [ansAt_eq]
        exact valid_obj (Cf (AZ Z) PadZ (holdZ Z)) (filesAt Z) (dataAtFiles flashProveData Z).P Rq w
          (x₀, (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2) ⟨rfl, hq⟩) ρ (hdue ρ) hρ'
  have base := step _ _ (keySeam_is Z val₂ val₃) (tableOf_is Z) hρ
  exact keyHonestObj_exact Z Fx BT (provK Z Fx BT GK HK)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) shT
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (dataAtFiles flashProveData Z).P _ w _ ρ base

/-- **D6: what a prover must be to be the rows' prover**: five equations. -/
structure IsProvK (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT) : Prop where
  key : HT.key = (cmKey Z).key
  stored : ∀ w rc it x, HT.stored w rc it x = if it == 0 then (cmKey Z).enc w rc x else none
  first : HT.first = GK.first.map fun L => ⟨L.place, L.row.map (·.1)⟩
  shared : HT.shared = GK.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩
  second : HT.second = GK.second.map fun L => ⟨L.place, L.row.map (·.1)⟩

theorem provK_self {HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT}
    (h : IsProvK Z Fx BT GK HT) : provK Z Fx BT GK HT = HT := by
  show GK.prover ((cmKey Z).proverAt 0 HT) = HT
  rw [ProofFile.Honest.Committer.proverAt_self h.key h.stored]
  unfold ProofFile.Honest.Sides.prover
  rw [← h.first, ← h.shared, ← h.second]

/-- **O4: S4 at a prover of the rows.** -/
theorem oneExact_keyZ_at (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (h : IsProvK Z Fx BT GK HT) (Rq : FullSizeMatrix → XF → Prop) (x₀ : XF)
    (hst : ∀ a : XF × RecFull, Fx.start₂ (Fx.pub (keyInstanceOfOutOfDomainSample a.2)) = shT (keyInstanceOfOutOfDomainSample a.2).key)
    (hit : AtPublicFiles.AtZero.ItemsZero Fx) (hD : ProofFile.Honest.DataFits Fx (DKz Z))
    (hdue : ∀ ρ, (ProofFile.Honest.drawsAt (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty ρ).due Fx = true)
    (hO : Owed Fx BT ((cmKey Z).proverAt 0 HT) GK.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) Rq wrK))
    (hE : GK.owns = true) :
    AtPublicFiles.KeyBridge.OneExact (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)
      (simKey Z Fx BT val₂ val₃ shT GK HT GK.sims) (TiedKey Z Rq x₀) := by
  have e := oneExact_keyZ_of_owedAt Z Fx BT val₂ val₃ shT GK HT Rq x₀ hst hit hD hdue hO hE
  rw [provK_self Z Fx BT GK h] at e
  exact e

/-- S5: every index in range is tied to its honest sample, at every randomness and seed. -/
theorem validTied_key (x₀ : XF) {ok : FullSizeMatrix → Prop} (hq : ∀ i, ok i → inRange i) :
    AtPublicFiles.KeyBridge.ValidTied (TiedKey Z (fun i _ => inRange i) x₀) ok fun _ => True :=
  fun i _ _ hi _ => ⟨rfl, hq i hi⟩

/-- S8c: with no second stop the private stops of offlineProverWithEncodedTable are empty. -/
theorem hid_keyZ_of_quiet (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (h : AtPublicFiles.Stops.NoSecondStop HT) (w) (x) : (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid w x = ∅ :=
  AtPublicFiles.Stops.hid_empty_of_quiet (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
    (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty Fx silKey BT
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) shT
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK) h w (keyInstanceOfOutOfDomainSample x)

section Paid
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- S6: the premises of S4 paid at the real description. -/
theorem key_paid (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (h : KeyNamed Z X N P) :
    (∀ a : XF × RecFull, (keyFileDescription X N P).start₂ ((keyFileDescription X N P).pub (keyInstanceOfOutOfDomainSample a.2)) =
        keyFirst X N P (keyInstanceOfOutOfDomainSample a.2).key) ∧
      AtPublicFiles.AtZero.ItemsZero (keyFileDescription X N P) ∧ ProofFile.Honest.DataFits (keyFileDescription X N P) (DKz Z) ∧
      ∀ ρ, (ProofFile.Honest.drawsAt (ckP .two) (DKz Z) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty ρ).due (keyFileDescription X N P) = true := by
  have hd := h.data_at
  have k := ProofFile.Honest.kinds_of_data hd
  have hz := AtPublicFiles.Written.nz_decl hd ((AtPublicFiles.Reads.key_data Z scope live).symm ▸ AtPublicFiles.Written.nz_writtenK)
  exact ⟨fun _ => keyFirst_is X N P _, AtPublicFiles.AtZero.itemsZero_of_data hd,
    ProofFile.Honest.dataFits_of_data hd h.plan,
    fun ρ => ProofFile.Honest.due_typed (ckP .two) ProofFile.Honest.kit_two _ _ _ _ k.1 k.2.1 k.2.2.1 hz k.2.2.2 ρ⟩

end Paid

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.ansKey_along
#print axioms AtPublicFiles.AtFiles.cmKey
#print axioms AtPublicFiles.AtFiles.tiedAt_key
#print axioms AtPublicFiles.AtFiles.simKey
#print axioms AtPublicFiles.AtFiles.TiedKey
#print axioms AtPublicFiles.AtFiles.tableOf_is
#print axioms AtPublicFiles.AtFiles.keySeam_is
#print axioms AtPublicFiles.AtFiles.oneExact_keyZ_of_owedAt
#print axioms AtPublicFiles.AtFiles.validTied_key
#print axioms AtPublicFiles.AtFiles.key_paid
#print axioms AtPublicFiles.Stops.hidB_false_of_quiet
#print axioms AtPublicFiles.AtFiles.hid_keyZ_of_quiet
#print axioms AtPublicFiles.AtFiles.provK_self
#print axioms AtPublicFiles.AtFiles.oneExact_keyZ_at
