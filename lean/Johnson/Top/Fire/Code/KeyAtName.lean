-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtName.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE SEVEN LETTERS THAT THE NAME's OWN CONFIGURATION FORCES WRITTEN: the out-of-domain (OOD) sample (in this library's names: the record), its reading off an instance, the stored table's decoded message, its decoder and the event «the OOD sample does not single one table out».
The setting. The first border's facts (`FirstFour`, KeyAtBase.lean) tie our tables' letters to the configuration of a stored table with an OOD sample (`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean) at the full size's decoder. NO HASH STANDS IN THAT CONFIGURATION: an OOD sample is any pair of a seed and answers; the seed is the sample's datum here. The chance, over what an oracle draws, that a seed is one at which a table collides is another row's, not this file's.
Main names.
  `MsgN`: a decoded table: over the extension field · `yOf cell`: the stored table off its cells · `recBack x`: the OOD sample whose key the instance x is (one at most: `keyOf_injective`, OnBytes/Slice/KeyOfRecInj.lean) · `decN cell r`: the configuration's own decoder at `yOf cell` · `collN s r`: its own event at `yOf s.cell` and r's seed.
  `recBack_instK` · `yOf_cell` (what is read off a boundary's strings is the stored table itself) · `cellOnly_collN`.
  `HeldAtName A E X tab`: THE ONE FIELD OF THE FIRST BORDER THAT IS LEFT: at every table u THAT THE DECODER RETURNS (the tables' field `held` as turned on a decision in this project): if both lookups' relation holds of the matrix that `tab u` says, the configuration holds an index at u.
  `firstFour_at_name`: recAt · coll · dec are paid; held is `HeldAtName`.
  `The21AtName A E X N P DK`: `The21AtBase` at these seven: beside the 21 laws: off · HeldAtName · the four bases. Letters left: tab · enc · rad · off₂ · off₃.
  `base_of_name`: it gives `The21AtBase`.
OBJECT: `Key.descriptionFromSource X N P`; `DecR.configurationOfStoredTable` at the full size's decoder · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: A · E.
Limits. NO LAW IS PAID. Each of the 21 laws is owed at these terms; `The21AtBase` and `The21Handed` stay beside. (Where
this and lean/THEOREM.md differ, the page holds.) `tab` has values in the base field's words while a decoded table is over the extension: that every member of the list of a table over the base field is over it lies in the library (`Cb.ldFc_overF`); its call at this decoder and a stored table is `dcd_base_full` (Johnson/Desc/K14/Law/BaseValued.lean); neither is called here. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtBase
import OnBytes.Slice.KeyOfRecInj

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (atSix)

/-- The full size's decoder of a stored table with an OOD sample. -/
abbrev DN : DecR := frS.toDecR frZ 402653181

/-- A decoded table: over the extension field. -/
abbrev MsgN : Type := DN.ix.Row × DN.toDec.En → GE

/-- The stored table, off its cells. -/
def yOf (cell : ℕ → Option (ℕ × List UInt64)) : Fin (2 ^ frS.P.T.a) → SgX := fun p => (cell p.val).getD (0, [])

theorem instK_injective : Function.Injective VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample := fun _ _ h =>
  OnBytes.Slice.keyOf_injective (fun β : NZ => β.val) Subtype.val_injective (congrArg (·.key) h)

open Classical in
/-- The OOD sample whose key the instance is. -/
def recBack (x : Xi) : Option RecFull :=
  if h : ∃ r, VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r = x then some (Classical.choose h) else none

theorem recBack_instK (r : RecFull) : recBack (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r) = some r := by
  have h : ∃ r', VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r' = VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r := ⟨r, rfl⟩
  unfold recBack
  rw [dif_pos h]
  exact congrArg some (instK_injective (Classical.choose_spec h))

/-- The configuration's own decoder, at the stored table off the cells. -/
def decN (cell : ℕ → Option (ℕ × List UInt64)) (r : RecFull) : Option MsgN := DN.dcd (yOf cell) r

/-- The configuration's own event «the OOD sample does not single one table out», at the stored table off the cells and the sample's seed. -/
def collN (s : Strs) (r : RecFull) : Prop := DN.coll (yOf s.cell) r.1

theorem cellOnly_collN : CellOnly collN := fun y y' x h => by
  unfold collN
  rw [h]

/-- **What is read off a boundary's strings is the stored table itself.** -/
theorem yOf_cell (D : WholeD) (y : (oneExternalString (2 ^ (D.at frS.P.T.a).a) SgX).Str) :
    yOf (strsOf (fr₁ (D.at frS.P.T.a)) ((y, fun _ => []) : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)).cell = y := by
  funext p
  show ((cellAt (fr₁ (D.at frS.P.T.a)) _ p.val).getD (0, [])) = y p
  unfold cellAt
  rw [dif_pos p.isLt]
  rfl

/-- **THE ONE FIELD OF THE FIRST BORDER THAT IS LEFT.** -/
def HeldAtName {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (tab : MsgN → ℕ → ℕ → OnBytes.F) : Prop :=
  ∀ (r : RecFull) (y : DN.toDec.Pos → SgX) (u : MsgN), DN.dcd y r = some u → (∀ l, l < Johnson.RunOne.KeyRows1.n₁ (oneAt X) → ∃ L, (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lookups[l]? = some L ∧
      InRange (readAt tab).same (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).m L (matAt (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lin (tab u))) →
    ((lettersAt A (relationsAndEncodingOfClaims A E)).conf.held u).isSome

/-- **recAt · coll · dec are paid at the written seven.** -/
theorem firstFour_at_name {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (tab : MsgN → ℕ → ℕ → OnBytes.F) (h : HeldAtName A E X tab) :
    FirstFour (fr₁ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₁ (oneAt X) (readAt tab) collN VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) id
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held id :=
  ⟨fun r => recBack_instK r,
    fun r y hc => by
      have hc' : DN.coll (yOf (strsOf (fr₁ (DK.at frS.P.T.a)) ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)).cell) r.1 := hc
      rw [yOf_cell] at hc'
      exact hc',
    fun r y c hd => by
      have hd' : DN.dcd (yOf (strsOf (fr₁ (DK.at frS.P.T.a)) ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)).cell) r = some c := hd
      rw [yOf_cell] at hd'
      exact ⟨c, hd', rfl⟩,
    fun r y u hu => h r y u hu⟩

/-- **WHAT IS OWED, AT THE SEVEN LETTERS THAT THE NAME FORCES.** -/
def The21AtName {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (tab : MsgN → ℕ → ℕ → OnBytes.F)
      (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (off₂ off₃ : ℕ → ℕ)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ off₃ ∧
      (∀ k ∈ [0, 2], off₃ (atSix k).1 = (atSix k).1) ∧
      HeldAtName A E X tab ∧
      (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[0]? = some p → ∀ j ∈ pinned seam, (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (atSix j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (atSix j).1 < p.base)

/-- **It gives what is owed at the written reading.** -/
theorem base_of_name {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (h : The21AtName A E X N P DK) : The21AtBase A E X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  obtain ⟨tab, enc, rad, off₂, off₃, dS, H, off, hh, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  exact ⟨MsgN, RecFull, ⟨fun _ => 0⟩, decN, recBack, tab, enc, rad, collN, off₂, off₃, id, id, dS, H, off,
    firstFour_at_name A E X N P DK tab hh, cellOnly_collN, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩

end LPFD

#print axioms LPFD.instK_injective
#print axioms LPFD.recBack_instK
#print axioms LPFD.cellOnly_collN
#print axioms LPFD.yOf_cell
#print axioms LPFD.HeldAtName
#print axioms LPFD.firstFour_at_name
#print axioms LPFD.The21AtName
#print axioms LPFD.base_of_name
