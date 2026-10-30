-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontAtK10.lean: e₁'s ROW 121: OF K10's FIRST TIE, THE CLAUSE "front" AT
THE CONCRETE fa (faK10, Johnson/Desc/First/Close/Law/FaK10.lean): FROM THE PROMISE IN
FRONT, AT THE COMPOSED MEANING (mgAll 𝔇 Mg). Theorems with their proofs; three facts on written
values by the kernel.

How. The promise, at a state without a mark, gives "no collision" at every sampled tenant whose pin
is open (Johnson/Desc/First/Borders.lean: onAt). At mgAll that is CfAt of each member of 𝔇.ms AT ITS
OWN SENDING's LIST; faK10 reads the GROUP's list lo. cf_move
(Johnson/Desc/Sound/PinMove.lean) carries CfAt between two members that are alike (one entry of the
list, one seat), where the samples' reader reads by the seat (SmpBySeat). Then fa_front.

  SitsIn           THE NAMED PREMISE ON lo AND seat: every member i of lo is alike to a member of
                   𝔇.ms, and seat i is a sampled tenant whose pin is open (sampledIn Nu O)
  cf_of_promise    the promise in front · no mark · SitsIn · SmpBySeat ⊢ CfAt at every member of lo
  front_of_promise **K10On's clause front at faK10**, from these and A₀.on (st₀, e₀)
  lists_fit_full   BY THE KERNEL, at the written values of the full size: at l = 1 … 25 the written
                   list of the link (Johnson.G.linksFullLit) has as many members as the table's
                   group has sampled tenants, and their shapes are, one by one in the group's order,
                   the plan's sampled seats'
  list0_parts      BY THE KERNEL: AT l = 0 IT HAS ONE MEMBER MORE (6 against 5): the fourth: its
                   shape is that of the plan's seat "at start" (the index masks' message), which the
                   table's numbers keep out of every group (its pin is pinI). By a reading,
                   not shown here, the typed group has five there too (its members are
                   those with a main row); the signature has six
  pinI_open_full   BY THE KERNEL: pinI is open at K10's 25 borders: so that tenant too is in
                   sampledIn

Limits. SitsIn AND A₀.on (st₀, e₀) ARE PREMISES: no term for seat is given here; lo's radii are held
against nothing. 𝔇 IS A LETTER. The clause tied, and masks · rows · code · the two equations, are
not treated. No soundness statement.

-/
import Johnson.Desc.First.Close.Law.FaK10
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.AtDriver
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start openSets sampledIn
  flatPlacesOf)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The named premise on the group's list and its seats.** -/
def SitsIn (Nu : Numbers) (O : List Item) (lo : List (OracleShape × ℕ))
    (seat : Fin lo.length → ℕ × ℕ) : Prop :=
  ∀ i : Fin lo.length, (∃ m ∈ 𝔇.ms, Alike m ⟨⟨lo, seat⟩, i⟩) ∧ seat i ∈ sampledIn Nu O

/-- **"No collision" at every member of the group's list, from the promise in front.** -/
theorem cf_of_promise {F : Frame} (Nu : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (a : (P × S) × F.E.Str) (hon : onQ Nu (mgAll 𝔇 Mg) links ps (fun a => a) k a)
    (hm : a.1.2.failed = none) (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
    (hM : SitsIn 𝔇 Nu ((openSets links ps (start links))[k]?.getD []) lo seat)
    (hS : SmpBySeat 𝔇.cs 𝔇.smp) (i : Fin lo.length) :
    CfAt 𝔇.G 𝔇.cs lo seat (fun z j => 𝔇.smp z ⟨lo, seat⟩ j) i a.1 (strsOf F a.2) := by
  obtain ⟨⟨m, hm1, hal⟩, hin⟩ := hM i
  rcases hon.2 with hx | ⟨-, -, hc, -⟩
  · exact absurd hm hx
  · have hn : noCollJT 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms (seat i).1 (seat i).2 a.1 (strsOf F a.2) :=
      (hc (seat i) hin).2
    have h1 := hn m hm1 hal.2
    exact (cf_move 𝔇.cs 𝔇.G 𝔇.smp m ⟨⟨lo, seat⟩, i⟩ hal a.1 (hS a.1 m _ hal) (strsOf F a.2)).1 h1

end

/-! ## The written values of the full size -/

/-- The plan's sampled seats' shapes at a group's tenants, in the group's order. -/
def groupShapes (l : ℕ) : List (Option OracleShape) :=
  (P5T.N0Full.group l).map fun t => (P5T.psFull.find? fun p => p.seat == t && p.smpd).map (·.shape)

/-- The written list fits the table's group. -/
def listFitsB (l : ℕ) : Bool :=
  let lo := Johnson.G.linksFullLit.getD l []
  decide (lo.length = (P5T.N0Full.group l).length) &&
    (lo.zip (groupShapes l)).all fun x => x.2 == some x.1.1

set_option maxRecDepth 1000000 in
theorem lists_fit_full : ((List.range 25).all fun l => listFitsB (l + 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At l = 0 the written list has one member more: the fourth, of the shape of the seat at
start. -/
theorem list0_parts : listFitsB 0 = false ∧ (Johnson.G.linksFullLit.getD 0 []).length = 6 ∧
    (P5T.N0Full.group 0).length = 5 ∧
    ((Johnson.G.linksFullLit.getD 0 [])[3]?.map (·.1)) =
      (P5T.psFull.find? (·.isStart)).map (·.shape) ∧
    (((Johnson.G.linksFullLit.getD 0 []).eraseIdx 3).zip (groupShapes 0)).all
      (fun x => x.2 == some x.1.1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- pinI is open at K10's 25 borders. -/
theorem pinI_open_full : ((List.range 25).all fun l =>
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[
      (if l = 24 then 350 else 14 * l + 12)]?.getD []).contains Item.pinI) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

namespace VerifiableInference.Desc.First.Close
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets)
open VerifiableInference.Desc.LinkJoin (SitsIn cf_of_promise)

variable {Xi Pz Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi Pz Tok rows cols nR X)
  (Mg : Meaning Pz (Wit (CellsQ rows cols) Tok MsgT))
  (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
variable (R : RowsK (sigOf 𝔇.cs lo)) (N : SlotNames R) (keep : (sigOf 𝔇.cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf 𝔇.cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf 𝔇.cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))
  (σ₀ : (sigOf 𝔇.cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : VerifiableInference.Desc.First.S × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **K10On's CLAUSE front AT faK10, FROM THE PROMISE IN FRONT.** -/
theorem front_of_promise (Nu : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (a : (Pz × VerifiableInference.Desc.First.S) × F.E.Str)
    (hon : onQ Nu (mgAll 𝔇 Mg) links ps (fun a => a) k a) (hm : a.1.2.failed = none)
    (hM : SitsIn 𝔇 Nu ((openSets links ps (start links))[k]?.getD []) lo seat)
    (hS : SmpBySeat 𝔇.cs 𝔇.smp) (hA : A₀.on (st₀, e₀)) :
    ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
      R.Sh.par.Cw.nat).on
      (faK10 𝔇.G 𝔇.cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun z j => 𝔇.smp z ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW a.1.1 (a.1.2, a.2)) :=
  fa_front 𝔇.G 𝔇.cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
    (fun z j => 𝔇.smp z ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW a.1.1 (a.1.2, a.2)
    (fun i => cf_of_promise 𝔇 Mg Nu links ps k a hon hm lo seat hM hS i) hA

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.LinkJoin.cf_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.lists_fit_full
#print axioms VerifiableInference.Desc.LinkJoin.list0_parts
#print axioms VerifiableInference.Desc.LinkJoin.pinI_open_full
#print axioms VerifiableInference.Desc.First.Close.front_of_promise
