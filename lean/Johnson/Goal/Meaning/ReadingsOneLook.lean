-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ReadingsOneLook.lean: THE LOOKUPS' FOUR CLAUSES OF THE MEANING's ROW, AT THE
MEANING's OWN LISTS. The lookups' closed callers (Johnson/Desc/First/Look/K3CallerAttMeans.lean,
K3CallerLay.lean) end in the clauses at whatever integer matrices their named readings CellsAre |
MatsAre hold of. Here these readings are paid at ownAtF, by baseAt_look and ownAtF_mzAt
(Johnson/Goal/Meaning/ReadingsOne.lean), and the four clauses follow as the fields of Twelve
(Johnson/Goal/Meaning/HidFirst.lean) type them. Three definitions, eleven theorems, proved. They add
no strength beyond syms_one_label and the lookups' theorems: compositions, and two equations on
sizes.

  zsOf_eq_mzTot   the lookups' zsOf and the library's mzTot are one function.
  sizesClosed_eq   sizesClosed X funs is fun k => szOf (closedRec X funs k), by unfolding.
  ownK, ownK_nr, szOf_closedRec, ownAtF_closed   THE SIZES: a list does not read the size's number
    of reads; a closed record's size parts from the plan's record's in that number alone; so, at
    seats by the label, ownAtF at sizesClosed X funs, at every funs, IS ownAtF at the sizes of the
    plans' own records tlAt X, sub-proof by sub-proof.
  ownL X D num tls msgF k   short for ownAtF at the sizes szOf (tls ·) and the seats seatBy (fLay
    D.layout num) X.
  SymsAre X D rad num idx tls msgF k m   the family's member k has, at the seats of sub-proof k
    within the sizes, the symbols of the tuple m: an equation of symbols, not of readings.
  matsAre_own, cellsAre_own   the two named readings at ownL, under three premises: linkTieB at the
    link x.link; SymsAre; BaseSegF (the meaning's own clause: the symbols of sub-proof x.link are
    the packing of small integers).
  gKey_own, gHot_own   KeyField | HotField at ownL … (2 g), where x.link = 2 g.
  aKey_own, aRidden_own   AttKey | AttRidden at ownL … (2 g + 1), where x.link = 2 g + 1.

Object, user, letters. Object: MatsAre, CellsAre, KeyField, HotField, AttKey, AttRidden, ownAtF.
User: none in the library yet; it is shaped for whoever owes Twelve's fields gKey, gHot, aKey and
aRidden at ownAtF (sizesClosed X funs) (seatBy (fLay layout num) X ·) msgF: take tls := tlAt X and
rewrite by ownAtF_closed. Letters: as in ReadingsOne.lean and the lookups' files; all free.

WHO PAYS THE PREMISES. The joint in front of the proved lookup block (relR), LayOK | AttOK, TabsAre,
hU: the lookups' files. WeightsAre: whoever pins the weights. BaseSegF: the smallness test's
clause. linkTieB: a test on public data. SymsAre: a choice of the family: ONE READING A LINK, a
borrowed array in the borrower's kept copy.

What is not claimed. Any premise. That reader's and owner's readings agree at that family
(ReadsOne). The other eight fields of Twelve. Anything at another size than the full one: KeyField
and HotField stand at the reference sizes. Nothing on soundness, nothing on hiding. The program does
not import this file.
-/
import Johnson.Goal.Meaning.ReadingsOne
import Johnson.Goal.Meaning.HidSumClosed
import Johnson.Goal.Meaning.Row
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Model
open OnBytes.Road (Mats)
open OnBytes.Road.Rows.Norms (mzTot KeyField HotField)
open Cb.Pv.Tail (Size BaseAt)
open Johnson.Pack (sigOf)
open VerifiableInference.OnPublicFiles (kLookupCR)
open VerifiableInference.Desc.First.Look

/-- The two ways to write integers at the cells as total matrices are one. -/
theorem zsOf_eq_mzTot (s : Size) (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) :
    zsOf s Mz = mzTot Mz := by
  funext a r c
  unfold zsOf mzTot
  by_cases h : a < s.NM
  · by_cases hc : c < s.k a
    · by_cases hr : r < s.m a
      · rw [dif_pos ⟨h, hc, hr⟩, dif_pos h, dif_pos hc, dif_pos hr]
      · rw [dif_neg (fun hh => hr hh.2.2), dif_pos h, dif_pos hc, dif_neg hr]
    · rw [dif_neg (fun hh => hc hh.2.1), dif_pos h, dif_neg hc]
  · rw [dif_neg (fun hh => h hh.1), dif_neg h]

/-- The closed records' sizes are the lookups' sizes of the closed records. -/
theorem sizesClosed_eq (X : Model.Verify.Public) (funs : ℕ → Array Model.HFun) :
    sizesClosed X funs = fun k => szOf (closedRec X funs k) := rfl

/-! ## The lists do not read the number of reads -/

/-- The list behind the symbols at one size, the seats a function of the entry's number. -/
noncomputable def ownK (σ : Size) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) : Mats ℤ :=
  mzTot (OnBytes.Road.Rows.mzAt (symAt σ (fun μ => f μ.val) msg))

/-- It does not read the size's number of reads. -/
theorem ownK_nr (σ : Size) (n : ℕ → ℕ) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) :
    ownK { σ with nr := n } f msg = ownK σ f msg := rfl

/-- The closed record's size is the plan's record's, but for the number of reads. -/
theorem szOf_closedRec (X : Model.Verify.Public) (funs : ℕ → Array Model.HFun) (k : ℕ) :
    szOf (closedRec X funs k) =
      { szOf (tlAt X k) with nr := (szOf (closedRec X funs k)).nr } := by
  unfold closedRec openAt
  split <;> rfl

/-- **The list of sub-proof k is one, at the closed records' sizes and at the plans' records'**, at
seats by the label. -/
theorem ownAtF_closed (X : Model.Verify.Public) (funs : ℕ → Array Model.HFun)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msgF : ℕ → Msgs) (k : ℕ) :
    ownAtF (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msgF k =
      ownAtF (fun j => szOf (tlAt X j)) (seatBy f X fun j => szOf (tlAt X j)) msgF k := by
  show ownK (szOf (closedRec X funs k)) (fun μ => f (labAt X k μ)) (msgF k) =
    ownK (szOf (tlAt X k)) (fun μ => f (labAt X k μ)) (msgF k)
  rw [szOf_closedRec, ownK_nr]

section
variable {X : Model.Verify.Public} {D : Sent} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  {rad : OracleShape → ℕ} (msgF : ℕ → Msgs) {x : Place}

/-- The meaning's list of sub-proof k, at the sizes of the records tls and the seats off the layout
by the label. -/
noncomputable abbrev ownL (X : Model.Verify.Public) (D : Sent) (num : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
    (msgF : ℕ → Msgs) (k : ℕ) : Mats ℤ :=
  ownAtF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF k

/-- The family's member k has, at the seats of sub-proof k, the symbols of the tuple m of link k. -/
def SymsAre (X : Model.Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ)
    (idx : ℕ → ℕ) (tls : ℕ → HTailF2) (msgF : ℕ → Msgs) (k : ℕ)
    (m : (sigOf D.codes (sigListCalls D rad k)).Msg) : Prop :=
  symAt (szOf (tls k)) (fun μ => fLay D.layout num (labAt X k μ.val)) (msgF k) =
    symAt (szOf (tls k)) (fun μ => fLay D.layout num (labAt X k μ.val))
      (msgsOfTuple D.codes (sigListCalls D rad k) idx m)

/-- **The layers' named reading of the cells, at the meaning's own list.** -/
theorem matsAre_own (T : linkTieB X D rad num idx x.link (tls x.link) = true) {oW : Cb.OMsg Cb.Gl.E}
    {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} (m : (laySg x D rad oW).Msg)
    (hm : SymsAre X D rad num idx tls msgF x.link (ownPart m))
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link) :
    MatsAre x (tls x.link) D rad oW wOf nr nc m (ownL X D num tls msgF x.link) := by
  unfold ownL
  rw [ownAtF_mzAt, ← zsOf_eq_mzTot]
  exact lay_mats_cast m _ (baseAt_look T (ownPart m) (msgF x.link) hm hB)

/-- **Attention's named reading of the cells, at the meaning's own list.** -/
theorem cellsAre_own (T : linkTieB X D rad num idx x.link (tls x.link) = true) {S : Attention.Shape}
    (m : (attSg x D rad).Msg)
    (hm : SymsAre X D rad num idx tls msgF x.link m)
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link) :
    CellsAre x S (tls x.link) D rad m (ownL X D num tls msgF x.link) := by
  unfold ownL
  rw [ownAtF_mzAt, ← zsOf_eq_mzTot]
  exact attCells_cast m _ (baseAt_look T m (msgF x.link) hm hB)

/-! ## The lookups' four clauses of the row, at the meaning's own lists -/

variable {set : Params.Setting} (Ex : Iop.ExtSpec) (Wp : Type) {g : ℕ}

/-- **gKey at group g**: the field of Twelve, at the list of sub-proof 2 g. -/
theorem gKey_own (hl : x.link = 2 * g) (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} (H : LayOK set x)
    (a : Unit × Ex.Str) (v : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩ (tls x.link) D rad oW
        wOf nr nc Ex Wp]).A
      (layRider x ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩ (tls x.link) D rad oW wOf nr nc Ex
        Wp)).relR a v)
    (hm : SymsAre X D rad num idx tls msgF x.link (ownPart v.1))
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link)
    (Wi : Inst.Model.Mat) (hW : WeightsAre x (tls x.link) D rad oW wOf nr nc g v.1 Wi) :
    KeyField (Verify.layerShape X.P) X.layers.sc X.y g (ownL X D num tls msgF (2 * g)) Wi := by
  rw [← hl]
  exact lay_layKey (p := ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩) Ex Wp H a v h _
    (matsAre_own tls msgF T v.1 hm hB) Wi hW

/-- **gHot at group g.** -/
theorem gHot_own (hl : x.link = 2 * g) (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
    (a : Unit × Ex.Str) (v : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩ (tls x.link) D rad oW
        wOf nr nc Ex Wp]).A
      (layRider x ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩ (tls x.link) D rad oW wOf nr nc Ex
        Wp)).relR a v)
    (hm : SymsAre X D rad num idx tls msgF x.link (ownPart v.1))
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link)
    (Wi : Inst.Model.Mat) (xi : Cm.Seg.XI) :
    HotField (Verify.layerShape X.P) X.layers.sc X.y g (ownL X D num tls msgF (2 * g)) Wi xi := by
  rw [← hl]
  exact lay_layHot (p := ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩) Ex Wp a v h _
    (matsAre_own tls msgF T v.1 hm hB) Wi xi

/-- **aKey at group g**: at the list of sub-proof 2 g + 1. -/
theorem aKey_own (hl : x.link = 2 * g + 1) (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (H : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad) (a : Unit × Ex.Str)
    (v : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x (Road.Hd.shapeA X g) (tls x.link) D rad Ex Wp]).A
      (attRider x (Road.Hd.shapeA X g) (tls x.link) D rad Ex Wp)).relR a v)
    (hm : SymsAre X D rad num idx tls msgF x.link v.1)
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link)
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) :
    AttKey (Road.Hd.shapeA X g) (ownL X D num tls msgF (2 * g + 1)) := by
  rw [← hl]
  exact att_attKey Ex Wp H a v h _ (cellsAre_own tls msgF T v.1 hm hB) hT hU

/-- **aRidden at group g.** -/
theorem aRidden_own (hl : x.link = 2 * g + 1)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (H : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad) (a : Unit × Ex.Str)
    (v : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x (Road.Hd.shapeA X g) (tls x.link) D rad Ex Wp]).A
      (attRider x (Road.Hd.shapeA X g) (tls x.link) D rad Ex Wp)).relR a v)
    (hm : SymsAre X D rad num idx tls msgF x.link v.1)
    (hB : BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j)) msgF
      x.link) :
    AttRidden (Road.Hd.shapeA X g) (ownL X D num tls msgF (2 * g + 1)) := by
  rw [← hl]
  exact att_attRidden Ex Wp H a v h _ (cellsAre_own tls msgF T v.1 hm hB)

end

end Meaning

#print axioms Meaning.ownK_nr
#print axioms Meaning.szOf_closedRec
#print axioms Meaning.ownAtF_closed
#print axioms Meaning.gKey_own
#print axioms Meaning.gHot_own
#print axioms Meaning.aKey_own
#print axioms Meaning.aRidden_own
#print axioms Meaning.zsOf_eq_mzTot
#print axioms Meaning.sizesClosed_eq
#print axioms Meaning.matsAre_own
#print axioms Meaning.cellsAre_own
