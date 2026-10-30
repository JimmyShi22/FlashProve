-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LaidArrAtHead.lean: THE KIND K9 (a link's batching): THE TWO TESTS hB | hZ THAT THE
SENTENCE cells OF hLeft STILL NAMES (laidArrB, Johnson/Desc/First/Link/Law/CellPub.lean, at
the counts' array ix.BZ and at the digits' array ix.ZZ), AT EACH OF THE 25 LINKS, FROM THE HEAD
ALONE, AT THE CLOSED LETTERS At.…. At every o; at every radii.
THE ARGUMENT. THE NAME THAT THE LINK's LIST GIVES THE ARRAY NEED NOT BE KNOWN. (a) The verifier's
own entry test on the digits (K3Asks.digEntry: LPFD.asks_rest; asks_digB) accepts under the
head: its clause arrB at ZZ and at BZ says: the list has an entry there; it names the link itself;
the layout has an array of that name at that link; the array's message's number lies in the list of
the link's messages (arr_parts). (b) At the written layout, codes and shape EVERY array of EVERY
link passes laidMatrixOk at its own message's bits: Lean's kernel
(Johnson/P2LawR/LaidArrWritten.lean). (c) Under the head layout, codes and shape are the written
ones (first_written_in_scope, Johnson/Goal/Numbers/MadeInScope.lean).
  arr_parts · mem_of_reqArray what arrB's yes says; an array that reqArray finds is one of the
      link's.
  laidArr_of   laidArrB from arrB, at data with the written codes, shape and layout.
  **AtMg.hBZ_cells**   the two.
Limits. xx.link = m IS A PREMISE (el): left_cells (Johnson/P5J/K09LeftCells.lean) has it in its own
proof. h3 AND hp | hpl ARE NOT HERE. NO MEMBER: that a head can be had is not said. The full size
alone. At the door's list of thirteen rows alone.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.

-/
import Johnson.P2LawR.LaidArrWritten
import Johnson.P2LawR.CellsAtHead
import Johnson.Desc.First.Look.K3AsksPlan
import Johnson.Desc.First.Look.K3AsksDoorLaw
import Johnson.Desc.Laid.ProofAsksLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K9C
open OnBytes
open VerifiableInference.Desc.LinkJoin (laidArrB)
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open VerifiableInference.Desc.First.Look (Sent sigList lastMoment arrB)
open P2Law.K3M (sentW)

/-- What a yes of the test on an array says of the list, the layout and the messages. -/
theorem arr_parts {S : Road.Rows.Shape} {D : Sent} {l : List (OracleShape × ℕ)} {i t : ℕ}
    (h : arrB S D l i t = true) :
    ∃ bn a o, (D.arrayOf.getD i #[])[t]? = some bn ∧ bn.1 = i ∧
      reqArray D.layout i bn.2 = some a ∧ l[a.message]? = some o := by
  unfold VerifiableInference.Desc.First.Look.arrB at h
  split at h
  · rename_i T bn hT hbn
    rw [Bool.and_eq_true] at h
    obtain ⟨hi, h⟩ := h
    split at h
    · rename_i a ha
      split at h
      · rename_i o ho
        exact ⟨bn, a, o, hbn, by simpa using hi, ha, ho⟩
      · cases h
    · cases h
  · cases h

/-- An array that reqArray finds is one of the link's. -/
theorem mem_of_reqArray {lay : Params.ReqLayout} {i : ℕ} {n : String} {a : Params.ReqArray}
    (h : reqArray lay i n = some a) : a ∈ (lay.link[i]?).getD [] := by
  unfold OnBytes.reqArray at h
  cases e : lay.link[i]? with
  | none =>
    rw [e] at h
    cases h
  | some arrs =>
    rw [e] at h
    have h' : arrs.find? (fun a => a.name == n) = some a := h
    exact List.mem_of_find?_eq_some h'

/-- **laidArrB from arrB, at data with the written codes, shape and layout.** -/
theorem laidArr_of (D : Sent) (rad : OracleShape → ℕ) {S : Road.Rows.Shape} {i t : ℕ}
    (hA : arrB S D (sigList D rad i (lastMoment D i)) i t = true) (hc : D.codes = sentW.codes)
    (hs : D.shape = sentW.shape) (hl : D.layout = sentW.layout) (hi : i < 25) :
    laidArrB D (sigList D rad i (lastMoment D i)) i t = true := by
  obtain ⟨bn, a, o, hbn, e1, ha, ho⟩ := arr_parts hA
  have W := List.all_eq_true.1 laidAll_written i (List.mem_range.2 hi)
  unfold laidLinkW at W
  have ma : a ∈ (sentW.layout.link[i]?).getD [] := by
    rw [← hl]
    exact mem_of_reqArray ha
  have W1 := List.all_eq_true.1 W a ma
  have f : ((sigList D rad i (lastMoment D i)).map (·.1))[a.message]? = some o.1 := by
    rw [List.getElem?_map, ho]
    rfl
  rw [last_congr hs i, sig_fst hs rad (fun _ => 0) i _] at f
  have f' : ((digW i).map (·.1))[a.message]? = some o.1 := f
  rw [List.getElem?_map] at f'
  obtain ⟨sh, hsh, esh⟩ := Option.map_eq_some_iff.1 f'
  rw [hsh] at W1
  have W2 : laidMatrixOk a (rowBitsOf sh.1 .main) (placeBitsOf sentW.codes sh.1 .main) = true := W1
  unfold VerifiableInference.Desc.LinkJoin.laidArrB
  rw [hbn]
  simp only [Option.any_some]
  rw [e1, ha]
  simp only [Option.any_some]
  rw [ho]
  simp only [Option.any_some]
  rw [hc, ← esh]
  exact W2

end P2Law.K9C

namespace P5J
open OnBytes OnBytes.Maker OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (laidArrB)
open VerifiableInference.Desc.First.Look (digList sigList lastMoment arrB)
open P2Law.K3M (sentW)
open P2Law.K9C

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **hB AND hZ AT EACH OF THE 25 LINKS, FROM THE HEAD ALONE.** -/
theorem AtMg.hBZ_cells (h : AtMg o Z D r Zp Np cF) {m : ℕ} (hm : m < 25)
    {xx : VerifiableInference.Desc.First.Look.Place} {tlD : HTailF2}
    (hd : VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD))
    (el : xx.link = m) (rad : OracleShape → ℕ) :
    laidArrB (At.sentAt Zp) (digList xx (At.sentAt Zp) rad) xx.link tlD.ix.BZ = true ∧
      laidArrB (At.sentAt Zp) (digList xx (At.sentAt Zp) rad) xx.link tlD.ix.ZZ = true := by
  have hF := VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
    h.made_accepts
  have hc : (At.sentAt Zp).codes = sentW.codes := hF.1
  have hl : (At.sentAt Zp).layout = sentW.layout := hF.2.2.2.2.2
  have hs : (At.sentAt Zp).shape = sentW.shape := h.masks_shape_written
  obtain ⟨k4, kN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  have hlk : VerifiableInference.Desc.K3Asks.linksOf (At.X Zp) = 25 :=
    VerifiableInference.Desc.K3Asks.links_25 (by rw [k4, kN]; rfl)
  have hr : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true :=
    (LPFD.asks_rest h.laid.asks h.laid.pub).1
  obtain ⟨x, tl, e, B⟩ := VerifiableInference.Desc.K3Asks.asks_digB hr rad m (by rw [hlk]; exact hm)
  have ex := Option.some.inj (e.symm.trans hd)
  obtain rfl : x = xx := congrArg Prod.fst ex
  obtain rfl : tl = tlD := congrArg Prod.snd ex
  unfold VerifiableInference.Desc.First.Look.digB at B
  rw [Bool.and_eq_true] at B
  have B4 := B.2
  unfold VerifiableInference.Desc.First.Look.digAddrB at B4
  simp only [Bool.and_eq_true] at B4
  obtain ⟨⟨⟨⟨-, aZ⟩, aB⟩, -⟩, -⟩ := B4
  have hi : x.link < 25 := by rw [el]; exact hm
  have aZ' : arrB x.arrays (At.sentAt Zp)
      (sigList (At.sentAt Zp) rad x.link (lastMoment (At.sentAt Zp) x.link)) x.link tl.ix.ZZ =
        true := aZ
  have aB' : arrB x.arrays (At.sentAt Zp)
      (sigList (At.sentAt Zp) rad x.link (lastMoment (At.sentAt Zp) x.link)) x.link tl.ix.BZ =
        true := aB
  exact ⟨laidArr_of (At.sentAt Zp) rad aB' hc hs hl hi,
    laidArr_of (At.sentAt Zp) rad aZ' hc hs hl hi⟩

end P5J

#print axioms P2Law.K9C.arr_parts
#print axioms P2Law.K9C.mem_of_reqArray
#print axioms P2Law.K9C.laidArr_of
#print axioms P5J.AtMg.hBZ_cells
