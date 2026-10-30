-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): two of the library's three families of identities on
an attention segment (at1: the bits of the index of a row's largest score are bits; at2: the row's
largest score is the score at that index) AT ANY FUNCTION t OF THE CELLS' NAMES THAT AGREES WITH THE
WITNESS's DATA ON THE VALID NAMES, FROM TWO ITEMS THAT THE ROW OF THE SEGMENT's OWN ROUNDS (kind K5)
ASKS IN FRONT: the constraint's parts "idn" and "small" of the segment.

Why. The laws on the values of the kind take the identities of the honest trace's cells as a premise
on the run's input. The row asks the item "idn" of the witness in front, and no law spends it.

What the item says, at the honest side's constant decoder (c: the input's cells): FOR EVERY INDEX i
THAT c HOLDS: the two families at the model's integers, as the witness is read
(`zofAll`, Johnson/Desc/First/Att/Door/Law/K5RestIdn.lean), over the base field. c STANDS IN IT AS A
GUARD ALONE: where c holds no index the item says nothing: so hH is a premise here.

The road, each step a lemma that lies:
  the item "small" has "the committed symbols are the packing of small integers" as its first
    clause; under it the cells read off the witness's messages ARE the casts of the model's integers
    (`cells_all`, Johnson/Desc/First/Att/Door/Law/K5RestCells.lean; its two conditions on public
    data from `k5CondAt_at_head`);
  the cells read off the messages are the matrices read off the data (`raw_is_data` over
    `addrTie_front_fs`, Johnson/Desc/K5/Honest/Law/KvOfCells.lean, AddrTieFs.lean);
  these agree with t on the valid names: THE PREMISE hc;
  an identity at a valid index reads valid names alone (`idnVal_agree`,
    Johnson/Road/Lane5AttValid.lean);
  an integer that is 0 in the base field is 0 in the challenge field: one characteristic.

Main names:
  `idn12_of_ints`: general: from the two families at integer cells over the base field, to t.
  `idn12_of_asked`: **at the head's letters, from the two items.**

Limits. THE THIRD FAMILY (at3: the denominator is the sum of the row's weights) IS NOT IN THE ITEM
"idn": nothing is said of it here. The head is a hypothesis. hH (the input's cells hold an index),
hc (the tie of t to the witness's data) and the two items are premises: none is shown here. That a
state of an honest run is reached, bears no mark and meets the promise is not shown here. At the
function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.AddrTieFs
import Johnson.Desc.First.Att.Door.Law.K5RestIdn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt Sent sigListCalls rawOf CellsAre)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (attMs attMu)
open Inst.Model.AttSeg (Raw Idn idnVal castT)
open OnBytes.Road.L5 (dimOf Zs cellsA)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- **From integer cells to t.** tz: integer cells; j: a valid index. Conditional: hz: the identity
at tz's casts into the base field; ht: tz's casts into the challenge field agree with t on the valid
names. -/
theorem idn12_of_ints {D : Inst.Model.AttSeg.Dim} {tz : Raw → ℤ} {t : Raw → Cb.Gl.E} {j : Idn}
    (hj : j.Valid D) (hz : idnVal D (castT tz : Raw → Cb.Gl.F) j = 0)
    (ht : ∀ q : Raw, q.Valid D → (castT tz : Raw → Cb.Gl.E) q = t q) : idnVal D t j = 0 := by
  rw [← OnBytes.Road.L5.V.idnVal_agree (D := D) ht hj, Inst.Model.AttSeg.idn_cast]
  rw [Inst.Model.AttSeg.idn_cast] at hz
  exact (CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).2
    ((CharP.intCast_eq_zero_iff Cb.Gl.F Cb.Gl.p _).1 hz)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE FAMILIES at1 AND at2 AT t, FROM THE TWO ASKED ITEMS.** c: the constant that the honest
side's decoder returns; w: the witness; t: any function of the cells' names. Conditional: as
`addrTie_front_fs`; hH: c holds an index; hI, hS: the items "idn" and "small" of the segment, at the
filling with that decoder; hc: THE TIE: the matrices read off the witness's data agree with t on the
valid names. -/
theorem idn12_of_asked {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {pt : K9.Part} (hpt : K9.segAt? s = some pt) (c : P5J.CellsM OnBytes.Flat.numsFull)
    (carryX : ℕ → ProofFile.InstPub × TS → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Prop)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hH : ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds c i) {a₁ a₂ : ProofFile.InstPub × TS}
    {y₁ y₂ : Strs}
    (hI : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr (2 * g + 1)
      .idn a₁ y₁ w)
    (hS : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr (2 * g + 1)
      .small a₂ y₂ w)
    {t : Raw → Cb.Gl.E}
    (hc : ∀ q : Raw, q.Valid (dimOf a.S) →
      OnBytes.Road.Rows.cellsK a.S
        (matsOfData a.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt
            (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w))) q = t q) :
    (∀ k b g' n, (Idn.at1 k b g' n).Valid (dimOf a.S) →
        idnVal (dimOf a.S) t (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Idn.at2 b g' n).Valid (dimOf a.S) → idnVal (dimOf a.S) t (.at2 b g' n) = 0 := by
  obtain ⟨i, hi⟩ := hH
  have hbase : h.𝔇.H.base (2 * g + 1) w :=
    ((constrIs_any _ mgBase _ _ _ _ _).1 hS).1 rfl
  have hbody := ((constrIs_any _ mgBase _ _ _ _ _).1 hI).2 c i rfl hi
  unfold bodyAll at hbody
  rw [if_neg (notHead_any (scope_all h).1 g), if_neg (by omega),
    show (2 * g + 1) / 2 = g by omega, shapeA_at ea] at hbody
  have C := k5CondAt_at_head h hL
  have hZ : CellsAre x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
      (msgsOf h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁) h.𝔇.arr w)
      (zofAll h g w) := cells_all h C.head.pads hg ea hx (C.each g hg a x₁ ea hx).cells w hbase
  have ht : ∀ q : Raw, q.Valid (dimOf a.S) →
      (castT (cellsA a.S (zofAll h g w)) : Raw → Cb.Gl.E) q = t q := by
    intro q hq
    rw [← hc q hq, ← raw_is_data x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w
      (addrTie_front_fs h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon hpt w []
        (fun f hf => absurd hf (List.not_mem_nil))) q]
    exact (congrFun hZ q).symm
  exact ⟨fun k b g' n hv => idn12_of_ints hv (hbody.1 k b g' n hv) ht,
    fun b g' n hv => idn12_of_ints hv (hbody.2 b g' n hv) ht⟩

end

end H2K5.Honest

#print axioms H2K5.Honest.idn12_of_ints
#print axioms H2K5.Honest.idn12_of_asked
