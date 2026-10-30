-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KvOfCells.lean: CONDITIONAL: the key vectors of which the library's item
on the worth of an attention segment's keys speaks (`K3WorthKeys` at the letters of
Johnson/Desc/First/Att/K05KeysPaid.lean) are the library's key vectors (`keyVec`,
Inst/Model/Att/Trace.lean) of ANY function t of the cells' names that agrees, on the valid names,
with the matrices read off the witness's DATA (`matsOfData`, Johnson/Desc/Sound/DataMats.lean).

Why this file. The item's key vectors are made of the cells unpacked from the witness's MESSAGES
(`rawOf` at `attMu`, Johnson/Desc/First/Look/K3CallerAtt.lean, K3AttGoodIn.lean). A tie of the
honest trace to the witness is typed at the other spelling, the matrices read off the data. The
library has the road between the two spellings:
  `rawOf` at `attMu` is `cellsK` at `matsOfMsg` (Johnson/Desc/First/Att/K05CellsTie.lean), by the
    two texts;
  `matsOfData_eq` (Johnson/Desc/First/Att/K05DataMats.lean): under `AddrTie` the two families of
    matrices are one function;
  `addrTie_at` (Johnson/Desc/First/Att/K05AddrTieAt.lean): `AddrTie` at the witness's messages and
    data, from tests with code on the state and on public data;
  `keyVec_agree` (Johnson/Road/Lane5AttValid.lean): key vectors of functions that agree on the
    valid names are equal, at every index.

Main names:
  `raw_is_msg`: the first step. No premise.
  `raw_is_data`: the cells unpacked from the messages are the matrices read off the data, at every
    name, under `AddrTie`.
  `kv_of_raw`: the item's key vectors are `keyVec` of t, where the unpacked cells agree with t on
    the valid names.
  `addrTie_head`: `AddrTie` under the library's one head on the public input, at one reached state
    that meets the promise in front of the block of the own rounds.
  `kv_of_cells`: **the item's key vectors are `keyVec` of t**, at the head's letters, where the
    matrices read off the data agree with t on the valid names.

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front is not shown here. THE PREMISE hc (the matrices read off the data agree with
t) IS THE TIE OF THE HONEST TRACE TO THE WITNESS: it is shown nowhere outright; `cells_named`
(Johnson/Desc/ProofFile/Honest/K5/Law/Script.lean) hands it from a named tie that is not shown.
At the function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PlanesAtHead
import Johnson.Desc.First.Att.K05KeysPaid
import Johnson.Road.Lane5AttValid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt Sent sigListCalls rawOf attLay JAtt)
open VerifiableInference.Desc.First.Att.P (AddrTie matsOfMsg)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (attMs attMu)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Cells Tok : Type} (x : Look.Place) (Sh : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT)

/-- The cells unpacked from the witness's messages are the matrices read off these messages, by the
library's rule of addresses. No premise. -/
theorem raw_is_msg (q : Inst.Model.AttSeg.Raw) :
    rawOf Sh x.ns tl (attMu x tl D rad seat arr w) q =
      OnBytes.Road.Rows.cellsK Sh (matsOfMsg x tl D rad (attMs x D rad seat arr w)) q := rfl

/-- **The cells unpacked from the messages are the matrices read off the data**, at every name.
Conditional: T: the library's tie of the two readings by address. -/
theorem raw_is_data {arrayOf : Array (ℕ × String)} {Dt : K9L.Bound GQ} {fs : List Aff}
    (T : AddrTie x tl D rad arrayOf (attMs x D rad seat arr w) Dt fs)
    (q : Inst.Model.AttSeg.Raw) :
    rawOf Sh x.ns tl (attMu x tl D rad seat arr w) q =
      OnBytes.Road.Rows.cellsK Sh (matsOfData tl arrayOf Dt) q := by
  rw [← Att.P.matsOfData_eq x tl D rad T]
  rfl

/-- **The item's key vectors are the library's key vectors of t.** μ: the entries; t: any function
of the cells' names. Conditional: H: the cells unpacked from μ agree with t on the valid names. -/
theorem kv_of_raw (μ : JAtt x.ns tl → Cb.Gl.E) {t : Inst.Model.AttSeg.Raw → Cb.Gl.E}
    (H : ∀ q : Inst.Model.AttSeg.Raw, q.Valid (OnBytes.Road.L5.dimOf Sh) →
      rawOf Sh x.ns tl μ q = t q) (c : Fin 4) (X : ℕ) :
    forK Cb.Gl.E (attLay Sh x.fs x.lm x.F.next x.ns tl) () (zext μ) c.val X =
      Inst.Model.AttSeg.keyVec (scl := OnBytes.Road.L5.sclOf Sh) (OnBytes.Road.L5.dimOf Sh)
        (OnBytes.Road.L5.tbOf Sh) t c X := by
  show (attLay Sh x.fs x.lm x.F.next x.ns tl).K () μ c.val X = _
  rw [Look.attLay_K]
  exact OnBytes.Road.L5.V.keyVec_agree (scl := OnBytes.Road.L5.sclOf Sh) H _ c X

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The library's tie of the two readings by address, at the head's letters**, at one reached
state that meets the promise in front of the block of the own rounds. pt: the open segment's part
there. Conditional as `front_at_head`, and on hpt: the state has such a part. -/
theorem addrTie_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT) :
    AddrTie x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad ((s.link?.map (·.arrayOf)).getD #[])
      (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)
      (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) [] := by
  obtain ⟨h4, _, _⟩ := scope_all h
  obtain ⟨_, _, hxl, _⟩ := Att.P.place_calls h4 ea hx
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  obtain ⟨_, gL, Y, _⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option Unit))
  have Fa := Att.P.frontAll_of_door hA (ofPlan_all h ea) Y
  have C := k5CondAt_at_head h hL
  have Tc := C.each g hg a x₁ ea hx
  obtain ⟨p1, p2, p3, p4⟩ := tiePubCells_all h hg ea hx Tc.cells
  obtain ⟨Lc, T⟩ := Fa.facts
  have led : Att.P.seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  obtain ⟨_, hnsF, _⟩ := Fa.ledger att.F led
  have TF := Att.P.tieFacts_here (rad := h.𝔇.l3.rad) (hi := a.ns) (fs := []) p3 p1
    (fun k hk => (Att.P.hcov_of h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl (seatAll h x₁) [] k hk).2) T hpt
    (by rw [Att.P.seg_ledger hpt e]; exact hnsF) (Fa.sec Lc T.hL)
    (fun f hf => absurd hf (List.not_mem_nil))
  have A := Att.P.addrTie_at x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad (ownAt h x₁) h.𝔇.arr (seatAll h x₁)
    h.𝔇.ms w [] a.ns _ _ p1 p2 (Att.P.kept_born h.𝔇.sent x₁.link) p4
    (fun j _ => memAt_field C.head.oneShape _ _ Tc.tests.someMem j) TF.hB1
    (Att.P.hcov_of h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl (seatAll h x₁) [])
    (Att.P.hcovM_of h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl) TF.hB2 TF.hB3 TF.hlink TF.hshape TF.hlay
    TF.harr TF.hok TF.hpt TF.hL (fun f hf => absurd hf (List.not_mem_nil))
  obtain ⟨e1, _, _⟩ := Att.P.seg_parts TF.hpt TF.hL
  rw [TF.hL]
  show AddrTie x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad Lc.arrayOf _ _ []
  rw [e1] at A
  unfold ownAt at A
  have eo : h.𝔇.pubD.N.sent x₁.link 0 = h.𝔇.pubD.N.sent (2 * g + 1) 0 := by rw [hxl]
  rw [eo] at A
  exact A

/-- **The item's key vectors are the library's key vectors of t, at the head's letters.** t: any
function of the cells' names. Conditional: as `addrTie_head`; hc: THE TIE: the matrices read off the
witness's data agree with t on the valid names. -/
theorem kv_of_cells {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT) {t : Inst.Model.AttSeg.Raw → Cb.Gl.E}
    (hc : ∀ q : Inst.Model.AttSeg.Raw, q.Valid (OnBytes.Road.L5.dimOf a.S) →
      OnBytes.Road.Rows.cellsK a.S
        (matsOfData a.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt
            (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w))) q = t q)
    (c : Fin 4) (X : ℕ) :
    forK Cb.Gl.E (attLay a.S x₁.fs x₁.lm x₁.F.next x₁.ns a.seam.tl) ()
        (zext (attMu x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)) c.val X =
      Inst.Model.AttSeg.keyVec (scl := OnBytes.Road.L5.sclOf a.S) (OnBytes.Road.L5.dimOf a.S)
        (OnBytes.Road.L5.tbOf a.S) t c X :=
  kv_of_raw x₁ a.S a.seam.tl _ (fun q hq =>
    (raw_is_data x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w
      (addrTie_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hpt w) q).trans (hc q hq)) c X

end

end H2K5.Honest

#print axioms H2K5.Honest.raw_is_msg
#print axioms H2K5.Honest.raw_is_data
#print axioms H2K5.Honest.kv_of_raw
#print axioms H2K5.Honest.addrTie_head
#print axioms H2K5.Honest.kv_of_cells
