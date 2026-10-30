-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/AddrTieFs.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the library's tie of the two readings of the witness
by address (`AddrTie`, Johnson/Desc/First/Att/K05AddrTieOf.lean) at one reached state that meets the
promise in front of the block of an attention segment's own rounds (kind K5), AT ANY LIST OF FORMS
fs WHOSE SLOTS LIE BELOW THE PLAN's NUMBER OF SLOTS. Two theorems: `addrTie_head_fs`, and
`addrTie_front_fs`: the same without the premise "an attention segment is open there".

Why. `addrTie_head` (Johnson/Desc/K5/Honest/Law/KvOfCells.lean) has it at fs := []: there the tie's
clause on the mask row speaks of no slot. Whoever ties the mask row's entries wants it at forms that
name slots.

How. It is that theorem's proof with fs in the place of [] at one call, the library's `addrTie_at`
(Johnson/Desc/First/Att/K05AddrTieAt.lean). NOTHING MORE IS ASKED OF THE HEAD: the public tests at
the door cover the mask row's message already: the list of read messages `readMsgs`
(Johnson/Desc/First/Att/K05ReadMsgs.lean) ends with it, and `hcov_of`, `hcovM_of` there are general
in fs; "the member sits in the list" is had at every member; the test on the mask row's length
(`masksUpTo`) says yes up to the plan's number of slots (the second clause of `TiePub`).

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise is not shown here. The tie is between two readings of ONE witness w: it says nothing on
what w holds. At the function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's
full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KvOfCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt Sent sigListCalls)
open VerifiableInference.Desc.First.Att.P (AddrTie K5Place)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (attMs)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The library's tie of the two readings by address, at the head's letters, at a list of forms
fs.** pt: the open segment's part at the state. Conditional as `addrTie_head`; hslots: every slot
that a form of fs names lies below the plan's number of slots. -/
theorem addrTie_head_fs {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT) (fs : List Aff)
    (hslots : ∀ f ∈ fs, ∀ z ∈ f.slots.toList, z.1 < a.ns) :
    AddrTie x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad ((s.link?.map (·.arrayOf)).getD #[])
      (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)
      (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) fs := by
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
    h.𝔇.ms w fs a.ns _ _ p1 p2 (Att.P.kept_born h.𝔇.sent x₁.link) p4
    (fun j _ => memAt_field C.head.oneShape _ _ Tc.tests.someMem j) TF.hB1
    (Att.P.hcov_of h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl (seatAll h x₁) fs)
    (Att.P.hcovM_of h.𝔇.sent h.𝔇.l3.rad x₁ a.seam.tl) TF.hB2 TF.hB3 TF.hlink TF.hshape TF.hlay
    TF.harr TF.hok TF.hpt TF.hL hslots
  obtain ⟨e1, _, _⟩ := Att.P.seg_parts TF.hpt TF.hL
  rw [TF.hL]
  show AddrTie x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad Lc.arrayOf _ _ fs
  rw [e1] at A
  unfold ownAt at A
  have eo : h.𝔇.pubD.N.sent x₁.link 0 = h.𝔇.pubD.N.sent (2 * g + 1) 0 := by rw [hxl]
  rw [eo] at A
  exact A

/-- **The same with no premise "an attention segment is open"**: the promise in front of the block
says so itself (the library's `k5_here`). Conditional as `addrTie_head_fs`, its premise e aside. -/
theorem addrTie_front_fs {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT) (fs : List Aff)
    (hslots : ∀ f ∈ fs, ∀ z ∈ f.slots.toList, z.1 < a.ns) :
    AddrTie x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad ((s.link?.map (·.arrayOf)).getD #[])
      (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)
      (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) fs := by
  have Ix : K5Place P5J.At.links (2 * g + 1) ⟨1, some (2 * g + 1), 3, .K5⟩
      ⟨1, some (2 * g + 1), 4, .K1⟩ := ⟨rfl, rfl, sub_full hg, rfl, rfl⟩
  obtain ⟨att, e⟩ := k5_here Ix (Att.P.onAt_shape hon hu)
  exact addrTie_head_fs h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hpt w fs hslots

end

end H2K5.Honest

#print axioms H2K5.Honest.addrTie_head_fs
#print axioms H2K5.Honest.addrTie_front_fs
