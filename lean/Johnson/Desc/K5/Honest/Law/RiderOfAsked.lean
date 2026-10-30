-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RiderOfAsked.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the batch of the third family of identities on
an attention segment (at3: the denominator is the sum of the row's weights) AT THE LOOKUP's POINT IS
0 (`Rider`, Johnson/Desc/K5/Honest/Law/Idn.lean), AT ANY FUNCTION t OF THE CELLS' NAMES THAT AGREES
WITH THE WITNESS's DATA ON THE VALID NAMES, FROM AN ITEM THAT THE ROW OF THE SEGMENT's OWN ROUNDS
(kind K5) ASKS IN FRONT: the lookup's worth "rider".

Why. The laws on the values of the kind spend the third family through that batch alone, at that
point alone. The row asks the item in front, and no law spends it.

How. The library has the other direction (`rider_of_denOut`,
Johnson/Desc/First/Att/K05RiderAt.lean); this is its mirror, by the same lemmas. The item says: at
all rounds for which what the verifier has received from the lookup stands, the rider's family is
met at these rounds' key point; the lookup's sharp promise in front hands such rounds
(`door_at_head`); `den_target_out` turns "the family is met" into "the batch is 0" at the cells read
off the witness's messages.
  To t: the batch reads the identities at valid indices alone (`denOut_agree`, by the library's
    `den_out` and `idnVal_agree`).
  To the point z of the open segment's own structure g0: that structure and the lookup's agree in
    the key points zk, and the batch reads its point through the key point of call 2 alone
    (`denOut_same_keys`, by the library's `den_out`).

Main names: `denOut_agree`, `denOut_same_keys`: general. `rider_of_asked`: at the head's letters,
from the sentence. `rider_item_at_head`: from the closed filling's own item.

Limits. The head is a hypothesis. The item, hc (the tie of t to the witness's data) and K3 (the open
segment's structure follows the lookup's rule for its points) are premises: none is shown here. Not
the third family at any index: its batch at one point. That a state of an honest run is reached,
bears no mark and meets the promise is not shown here. At the function `OnBytes.secondHashFunction`, of which
nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.AddrTieFs
import Johnson.Desc.K5.Honest.Law.Idn
import Johnson.Desc.K5.Honest.Law.JoinMeetsAtHead
import Johnson.Desc.First.Att.K05RiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt Sent sigListCalls rawOf attCells attRider
  attFits_of)
open VerifiableInference.Desc.First.Att.P (K3Pts KeyPtsAre)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (attMs attMu K3WorthRider keyPt)
open Inst.Model.AttSeg
open OnBytes.Road.L5 (dimOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door
open Finset

/-- **The batch reads valid names alone.** Conditional: hN: the pieces' numbers fit into call 2; H:
t and t' agree on the valid names. -/
theorem denOut_agree {D : Dim} {C : Calls} (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW)) (z : ℕ → Cb.Gl.E)
    {t t' : Raw → Cb.Gl.E} (H : ∀ q : Raw, q.Valid D → t q = t' q) :
    Cb.Pv.Att.denOut D C z t = Cb.Pv.Att.denOut D C z t' := by
  rw [← Cb.Rider.den_out D C hN z t, ← Cb.Rider.den_out D C hN z t']
  have e : Cb.Pv.Att.denVec D t = Cb.Pv.Att.denVec D t' := by
    funext X
    unfold Cb.Pv.Att.denVec
    split
    · rename_i hb
      exact OnBytes.Road.L5.V.idnVal_agree (D := D) H
        (j := .at3 (X / D.T / D.nG) (X / D.T % D.nG) (X % D.T))
        ⟨hb, Nat.mod_lt _ OnBytes.Road.L5.V.nG_pos,
          Nat.mod_lt _ (by rw [D.T_eq]; exact Nat.two_pow_pos _)⟩
    · rfl
  rw [e]

/-- **The batch reads its point through the key points alone.** Conditional: F: the lookup's public
numbers fit; K, K': both points read as one list of key points. -/
theorem denOut_same_keys {hS : Forest.Shape} {D : Dim} {C : Calls}
    (F : Cb.Rider.AttFits hS D C) {z z' : ℕ → Cb.Gl.E} {zk : Array (Array E)}
    (K : KeyPtsAre Reading.gl C z zk) (K' : KeyPtsAre Reading.gl C z' zk) (t : Raw → Cb.Gl.E) :
    Cb.Pv.Att.denOut D C z t = Cb.Pv.Att.denOut D C z' t := by
  rw [← Cb.Rider.den_out D C F.nb z t, ← Cb.Rider.den_out D C F.nb z' t]
  refine Blocks.ext_congr_point (fun s hs => ?_) _
  have hlt : Cb.Rider.callIx (C.a 2 - D.lW) s < C.a 2 := by
    have h1 := F.lw
    unfold Cb.Rider.callIx
    unfold Dim.lW at h1 hs ⊢
    split <;> omega
  rw [← K.read 2 _ hlt, ← K'.read 2 _ hlt]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE BATCH OF at3 AT THE LOOKUP's POINT IS 0 AT t, FROM THE SENTENCE OF THE ASKED ITEM.** g0:
what the open segment's own field holds of the lookup; z: its point; t: any function of the cells'
names. Conditional: as `addrTie_front_fs`; e; hW: the sentence of worth "rider" at the witness w;
hg0, K3; hc: THE TIE: the matrices read off the witness's data agree with t on the valid names. -/
theorem rider_of_asked {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT)
    (hW : K3WorthRider (K3.seatCalls K3Lot.ofForm).fork (K3.seatCalls K3Lot.ofForm).heard
      (attRider x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad Iop.extNone Unit) x₁.lm x₁.F.next
      (fun _ => ()) (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr) s w)
    {g0 : Forest.Heard} (hg0 : att.g = some g0) {z : ℕ → Cb.Gl.E}
    (K3 : K3Pts a.fs g0.zx g0.zy g0.zk z) {t : Raw → Cb.Gl.E}
    (hc : ∀ q : Raw, q.Valid (dimOf a.S) →
      OnBytes.Road.Rows.cellsK a.S
        (matsOfData a.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt
            (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w))) q = t q) :
    Rider (dimOf a.S) (OnBytes.Road.L5.callsOf a.fs) z t := by
  obtain ⟨h4, _, _⟩ := scope_all h
  have hP := planIs_all h
  obtain ⟨_, hxns, hxl, hfs⟩ := Att.P.place_calls h4 ea hx
  obtain ⟨blk, hat⟩ := seated_all h hg
  obtain ⟨hok, hG⟩ := seatedOk_guard_all h hg hat
  have pOk := planOk_plus (beforeAll Zp g) hat hok ea
  have cOk := claimsOk_plus (beforeAll Zp g) hat hok ea
  have hA : (P5J.At.X Zp).A[x₁.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ea
  have AO := attOK_plus (beforeAll Zp g) h.𝔇.sent h.𝔇.l3.rad hP h4 ea hx hG pOk cOk
  obtain ⟨_, gL, Y, hLf⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    K3Lot.ofForm (fun _ => (none : Option Unit))
  have FA := Att.P.frontAll_of_door hA (ofPlan_all h ea) Y
  obtain ⟨g1, hg1, Sr⟩ := FA.reads att e
  obtain rfl : g1 = g0 := Option.some.inj (hg1.symm.trans hg0)
  obtain ⟨F₀, F', rsK, _, hnx, Lf, e1, e2, _⟩ := hLf
  have hF := attFits_of AO.fits
  have hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf x₁.fs x₁.lm x₁.F.next rsK) := by
    rw [← hnx]
    exact Lf.heardIs
  have hO := hW gL F' e2 e1 rsK hI
  have hd := (Cb.Rider.den_target_out hF.e2 hF.nb
    (fun _ m => attCells x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad m) ()
    (keyPt (Fo.endsOf x₁.fs x₁.lm x₁.F.next rsK))
    (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)).1 hO
  have K3L : K3Pts x₁.fs gL.zx gL.zy gL.zk (keyPt (Fo.endsOf x₁.fs x₁.lm x₁.F.next rsK)) :=
    Att.P.k3pts_of_left Lf AO.four (fun t => by rw [hnx]; rfl)
  rw [Att.P.callsOf_eq] at hF hd
  rw [hfs] at hF hd K3L
  have Kf := (public_at_head h hg ea).keys
  have Kp0 := keyPts_of_keysFit Kf K3
  have KpL : KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf a.fs)
      (keyPt (Fo.endsOf a.fs x₁.lm x₁.F.next rsK)) g1.zk := by
    rw [Sr.zk]
    exact keyPts_of_keysFit Kf K3L
  have hag : ∀ q : Raw, q.Valid (dimOf a.S) →
      attCells x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w) q = t q := by
    intro q hq
    rw [← hc q hq, ← raw_is_data x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w
      (addrTie_front_fs h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon hpt w []
        (fun f hf => absurd hf (List.not_mem_nil))) q]
    rfl
  unfold Rider
  rw [denOut_same_keys hF Kp0 KpL, ← denOut_agree hF.nb _ hag]
  exact hd

/-- **The same from the closed filling's own item.** y₁: the item's strings, which the sentence does
not read. Conditional as `rider_of_asked`. -/
theorem rider_item_at_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {k : ℕ} {π : ProofFile.InstPub} {s : S} {y : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) y)
    {att : AttOwn} (e : s.here = .att att) {pt : K9.Part} (hpt : K9.segAt? s = some pt)
    (y₁ : Strs) (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hW : (mgAtAll h).worth (2 * g + 1) 2 "rider" (π, s) y₁ w)
    {g0 : Forest.Heard} (hg0 : att.g = some g0) {z : ℕ → Cb.Gl.E}
    (K3 : K3Pts a.fs g0.zx g0.zy g0.zk z) {t : Raw → Cb.Gl.E}
    (hc : ∀ q : Raw, q.Valid (dimOf a.S) →
      OnBytes.Road.Rows.cellsK a.S
        (matsOfData a.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt
            (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w))) q = t q) :
    Rider (dimOf a.S) (OnBytes.Road.L5.callsOf a.fs) z t := by
  have Gn := mgGains_all h (scope_all h).1 ea hx
  rw [Gn.rider] at hW
  exact rider_of_asked h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hpt w hW hg0 K3 hc

end

end H2K5.Honest

#print axioms H2K5.Honest.denOut_agree
#print axioms H2K5.Honest.denOut_same_keys
#print axioms H2K5.Honest.rider_of_asked
#print axioms H2K5.Honest.rider_item_at_head
