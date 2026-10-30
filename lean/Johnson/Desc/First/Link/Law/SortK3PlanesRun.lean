-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3PlanesRun.lean (kind K9): WHAT IS LEFT OF A LINK's LAW: THE FIELD
  k3 (RunOk) OF `LookRest` AT THE ENTRIES "planes" (the 12 attention links and the
  head's) AND "join" (the 12 attention links), AT THE LINK's LAW's CLOSED LETTERS: φ := phiAll u
  psiAll · Fu := FullAt nU · the bare promise fun q => ‹the sort's named Ok› q ∧ Kx q. Theorems:
  joins. It pays no law of its own.

  `k3_planes_of`: the tie (at_planes_is: what the link states under "planes"
    is the lookup's own run at the calling kind's readers r) ·
    planes_plainOk_ofQ (the caller's clause from the three sentences read · filled · pinned) · the
    batching's runOk_of_plain. General in Ok, r and the two families off q.
  `k3pl_att` · `k3jn_att` · `k3pl_head`: **RunOk of the run at (1, "planes") | (2, "join") | (2,
    "planes"), at plainTm (plVals hdCalls lmC jC bv pv) · pickLen hdCalls lmC jC 3 | plainTm (jnVals
    hdCalls lmC jC kv) · pickLen hdCalls lmC jC 1**, with bv | pv | kv := the choice (bvAtt
    · pvAtt · kvAtt · bvHead · pvHead) of Johnson/P1K9R/CallerAtLetters.lean. read | filled: that
    file's (attBits · attPin · attKeys · headBits · headPin); pinned: PlanesPinned.lean.
  `readersAt_head`: the lot's readers at the head's link.
PREMISES OF THE SCOPE, IN THE BINDERS' OWN TEXTS: hS : VerifierAndGoals.InScope Pf = true · hR :
  VerifierAndGoals.readFiles Pf = .ok pp₀ · O : IM.Open … (k3jn_att takes O alone of these three) · hL :
  c.links[‹the link's number›]? = some L · at attention: h4 : Bs.G₀.W.p4 = true · ha : Bs.G₀.W.A[g]?
  = some a · k3pl_att: hm : 2 * g + 1 < 25 · k3jn_att: hg : g < Bs.G₀.W.NGr. PREMISES ON Kx: hK (it
  gives kxAll lmC jC lmD jD) · hP (it gives PlanesAttOk | PlanesHeadOk: OkPlanes.lean). ON THE PLAN:
  hlm: the place's number lm at that link is lmC (closed; "planes" alone: the run bears the place's
  own lm) · at the head: hH | hi (the link is the head's; the reads' array's number).
Limits. Implications. NO MEMBER: that any link states these runs, or that a state goes on from any
  q, is not shown. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.PlanesPinned
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Desc.First.Link.Law.SortK3Join
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.First.Batch.Law.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K3 (seatCalls)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (RunOk plainTm Pub9 Fx9 O9 Bound runOk_of_plain part_of_more)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin (At FullAt Q OkAtt OkHead PlanesAttOk PlanesHeadOk
  pinned_bits_att pinned_pin_att pinned_keys_att pinned_bits_head pinned_pin_head)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open H2K5.Door (readersAt_att)

theorem readersAt_head {X : Verify.Public} {i iU3 : ℕ} (hH : Desc.K3.isHead X i = true)
    (hi : X.H.tl.ix.U.getD 2 none = some iU3) :
    K3Lot.readersAt X i = some (callerReaders (planesAt iU3)) := by
  unfold K3Lot.readersAt
  simp only [hH, if_true, hi, Option.map_some]

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
include hS hR O

/-- **k3 at "planes"**, from the three sentences on the calling kind's two families. -/
theorem k3_planes_of {m : ℕ} (hm : m < 25) {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
    {r : Desc.K3.Readers S} (hr : K3Lot.readersAt Bs.G₀.W m = some r) (u : HTailF2)
    (Ok : Q BetaAll → Prop) (nU : Array ℕ) {lmC jC lmD jD : ℕ}
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (hlm : ∀ p, Desc.First.Look.placeAt Bs.G₀.W m false = some p → p.lm = lmC)
    {bQ : ℕ × ℕ → Q BetaAll → Aff} {pQ : ℕ → Q BetaAll → Aff}
    (HB : CallerFormsQ (phiAll u psiAll) Ok (FullAt nU)
      (fun (i : ℕ × ℕ) e => bitOf r e i.1 i.2) bQ entUnit)
    (HP : CallerFormsQ (phiAll u psiAll) Ok (FullAt nU) (fun (col : ℕ) e => pinOf r e col) pQ
      entUnit)
    (run : ℕ → S → Except String (List ProofFile.Cl × S)) (h : At L (IM.k3Ix m false, "planes") run) :
    RunOk Reading.gl atS (O9 (phiAll u psiAll) Ok (FullAt nU)) (Fx9 (phiAll u psiAll) Ok) run
      (plainTm (plVals hdCalls lmC jC (fun q y k col => refValQ bQ entUnit (k, col) q y)
        (fun q y col => refValQ pQ entUnit col q y))) (pickLen hdCalls lmC jC 3) := by
  obtain ⟨p, hp, rfl⟩ := at_planes_is hS hR O hm hL hr h
  rw [hlm p hp]
  exact runOk_of_plain Reading.gl atS _ _ _ _ _ (part_of_more _)
    (planes_plainOk_ofQ (phiAll u psiAll) Ok (FullAt nU) hdCalls lmC jC (seatCalls K3Lot.ofForm)
      k03_atS2_calls (fits_at false) (phiAll_putFork_all u) (heard_at u false) (k3Ok_at hK false) r
      HB HP)

/-- **k3 AT (1, "planes") AT AN ATTENTION LINK.** -/
theorem k3pl_att (h4 : Bs.G₀.W.p4 = true) {g : ℕ} {a : Attention.Plan}
    (ha : Bs.G₀.W.A[g]? = some a) (hm : 2 * g + 1 < 25) {L : Link S ProofFile.Cl}
    (hL : c.links[2 * g + 1]? = some L) (u tlD : HTailF2) (nU : Array ℕ)
    (Kx : Q BetaAll → Prop) {lmC jC lmD jD : ℕ} (hK : ∀ q, Kx q → kxAll lmC jC lmD jD q)
    (hP : ∀ q, Kx q → PlanesAttOk rdAll (P.parCOf a) nU q)
    (hlm : ∀ p, Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some p → p.lm = lmC) :
    ∀ run, At L (1, "planes") run → RunOk Reading.gl atS
      (O9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf a) nU tlD q ∧ Kx q) (FullAt nU))
      (Fx9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf a) nU tlD q ∧ Kx q)) run
      (plainTm (plVals hdCalls lmC jC (bvAtt a) (pvAtt a))) (pickLen hdCalls lmC jC 3) := by
  intro run h
  have h24 : 2 * g + 1 ≠ 24 := by omega
  exact k3_planes_of hS hR O hm hL (readersAt_att h4 ha) u _ nU (fun q hq => hK q hq.2) hlm
    (attBits u _ (FullAt nU) a (fun q v g' h' hq hv hr => hq.1.k5 v g' h' hv hr)
      (pinned_bits_att u _ nU tlD (fun q hq => hq.1.core) (P.parCOf a) fun q hq => hP q hq.2))
    (attPin u _ (FullAt nU) a (fun q v g' h' hq hv hr => hq.1.k5 v g' h' hv hr)
      (pinned_pin_att u _ nU tlD (fun q hq => hq.1.core) (P.parCOf a) fun q hq => hP q hq.2))
    run (planes_entry_low h24 ▸ h)

/-- **k3 AT (2, "planes") AT THE HEAD's LINK.** -/
theorem k3pl_head {L : Link S ProofFile.Cl} (hL : c.links[24]? = some L) {iU3 : ℕ}
    (hH : Desc.K3.isHead Bs.G₀.W 24 = true) (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3)
    (hs : OnBytes.Model.Head.Shape) (pH : Desc.Kinds.Head.Par) (u tlD : HTailF2) (nU : Array ℕ)
    (Kx : Q BetaAll → Prop) {lmC jC lmD jD : ℕ} (hK : ∀ q, Kx q → kxAll lmC jC lmD jD q)
    (hP : ∀ q, Kx q → PlanesHeadOk iU3 kapAll nU q)
    (hlm : ∀ p, Desc.First.Look.placeAt Bs.G₀.W 24 false = some p → p.lm = lmC) :
    ∀ run, At L (2, "planes") run → RunOk Reading.gl atS
      (O9 (phiAll u psiAll) (fun q => OkHead hs iU3 pH kapAll nU tlD q ∧ Kx q) (FullAt nU))
      (Fx9 (phiAll u psiAll) (fun q => OkHead hs iU3 pH kapAll nU tlD q ∧ Kx q)) run
      (plainTm (plVals hdCalls lmC jC (bvHead iU3) (pvHead iU3))) (pickLen hdCalls lmC jC 3) := by
  intro run h
  exact k3_planes_of hS hR O (by omega) hL (readersAt_head hH hi) u _ nU (fun q hq => hK q hq.2) hlm
    (headBits u _ (FullAt nU) iU3
      (pinned_bits_head u _ nU tlD (fun q hq => hq.1.core) iU3 fun q hq => hP q hq.2))
    (headPin u _ (FullAt nU) iU3
      (pinned_pin_head u _ nU tlD (fun q hq => hq.1.core) iU3 fun q hq => hP q hq.2))
    run (planes_entry_head ▸ h)

end

/-- **k3 AT (2, "join") AT AN ATTENTION LINK.** -/
theorem k3jn_att {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true)
    {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a)
    {L : Link S ProofFile.Cl} (hL : c.links[2 * g + 1]? = some L) (u tlD : HTailF2) (nU : Array ℕ)
    (Kx : Q BetaAll → Prop) {lmC jC lmD jD : ℕ} (hK : ∀ q, Kx q → kxAll lmC jC lmD jD q)
    (hP : ∀ q, Kx q → PlanesAttOk rdAll (P.parCOf a) nU q) :
    ∀ run, At L (2, "join") run → RunOk Reading.gl atS
      (O9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf a) nU tlD q ∧ Kx q) (FullAt nU))
      (Fx9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf a) nU tlD q ∧ Kx q)) run
      (plainTm (jnVals hdCalls lmC jC (kvAtt a))) (pickLen hdCalls lmC jC 1) := by
  intro run h
  rw [Desc.LinkJoin.at_join_is O h4 hg ha hL h]
  exact runOk_of_plain Reading.gl atS _ _ _ _ _ (part_of_more _)
    (join_plainOk_ofQ (phiAll u psiAll) _ (FullAt nU) hdCalls lmC jC (seatCalls K3Lot.ofForm)
      k03_atS2_calls (fits_at false) (phiAll_putFork_all u) (heard_at u false)
      (k3Ok_at (fun q hq => hK q hq.2) false) (P.keysOfO a)
      (attKeys u _ (FullAt nU) a (fun q v g' h' hq hv hr => hq.1.k5 v g' h' hv hr)
        (pinned_keys_att u _ nU tlD (fun q hq => hq.1.core) (P.parCOf a) fun q hq => hP q hq.2)))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.readersAt_head
#print axioms VerifiableInference.OnPublicFiles.k3_planes_of
#print axioms VerifiableInference.OnPublicFiles.k3pl_att
#print axioms VerifiableInference.OnPublicFiles.k3pl_head
#print axioms VerifiableInference.OnPublicFiles.k3jn_att
