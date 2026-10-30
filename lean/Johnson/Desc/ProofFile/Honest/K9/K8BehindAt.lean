-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/K8BehindAt.lean: FOR THE ITEM "totalB": `K8Behind` (Honest/K9/TotalFront.lean: what
the smallness test's house owes behind the batching) AT K9's THREE CONSTANTS (Honest/K9/TotalFill.lean), under the
library's head: THE JOINT of that house's `k8Behind_ok` (Honest/K8/RestJoinOk.lean) with our filling. AN IMPLICATION
STILL: SIX PREMISES AT EACH SORT. Statements and proofs: calls alone; no prover is in this file; the thread T and the
border b are letters; no goal is stated.
  `take_lay`, `take_att`, `take_head`   THE SORT's TIES AT THE CONSTANTS (the library's `LayersTake`, `AttTake`,
      `HeadTake`), under premises of `seal_lay`, `seal_att`, `seal_head`, by the same calls of our own sealed
      `LPFK9.layersOwesC_whole`, `attOwesC_g`, `headOwesC_24`. Their witnesses and those of `seal_…` are pinned by the
      same equations: a caller joins them by these
  **`k8Behind_lay`**, **`k8Behind_att`**, **`k8Behind_head`**   from `SegAt l ‹the sort› Lk`, the sort's tie, `K8At`
      at the link, and
      (1) hk3: the ledger's batching element is handed on at the lookups' entries of the order (`ThetaAt` at their
      two, four, three entries): the lookups': their `theta_at_…` end in it by our readers' reading: not called, not
      ridden here
      (2) `FrontAtStandN`: at each stand of the batching, in front: two facts on the structure and the ledger: paid by
      nobody
      (3) `ValuesAtStand`: at each stand, behind: the hard part lies whole in it: paid by nobody
    ⊢ `K8Behind Lk p (phiFill tlD) ‹the sort's Ok› nU T b (k8Share nU)`
OF `k8Behind_ok`'s EIGHT: THREE PASS THROUGH (`K8At` · `FrontAtStandN` · `ValuesAtStand`) · TWO ARE PAID (the field
reads, by unfolding, at `pi8` and u := tlD; "the promise holds the static clauses", Honest/K9/OkCoreAt.lean) · THREE
ARE EXCHANGED: the order's split for `SegAt` (`split_…`) · the powers behind "K8.equations" for the tie
(its `powOn_…`; at attention: paid: nothing stands behind) · `ThetaAt` at the whole order for `SegAt`, the tie and hk3
(its `thetaRun_…`). FOR A CALLER: our `tied_of_seated` and `take_…` have `SegAt l (IM.subAt l) Lk`; the three here
want the sort written out: the caller rewrites by the sort's equation. `K8At`: it is had at each of the 25
links in scope (`k8At_layers`, `k8At_attention`, `k8At_head`, Honest/K8/K8AtLinks.lean): not called here; `k8At_…` ask
cF.links[…]? = some Lk, `take_…` ask h.𝔇.lk … = some L (joined by our sealed `LPFK9.link_of_lk`); `take_lay` has
built.toList[m]?, `k8At_layers` built[2 * g]?: one rewriting. No tie between nU and the numbers pW of `K8At` stands in
the statements, and none is spent.
WHAT IS NOT CLAIMED. Any of the other five at any link or thread; the tie at a link only as `take_…` have it, under
their premises. That a stand is there. No member: the six theorems are called by no line. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.OkCoreAt
import Johnson.Desc.ProofFile.Honest.K8.RestJoinOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt bvHead pvHead)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt thetaRun_layers thetaRun_attention thetaRun_head)
open ProofFile.Honest.K8 (K8At FrontAtStandN ValuesAtStand k8Behind_ok k8Share)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-! ## The sort's ties at the constants -/

/-- At a feed-forward segment. -/
theorem take_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (IM.subAt m) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) (pC pD : First.Look.P) (tlD : HTailF2) :
    ∃ p4 X, LPFK9.k4ParAt Zp Bs.G₀ m = some p4 ∧ Bs.G₀.built.toList[m]? = some X ∧
      LayersTake L tlD psiAll (okFillLay p4 (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (FullAt (ProofFile.k8NU Bs.G₀ X)) p4
        (ProofFile.k8NU Bs.G₀ X) entUnit tmFour
        (t3All pC.lm pC.first 0 pD.first (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0))
        (l3All pC.lm pC.first 0 pD.first) := by
  obtain ⟨p4, X, e1, e2, Wh⟩ := LPFK9.layersOwesC_whole h O m hm hs L p hlk seg drawB kp
  exact ⟨p4, X, e1, e2, take_of_layersOwesC (Wh (kxAll3 pC.lm pC.first 0 pD.first) pC.lm pC.first 0 pD.first
    (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) tlD tlD (fun _ hq => hq.1))⟩

/-- At an attention segment. -/
theorem take_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (pC pD : First.Look.P)
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (tlD : HTailF2) :
    ∃ A X, Bs.G₀.W.A[g]? = some A ∧ Bs.G₀.built[2 * g + 1]? = some X ∧
      AttTake L tlD psiAll (okFillAtt A (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (FullAt (ProofFile.k8NU Bs.G₀ X)) rdAll (P.parCOf A)
        (ProofFile.k8NU Bs.G₀ X) entUnit tmFour (t3All pC.lm pC.first 0 pD.first (bvAtt A) (pvAtt A) (kvAtt A))
        (l3All pC.lm pC.first 0 pD.first) := by
  obtain ⟨A, X, hA, e3, Wh⟩ := LPFK9.attOwesC_g h O hg hs L p hlk seg drawB kp
  exact ⟨A, X, hA, e3, take_of_attOwesC (Wh (kxAtt pC.lm pC.first 0 pD.first (P.parCOf A) (ProofFile.k8NU Bs.G₀ X)) pC.lm
    pC.first 0 pD.first tlD tlD kxAtt_k3 kxAtt_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl))⟩

/-- At the head's segment. -/
theorem take_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (hs : IM.subAt 24 = .head)
    (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (hlk : h.𝔇.lk 24 = some L) (seg : SegAt 24 (IM.subAt 24) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp 24 = some p) (pC pD : First.Look.P) (hC : placeAt (P5J.At.X Zp) 24 false = some pC)
    (tlD : HTailF2) :
    ∃ X, Bs.G₀.built[24]? = some X ∧
      HeadTake L tlD psiAll (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ X) tlD pC pD) (FullAt (ProofFile.k8NU Bs.G₀ X)) Bs.G₀.W.hS
        (Kinds.Head.Law.readsOf Bs.G₀.W) 24 4 (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll (ProofFile.k8NU Bs.G₀ X)
        entUnit tmFour
        (t3All pC.lm pC.first 0 pD.first (bvHead (Kinds.Head.Law.readsOf Bs.G₀.W))
          (pvHead (Kinds.Head.Law.readsOf Bs.G₀.W)) (fun _ _ _ => 0))
        (l3All pC.lm pC.first 0 pD.first) := by
  obtain ⟨X, e3, Wh⟩ := LPFK9.headOwesC_24 h O hs L p hlk seg drawB kp
  exact ⟨X, e3, take_of_headOwesC (Wh
    (kxHead pC.lm pC.first 0 pD.first (Kinds.Head.Law.readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ X)) pC.lm pC.first 0 pD.first
    (fun _ _ _ => 0) tlD tlD kxHead_k3 kxHead_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl))⟩

/-! ## The joint -/

section
variable {V W X' Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X' Pb) (b : ℕ) {Lk : Link S Claim}
  {p : Desc.K9.Where} {nU : Array ℕ} {tlD : HTailF2} {pC pD : First.Look.P} {l : ℕ} {pW : First.K8.ParW}
  {Fu : S → Prop} {ent : Q BetaAll → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q BetaAll → ℕ}

/-- **At a feed-forward segment.** -/
theorem k8Behind_lay {p4 : OnBytes.Desc.First.K4.Par} (seg : SegAt l .layers Lk)
    (A : LayersTake Lk tlD psiAll (okFillLay p4 nU tlD pC pD) Fu p4 nU ent tm4 t3 l3) (hK : K8At Lk .layers pW)
    (hk3 : ThetaAt Lk [(1, "objects"), (6, "objects")])
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillLay p4 nU tlD pC pD) nU T b)
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillLay p4 nU tlD pC pD) nU T b) :
    K8Behind Lk p (phiFill tlD) (okFillLay p4 nU tlD pC pD) nU T b (k8Share nU) :=
  k8Behind_ok (u := tlD) (π := pi8) hK (thetaRun_layers seg A hk3).1 (split_layers seg) (powOn_layers A)
    (fun _ => rfl) (fun q tlb v hq ht hv => static_lay q tlb v hq ht hv) hFront hVals

/-- **At an attention segment.** -/
theorem k8Behind_att {A₀ : Attention.Plan} {rd : Phi BetaAll → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} (seg : SegAt l .attention Lk)
    (A : AttTake Lk tlD psiAll (okFillAtt A₀ nU tlD pC pD) Fu rd c nU ent tm4 t3 l3) (hK : K8At Lk .attention pW)
    (hk3 : ThetaAt Lk [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")])
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillAtt A₀ nU tlD pC pD) nU T b)
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillAtt A₀ nU tlD pC pD) nU T b) :
    K8Behind Lk p (phiFill tlD) (okFillAtt A₀ nU tlD pC pD) nU T b (k8Share nU) :=
  k8Behind_ok (u := tlD) (π := pi8) hK (thetaRun_attention seg A hk3).1 (split_attention seg) (powOn_nil Lk)
    (fun _ => rfl) (fun q tlb v hq ht hv => static_att q tlb v hq ht hv) hFront hVals

/-- **At the head's segment.** -/
theorem k8Behind_head {Wp : Verify.Public} {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p6 : Kinds.Head.Par} {kap : Phi BetaAll → Option Kinds.Head.Law.Seen} (seg : SegAt l .head Lk)
    (A : HeadTake Lk tlD psiAll (okFillHead Wp nU tlD pC pD) Fu hS iU3 l' piece p6 kap nU ent tm4 t3 l3)
    (hK : K8At Lk .head pW) (hk3 : ThetaAt Lk [(2, "objects"), (2, "planes"), (7, "objects")])
    (hFront : FrontAtStandN Lk p (phiFill tlD) (okFillHead Wp nU tlD pC pD) nU T b)
    (hVals : ValuesAtStand Lk p (phiFill tlD) (okFillHead Wp nU tlD pC pD) nU T b) :
    K8Behind Lk p (phiFill tlD) (okFillHead Wp nU tlD pC pD) nU T b (k8Share nU) :=
  k8Behind_ok (u := tlD) (π := pi8) hK (thetaRun_head seg A hk3).1 (split_head seg) (powOn_head A)
    (fun _ => rfl) (fun q tlb v hq ht hv => static_head q tlb v hq ht hv) hFront hVals

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.take_lay
#print axioms ProofFile.Honest.K9.take_att
#print axioms ProofFile.Honest.K9.take_head
#print axioms ProofFile.Honest.K9.k8Behind_lay
#print axioms ProofFile.Honest.K9.k8Behind_att
#print axioms ProofFile.Honest.K9.k8Behind_head
