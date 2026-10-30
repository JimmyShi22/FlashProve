-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/LawAtThree.lean: THE LAW OF THE KIND K11 (the merge of the claims on the committed table)
ENDS IN THE NAME IN WHICH THE COUNTED LAWS END: `KindTiedR` (Johnson/Desc/Sound/TiedR.lean), at the
composed meaning over its base `mgAll Dm mgBase`, the written list of places, the table's own
extractor, and the first row of the three rows of pieces with the cap (`threeCap`,
Johnson/Goal/Skeleton/TheThree.lean). Small lemmas and one theorem: a joining.

What is said.
  `FD Z A B c`: the IOP as written in Lean, at an opening's letters.
  `lays346`, `extQAt_346`: the table's own extractor lays nothing at the merge's row (by the kernel,
    and `extQ_id`, Johnson/Desc/Sound/BordersFill.lean). Another file has the like, general in the
    place (`extQAt_id_at`, ExtQAtId.lean): where both load, this one gives way.
  `flat_len`: in scope the first chain has 358 sub-protocols.
  `k11_law_atThree`: in scope, at an opening's letters, where the data are the description's and its
    test on the plan accepts: `KindTiedR Dm.N (mgAll Dm mgBase) linksFull … Rch (the extractor) (the
    first row) K11`, FROM ONE PREMISE H: the piece at 346 is tied (`TiedAtR`), GIVEN FIVE FACTS ON
    IT, which are paid here: its errors are the cap (`cutRow_err`, Johnson/Road/K4/PieceAtCut.lean);
    no round behind; the written rounds have the merge's own entries; each has the kind of its name
    (`k11_facts`, Tied.lean, over `threeCap_ofDesc`, `threeCap_fits`); it holds a sub-protocol
    that narrows the merge's, whose accepting step bears no mark.

Limits. H is `merge_tiedAtR`'s end (Johnson/Top/H0/MergeLaw/TiesReached.lean): its other premises
are not laid in here. Rch, Dm and the rows' extractors are letters. Nothing on soundness.

-/
import Johnson.K11R.TiedReach
import Johnson.IMR.PlacesScope
import Johnson.Goal.Skeleton.TheThree
import Johnson.Road.K4.PieceAtCut
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Wit Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Meaning Numbers start flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide mergeEntries)
open ProofFile (Cl)

/-- The IOP as written in Lean, at an opening's letters. -/
abbrev FD (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

theorem lays346 : (VerifiableInference.Desc.First.rowOf linksFull IM.k11Place).lays = false := by
  decide +kernel

section
variable (cs : OnBytes.Codes) {A' Xi Pp Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
  (tokOf : Pp × S → Tok)

/-- **The table's own extractor lays nothing at the merge's row.** -/
theorem extQAt_346 (N : Numbers) (get : A' → Pp × S) (a b : A' × Fr.E.Str)
    (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get 346 a b w =
      w := by
  unfold extQAt
  rw [k11_there]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ lays346 _ _ _ w
end

/-- In scope the first chain has 358 sub-protocols. -/
theorem flat_len {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.blocksInOrder.length = 358 := by
  rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]

/-- **THE LAW OF THE KIND K11, AT THE THREE ROWS OF PIECES WITH THE CAP, AT THE COMPOSED MEANING
OVER ITS BASE, WITH THE TABLE's OWN EXTRACTOR**: every piece at a place of the kind is tied, in the
form with Rch. PAID HERE, beside what `k11_tiedR` pays: that the pieces hold the sub-protocols and
tile the first chain; the cap; "346 is not the last number"; that the extractor lays nothing at 346.
-/
theorem k11_law_atThree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {D : WholeD} {file : String} (hD : (FD Z A B c).data file = .ok D)
    (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl} {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl} {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl} {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    {Xi Tok : Type} {rows cols nR : ℕ} {X₉ : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X₉)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((FD Z A B c).XiPub × (FD Z A B c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((FD Z A B c).XiPub × (FD Z A B c).S₁) × (FD Z A B c).S₂) ×
        (frameAt D (allOf D) D.key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((FD Z A B c).XiPub × (FD Z A B c).S₁ × (FD Z A B c).S₂) × (FD Z A B c).S₃) ×
        (frameAt D (allOf D) D.key₃ (FD Z A B c).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (dW wEnd : Wit (CellsQ rows cols) Tok MsgT) (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (H : ∀ q : Piece (ckP .two) (frameAt D (allOf D) D.key₁ 0) (ProofFile.InstPub × S) Cl
        (Wit (CellsQ rows cols) Tok MsgT),
      ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[346]? = some q →
      q.err = Err.cap 128 (uLT (ckP .two) q.ds) → q.back = [] →
      q.ds.map (·.entry) = mergeEntries (parOf Z Bs.G₀).lay.lk 1 (parOf Z Bs.G₀).work →
      (∀ d ∈ q.ds, Fmt.kindOf d.entry.name = some d.kind) →
      (∃ b : Block S Cl, SeatOf (headClaimMergeKind (parOf Z Bs.G₀)) b ∧
        q.b = (below b).lift Prod.snd fun t s => (t.1, s)) →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 346
        (q.withMap fun _ _ w => w)) :
    KindTiedR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) Rch
      (fun i => (extQAt Dm.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull
        (flatPlacesOf linksFull true) (fun a => a) i))
      ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁) KindName.K11 := by
  have hT := threeCap_ofDesc e₁ e₂ e₃ dW wEnd hD hp q₁ q₂ q₃
  have hFit := threeCap_fits e₁ e₂ e₃ dW wEnd hD hp q₁ q₂ q₃
  refine k11_kindTiedR Dm.N (mgAll Dm mgBase) Rch _ _ fun q hq => ?_
  have hE : (extQAt Dm.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull
      (flatPlacesOf linksFull true) (fun a => a) 346 :
      (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ 0).E.Str → _ → _ → _) = fun _ _ w => w := by
    funext a b w
    exact extQAt_346 Dm.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N (fun a => a) a b w
  rw [hE]
  have hlen : 346 + 1 < c.blocksInOrder.length := by rw [flat_len hS hR O]; decide
  obtain ⟨hb, he, hkd⟩ := k11_facts hS hR O file hD _ hT hFit.tiled₁ hFit.data₁ hq hlen
  obtain ⟨Lk, b, f1, f2, hla, _⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat f1 f2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  exact H q hq
    (OnBytes.Road.K4.cutRow_err (restCap e₁) (fun _ _ => rfl) [sealRound] (l₁.map held) (held b₁) 0
      0 D.ds₁ q (List.mem_of_getElem? hq))
    hb he hkd
    ⟨b, seatOf_blkAt ⟨IM.alone_underR hla,
      fun s rs gs t hy => ((IM.yes_alone hla (by decide) s t rs gs).1 hy).2.1⟩,
      OfDesc.pieceAt hT hq h3⟩

end K11

#print axioms K11.flat_len
#print axioms K11.k11_law_atThree
#print axioms K11.lays346
#print axioms K11.extQAt_346
