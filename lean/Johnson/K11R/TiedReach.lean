-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/TiedReach.lean: the piece at number 346 of the IOP as written in Lean, which holds the
merge of the claims on the committed table, is tied to the table of joints, in the form in which
each tie has beside the table's condition a condition Rch that every accepting step hands on. Two
theorems with their proofs.

What is said.
  `k11_tiedR`: in scope, at an opening's letters, for three rows of pieces that hold the
    sub-protocols and tile the first chain: `TiedAtR … Rch 346 (q.withMap E)`. It is `merge_tiedAtR`
    (Johnson/Top/H0/MergeLaw/TiesReached.lean) with five of its premises PAID: what the piece holds
    (a sub-protocol that narrows the merge's, whose accepting step bears no mark: by `IM.k11_of`,
    `OfDesc.pieceAt`, `seatOf_blkAt`) and three facts on the piece (no round behind; the written
    rounds have the merge's own entries; each has the kind of its name: `k11_facts`, K11/Tied.lean).
  `k11_kindTiedR`: the kind stands at number 346 of the written list of places alone
    (`k11_places_full`, by the kernel): so the piece there tied is the whole kind tied.

Limits. All other premises of `merge_tiedAtR` stand as premises: among them the second tie whole,
what rides, and "decodes rides". Shown at no filling and no Rch. Nothing on soundness.

-/
import Johnson.K11R.Tied
import Johnson.Top.H0.MergeLaw.TiesReached

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

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : ProofFile.InstPub → S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE)
  (decT : ProofFile.InstPub → (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **THE PIECE AT NUMBER 346 OF THE IOP AS WRITTEN IN LEAN IS TIED, IN THE FORM WITH Rch**: in
scope, at an opening's letters, for three rows of pieces that hold its sub-protocols and tile its
first chain. PAID HERE, of `merge_tiedAtR`'s premises: what the piece holds; three of the five facts
on the piece. -/
theorem k11_tiedR {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {D : WholeD} {all : List LeftT} {X₁ X₂ : Type} (file : String)
    (hData : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).data file = .ok D)
    (T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit Cells Tok MsgT))
    (hT : OfDesc _ T) (ht : Tiled T.p₁ T.l₁) (hd : rowData T.p₁ T.l₁ = D.ds₁)
    {q : Piece (ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl (Wit Cells Tok MsgT)}
    (hq : (T.p₁ :: T.l₁)[346]? = some q) (hlen : 346 + 1 < c.blocksInOrder.length)
    (links : List ModelPart) (ps : List Place) (m : ℕ) (Nn : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w)
    (Pm : HeadMergeP) (hPm : Pm = parOf Z Bs.G₀)
    {s₀ : OnBytes.Model.WsShape} {p3 : Bool} {lkW : ℕ}
    (h : OnBytes.Model.wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (hni : 0 < ni)
    (hinM : ∀ j, j < Pm.nMsg → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp z { s with rowsOwed := none, here := .head a' } = smp z s)
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      decT z c { s with rowsOwed := none, here := .head a' } = decT z c s)
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds)) (hF : Fenced q.base [xM, xI])
    (own : List (ℕ × ℕ)) (R : ℕ) (Wa Wb : S → Prop)
    (M : MergeFill cs G arr smp rc decT 1 lin xM xI posM posI Pm h hn ni own R Wa Wb Nn Mg links ps
      346 m)
    (hFr : ∀ (z : ProofFile.InstPub) (a : S × (frameAt D all D.key₁ T.ft₁).E.Str),
      onQ Nn Mg links ps (fun s => (z, s)) 346 a → Rch 346 ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1)
    (hB : pendAllB Pm.lay lin = true)
    (hWa : ∀ (z : ProofFile.InstPub) (a : S × (frameAt D all D.key₁ T.ft₁).E.Str),
      onQ Nn Mg links ps (fun s => (z, s)) 346 a → Rch 346 ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → Wa a.1)
    (hWb : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str),
      onQ Nn Mg links ps (fun s => (z, s)) 346 a → Rch 346 ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) → Wb b.1)
    (hcb : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str) w,
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds),
        b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      ∀ i ∈ [Item.pinW, .pin m 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i b w →
        meansQ Nn Mg (fun s => (z, s)) i a w)
    (t2 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str),
      onQ Nn Mg links ps (fun s => (z, s)) 346 a → Rch 346 ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds),
        b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      BehindR Pm h hn ni b.1 → onQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b)
    (t5 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str) w i,
      onQ Nn Mg links ps (fun s => (z, s)) 346 a → Rch 346 ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds),
        b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) 346 i → ¬ insQ links ps 346 i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    (hD : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str),
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds),
        b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf (frameAt D all D.key₁ T.ft₁) a.2) →
      Mg.decodes (z, b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2)) :
    TiedAtR Nn Mg links ps (fun a => a) Rch 346 (q.withMap E) := by
  subst hPm
  obtain ⟨hb, he, hkd⟩ := k11_facts hS hR O file hData T hT ht hd hq hlen
  obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  exact merge_tiedAtR cs G arr smp rc decT lin xM xI posM posI links ps 346 m q _ b
    (seatOf_blkAt ⟨IM.alone_underR hla,
      fun s rs gs t hy => ((IM.yes_alone hla (by decide) s t rs gs).1 hy).2.1⟩)
    (OfDesc.pieceAt hT hq h3) Nn Mg Rch E hE h hn ni hni hinM hinI hsmp hdec he hkd hb herr hF own R
    Wa Wb M hFr hB hWa hWb hcb t2 t5 hD

end

/-- **THE KIND K11's SHARE OF THE CHAIN OF PROMISES, IN THE FORM WITH Rch**, at the written list of
places: the kind stands at number 346 alone: so whoever shows the piece there tied has shown every
piece of the kind tied. -/
theorem k11_kindTiedR {Pp Cl' W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : ℕ → (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (Pp × S) Cl' W))
    (H : ∀ q, l[346]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 346
        (q.withMap (E 346))) :
    ∀ i q a, l[i]? = some q → (flatPlacesOf linksFull true)[i]? = some a → a.kind = KindName.K11 →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch i
        (q.withMap (E i)) := by
  intro i q a hq ha hk
  obtain ⟨rfl, -⟩ := k11_places_full i a ha hk
  exact H q hq

end K11

#print axioms K11.k11_kindTiedR
#print axioms K11.k11_tiedR
