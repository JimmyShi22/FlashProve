-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/Tied.lean: THE MERGE AT THE TABLE OF JOINTS, AT THE PROOF FILE's DESCRIPTION: ALL STOREYS OF THE ROW K11_sits JOINED IN ONE THEOREM: OVER THE LOT (Johnson/Desc/ProofFile/Lot/K11.lean). JOININGS.
k11_of's term is the lot's blkAt: hence seatOf_blkAt · seatLaws_blkAt (what narrows the lot's block narrows the kind's: one list of rounds, one decision) · k11_tied calls the rule tiedBy_of_seatLaws (Johnson/Desc/Sound/TiedSeat.lean) and OfDesc.pieceAt (Johnson/Desc/Sound/AtDriver.lean) themselves, in the six lines of tied_of_alone (Johnson/P5K3R/SitsAny.lean).
k11_tied · k11_joined · k11_kindTied STAND IN THE FORM WITHOUT «REACHED»: at the composed meaning their ties t2, t3 and t4 cannot be shown from the table's condition alone (the public item hasRow behind the merge, and the two readings of the mask row and of the index masks' ledger, want facts on the states that the verifier reaches). THE FORM THAT COUNTS IS Johnson/K11R/TiedReach.lean. THIS FILE IS KEPT FOR seatOf_blkAt · k11_facts · k11_numbers · k11_places_full, WHICH THAT FILE CALLS.
WHAT IS SAID.
  seatLaws_blkAt    SeatLaws at the kind's headClaimMergeKind (parOf Z G) gives SeatLaws at the lot's own block.
  k11_tied          in scope, at an opening's letters, for three rows of pieces that hold the description's blocks (OfDesc): the piece at number 346 of the first row, with an extractor that lays nothing, is TiedBy at the table's own words, IF SeatLaws holds at headClaimMergeKind (parOf Z G₀).
  k11_facts         THREE OF THE FIVE FACTS ON THAT PIECE, where the rows also tile the first chain (Tiled · rowData) and 346 is not the last number: no round behind · the written rounds have the block's own entries · each has the kind of its name. By fits_piece (Johnson/Road/K4/PieceAtFits.lean) and merge_stretch (Johnson/Top/H0/MergeLaw/PieceFacts.lean).
  k11_numbers       THE NUMBERS: the lot's numbers parOf Z G₀ meet the law's two premises on public numbers. By public_merge (Johnson/Top/H0/MergeLaw/PlanNums.lean).
  k11_joined        ALL STOREYS IN ONE: THE PIECE AT 346 IS TiedBy AT THE TABLE's OWN WORDS. WHAT IS LEFT AS PREMISES: (a) scope · an opening's letters · OfDesc · Tiled · rowData · «346 is not the last number» · (b) TWO FACTS ON THE PIECE: its errors are the cap (herr) · the two members' trees lie in front of it (hF) · (c) h · hn (paid by k11_numbers: the caller opens its «there are» first) · 0 < ni · (d) four on the reading of the oracles (hinM hinI hsmp hdec) · (e) THE FIVE TIES t1 … t5 AND hD AT THE TABLE's LETTERS (t1, and the merge's share of t2: Johnson/Top/H0/MergeLaw/TieOneTwo.lean).
  k11AllB_full · k11_there · k11_places_full     by Lean's kernel (decide +kernel): in the written list of places the kind K11 stands at number 346 alone, and that entry is the merge's address.
  k11_kindTied      THE KIND K11's SHARE OF THE CHAIN OF PROMISES (KindTied … K11, Johnson/Desc/Sound/TiedPlaces.lean), under SeatLaws at the constant.
LIMITS. NOT «K11_sits IS MET»: THE VERSION OF THE FILES BELOW IT OVER WHICH THIS FILE WAS WRITTEN IS NOT THE ONE THAT WAS FROZEN. THE TIES ARE SHOWN AT NO FILLING. «onlineDescription returns in scope» stands behind the opening's letters. The reference shape; secondHashFunction. k11_kindTied is idle where the row of pieces has no entry 346. That the description's own flat list has the written list's places: the driver's law, not called. No soundness. Nothing on hiding.
-/
import Johnson.K11R.Sits
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Top.H0.MergeLaw.TieLaws
import Johnson.Top.H0.MergeLaw.PieceFacts
import Johnson.Top.H0.MergeLaw.PlanNums
import Johnson.Road.K4.PieceAtFits

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
open VerifiableInference.Desc.First (S HeadOwn ModelPart Meaning Numbers start flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide mergeEntries)
open ProofFile (Cl)

/-- What narrows the lot's block narrows the kind's: the two have one list of rounds and one decision. -/
theorem seatOf_blkAt {Z : ProofFile.Pub} {G : ProofFile.Ground} {B' : Block S Cl}
    (h : SeatOf (blkAt Z "H.8.call" G) B') : SeatOf (headClaimMergeKind (parOf Z G)) B' :=
  ⟨⟨h.1.1, h.1.2⟩, h.2⟩

/-- **What the merge's authors owe, at the lot's own block**: from the same at the kind's. -/
theorem seatLaws_blkAt {Pp W : Type} {C : CK} {Fr : Frame} {links : List ModelPart} {ps : List Place}
    {k : ℕ} {q : Piece C Fr (Pp × S) Cl W} {N : Numbers} {Mg : Meaning Pp W} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (H : SeatLaws links ps k q N Mg (headClaimMergeKind (parOf Z G))) :
    SeatLaws links ps k q N Mg (blkAt Z "H.8.call" G) :=
  ⟨fun B' h => H.1 B' (seatOf_blkAt h), fun B' h => H.2.1 B' (seatOf_blkAt h),
    fun B' h => H.2.2.1 B' (seatOf_blkAt h), fun B' h => H.2.2.2 B' (seatOf_blkAt h)⟩

/-- **THE MERGE's PIECE IS TIED AT THE TABLE, where its authors' four hold at the kind's block**: at
the letters that the walk through the maker hands out, in scope, for three rows of pieces that hold
the description's blocks: the piece at number 346 of the first row. -/
theorem k11_tied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[346]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (H : SeatLaws links ps 346 q N Mg (headClaimMergeKind (parOf Z Bs.G₀))) :
    TiedBy N Mg links ps (fun a => a) 346 (q.withMap E) (onQ N Mg links ps (fun a => a) 346)
      (onQ N Mg links ps (fun a => a) (346 + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps 346))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps 346)) := by
  obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  exact tiedBy_of_seatLaws links ps 346 (blkAt Z "H.8.call" Bs.G₀) b q
    ⟨IM.alone_underR hla, fun s rs gs t hy => ((IM.yes_alone hla (by decide) s t rs gs).1 hy).2.1⟩
    (OfDesc.pieceAt hT hq h3) N Mg E hE (seatLaws_blkAt H)

/-- **THREE OF THE FIVE FACTS ON THE MERGE's PIECE**, at any three rows of pieces that hold the
description's blocks and tile its first chain: no round behind; the written rounds have the block's
own entries; each has the kind of its name. By fits_piece and merge_stretch. -/
theorem k11_facts {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type} (file : String)
    (hD : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).data file = .ok D)
    (T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W)
    (hT : OfDesc _ T) (ht : Tiled T.p₁ T.l₁) (hd : rowData T.p₁ T.l₁ = D.ds₁)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[346]? = some q) (hlen : 346 + 1 < c.blocksInOrder.length) :
    q.back = [] ∧
      q.ds.map (·.entry) = mergeEntries (parOf Z Bs.G₀).lay.lk 1 (parOf Z Bs.G₀).work ∧
      ∀ d ∈ q.ds, Fmt.kindOf d.entry.name = some d.kind := by
  obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  obtain ⟨_, hb, hl, hA⟩ := OnBytes.Road.K4.fits_piece _ file D hD T hT ht hd hq h3 hlen
  exact ⟨hb, merge_stretch (parOf Z Bs.G₀) b
    ((IM.alone_rounds hla).trans (blkAt_fields Z Bs.G₀).2.1) q.ds hl hA⟩

/-- **THE NUMBERS**: at an opening's letters the lot's numbers meet the two premises of the merge's
law on public numbers: the layout is a return of the planner's wsLayOf; 2 lk + 3 ≤ nMsg. -/
theorem k11_numbers {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open OnBytes.secondHashFunction pol lay KL F Z Bs base c A B) :
    (∃ s p3 lkW, OnBytes.Model.wsLayOf s p3 lkW = .ok (parOf Z Bs.G₀).lay) ∧
      2 * (parOf Z Bs.G₀).lay.lk + 3 ≤ (parOf Z Bs.G₀).nMsg :=
  public_merge O.public

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **ALL STOREYS IN ONE**: in scope, at an opening's letters, for three rows of pieces that hold the
description's blocks and tile its first chain: THE PIECE AT NUMBER 346 IS TIED AT THE TABLE's OWN
WORDS: under: the cap and the fence at that piece; four premises on the reading of the oracles; the
five ties and "decodes rides" at the table's letters. Pm: the lot's numbers. -/
theorem k11_joined {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
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
    (links : List ModelPart) (ps : List Place) (Nn : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w)
    (Pm : HeadMergeP) (hPm : Pm = parOf Z Bs.G₀)
    {s₀ : OnBytes.Model.WsShape} {p3 : Bool} {lkW : ℕ}
    (h : OnBytes.Model.wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (hni : 0 < ni)
    -- on the reading of the oracles
    (hinM : ∀ j, j < Pm.nMsg → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    -- the two facts on the piece that are left
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds)) (hF : Fenced q.base [xM, xI])
    -- four ties between the merge's own words and the table's; the fifth, what rides, beneath
    (t1 : ∀ (z : ProofFile.InstPub) (a : S × (frameAt D all D.key₁ T.ft₁).E.Str), onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      ¬ a.1.failed ≠ none →
      frontR Pm a.1 = true)
    (t2 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str), onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      BehindR Pm h hn ni b.1 → onQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b)
    (t3 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      BehindR Pm h hn ni b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps 346) b w →
      RelBehindR cs G arr smp rc decT claims lin xM xI posM posI Pm h hn ni b w)
    (t4 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      BehindR Pm h hn ni b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps 346) b w →
      RelFrontR cs G arr smp rc decT xM xI posM Pm h hn ni a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps 346) a w)
    -- what rides
    (t5 : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (346 + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) 346 i → ¬ insQ links ps 346 i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    -- "decodes" rides past the merge's yes
    (hD : ∀ (z : ProofFile.InstPub) (a b : S × (frameAt D all D.key₁ T.ft₁).E.Str), (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf (frameAt D all D.key₁ T.ft₁) a.2) →
      Mg.decodes (z, b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2)) :
    TiedBy Nn Mg links ps (fun a => a) 346 (q.withMap E) (onQ Nn Mg links ps (fun a => a) 346)
      (onQ Nn Mg links ps (fun a => a) (346 + 1))
      (relAt (meansQ Nn Mg fun a => a) (insQ links ps 346))
      (relAt (meansQ Nn Mg fun a => a) (outsQ links ps 346)) := by
  subst hPm
  obtain ⟨hb, he, hkd⟩ := k11_facts hS hR O file hData T hT ht hd hq hlen
  exact k11_tied hS hR O hT hq links ps Nn Mg E hE
    (merge_seatLawsR cs G arr smp rc decT claims lin xM xI posM posI links ps 346 q Nn Mg _ h hn ni
      hni hinM hinI hsmp hdec he hkd hb herr hF t1 t2 t3 t4 t5 hD)

end

/-- The test over a list of places: every entry of the kind K11 stands at number 346 and is the
merge's address. -/
def k11AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K11 || (i == 346 && decide (a = IM.k11Place))
    | none => true

set_option maxRecDepth 1000000 in
theorem k11AllB_full : k11AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- The merge's address does stand there. -/
theorem k11_there : (flatPlacesOf linksFull true)[346]? = some IM.k11Place := by decide +kernel

/-- **Where the kind stands in the full list of places**: at number 346 alone. -/
theorem k11_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K11) : i = 346 ∧ a = IM.k11Place := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k11AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [hk] at h1
    exact absurd h1 (by decide)
  · obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h1
    exact ⟨by simpa using h5, of_decide_eq_true h6⟩

/-- **THE KIND K11's SHARE OF THE CHAIN OF PROMISES, at the proof file's written description.** -/
theorem k11_kindTied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E 346 a b w = w)
    (H : ∀ q, (T.p₁ :: T.l₁)[346]? = some q →
      SeatLaws linksFull (flatPlacesOf linksFull true) 346 q N Mg
        (headClaimMergeKind (parOf Z Bs.G₀))) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K11 := by
  intro i q a hq ha hk
  obtain ⟨rfl, -⟩ := k11_places_full i a ha hk
  exact (k11_tied hS hR O hT hq linksFull _ N Mg (E _) hE (H q hq)).tiedAt

end K11

#print axioms K11.k11AllB_full
#print axioms K11.k11_places_full
#print axioms K11.k11_kindTied
#print axioms K11.seatLaws_blkAt
#print axioms K11.k11_facts
#print axioms K11.k11_numbers
#print axioms K11.k11_joined
#print axioms K11.k11_tied
