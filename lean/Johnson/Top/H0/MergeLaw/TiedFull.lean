-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TiedFull.lean: THE PIECE THAT HOLDS THE MERGE OF THE CLAIMS ON THE COMMITTED
TABLE (kind K11) IS TIED, AT THE COMPOSED MEANING OVER ITS BASE `mgAll D mgBase` AND THE WRITTEN
LIST OF PLACES, IN THE FORM WITH "REACHED": ALL THE TIES LAID IN. Two small lemmas and one theorem:
a joining.

What is said.
  `pubHeld_of_on`: the public tests that the table's condition at 346 holds, where the state bears
    no mark.
  `six_in_keep`: a closed fact on two written lists.
  `merge_tied_full`: `TiedAtR D.N (mgAll D mgBase) linksFull … Rch 346` of the piece with an
    extractor that lays nothing. It is `merge_tiedAtR` (TiesReached.lean) with four of its premises
    PAID: hcb (`merge_hcb_low`, FenceDecodesFit.lean); t2 (`merge_t2_full`, SecondTieFull.lean); t5
    (`t5_cut_low`, RidesJoinLow.lean: its six public tests in front are drawn here from the table's
    condition, by `k11_hIn`, K11PubClosed.lean); hD (`merge_hD_of_hdec`, DecodesAtMerge.lean).


THE PREMISES THAT ARE LEFT, BY SORT. Five facts on the piece. The two members, the numbers, and the
reading of their mask tables (hni, hinM, hinI); hF and low: the fence, in two forms. M: the premises
on the filling (`MergeFill`, TieThreeFour.lean). Closed facts on D's parameters. hFr, hWa, hWb:
facts on a reached state in front, and behind the accepting step. hkeep, hmk, hf, hW: what other
kinds' items ask across the merge's accepting step: eight public tests; what the row's new items
say; `Fwd` at the runs of six names; "worth" at two names.

Limits. Shown at no closed value of D. Rch is a letter. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.TiesReached
import Johnson.Top.H0.MergeLaw.SecondTieFull
import Johnson.Top.H0.MergeLaw.RidesJoinLow
import Johnson.Top.H0.MergeLaw.FenceDecodesFit
import Johnson.Desc.Sound.MgAt.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open OnBytes.Model (WsShape wsLayOf)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Link Claim Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Pub Meaning Numbers start flatPlacesOf
  openSets pubSets pubStep pubRowM sampledIn pubHeld pubOfItems)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeClaim headMergeDecide
  mergeEntries)
open VerifiableInference.Desc.Sound.MgAt (mergeAt behindAt)

variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (D : MgData Xi Pp Tok rows cols nR X)

/-- The public tests that the table's condition at 346 holds, where the state bears no mark. -/
theorem pubHeld_of_on (z : Pp) (a : S × Fr.E.Str)
    (ha : onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a)
    (hm : ¬ a.1.failed ≠ none) :
    pubHeld (mgAll D mgBase)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD [])
      ((pubSets (mgAll D mgBase).more linksFull (flatPlacesOf linksFull true))[346]?.getD [])
      (z, a.1) = true := by
  unfold onQ onAt at ha
  rcases ha.2 with h | ⟨hBk, _⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at hBk
    exact hBk.1.2

/-- Each of the six names of runs that are open across the merge has its public test among the
eight. -/
theorem six_in_keep : ∀ x ∈ sixNames, Pub.formsIn 24 x.1 x.2 ∈ keep24 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **THE PIECE THAT HOLDS THE MERGE IS TIED, AT THE COMPOSED MEANING OVER ITS BASE AND THE WRITTEN
LIST, IN THE FORM WITH Rch: ALL FIVE TIES LAID IN.** -/
theorem merge_tied_full (hl : D.links = linksFull)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit (CellsQ rows cols) Tok MsgT)) (Pm : HeadMergeP)
    (B : Block S Claim) (hS : SeatOf (headClaimMergeKind Pm) B)
    (hqb : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    -- the facts on the piece
    (he : q.ds.map (·.entry) = mergeEntries Pm.lay.lk 1 Pm.work)
    (hkd : ∀ d ∈ q.ds, Fmt.kindOf d.entry.name = some d.kind) (hback : q.back = [])
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    -- the two members, the numbers, the reading of the oracle messages
    (rc : CellsQ rows cols → ℕ → ℕ → GE) (xM xI : Mem) (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ)
    (Wa : S → Prop)
    {s₀ : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s₀ p3 lkW = .ok Pm.lay)
    (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (hni : 0 < ni)
    (hinM : ∀ j, j < Pm.nMsg → InMsg D.cs (xM.1.l.get xM.2).1 (posMask R j).1 (posMask R j).2.1
      (posMask R j).2.2)
    (hinI : ∀ j, j < ni → InMsg D.cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hF : Fenced q.base [xM, xI])
    (M : MergeFill D.cs D.G D.arr (fun z s => D.smp (z, s)) rc (fun z c s => D.decT c (z, s)) 1
      D.d1.lin xM xI (posMask R) posI Pm h hn ni (D.N.group 24) R Wa (idxAt D ni posI xI) D.N
      (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) 346 24)
    -- on D's parameters
    (hlay : D.d1.lay = Pm.lay) (hncl : D.d1.ncl 24 = 1)
    (hns : (D.built[24]?).map (·.ns) = some Pm.nMsg)
    (hB : pendAllB Pm.lay D.d1.lin = true)
    (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S))
    (hlk : D.lk 24 = some l)
    (hst : ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (htr : D.N.treesAt (some behindAt) = D.N.treesAt (some mergeAt))
    (hms : D.N.msgsAt (some behindAt) = D.N.msgsAt (some mergeAt))
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      D.decT c (z, { s with rowsOwed := none, here := .head a' }) = D.decT c (z, s))
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      D.smp (z, { s with rowsOwed := none, here := .head a' }) = D.smp (z, s))
    (low : ∀ x ∈ sampledIn D.N ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[346]?.getD []), x.1 < q.base)
    -- the facts on a reached state in front
    (hFr : ∀ (z : Pp) (a : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront (D.N.group 24) xM R ni a.1)
    (hWa : ∀ (z : Pp) (a : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Wa a.1)
    (hWb : ∀ (z : Pp) (a b : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) → idxAt D ni posI xI b.1)
    -- what other authors' lemmas carry across the merge's accepting step, at a reached state
    (hkeep : ∀ (z : Pp) (a b : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      ∀ p ∈ keep24, (mgAll D mgBase).pub p (z, a.1) = true →
        (mgAll D mgBase).pub p (z, b.1) = true)
    (hmk : ∀ (z : Pp) (b : S × Fr.E.Str),
      ∀ p ∈ (pubRowM (mgAll D mgBase).more linksFull mergeAt).makes,
      p ∉ (pubSets (mgAll D mgBase).more linksFull (flatPlacesOf linksFull true))[346]?.getD [] →
      (mgAll D mgBase).pubP p (z, b.1))
    (hf : ∀ (z : Pp) (a b : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      ∀ x ∈ sixNames, ∀ p ∈ D.runs 24 x.1 x.2, Fwd (D.Rd 24) p.1 p.2 a.1 b.1)
    (hW : ∀ (z : Pp) (a b : S × Fr.E.Str) w,
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      ∀ j ∈ worthAtMerge, meansQ D.N (mgAll D mgBase) (fun s => (z, s)) j b w →
        meansQ D.N (mgAll D mgBase) (fun s => (z, s)) j a w) :
    TiedAtR D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 346
      (q.withMap fun _ _ w => w) := by
  have hcb : ∀ (z : Pp) (a b : S × Fr.E.Str) w, (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      ∀ i ∈ [Item.pinW, .pin 24 0, .pinI],
        meansQ D.N (mgAll D mgBase) (fun s => (z, s)) i b w →
        meansQ D.N (mgAll D mgBase) (fun s => (z, s)) i a w :=
    fun z a b w hy hb => merge_hcb_low D.cs D.G D.arr D.smp D.decT D.ms D.N (mgAll D mgBase) Pm
      q.base q.ds (fun _ _ _ _ _ => by rw [mgAll_pin]) (fun _ _ _ => by rw [mgAll_pinW]) low hsmp
      hdec z a b w hy hb
  have t2 : ∀ (z : Pp) (a b : S × Fr.E.Str),
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR Pm h hn ni b.1 →
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (346 + 1)
        b :=
    fun z a b ha hR hm hy hb _ => merge_t2_full D hl Pm q.base q.ds xM R ni hlay hncl hns hB l name
      r hlk hst hr htr hms hdec hsmp low z a b ha hm (hFr z a ha hR hm) hy hb
      (hkeep z a b ha hR hm hy) (hmk z b)
  have t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i,
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (346 + 1)
        b →
      relQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (346 + 1)
        b w →
      openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true))
        (· ∈ start linksFull) 346 i → ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i →
      meansQ D.N (mgAll D mgBase) (fun s => (z, s)) i a w := by
    intro z a b w i ha hR hm hy hb _ hrel hi hni'
    have hP := pubHeld_of_on D z a ha hm
    unfold pubHeld at hP
    have hall := List.all_eq_true.1 hP
    exact t5_cut_low D mgBase D.N Pm q.base q.ds low hsmp z a b w i hy hb hrel
      (hf z a b ha hR hm hy)
      (fun x hx => hall _ (k11_hIn D mgBase rfl _ (List.mem_append_right _ (six_in_keep x hx))))
      (hW z a b w ha hR hm hy) hi hni'
  have hD : ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      (mgAll D mgBase).decodes (z, a.1) (strsOf Fr a.2) →
      (mgAll D mgBase).decodes (z, b.1) (strsOf Fr b.2) :=
    fun z a b hy hb => merge_hD_of_hdec D mgBase Pm q.base q.ds hdec z a b hy hb
  exact merge_tiedAtR D.cs D.G D.arr (fun z s => D.smp (z, s)) rc (fun z c s => D.decT c (z, s))
    D.d1.lin xM xI (posMask R) posI linksFull (flatPlacesOf linksFull true) 346 24 q Pm B hS hqb D.N
    (mgAll D mgBase) Rch (fun _ _ w => w) (fun _ _ _ => rfl) h hn ni hni hinM hinI hsmp hdec he hkd
    hback herr hF (D.N.group 24) R Wa (idxAt D ni posI xI) M hFr hB hWa hWb hcb t2 t5 hD

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.six_in_keep
#print axioms VerifiableInference.Desc.First.MergeLaw.pubHeld_of_on
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_tied_full
