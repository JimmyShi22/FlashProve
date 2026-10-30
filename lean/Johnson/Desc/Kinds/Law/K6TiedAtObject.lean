-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6TiedAtObject.lean (IT ASKS
Seated and the place's number, not Object61): THE SUB-PROTOCOL
AT THE OUTPUT HEAD IN THE CHAIN OF PROMISES, IN THE SECOND FORM (Johnson/Desc/Sound/TiedR.lean:
TiedByR: general in a condition Rch that stands beside the table's promise), AT THE LAW UNDER THE
GUARD ON THE WITNESS (Law/K6CutGuarded.lean), AT THE DRIVER'S OWN SUB-PROTOCOL. A joining, through
k6_tiedBy_of_lawR (Johnson/Desc/Sound/K6TiedR.lean): Seated (Johnson/Desc/Sound/
K6Tied.lean) is a premise; the first tie (k6_t1); the second
(Law/K6SecondKept.lean: k6_t2_kept); the third and the fourth, item by item (Law/K6ItemsCut.lean);
"decodes", "shown", "no collision" ride (Johnson/Desc/Sound/K6AtSig.lean); the fifth tie is a field.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  K6DueAt ... links k Rch bS num q: all that is left beside Seated, the table's tests and the
      six parameters on the oracles: ONE FIELD A PREMISE.
  k6_tied_cut_at_object: TiedByR at sub-protocol number k of the driver's flat places, at segment
      24.
  k6_tied_cut_full: the same at the full chain: links := linksFull, k := 341.

Every letter under "there is": none.
THE FIELDS. planS (the seated value's test on the plan) · plan6 (PlanK6) · fenced, fence, numbers
(on the plan's numbers) · blind · order ("in order" is kept across an accepting step) · pubSays ·
pubBehind, pubSentences (every public test, every public sentence that is open behind holds there:
under Rch) · len, along, cap (the tiling's) · t5 (the fifth tie, in the second form) · items (the
third and the fourth tie's substance).
What it does not say. THAT THE PREMISES CAN BE MET. The chain spends TiedAtR, where the relations
stand under "there are": theorems are not enough: at a decoder that answers nothing Blind and
SigFields hold and every sentence that starts from the promise is free: AN EXAMPLE IS WANTED BESIDE
THEM. Seated is a premise. One list msR for the reader and the table. THE
FULL CHAIN ALONE: 24 is a literal. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6TiedPaid
import Johnson.Desc.Kinds.Law.K6ItemsCut
import Johnson.Desc.Sound.Border62At
import Johnson.Desc.Sound.K6TiedR
import Johnson.Desc.Kinds.Law.K6SecondKept

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning pubFit pubOfItems sampledIn start
  readsOpen)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ relQ insQ outsQ
  extQAt openQ pubQ insL Fenced TiedByR SigFields rowsApart ridersK6 linksFull head_full mark_full
  len_full place342_full reads_full apart_full riders341_full Along RoundIs)
open _root_.Iop (Err)

namespace AtTable

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (c₀ : Fin rows → Fin cols → GE) (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (Fr : Frame) (tokOf : P × S → Tok)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

section
variable (links : List ModelPart) (k : ℕ)

set_option quotPrecheck false in
/-- The driver's list of places. -/
local notation "PS" => First.flatPlacesOf links true

/-- **THE BILL.** -/
structure K6DueAt (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (bS : Block S Claim)
    (num : Fmt.TreeSource → Nat)
    (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)) :
    Prop where
  /-- the seated value's own test on the plan -/
  planS : bS.planOk = true
  /-- the conditions on the public letters of the reading -/
  plan6 : PlanK6 cs arr msR N s seat Wp pl
  /-- the trees of what the head reads were sent in front of the piece -/
  fenced : Fenced q.base (ms0 msR N)
  /-- so were the trees of every pin that is open in front of it -/
  fence : ∀ x ∈ sampledIn N (openQ links PS k), x.1 < q.base
  /-- the plan's numbers: the sub-protocol sends no tree and no message -/
  numbers : N.treesAt PS[k + 1]? = N.treesAt PS[k]? ∧ N.msgsAt PS[k + 1]? = N.msgsAt PS[k]?
  /-- the samples' reader and the decoder do not read where the chain stands -/
  blind : Blind cs smp decT
  /-- three public items give three of the head's tests -/
  pubSays : PubSays Wp Mg 24
  /-- "in order" is kept across an accepting step -/
  order : ∀ a τ b, q.ior.red.out a τ = some b → Mg.inOrder a.1 = true → Mg.inOrder b.1 = true
  /-- every public item that is open behind holds there, as a Bool -/
  pubBehind : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → Rch k a →
    a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1) ++ pubOfItems (openQ links PS (k + 1)), Mg.pub x b.1 = true
  /-- and as a sentence -/
  pubSentences : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → Rch k a →
    a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1), Mg.pubP x b.1
  /-- the piece has as many rounds as its sub-protocol declares -/
  len : q.ds.length + q.back.length = q.b.rounds.length
  /-- and they are the declared ones -/
  along : Along (RoundIs num) q.b.rounds q.ds
  /-- its errors are the cap's -/
  cap : q.err = Err.cap 128 (uLT (_root_.Run.ckP .two) q.ds)
  /-- the fifth tie, in the second form -/
  t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → Rch k a →
    a.1.2.failed = none → q.ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b →
    Sound.relQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b w →
    Sound.openAfter (Sound.insQ links PS) (Sound.outsQ links PS) (· ∈ start links) k i →
    ¬ Sound.insQ links PS k i → Sound.meansQ (Fr := Fr) N Mg (fun a => a) i a w
  /-- the third and the fourth tie, one sentence an item -/
  items : K6ItemsCut cs G arr smp decT msR N s seat Wp pl .two Fr Mg links PS k q Rch

/-- **THE TIE AT THE SEATED PIECE.** hpl hfit hs hp': ON THE TABLE. -/
theorem k6_tied_cut_at_object (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (bef : List (ℕ × ℕ))
    (bS B : Block S Claim)
    (num : Fmt.TreeSource → Nat)
    (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hpl : PS[k]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 })
    (hfit : pubFit Mg.more links PS = true) (hs : links[24]? = some .head)
    (hp' : PS[k + 1]? = some { chain := 1, link := some 24, piece := 5, kind := .K1 })
    (hSig : SigFields cs G arr smp msR decT Mg)
    (D : K6DueAt cs G arr smp decT msR N s seat Wp pl Fr Mg links k Rch bS num q) :
    TiedByR N Mg links PS (fun a => a) Rch k
      (q.withMap (extQAt cs G arr smp msR decT c₀ tokOf N links PS (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => meansCutG cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          InK6)
      (relAt (fun i a w => meansCutG cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          OutK6) := by
  have hDec := k6_dec_rides cs G arr smp decT msR hSig Hs D.blind
  have t3 := k6_t3_cut_of_items D.items _ hpl rfl hs rfl
  have t4 := k6_t4_cut_of_items Hs D.blind D.items _ hpl rfl hs rfl
  rw [hSig.eq] at t3 t4
  have hrd : q.b.rounds = bS.rounds := by
    rw [Hs.piece]
    exact Hs.narrows.1
  exact k6_tiedBy_of_lawR cs G arr smp decT c₀ Wp .two Fr q 24 bef B bS msR tokOf N Mg links PS k _
    Rch hpl rfl Hs (planB_seated Hs.lot D.planS)
    (meansCutG cs G arr smp decT msR N s seat Wp pl Fr) InK6 OutK6
    (k6_law_cutG cs G arr smp decT msR N s seat Wp pl .two Fr q Hs.back D.blind D.plan6 D.fenced
      (PiecePays.pays_logN q Hs.lot D.planS hrd Hs.back D.len D.along)
      (PiecePays.pays_err q Hs.lot D.planS hrd Hs.back D.len D.along D.cap))
    (fun a ha _ hm => k6_t1 Wp N Mg links PS k _ 24 hfit hpl rfl hs rfl D.pubSays a ha
      (fun e => e hm))
    (fun a τ b ha hrc hm hb hA => k6_t2_kept Hs N Mg links PS k _ _ 24 hpl hp' rfl rfl hs
        rfl
      rfl D.numbers a τ b ha hm hb (D.order a τ b hb)
      (fun x h => by
        obtain ⟨o, F1, X, Q, _, _, _, e⟩ := k6_behind Hs a b τ hb
        rw [e, hSig.held]
        rw [hSig.held] at h
        exact h)
      (hDec a τ b hb)
      (fun x hx h => k6_shown_rides cs G arr smp decT msR hSig a τ b hb x (D.fence x hx) h)
      (fun x hx h =>
        k6_noColl_rides cs G arr smp decT msR hSig Hs D.blind a τ b hb x (D.fence x hx) h)
      (D.pubBehind a τ b ha hrc hm hb hA) (D.pubSentences a τ b ha hrc hm hb hA))
    t3 t4 D.t5 hDec

end

/-- **THE TIE AT SUB-PROTOCOL 341 OF THE FULL CHAIN.** -/
theorem k6_tied_cut_full (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (bef : List (ℕ × ℕ))
    (bS B : Block S Claim)
    (num : Fmt.TreeSource → Nat)
    (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit Mg.more linksFull (First.flatPlacesOf linksFull true) = true)
    (hSig : SigFields cs G arr smp msR decT Mg)
    (D : K6DueAt cs G arr smp decT msR N s seat Wp pl Fr Mg linksFull 341 Rch bS num q) :
    TiedByR N Mg linksFull (First.flatPlacesOf linksFull true) (fun a => a) Rch 341
      (q.withMap (extQAt cs G arr smp msR decT c₀ tokOf N linksFull
        (First.flatPlacesOf linksFull true) (fun a => a) 341))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => meansCutG cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          InK6)
      (relAt (fun i a w => meansCutG cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          OutK6) :=
  k6_tied_cut_at_object cs G arr smp decT c₀ msR N s seat Wp pl Fr tokOf Mg linksFull 341 Rch
    bef bS B num q Hs Sound.place341_full hfit head_full place342_full hSig D

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tied_cut_at_object
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tied_cut_full
