-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6TiedPaid.lean: the output head's block in the chain of promises, at the law
without a letter for the reading (Law/K6TiedCut.lean: k6_tiedBy_cut), WITH THREE OF ITS PREMISES
PAID BY LAWS THAT LAY BESIDE IT.

Main name (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  k6_tiedBy_cut_paid: k6_tiedBy_cut at the field .two, without hplan, hlog and hErr. In their place:
      hpS: the seated value's own test on the plan says yes (hplan: Law/AtBorder.lean's
      planB_seated); and three conditions on the description's piece q that other
      files pay for the pieces that the maker cuts: hlen, hA, herr (hlog, hErr:
      Law/K6PiecePays.lean's pays_logN, pays_err, called AT q ITSELF: that q's block declares the
      seated value's rounds follows from Seated's fields "piece" and "narrows").

Every letter under "there is": none.
LEFT, BY NAME. ON THE TABLE: hfit hp hk hl hs hpc. ON THE SEAT'S TEXT: H. ON THE PLAN: hpS, hP
(PlanK6), hF. ON THE PIECE: hlen hA herr. ON THE FILLINGS: hPub hBl hDec. THE TIES: t2 t3 t4 t5.
What it does not say. All that Law/K6TiedCut.lean does not say. The field .two alone. A joining: no
new mathematics. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6TiedCut
import Johnson.Desc.Kinds.Law.K6PiecePays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S HeadOwn ModelPart Numbers Meaning Pub pubFit pubRowOf)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT Fenced SmpStays ErrBears
  kitK kitFs onQ meansQ relQ insQ outsQ openAfter extQAt strsOf TiedBy out_yes below_narrows
  out_behind Along RoundIs)
open _root_.Iop (Err)

namespace AtTable

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (c₀ : Fin rows → Fin cols → GE) (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (Fr : Frame)
  (q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
  (bef : List (ℕ × ℕ)) (B bS : Block S Claim)

/-- **K6 in the chain of promises, at the law without a letter for the reading, three premises
paid.** -/
theorem k6_tiedBy_cut_paid (msT : List Mem) (tokOf : P × S → Tok)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart) (ps : List Place)
        (k : ℕ) (p : Place)
    (m : ℕ) (hfit : pubFit Mg.more links ps = true) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (hl : p.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (H : Seated Wp .two Fr q 24 bef B bS) (hpS : bS.planOk = true) (hPub : PubSays Wp Mg m)
    (hBl : Blind cs smp decT) (hP : PlanK6 cs arr msR N s seat Wp pl)
    (hF : Fenced q.base (ms0 msR N))
    (hlen : q.ds.length + q.back.length = q.b.rounds.length) {num : Fmt.TreeSource → Nat}
    (hA : Along (RoundIs num) q.b.rounds q.ds)
    (herr : q.err = Err.cap 128 (uLT (_root_.Run.ckP .two) q.ds))
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansCut cs G arr smp decT msR N s seat Wp pl Fr b.1.1) OutK6 (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansCut cs G arr smp decT msR N s seat Wp pl Fr a.1.1) InK6 (a.1.2, a.2) w → relAt
          (meansQ (Fr := Fr) N Mg fun a => a) (insQ links
    ps k) a w) (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed =
      none → q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b →
      relQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedBy N Mg links ps (fun a => a) k
      (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => meansCut cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          InK6)
      (relAt (fun i a w => meansCut cs G arr smp decT msR N s seat Wp pl Fr a.1.1 i (a.1.2, a.2) w)
          OutK6) :=
  have hr : q.b.rounds = bS.rounds := by
    rw [H.piece]
    exact H.narrows.1
  k6_tiedBy_cut cs G arr smp decT c₀ msR N s seat Wp pl .two Fr q bef B bS msT tokOf Mg links ps k p
    m hfit hp hk hl hs hpc H (planB_seated H.lot hpS) hPub hBl hP hF
    (PiecePays.pays_logN q H.lot hpS hr H.back hlen hA)
    (PiecePays.pays_err q H.lot hpS hr H.back hlen hA herr) t2 t3 t4 t5 hDec

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedBy_cut_paid
