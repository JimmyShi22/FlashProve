-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6TiedCut.lean: THE OUTPUT HEAD'S BLOCK IN THE CHAIN OF PROMISES, AT THE
LAW OF K6 THAT HAS NO LETTER FOR THE READING: the call of Law/K6Cut.lean's k6OwnCut into the
road from a kind's law to the table's tie (Johnson/Desc/Sound/K6Tied.lean: k6_tiedBy_of_law,
which is general in the law).

That road first stood on Law/K6Own.lean's k6Own, where the reading rd6 and the list ms are free
letters: at a constant rd6 the tie held and read nothing of the witness. Here the law is k6OwnCut:
the components are read off the table's witness by other files' own readers, cut to the four
ranges of the head's cells; the pinned members are ms0 msR N; the mask row has the plan's length;
the conditions on the public letters are PlanK6.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  meansCut ... z: the law's three items (closed, opened, pins) at the public part z:
      Law/K6OwnW.lean's meansW at compCut, ms0 and base24, with the two readers smp and decT taken
      at z.
  k6_law_cut: THE PREMISE "law" OF THAT ROAD, PAID: for every public part z and every value b6 of
      blockOf Wp 24: the piece that holds "below b6" with q's base, rounds and errors has Own
      between K6On and K6After at meansCut. "The samples stay" and "the stored table's decoding
      stays" are paid from Blind (the two readers do not read where the chain stands), as in
      K6Tied.lean's own proof for the older law.
  k6_tiedBy_cut: SO: TiedBy at block number k, at the description's piece q with the table's
      extractor: in front K6Left; behind K6After and no mark; the relations are meansCut's.

Every letter under "there is": none in the tops' own text.
LEFT, BY NAME, in k6_tiedBy_cut. ON THE TABLE: hfit hp hk hl hs hpc. ON THE SEAT'S TEXT: H (in this
library one theorem, Johnson/Desc/Sound/Border62.lean's seated_of_object, gives all five fields of Seated from the premise Object61). ON THE PLAN: hplan, hP (PlanK6:
Law/PlanK6At.lean has a candidate filling of its letters; four clauses have been evaluated true at
both stored plans at the own fillings of a file of evaluations that is not named here (its pl is the
candidate's; that its seat is the candidate's is not held by a run), under riders; no theorem),
hF (Law/NamedAtCut.lean [not in this library]: fenced_ms0), hlog, hErr (Law/K6PiecePays.lean).
ON THE FILLINGS: hPub, hBl,
hDec. THE TIES: t2 t3 t4 t5, stated at meansCut.
What it does not say. That any of these holds. OF THE TIE'S EIGHT CLAUSES THREE ARE PROVED HERE (the
law, the first tie, "a mark stays"); FIVE ARE PREMISES ALMOST WORD FOR WORD (t2 t3 t4 t5 hDec). The
chain spends TiedAt, where the law's relations stand under "there are": SO WHAT THE READING IS WORTH
TO THE CHAIN IS WHAT t3 AND t4 AT meansCut CAN BE PAID FOR AT THE TABLE'S OWN MEANING: this is the
rule through which a tie that reads the witness can be had, not that tie.
Law/K6TiedAtObject.lean calls the payers of t2, t5 and hDec. WHAT is read has no letter;
WHERE it is read (seat 24, pl) are letters still. The reader's numbers and the table's are ONE
letter N here. The link's number 24 is a literal, and m is tied to it by nothing in the binder:
the theorem serves the full chain's block 341 alone; at the small chain Seated ... 24 ... cannot
hold. No values are shown at which the premises hold together. Nothing on soundness.
-/
import Johnson.Desc.Sound.K6Tied
import Johnson.Desc.Kinds.Law.K6Cut

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
  out_behind)

namespace AtTable

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (c₀ : Fin rows → Fin cols → GE) (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (fld : Fmt.Fld) (Fr : Frame)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))
  (bef : List (ℕ × ℕ)) (B bS : Block S Claim)

/-- The law's three items at the public part z. -/
def meansCut (z : P) :
    K6Item → S × Fr.E.Str → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop :=
  meansW cs G arr (fun t => smp (z, t)) (fun c t => decT c (z, t)) (ms0 msR N)
    (compCut cs arr msR N s seat Wp pl) (base24 cs arr msR N s seat) Wp Fr

/-- **The road's premise "law", paid by K6's law at the cut.** -/
theorem k6_law_cut (hback : q.back = []) (hBl : Blind cs smp decT)
    (hP : PlanK6 cs arr msR N s seat Wp pl) (hF : Fenced q.base (ms0 msR N))
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (z : P) (b6 : Block S Unit) (h6 : blockOf Wp 24 = some b6) :
    (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)).Own
      (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansCut cs G arr smp decT msR N s seat Wp pl Fr z) InK6 OutK6 := by
  have hrec : ∀ (a b : S × Fr.E.Str) τ,
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit
          (Wit (Fin rows → Fin cols → GE) Tok MsgT)).ior.red.out a τ = some b →
      ∃ h, b.1 = { a.1 with here := h } := by
    intro a b τ hb
    obtain ⟨rs, gs, hd⟩ := out_yes (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)) a b τ hb
    obtain ⟨o, F1, X, Q, _, _, _, e⟩ := record6 h6 ((below_narrows b6).2 _ _ _ _ hd)
    exact ⟨_, e⟩
  refine Came.k6OwnCut cs arr msR N s seat Wp pl G (fun t => smp (z, t))
    (fun c t => decT c (z, t)) fld Fr _ b6 h6 rfl hback (fun _ _ _ => rfl) hP hF ?_ ?_ hlog hErr
  · intro a τ b hb x _
    obtain ⟨h, e⟩ := hrec a b τ hb
    show smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2
    rw [e, hBl.smp]
  · intro a τ b hb
    obtain ⟨h, e⟩ := hrec a b τ hb
    have e2 := out_behind (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)) a b τ hb
    show decT (strsOf Fr b.2).cell (z, b.1) = decT (strsOf Fr a.2).cell (z, a.1)
    rw [e, hBl.dec, e2]
    rfl

/-- **K6 IN THE CHAIN OF PROMISES, AT THE LAW WITHOUT A LETTER FOR THE READING.** -/
theorem k6_tiedBy_cut (msT : List Mem) (tokOf : P × S → Tok)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart) (ps : List Place)
        (k : ℕ) (p : Place)
    (m : ℕ) (hfit : pubFit Mg.more links ps = true) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (hl : p.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (H : Seated Wp fld Fr q 24 bef B bS) (hplan : planB Wp = true) (hPub : PubSays Wp Mg m)
    (hBl : Blind cs smp decT) (hP : PlanK6 cs arr msR N s seat Wp pl)
    (hF : Fenced q.base (ms0 msR N)) (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
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
  k6_tiedBy_of_law cs G arr smp decT c₀ Wp fld Fr q 24 bef B bS msT tokOf N Mg links ps k p m hfit
    hp hk hl hs hpc H hplan hPub (meansCut cs G arr smp decT msR N s seat Wp pl Fr) InK6 OutK6
    (k6_law_cut cs G arr smp decT msR N s seat Wp pl fld Fr q H.back hBl hP hF hlog hErr) t2 t3 t4
    t5 hDec

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_law_cut
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedBy_cut
