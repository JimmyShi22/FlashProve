-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
lean/Johnson/Desc/Sound/K6TiedR.lean: K6 IN THE CHAIN OF PROMISES, SECOND FORM: K6Tied.lean's two
    end theorems with the condition Rch k a in hand in each tie
(`TiedByR`, TiedR.lean). Made from their texts by program.
  WHAT TURNS BESIDE THE ONE PREMISE MORE: THE FIRST TIE IS A PREMISE NOW (t1: the promise in front,
      Rch, no mark ⟹
    K6Left): in the first form it was paid here from three public items (`k6_t1`: hfit,
        hPub); which of these
    items stay in the table and which become facts along the fold is not settled: so t1 is left
        to K6's files, from
    either. `k6_t1` still pays it where the three items stand (drop Rch).
  `k6_tiedBy_of_lawR` (general in the law) · `k6_tiedByR` (at K6's files' own law).
Limits. General in Rch. K6Tied.lean's own limits. A rule over letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.K6Tied
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn ModelPart Numbers Meaning Pub pubFit pubRowOf)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT Fenced SmpStays ErrBears
  kitK kitFs rowOfPart yes_of_part onQ meansQ relQ insQ outsQ openAfter extQAt extQAt_quiet
  lays_nothing_K6 strsOf TiedAt TiedBy TiedByR asked_of_on goodIn_across out_yes below_narrows
      out_behind)

namespace AtTable


section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) (l : ℕ)
  (bef : List (ℕ × ℕ)) (B bS : Block S Claim)

/-- **K6 IN THE CHAIN OF PROMISES, SECOND FORM, GENERAL IN THE LAW.** -/
theorem k6_tiedBy_of_lawR {ι : Type} (msT : List Mem) (tokOf : P × S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true)
    (means : P → ι → S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (In Out : ι → Prop)
    (law : ∀ (z : P) (b6 : Block S Unit), blockOf Wp l = some b6 →
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)).Own (fun a => K6On Wp a.1)
        (fun b => K6After Wp b.1) (means z) In Out)
    (t1 : ∀ a, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      K6Left Wp a.1.2)
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means b.1.1) Out (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means a.1.1) In (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links
    ps k) a w) (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links ps (fun a => a)
          (k + 1) b →
      relQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedByR N Mg links ps (fun a => a) Rch k
      (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => means a.1.1 i (a.1.2, a.2) w) In)
      (relAt (fun i a w => means a.1.1 i (a.1.2, a.2) w) Out) := by
  have hE := extQAt_quiet (Fr := Fr) cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k p hp
    (lays_nothing_K6 N links p hk).1 (lays_nothing_K6 N links p hk).2.1
    (lays_nothing_K6 N links p hk).2.2
  have hid := Sound.withMap_id q
    (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k) hE
  refine ⟨
    k6_carry_left Wp fld Fr q l bef B bS H hplan means In Out law _ hE,
    fun a ha hr hm => t1 a ha hr (Classical.not_not.1 hm),
    fun a τ b ha hr hm hb h' => t2 a τ b ha hr (Classical.not_not.1 hm) hb h'.1,
    fun a τ b w ha hr hm hb h' hw => t3 a τ b w ha hr (Classical.not_not.1 hm) hb h'.1 hw,
    fun a τ b w ha hr hm hb h' hw hi => ?_,
    fun a τ b w i ha hr hm hb hon hall hi hin => ?_,
    fun a τ b hb hm => absurd (k6_no_mark H a b τ hb) hm,
    hDec⟩
  · rw [hid] at hi ⊢
    exact t4 a τ b w ha hr (Classical.not_not.1 hm) hb h'.1 hw hi
  · rw [hid]
    exact t5 a τ b w i ha hr (Classical.not_not.1 hm) hb hon hall hi hin

/-- **K6 IN THE CHAIN OF PROMISES, SECOND FORM.** -/
theorem k6_tiedByR (msT : List Mem) (tokOf : P × S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true) (hF : Fenced q.base ms)
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64) (hBl : Blind cs smp decT)
    (hloc : ReadsPinned cs ms rd6)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (t1 : ∀ a, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      K6Left Wp a.1.2)
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansK6 cs G arr (fun s => smp (b.1.1, s)) (fun c s => decT c (b.1.1, s)) ms rd6 Wp
        Fr) OutK6 (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms rd6 Wp
        Fr) InK6 (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links ps k) a w)
    (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none
        →
      q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b →
      relQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedByR N Mg links ps (fun a => a) Rch k
      (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s))
        (fun c s => decT c (a.1.1, s)) ms rd6 Wp Fr i (a.1.2, a.2) w) InK6)
      (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s))
        (fun c s => decT c (a.1.1, s)) ms rd6 Wp Fr i (a.1.2, a.2) w) OutK6) := by
  have hE := extQAt_quiet (Fr := Fr) cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k p hp
    (lays_nothing_K6 N links p hk).1 (lays_nothing_K6 N links p hk).2.1
    (lays_nothing_K6 N links p hk).2.2
  have hid := Sound.withMap_id q
    (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k) hE
  refine ⟨
    k6_own_left cs G arr smp decT c₀ ms rd6 Wp fld Fr q l bef B bS H hplan hBl hloc hF hlog hErr _
      hE,
    fun a ha hr hm => t1 a ha hr (Classical.not_not.1 hm),
    fun a τ b ha hr hm hb h' => t2 a τ b ha hr (Classical.not_not.1 hm) hb h'.1,
    fun a τ b w ha hr hm hb h' hw => t3 a τ b w ha hr (Classical.not_not.1 hm) hb h'.1 hw,
    fun a τ b w ha hr hm hb h' hw hi => ?_,
    fun a τ b w i ha hr hm hb hon hall hi hin => ?_,
    fun a τ b hb hm => absurd (k6_no_mark H a b τ hb) hm,
    hDec⟩
  · rw [hid] at hi ⊢
    exact t4 a τ b w ha hr (Classical.not_not.1 hm) hb h'.1 hw hi
  · rw [hid]
    exact t5 a τ b w i ha hr (Classical.not_not.1 hm) hb hon hall hi hin

end

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedBy_of_lawR
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedByR
