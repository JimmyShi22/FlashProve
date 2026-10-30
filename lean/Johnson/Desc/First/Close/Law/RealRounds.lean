-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealRounds.lean: the six readings of K10's law at the real written
rounds.

Why. K10's law over its written rounds (Johnson/Desc/First/Close/Law/Leads.lean) has the three kinds
of written round and the six readings (`Rd`, Johnson/Top/H/BatFoldPlace.lean) as letters. Here they
are filled: the rounds are those of a chain's stretch "BAT", "FOLD epsilon", k times "FOLD round"
(`uLT (ckP .two)`), and a round is read as a kind is shown it.
  `shownP d m ch`: what a kind is shown of a written round (`shownR`, without the sealed digest);
  WHERE THE ROUND'S TEST OF WORK FAILS, NOTHING DRAWN. So the work is credited: a written challenge
  that fails the test is read as no typed challenge. What was sent does not hang on the challenge.
  `realRd`: the six readings. How a seed and a challenge are read off the list of drawn elements
  (rdZ, rdCh) stay letters.
  `realRd_scal`: `Rd.Scal`, from the one law on rdCh.
  `shape_k10`: the stretch's written rounds are the three rounds, the third k times.
  `realRd_V`: where all tests of work pass, the reading of the written stretch is the view's list of
  rounds (`rvT`), each without the sealed digest: what `Block.step` hands a kind.
  `RealReads`: on what a round draws, rdZ | rdCh are one-to-one maps of the typed values; at nothing
  drawn they give nothing. `real_fits`: then the written counts "typed count times the sampler's
  number" bear the typed ones (`CarryS.Fits`). `real_fits_cap`: if these are shares of at most 2⁻¹ ^
  128, so does the cap.
  `oneOf ι`, `realReads_of_sends`, `realRd_scal_one`: the two readings as "the one element drawn,
  read in the field, through ι": at three rounds that each draw one element and nothing else
  (`SendsDraws`) and one-to-one ι they are as `RealReads` asks.
  `CarryS.Fits.mono_written`: larger written counts bear what smaller ones bear. `cap_cast`: the cap
  along an equation of shapes.
Limits. Readings and counts: no verifier's decision occurs, and no count is shown small:
`real_fits_cap`'s premise is the kind's row "count at most the cap". That a chain's stretch at K10's
place has these data is a premise of whoever calls this.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.BatFoldTied
import Johnson.Flat.ReadingShown
import OnBytes.Slice.RoundsMaps
import Johnson.Desc.Block
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat.CarryS
open Iop

/-- Larger written counts bear what smaller ones bear. -/
theorem Fits.mono_written : ∀ {s s' : Shape} (F : CarryS s s') (ε : Err s') (ε₁ ε₂ : Err s),
    F.Fits ε ε₁ → Err.le ε₁ ε₂ → F.Fits ε ε₂
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .step _ _ k, (_, ε), (_, ε₁), (_, ε₂), h, hl =>
    ⟨h.1.imp fun _ hw => ⟨hw.1, hw.2.trans hl.1⟩,
      fun m c => Fits.mono_written (k m c) ε ε₁ ε₂ (h.2 m c) hl.2⟩
  | _, _, .skip k, ε, (_, ε₁), (_, ε₂), h, hl =>
    fun m c => Fits.mono_written (k m c) ε ε₁ ε₂ (h m c) hl.2

end OnBytes.Flat.CarryS

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Prob Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt

/-! ## 1 A written round as a kind is shown it -/

/-- What a view shows as sent in a written round. -/
def sentP (d : RDT) (m : (wT d).Msg) : List Fmt.ItemValue :=
  PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)

/-- What a kind is shown of a written round; where the round's test of work fails, nothing drawn. -/
def shownP (d : RDT) (m : (wT d).Msg) (ch : (wT d).Chal) : Fmt.RoundView :=
  ⟨sentP d m,
    if GChal.pass (b := d.entry.work) ch = true then (noDigest (shownR d m ch)).drawn
    else ⟨[], [], [], none⟩⟩

/-- What is shown as sent does not hang on the verifier's message. -/
theorem shownP_vals (d : RDT) (m : (wT d).Msg) (ch : (wT d).Chal) :
    (shownP d m ch).vals = sentP d m := rfl

theorem shownP_pass {d : RDT} {m : (wT d).Msg} {ch : (wT d).Chal}
    (h : GChal.pass (b := d.entry.work) ch = true) : shownP d m ch = noDigest (shownR d m ch) := by
  unfold shownP
  rw [if_pos h]
  rfl

/-- The elements that a round's typed values show as drawn, as the program's elements. -/
def elemsE (d : RDT) (v : Vals .two (Fmt.dsOf d.entry d.kind)) : List E :=
  (_root_.Run.drawnOf .two d.entry d.kind v).elems.map E.ofTriple

theorem drawn_shownP_pass {d : RDT} {m : (wT d).Msg} {ch : (wT d).Chal}
    (h : GChal.pass (b := d.entry.work) ch = true) :
    PscRun.drawnOf (shownP d m ch) = elemsE d (valsOf (toRD d) ch) := by
  rw [shownP_pass h]
  rfl

theorem drawn_shownP_fail {d : RDT} {m : (wT d).Msg} {ch : (wT d).Chal}
    (h : ¬ GChal.pass (b := d.entry.work) ch = true) : PscRun.drawnOf (shownP d m ch) = [] := by
  unfold shownP
  rw [if_neg h]
  rfl

/-- Under a reading that is g on what is drawn and nothing at nothing, the map of verifier messages
is `chalTo` (OnBytes/Slice/Draws.lean). -/
theorem read_eq_chalTo {γ : Type} (d : RDT) (φ : List E → Option γ)
    (g : Vals .two (Fmt.dsOf d.entry d.kind) → γ) (hrd : ∀ v, φ (elemsE d v) = some (g v))
    (hnil : φ [] = none) (m : (wT d).Msg) (ch : (wT d).Chal) :
    φ (PscRun.drawnOf (shownP d m ch)) = chalTo (toRD d) g ch := by
  show _ = if GChal.pass (b := d.entry.work) ch = true then some (g (valsOf (toRD d) ch)) else none
  by_cases h : GChal.pass (b := d.entry.work) ch = true
  · rw [if_pos h, drawn_shownP_pass h, hrd]
  · rw [if_neg h, drawn_shownP_fail h, hnil]

/-- So at most w written verifier messages are read as one typed one. -/
theorem read_fib {γ : Type} (d : RDT) (φ : List E → Option γ)
    (g : Vals .two (Fmt.dsOf d.entry d.kind) → γ) (hrd : ∀ v, φ (elemsE d v) = some (g v))
    (hnil : φ [] = none) (hg : Function.Injective g) (hlog : d.entry.logN ≤ 64) (m : (wT d).Msg)
    (c' : γ) :
    cnt (fun ch : (wT d).Chal => φ (PscRun.drawnOf (shownP d m ch)) = some c') ≤
      (bsRound .two d.entry d.kind).w := by
  have e : (fun ch : (wT d).Chal => φ (PscRun.drawnOf (shownP d m ch)) = some c') =
      fun ch => chalTo (toRD d) g ch = some c' :=
    funext fun ch => by rw [read_eq_chalTo d φ g hrd hnil m ch]
  rw [e]
  exact chalTo_fib (toRD d) g hg hlog c'

/-! ## 2 The six readings -/

variable (c : BatFoldCaller GE) (dB dE dR : RDT) (rdZ : List E → Option c.s.Z.D)
  (rdCh : List E → Option (Yc c).Ch)

/-- The six readings at the real written rounds. -/
def realRd : Rd c (wT dB) (wT dE) (wT dR) :=
  ⟨shownP dB, shownP dE, shownP dR, readE, rdZ, rdCh⟩

theorem realRd_scal (hval : ∀ g ch, rdCh [g] = some ch → (Yc c).val ch = readE g) :
    (realRd c dB dE dR rdZ rdCh).Scal :=
  ⟨rfl, hval, fun m ch ch' => (shownP_vals dE m ch).trans (shownP_vals dE m ch').symm,
    fun m ch ch' => (shownP_vals dR m ch).trans (shownP_vals dR m ch').symm⟩

/-! ## 3 The stretch's shape, and its reading -/

theorem uLT_replicate (d : RDT) :
    ∀ k : ℕ, uLT (ckP .two) (List.replicate k d) = List.replicate k (wT d)
  | 0 => rfl
  | k + 1 => congrArg (List.cons (wT d)) (uLT_replicate d k)

theorem shape_k10 (k : ℕ) :
    uLT (ckP .two) (dB :: dE :: List.replicate k dR) =
      wT dB :: wT dE :: List.replicate k (wT dR) :=
  congrArg (fun s => wT dB :: wT dE :: s) (uLT_replicate dR k)

theorem cast_tr_cons (r : Round) {s t : Shape} (h : s = t) (m : r.Msg) (ch : r.Chal)
    (τ : Iop.Tr s) :
    cast (congrArg Iop.Tr (congrArg (List.cons r) h)) ((m, ch, τ) : Iop.Tr (r :: s)) =
      ((m, ch, cast (congrArg Iop.Tr h) τ) : Iop.Tr (r :: t)) := by
  subst h
  rfl

theorem cap_cast {s t : Shape} (h : s = t) (k : ℕ) :
    cast (congrArg Err h) (Err.cap k s) = Err.cap k t := by
  subst h
  rfl

theorem realRd_vK : ∀ (k : ℕ) (τ : Iop.Tr (uLT (ckP .two) (List.replicate k dR))),
    passT (ckP .two) (List.replicate k dR) (rhoT (ckP .two) (List.replicate k dR) τ) = true →
    (realRd c dB dE dR rdZ rdCh).vK k (cast (congrArg Iop.Tr (uLT_replicate dR k)) τ) =
      (rvT (ckP .two) (List.replicate k dR) τ).map noDigest
  | 0, _, _ => rfl
  | k + 1, (m, ch, τ), hp => by
    have hp' : (GChal.pass (b := dR.entry.work) ch &&
        passT (ckP .two) (List.replicate k dR) (rhoT (ckP .two) (List.replicate k dR) τ)) =
        true := hp
    obtain ⟨p1, p2⟩ := Bool.and_eq_true_iff.1 hp'
    have e : cast (congrArg Iop.Tr (uLT_replicate dR (k + 1)))
        ((m, ch, τ) : Iop.Tr (uLT (ckP .two) (List.replicate (k + 1) dR))) =
        ((m, ch, cast (congrArg Iop.Tr (uLT_replicate dR k)) τ) :
          Iop.Tr (wT dR :: List.replicate k (wT dR))) :=
      cast_tr_cons (wT dR) (uLT_replicate dR k) m ch τ
    rw [e]
    show shownP dR m ch ::
        (realRd c dB dE dR rdZ rdCh).vK k (cast (congrArg Iop.Tr (uLT_replicate dR k)) τ) =
      noDigest (shownR dR m ch) :: (rvT (ckP .two) (List.replicate k dR) τ).map noDigest
    rw [realRd_vK k τ p2, shownP_pass p1]

/-- **Where all tests of work pass, the reading of the written stretch is what a kind is shown.** -/
theorem realRd_V (τ : Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)))
    (hp : passT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR)
      (rhoT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR) τ) = true) :
    (realRd c dB dE dR rdZ rdCh).V (cast (congrArg Iop.Tr (shape_k10 dB dE dR (Yc c).k)) τ) =
      (rvT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR) τ).map noDigest := by
  obtain ⟨mB, cB, mE, cE, τ'⟩ := τ
  have hp' : (GChal.pass (b := dB.entry.work) cB && (GChal.pass (b := dE.entry.work) cE &&
      passT (ckP .two) (List.replicate (Yc c).k dR)
        (rhoT (ckP .two) (List.replicate (Yc c).k dR) τ'))) = true := hp
  obtain ⟨pB, h2⟩ := Bool.and_eq_true_iff.1 hp'
  obtain ⟨pE, pR⟩ := Bool.and_eq_true_iff.1 h2
  have e : cast (congrArg Iop.Tr (shape_k10 dB dE dR (Yc c).k))
      ((mB, cB, mE, cE, τ') : Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate (Yc c).k dR))) =
      ((mB, cB, mE, cE, cast (congrArg Iop.Tr (uLT_replicate dR (Yc c).k)) τ') :
        Iop.Tr (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) :=
    (cast_tr_cons (wT dB) (congrArg (List.cons (wT dE)) (uLT_replicate dR (Yc c).k)) mB cB
      (mE, cE, τ')).trans
      (congrArg (fun x => (mB, cB, x)) (cast_tr_cons (wT dE) (uLT_replicate dR (Yc c).k) mE cE τ'))
  rw [e]
  show shownP dB mB cB :: shownP dE mE cE ::
      (realRd c dB dE dR rdZ rdCh).vK (Yc c).k
        (cast (congrArg Iop.Tr (uLT_replicate dR (Yc c).k)) τ') =
    noDigest (shownR dB mB cB) :: noDigest (shownR dE mE cE) ::
      (rvT (ckP .two) (List.replicate (Yc c).k dR) τ').map noDigest
  rw [realRd_vK c dB dE dR rdZ rdCh (Yc c).k τ' pR, shownP_pass pB, shownP_pass pE]

/-! ## 4 The counts -/

/-- On what a round draws the two readings are one-to-one maps of the typed values; at nothing drawn
they give nothing. -/
structure RealReads where
  gB : Vals .two (Fmt.dsOf dB.entry dB.kind) → c.s.Z.D
  gE : Vals .two (Fmt.dsOf dE.entry dE.kind) → (Yc c).Ch
  gR : Vals .two (Fmt.dsOf dR.entry dR.kind) → (Yc c).Ch
  injB : Function.Injective gB
  injE : Function.Injective gE
  injR : Function.Injective gR
  logB : dB.entry.logN ≤ 64
  logE : dE.entry.logN ≤ 64
  logR : dR.entry.logN ≤ 64
  rdB : ∀ v, rdZ (elemsE dB v) = some (gB v)
  rdE : ∀ v, rdCh (elemsE dE v) = some (gE v)
  rdR : ∀ v, rdCh (elemsE dR v) = some (gR v)
  nilZ : rdZ [] = none
  nilCh : rdCh [] = none

/-- Each typed count times w. -/
def timesW (w : ℕ) {r r' : Round} : ∀ k : ℕ, Err (List.replicate k r') → Err (List.replicate k r)
  | 0, _ => ()
  | k + 1, (e, ε) => (e * w, timesW w k ε)

variable {c dB dE dR rdZ rdCh}

theorem carK_fits (H : RealReads c dB dE dR rdZ rdCh) :
    ∀ (k : ℕ) (ε : Err (List.replicate k (Cb.sRoundS GE (Yc c).Ch (Yc c).n))),
      ((realRd c dB dE dR rdZ rdCh).carK k).Fits ε
        (timesW (bsRound .two dR.entry dR.kind).w k ε)
  | 0, _ => trivial
  | k + 1, (_, ε) =>
    ⟨⟨(bsRound .two dR.entry dR.kind).w,
        fun m c' => read_fib dR rdCh H.gR H.rdR H.nilCh H.injR H.logR m c', le_rfl⟩,
      fun _ _ => carK_fits H k ε⟩

/-- **The written counts "typed count times the sampler's number" bear the typed ones.** -/
theorem real_fits (H : RealReads c dB dE dR rdZ rdCh) (eB eE : ℕ)
    (εK : Err (List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n))) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits (eB, eE, εK)
      (eB * (bsRound .two dB.entry dB.kind).w, eE * (bsRound .two dE.entry dE.kind).w,
        timesW (bsRound .two dR.entry dR.kind).w (Yc c).k εK) :=
  ⟨⟨(bsRound .two dB.entry dB.kind).w,
      fun m c' => read_fib dB rdZ H.gB H.rdB H.nilZ H.injB H.logB m c', le_rfl⟩,
    fun _ _ =>
      ⟨⟨(bsRound .two dE.entry dE.kind).w,
          fun m c' => read_fib dE rdCh H.gE H.rdE H.nilCh H.injE H.logE m c', le_rfl⟩,
        fun _ _ => carK_fits H (Yc c).k εK⟩⟩

/-- **If these are shares of at most 2⁻¹ ^ 128, the cap bears the typed counts.** -/
theorem real_fits_cap (H : RealReads c dB dE dR rdZ rdCh) (eB eE : ℕ)
    (εK : Err (List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n)))
    (hb : Err.Below (s := wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))
      (eB * (bsRound .two dB.entry dB.kind).w, eE * (bsRound .two dE.entry dE.kind).w,
        timesW (bsRound .two dR.entry dR.kind).w (Yc c).k εK) ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits (eB, eE, εK)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) :=
  CarryS.Fits.mono_written _ _ _ _ (real_fits H eB eE εK) (Err.le_cap_of_below_inv 128 _ hb)

/-! ## 5 The two readings as "the one element drawn" -/

/-- A list of one element is read through ι; any other list as nothing. -/
def oneOf {γ : Type} (ι : GE → γ) : List E → Option γ
  | [g] => some (ι (readE g))
  | _ => none

theorem oneOf_some {γ : Type} (ι : GE → γ) (e : E) : (oneOf ι [e]).isSome := rfl

/-- Read in the field, the elements shown as drawn are the typed values' elements. -/
theorem elemsE_read (d : RDT) (v : Vals .two (Fmt.dsOf d.entry d.kind)) :
    (elemsE d v).map readE = elemsV _ v := by
  have e : (readE ∘ E.ofTriple) = toE := funext readE_ofTriple
  unfold elemsE
  rw [List.map_map, e]
  exact elems_collect _ v

/-- At a round that draws one element and nothing else. -/
theorem oneOf_elemsE {γ : Type} (ι : GE → γ) (d : RDT) {ns a : ℕ}
    (h : SendsDraws (toRD d) ns 1 0 a) (v : Vals .two (Fmt.dsOf d.entry d.kind)) :
    oneOf ι (elemsE d v) = some (ι (gOne _ v)) := by
  have hm := elemsE_read d v
  have hl : (elemsE d v).length = 1 := by
    have h1 := congrArg List.length hm
    rw [List.length_map, elemsV_length] at h1
    exact h1.trans h.els
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
  rw [hx] at hm ⊢
  show some (ι (readE x)) = some (ι ((elemsV _ v).getD 0 0))
  rw [← hm]
  rfl

/-- **The readings "the one element drawn, through ι" are as asked**, at three rounds that each draw
one element and nothing else. -/
def realReads_of_sends (c : BatFoldCaller GE) (dB dE dR : RDT) (ιZ : GE → c.s.Z.D)
    (ιC : GE → (Yc c).Ch) (hZ : Function.Injective ιZ) (hC : Function.Injective ιC)
    {nB aB nE aE nR aR : ℕ} (hB : SendsDraws (toRD dB) nB 1 0 aB)
    (hE : SendsDraws (toRD dE) nE 1 0 aE) (hR : SendsDraws (toRD dR) nR 1 0 aR) :
    RealReads c dB dE dR (oneOf ιZ) (oneOf ιC) where
  gB := fun v => ιZ (gOne _ v)
  gE := fun v => ιC (gOne _ v)
  gR := fun v => ιC (gOne _ v)
  injB := hZ.comp hB.gOne_inj
  injE := hC.comp hE.gOne_inj
  injR := hC.comp hR.gOne_inj
  logB := hB.logN
  logE := hE.logN
  logR := hR.logN
  rdB := oneOf_elemsE ιZ dB hB
  rdE := oneOf_elemsE ιC dE hE
  rdR := oneOf_elemsE ιC dR hR
  nilZ := rfl
  nilCh := rfl

theorem realRd_scal_one (c : BatFoldCaller GE) (dB dE dR : RDT) (ιZ : GE → c.s.Z.D)
    (ιC : GE → (Yc c).Ch) (hv : ∀ x, (Yc c).val (ιC x) = x) :
    (realRd c dB dE dR (oneOf ιZ) (oneOf ιC)).Scal :=
  realRd_scal c dB dE dR (oneOf ιZ) (oneOf ιC) fun g ch h => by
    have h1 : some (ιC (readE g)) = some ch := h
    rw [← Option.some.inj h1]
    exact hv _

end VerifiableInference.Desc.First.Close

#print axioms OnBytes.Flat.CarryS.Fits.mono_written
#print axioms VerifiableInference.Desc.First.Close.realRd_scal
#print axioms VerifiableInference.Desc.First.Close.realRd_V
#print axioms VerifiableInference.Desc.First.Close.real_fits
#print axioms VerifiableInference.Desc.First.Close.real_fits_cap
#print axioms VerifiableInference.Desc.First.Close.cap_cast
#print axioms VerifiableInference.Desc.First.Close.oneOf_elemsE
#print axioms VerifiableInference.Desc.First.Close.realReads_of_sends
#print axioms VerifiableInference.Desc.First.Close.realRd_scal_one
