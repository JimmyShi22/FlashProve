-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadCallSum.lean: the keys in the columns of the output head's lookup calls are the
library's, and they are the keys from which Johnson/Road/HeadSum.lean starts.

Johnson/Road/HeadSum.lean goes from statements on the key vectors of the lookup calls to the field
relation of the library's plain head. It asks, in the property CallsFit, that the keys under the
verifier's names be the library's, the third digit of a margin times a factor c.
Johnson/Road/HeadCallLib.lean shows of which keys the verifier's forms are the extensions (kvOf).
This file shows that at the library's sizes, for a request without a counted position, these are
the keys that CallsFit asks for. So that clause of CallsFit is a theorem, and what is left of
CallsFit speaks of the layout alone.

The file also states the result of Johnson/Road/HeadCallLib.lean in the library's own names: what
the form that the verifier's keyForm returns is worth, against a function that has the keys of
Policy/Rel/LedgerHead.lean, or of Cm/TargetPHead.lean, in the call's columns.

Main theorems: segName_eq, kv_keyOf, callsFit_of; keyForm_ref_zero, keyForm_ref_brackets,
keyForm_plain_zero, keyForm_plain_brackets. The last four are end statements: no other file reads
them. The theorems on the head's link read keyForm_keys_zero of Johnson/Road/HeadCallLib.lean, and
kv_keyOf through callsFit_of.

What is not claimed. That the layout has each family as a segment of a call, with enough entries and
the family's table, stays a hypothesis. So do the record LinesFit, the property Found and what the
two slots hold. Nothing is said about a verifier's acceptance. The program does not import this
file.
-/
import Johnson.Road.HeadCallLib
import Johnson.Road.HeadSum

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)

variable {K : Type} [Field K]

/-- The two lists of the verifier's names agree. -/
theorem segName_eq (f : Cm.Plain.Fam) : segName f = nameOf (toFam f) := by
  cases f <;> rfl

/-- For a request without a counted position the keys under the verifier's seven names of the plain
head are the keys of Johnson/Road/HeadSum.lean. -/
theorem kv_keyOf (c : K) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    {y : Inst.Model.Head.Req} (h0 : ∀ i, i < 1024 → y.rhoC i = 0) (f : Cm.Plain.Fam) :
    kvOf c HeadSizes.ref np t H y (segName f) = keyOf c np t H y f := by
  cases f
  case NF => exact kv_plain c np t H y (f := .NF) (by decide)
  case NFH => exact kv_plain c np t H y (f := .NFH) (by decide)
  case HD0 => exact kv_plain_HD0 c np t H h0
  case HD1 => exact kv_plain c np t H y (f := .HD1) (by decide)
  case ROW => exact kv_plain c np t H y (f := .ROW) (by decide)
  case HD2 => exact kv_plain c np t H y (f := .HD2) (by decide)
  case CNF => exact kv_plain c np t H y (f := .CNF) (by decide)

/-- What Johnson/Road/HeadSum.lean asks of the layout and of the keys, from the layout alone: for
the keys of this file its clause on the keys holds. -/
theorem callsFit_of {R : Model.Head.Run} {T : ℕ → Inst.Model.Lut} (c : K) (np : NormPar)
    (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (h0 : ∀ i, i < 1024 → y.rhoC i = 0)
    (A : ∀ f : Cm.Plain.Fam, ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = segName f ∧
      Cm.Plain.len f ≤ g.n ∧ T q = lutOf f) :
    CallsFit R (kvOf c HeadSizes.ref np t H y) T c np t H y := fun f => by
  obtain ⟨q, g, h1, h2, h3, h4⟩ := A f
  exact ⟨q, g, h1, h2, h3, h4, kv_keyOf c np t H h0 f⟩

variable {ρ : Reading K} {W : World K}

/-! ## The form of a call, on the library's keys -/

/-- The form of a call at the library's sizes, on the keys of Policy/Rel/LedgerHead.lean.
If f has these keys in the segments' columns (the third digit of a margin times the program's
inverse of 2^(sh + 15)) and the padding key in the columns without a mark, and the two slots hold
what they are meant to hold, the form that the verifier's keyForm returns is worth the extension of
f at the call's key point. -/
theorem keyForm_ref_zero (hρ : Numerals ρ) {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ}
    {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (X : LinesFit ρ W R HeadSizes.ref (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs,
      Found R q g ∧ ∃ s : Inst.Model.Head.Fam, g.name = nameOf s)
    (hsO : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ s : Inst.Model.Head.Fam, s ≠ .HD0 →
      g.name = nameOf s → ∀ a, a < g.n →
      f (g.pos.getD a 0) = Policy.LedgerHead.key (npOf R.h) t H y s a)
    (hsH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" → ∀ a, a < g.n →
      f (g.pos.getD a 0) = fun i => ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        Policy.LedgerHead.key (npOf R.h) t H y .HD0 a i)
    (hpad : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      ∀ j, j < (R.L.calls.getD q default).J → w.getD j 0 = 0 → f j = fun _ =>
        ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
    (hH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" →
      (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl =
        wsum (wOf ρ R q g) R.h.lt u g.n (fun a i => ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i a)))
    (hNF : (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      ((R.L.calls.getD q default).segs.map fun g =>
        if g.name = "NF" then
          wsum (wOf ρ R q g) R.h.lt u g.n (fun a i =>
            Inst.Model.Head.xv t a i *
              Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
        else 0).sum)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
        (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p := by
  have Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f := by
    intro w hw
    refine ⟨fun g hg a ha => ?_, fun j hj hj0 => hpad w hw j hj hj0⟩
    obtain ⟨_, s, hs⟩ := hN g hg
    by_cases hne : s = .HD0
    · subst hne
      rw [hsH g hg hs a ha, hs]
      exact (congrFun (kv_ref_HD0 _ _ t H y) a).symm
    · rw [hsO g hg s hne hs a ha, hs, kv_ref _ _ t H y hne]
  exact keyForm_keys_zero hρ H X hJ hz hp hu hN Kf hH hNF h

/-- The same without a hypothesis on the two slots: the form is worth the extension plus two
brackets, slot less what the slot is meant to hold. -/
theorem keyForm_ref_brackets (hρ : Numerals ρ) {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ}
    {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (X : LinesFit ρ W R HeadSizes.ref (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs,
      Found R q g ∧ ∃ s : Inst.Model.Head.Fam, g.name = nameOf s)
    (hsO : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ s : Inst.Model.Head.Fam, s ≠ .HD0 →
      g.name = nameOf s → ∀ a, a < g.n →
      f (g.pos.getD a 0) = Policy.LedgerHead.key (npOf R.h) t H y s a)
    (hsH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" → ∀ a, a < g.n →
      f (g.pos.getD a 0) = fun i => ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        Policy.LedgerHead.key (npOf R.h) t H y .HD0 a i)
    (hpad : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      ∀ j, j < (R.L.calls.getD q default).J → w.getD j 0 = 0 → f j = fun _ =>
        ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
          (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p +
        ((if q = R.x.qN then W.slot R.x.tN.sCl else 0) -
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "NF" then
              wsum (wOf ρ R q g) R.h.lt u g.n (fun a i =>
            Inst.Model.Head.xv t a i *
              Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
            else 0).sum) +
        ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "HD0" then
              (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl -
                wsum (wOf ρ R q g) R.h.lt u g.n (fun a i => ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i a))
            else 0).sum := by
  have Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f := by
    intro w hw
    refine ⟨fun g hg a ha => ?_, fun j hj hj0 => hpad w hw j hj hj0⟩
    obtain ⟨_, s, hs⟩ := hN g hg
    by_cases hne : s = .HD0
    · subst hne
      rw [hsH g hg hs a ha, hs]
      exact (congrFun (kv_ref_HD0 _ _ t H y) a).symm
    · rw [hsO g hg s hne hs a ha, hs, kv_ref _ _ t H y hne]
  exact keyForm_keys_brackets hρ H X hJ hz hp hu hN Kf h

/-- The form of a call at the library's sizes, on the keys of Cm/TargetPHead.lean,
for a request without a counted position and a call whose segments are families of the plain head.
If f has these keys in the segments' columns (the third digit of a margin times the program's
inverse of 2^(sh + 15)) and the padding key in the columns without a mark, and the two slots hold
what they are meant to hold, the form that the verifier's keyForm returns is worth the extension of
f at the call's key point. -/
theorem keyForm_plain_zero (hρ : Numerals ρ) {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ}
    {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (h0 : ∀ i, i < 1024 → y.rhoC i = 0)
    (X : LinesFit ρ W R HeadSizes.ref (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs,
      Found R q g ∧ ∃ s : Cm.Plain.Fam, g.name = segName s)
    (hsO : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ s : Cm.Plain.Fam, s ≠ .HD0 →
      g.name = segName s → ∀ a, a < g.n →
      f (g.pos.getD a 0) = Cm.Plain.TP.key (npOf R.h) t H y s a)
    (hsH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" → ∀ a, a < g.n →
      f (g.pos.getD a 0) = fun i => ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        Cm.Plain.TP.key (npOf R.h) t H y .HD0 a i)
    (hpad : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      ∀ j, j < (R.L.calls.getD q default).J → w.getD j 0 = 0 → f j = fun _ =>
        ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
    (hH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" →
      (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl =
        wsum (wOf ρ R q g) R.h.lt u g.n (fun a i => ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i a)))
    (hNF : (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      ((R.L.calls.getD q default).segs.map fun g =>
        if g.name = "NF" then
          wsum (wOf ρ R q g) R.h.lt u g.n (fun a i =>
            Inst.Model.Head.xv t a i *
              Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
        else 0).sum)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
        (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p := by
  have Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f := by
    intro w hw
    refine ⟨fun g hg a ha => ?_, fun j hj hj0 => hpad w hw j hj hj0⟩
    obtain ⟨_, s, hs⟩ := hN g hg
    by_cases hne : s = .HD0
    · subst hne
      rw [hsH g hg hs a ha, hs]
      exact (congrFun (kv_plain_HD0 _ _ t H h0) a).symm
    · rw [hsO g hg s hne hs a ha, hs, segName_eq, kv_plain _ _ t H y hne]
  exact keyForm_keys_zero hρ H X hJ hz hp hu (fun g hg => ⟨(hN g hg).1, by
      obtain ⟨_, s, hs⟩ := hN g hg
      exact ⟨toFam s, hs.trans (segName_eq s)⟩⟩) Kf hH hNF h

/-- The same without a hypothesis on the two slots: the form is worth the extension plus two
brackets, slot less what the slot is meant to hold. -/
theorem keyForm_plain_brackets (hρ : Numerals ρ) {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ}
    {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (h0 : ∀ i, i < 1024 → y.rhoC i = 0)
    (X : LinesFit ρ W R HeadSizes.ref (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs,
      Found R q g ∧ ∃ s : Cm.Plain.Fam, g.name = segName s)
    (hsO : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ s : Cm.Plain.Fam, s ≠ .HD0 →
      g.name = segName s → ∀ a, a < g.n →
      f (g.pos.getD a 0) = Cm.Plain.TP.key (npOf R.h) t H y s a)
    (hsH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" → ∀ a, a < g.n →
      f (g.pos.getD a 0) = fun i => ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        Cm.Plain.TP.key (npOf R.h) t H y .HD0 a i)
    (hpad : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      ∀ j, j < (R.L.calls.getD q default).J → w.getD j 0 = 0 → f j = fun _ =>
        ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
          (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p +
        ((if q = R.x.qN then W.slot R.x.tN.sCl else 0) -
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "NF" then
              wsum (wOf ρ R q g) R.h.lt u g.n (fun a i =>
            Inst.Model.Head.xv t a i *
              Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
            else 0).sum) +
        ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "HD0" then
              (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl -
                wsum (wOf ρ R q g) R.h.lt u g.n (fun a i => ((y.rho i : ℤ) : K) *
            (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i a))
            else 0).sum := by
  have Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f := by
    intro w hw
    refine ⟨fun g hg a ha => ?_, fun j hj hj0 => hpad w hw j hj hj0⟩
    obtain ⟨_, s, hs⟩ := hN g hg
    by_cases hne : s = .HD0
    · subst hne
      rw [hsH g hg hs a ha, hs]
      exact (congrFun (kv_plain_HD0 _ _ t H h0) a).symm
    · rw [hsO g hg s hne hs a ha, hs, segName_eq, kv_plain _ _ t H y hne]
  exact keyForm_keys_brackets hρ H X hJ hz hp hu (fun g hg => ⟨(hN g hg).1, by
      obtain ⟨_, s, hs⟩ := hN g hg
      exact ⟨toFam s, hs.trans (segName_eq s)⟩⟩) Kf h

#print axioms segName_eq
#print axioms kv_keyOf
#print axioms callsFit_of
#print axioms keyForm_ref_zero
#print axioms keyForm_ref_brackets
#print axioms keyForm_plain_zero
#print axioms keyForm_plain_brackets

end OnBytes.Road.Hd
