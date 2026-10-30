-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoKfDig.lean.
The key forms of the lookup on the digits of a sub-proof's smallness test.

A caller of a sub-proof's lookup hands the join one affine form for each call: "this call's key
vector at this call's point". What is asked of these forms is Fo.KFok
(OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean). In the lookup
on the digits a key is one committed entry, a low or a high digit, or 0. So the form that lists the
digits' entries under their equality weights meets KFok, under every reading of the entries: here as
a theorem, at the byte-level verifier's own record of a smallness test, at the points of the record
of end values.

Defines:
  someK: a form on the caller's entries, as a form on the lookup's entries.
  digKF: the digits' key forms at given points.
States:
  extL_ofList: the extension at a list, the top bit's coordinate first, is the library's.
  val_someK: the value of someK.
  dig_KFok: the digits' key forms meet KFok, at all points of the right lengths.
  ends_zk_len: each call's point in the record of end values has as many coordinates as the call's
    key numbers have bits.
  dig_KFok_ends: the digits' key forms meet KFok at the points of the record of end values.
Premises: TailOK tl (a test on the record's public numbers gives it); FoNums.ok tl.f9 = true.
By: dgP_KFokJ (OnBytes/Tie/Pv/Lookup/Digits/PortJ.lean).
Does not say: that the claim which the smallness test's routine linJoin9 (OnBytes/Model/Tail.lean)
writes by hand is the join's form at digKF.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut
import OnBytes.Tie.Pv.Lookup.Digits.PortKnow

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.DgP Cb Cb.LdLkp Cb.Fo

section
variable {E : Type} [Field E]

/-- The extension at a list is the library's extension at the list read as a point. -/
theorem extL_ofList (f : ℕ → E) (z : List E) :
    extL f z = Blocks.ext z.length f (Blocks.ofList z) := by
  have e := ext_top f z.length (Blocks.ofList z)
  rw [show (List.range z.length).map (Blocks.ofList z) = z from rho_ptL z] at e
  exact e

variable {J₀ : Type}

/-- A form on the caller's entries, as a form on the lookup's entries. -/
def someK (f : AffK J₀ E) : AffK (Option J₀) E := (f.1.map fun x => (some x.1, x.2), f.2)

theorem val_someK (f : AffK J₀ E) (μ : Option J₀ → E) :
    AffK.val (someK f) μ = AffK.val f fun j => μ (some j) := by
  unfold AffK.val someK
  rw [List.map_map]
  rfl

/-- The digits' key forms, at the points zk. -/
def digKF (tl : HTailF2) (en : Ent3 → J₀) (zk : ℕ → List E) (q : ℕ) : AffK (Option J₀) E :=
  someK (KFlJ tl en q (zk q))

/-- **The digits' key forms read the calls' key vectors at the calls' points.** -/
theorem dig_KFok {tl : HTailF2} (hT : TailOK tl) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ)
    {St₀ : Type} (st : St₀) (zk : ℕ → List E)
    (hz : ∀ q < tl.f9.NC, (zk q).length = Port.nOf tl.f9 q) :
    KFok tl.f9 (forK E (digL E tl en mk jLK St₀) st) zk (digKF tl en zk) := by
  intro μ q hq
  unfold digKF
  rw [val_someK, extL_ofList]
  exact dgP_KFokJ en hT (fun j => μ (some j)) (hT.nc ▸ hq) (zk q) (hz q hq)

/-- Each call's point in the record has as many coordinates as the call's key numbers have bits. -/
theorem ends_zk_len (h : FoNums.Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : Rounds E) (c : ℕ)
    (hc : c < h.NC) : ((endsOf h lm jLK rs).zk.getD c []).length = nOf h c := by
  have hio : io h c ≤ h.rK := (ok_prem H).le c hc
  have hn : nOf h c = io h c + h.dT := ((ok_parts H).2.2.1 c hc).2.2.1
  rw [ends_zk h H lm jLK rs c hc, hn]
  unfold zk
  rw [List.length_append, List.length_drop, ends_zx_len h H, ends_zy_len h H]
  omega

/-- At the points of the record of end values. -/
theorem dig_KFok_ends {tl : HTailF2} (hT : TailOK tl) (H : FoNums.ok tl.f9 = true)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) {St₀ : Type} (st : St₀) (lm j0 : ℕ) (rs : Rounds E) :
    KFok tl.f9 (forK E (digL E tl en mk jLK St₀) st)
      (fun c => (endsOf tl.f9 lm j0 rs).zk.getD c [])
      (digKF tl en fun c => (endsOf tl.f9 lm j0 rs).zk.getD c []) :=
  dig_KFok hT en mk jLK st _ fun q hq => ends_zk_len tl.f9 H lm j0 rs q hq

end
end Fo
