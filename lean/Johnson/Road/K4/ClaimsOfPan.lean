-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ClaimsOfPan.lean: the verifier's weight claims of a panel, by their numbers in the
verifier's list, say of every matrix W what the library's panel says.

Other files have, kind by kind, that a member of the verifier's list of claims of a segment is
worth, on any matrix W, the library's Pan.TnRow or Pan.TnPan (list_G … list_Dr,
Johnson/Road/FormsKeysAim.lean; claims_QK, Johnson/Road/FormsKeysQKF.lean), and that a panel of the
verifier's list of panels comes with its claims' places in the one list cl of all weight claims
(IsPanelOf, Johnson/Road/FormsKeysPans.lean). Here the two are joined, for the ten kinds of weight
panels at once.

  `claim_of_panel`: if b is the verifier's panel of the library's weight panel pn, then b has a
    first number v0, and for each piece i of pn on the second side (i below cntB D pn) member
    v0 + i of cl is there and is worth, on every W, pn's TnRow at row i (two factors) or pn's TnPan
    (three factors).
Limits. Premises: SigFits (Johnson/Road/FormsKeysPortSig.lean), IsPanelOf, and that a panel with two
factors has as many rows as the library's. An identity on public data and any matrix W: nothing on
which matrix is committed, on a draw, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysPortSig
import Johnson.Road.FormsKeysQKF
import Cb.Pv.Lay.At.InnerGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World WsShape WsClaim)
open OnBytes.Model.Layer (SBlk PanelEnv ClaimEnv)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Pan Rd layerR)
open Cb.Pv.Lay.At (cntB)

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv}
  {c : ClaimEnv} {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
  {lk L0 : ℕ} {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- **The claims of a weight panel, by their numbers.** -/
theorem claim_of_panel (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (W : Wm K)
    (r : Rd K) {TS : List ℕ} {cl : List WsClaim} {b : SBlk} {pn : Pan}
    (hI : IsPanelOf p c TS cl b pn) (hw : pn.weight = true)
    (hni : pn.three = false → b.ni = pn.nr D) :
    ∃ v0, b.v0 = some v0 ∧ ∀ i, i < cntB D pn → ∃ c0, cl[v0 + i]? = some c0 ∧
      (pn.three = false → claimVal ρ c.wsLay W c0 =
        pn.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i) ∧
      (pn.three = true → claimVal ρ c.wsLay W c0 =
        pn.TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ) := by
  cases pn with
  | G =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_G S.aim W r tb zh (S.tie .G (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | U =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_U S.aim W r tb zh (S.tie .U (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | O =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_O S.aim W r tb zh (S.tie .O (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | D =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_D S.aim W r tb zh (S.tie .D (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | V =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_V S.aim W r tb zh (S.tie .V (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | LR =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨st, l, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => list_LR S.aim W r tb zh (S.tie .LR (by decide)) hl
        (List.getElem?_eq_getElem hil), fun h3 => absurd h3 (by simp [Pan.three])⟩
  | Gr lm =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨s1, s2, l, -, -, hlm, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    have hil : lm < l.length := by
      rw [hlen]
      exact hlm
    subst hi0
    exact ⟨l[lm], by rw [Nat.add_zero, hat, List.getElem?_eq_getElem hil],
      fun h3 => absurd h3 (by simp [Pan.three]),
      fun _ => list_Gr S.aim W r tb zh (S.tie .G (by decide)) hl
        (List.getElem?_eq_getElem hil)⟩
  | Ur lm =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨s1, s2, l, -, -, hlm, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    have hil : lm < l.length := by
      rw [hlen]
      exact hlm
    subst hi0
    exact ⟨l[lm], by rw [Nat.add_zero, hat, List.getElem?_eq_getElem hil],
      fun h3 => absurd h3 (by simp [Pan.three]),
      fun _ => list_Ur S.aim W r tb zh (S.tie .U (by decide)) hl
        (List.getElem?_eq_getElem hil)⟩
  | Dr lm =>
    obtain ⟨v0, hv0, -, q, -, g, -, hn, H⟩ := hI
    obtain ⟨s1, s2, l, -, -, hlm, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    have hil : lm < l.length := by
      rw [hlen]
      exact hlm
    subst hi0
    exact ⟨l[lm], by rw [Nat.add_zero, hat, List.getElem?_eq_getElem hil],
      fun h3 => absurd h3 (by simp [Pan.three]),
      fun _ => list_Dr S.aim W r tb zh (S.tie .D (by decide)) hl
        (List.getElem?_eq_getElem hil)⟩
  | QK =>
    obtain ⟨v0, hv0, -, q, -, g, -, H⟩ := hI
    obtain ⟨s1, s2, l, hn, -, -, -, hl, hlen, hat⟩ := id H
    rw [hn] at hl
    obtain ⟨q', cd, sg, F, hz⟩ := S.qk
    refine ⟨v0, hv0, fun i hi => ?_⟩
    have hi' : i < b.ni := by
      rw [hni rfl]
      exact hi
    have hil : i < l.length := by
      rw [hlen]
      exact hi'
    exact ⟨l[i], by rw [hat i hi', List.getElem?_eq_getElem hil],
      fun _ => (claims_QK ρ S.aim.claim F S.rt S.rope hz S.zh r W hl).2 i hil,
      fun h3 => absurd h3 (by simp [Pan.three])⟩
  | N1 => exact absurd hw (by simp [Pan.weight])
  | N2 => exact absurd hw (by simp [Pan.weight])
  | XR => exact absurd hw (by simp [Pan.weight])
  | DD => exact absurd hw (by simp [Pan.weight])
  | MR => exact absurd hw (by simp [Pan.weight])

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.claim_of_panel
