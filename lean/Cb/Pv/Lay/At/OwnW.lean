-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/OwnW.lean: the own rounds of a layers' sub-proof that is not the first, at a value,
with the weights' stretch filled: no stage's record is left as a letter with a law. The readings
rd and rw keep theirs (hrd, hrw).

Main names:
  `piece_layer`: the layer of a weight claim is a layer of the group.
  `FullPar`: over the letters of Cb/Pv/Lay/At/Own.lean: the committed matrix's column bits kW and
    rows hW; how the entries are read as the matrix (Wn); that the group's weights are the library's
    reading of that matrix (hrw : rw m l = layerR D.P kW (Wn m) (L0 + l)); a numbering of the weight
    claims (num); the merge's masks; five conditions on sizes: the group's first layer is even; a
    layer has twice the hidden units of an expert; at most 64 heads; the group's layers are layers
    of the model; the matrix has room for all units.
  `hL`: the weight claims' layers are layers of the model. `wp0`: the letters of FootW.lean.
  `wPart`: the weights' stretch of Cb/Pv/Lay/At/FootW.lean at the pairs of TnSplit.lean, with seam_w
    (SeamW.lean) as its law.
  `own`: the record LayVO. `own_pT`: what is claimed before the first round.
  `own_knowAt`: knowledge soundness of the chain at the value: from "Dn, all 17 identities of every
    norm at every position, and the lookup's join at the true sum of the terms" to the chain's last
    claim. What that join says in the library's key vectors: OnBytes.Road.own_join, in a later file.

Limits: those of Cb/Pv/Lay/At/Own.lean. The theorem's premises are the fields of the letters'
records; that they can be met together is shown at trivial readings alone (TestOwn.lean). The tuple
of messages must hold, beside the cells and the sub-proof's mask row, the committed matrix and the
message in which the mask of the merge's shown value lies (c7): all fixed before the first draw.


-/
import Cb.Pv.Lay.At.Own
import Cb.Pv.Lay.At.SeamW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.FFSeg (Dim Cell LW Pan pans layerR dJ)

noncomputable section

/-- The layer of a weight claim is a layer of the group. -/
theorem piece_layer (D : Dim) (i : Piece D) : layerOfRow i.1.1 i.2 < D.nl := by
  obtain ⟨⟨p, hp⟩, ρ⟩ := i
  have hρ : (ρ : ℕ) < cntB D p := ρ.isLt
  have hne : 2 * D.ne ≤ D.nl := by
    unfold Dim.ne
    omega
  cases p with
  | LR =>
    have h : (ρ : ℕ) < D.ne := hρ
    show 2 * (ρ : ℕ) + 1 < D.nl
    omega
  | Gr l =>
    have hl : l < D.ne := by simpa [pans] using hp
    show 2 * l + 1 < D.nl
    omega
  | Ur l =>
    have hl : l < D.ne := by simpa [pans] using hp
    show 2 * l + 1 < D.nl
    omega
  | Dr l =>
    have hl : l < D.ne := by simpa [pans] using hp
    show 2 * l + 1 < D.nl
    omega
  | G => exact hρ
  | U => exact hρ
  | O => exact hρ
  | D => exact hρ
  | V => exact hρ
  | QK => exact hρ
  | N1 => exact absurd hρ (Nat.not_lt_zero _)
  | N2 => exact absurd hρ (Nat.not_lt_zero _)
  | XR => exact absurd hρ (Nat.not_lt_zero _)
  | DD => exact absurd hρ (Nat.not_lt_zero _)
  | MR => exact absurd hρ (Nat.not_lt_zero _)

/-- The letters of the weights' stretch that stay free, beside At/Own.lean's. -/
structure FullPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends OwnPar E M X where
  /-- the committed matrix: its column bits, its rows, how the entries are read as it -/
  kW : ℕ
  hW : ℕ
  Wn : (J → E) → ℕ → ℕ → E
  /-- the group's weights are the library's reading of the matrix -/
  hrw : ∀ m, rw m = fun l => layerR D.P kW (Wn m) (L0 + l)
  /-- a numbering of the weight claims -/
  nW : ℕ
  num : Fin nW ≃ Piece D
  /-- the merge's masks -/
  w7 : PIdx (ldPartFmt E kW (fun _ => 2) ++ [pDummy E 1]) → J
  c7 : J
  /-- conditions on the sizes -/
  h0 : L0 % 2 = 0
  hf : D.f = 2 * D.fe
  hh : D.P.nq + D.P.nkv ≤ 64
  hLay : L0 + D.nl ≤ D.P.layers
  hH : off kW (units D.P) (units D.P).length ≤ hW

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace FullPar
variable (P : FullPar E M X)

/-- The weight claims' layers are layers of the model. -/
theorem hL (i : Piece P.D) : P.L0 + layerOfRow i.1.1 i.2 < P.D.P.layers := by
  have h1 := piece_layer P.D i
  have h2 := P.hLay
  omega

/-- The letters of At/FootW.lean. -/
abbrev wp0 : FootW0 E := P.ip.wPar P.kW P.hW P.nW P.Wn P.num P.w7 P.c7

/-- The weights' stretch, with its law. -/
def wPart : P.WPart where
  Wt := P.wp0.wt
  st7 := P.ip.st7 P.num
  rd7 := P.msg
  law := fun o m hc => P.ip.seam_w P.kW P.hW P.nW P.Wn P.num P.w7 P.c7 o (P.msg m) (P.hrw _) P.h0
    P.hf P.hh P.hL P.hH hc

/-- The own rounds of a sub-proof that is not the first, at the value. -/
def own : LayVO E M X := P.layVO P.wPart

/-- What is claimed before the first round. -/
theorem own_pT (x : X) (m : M) :
    P.own.pT x m ↔
      (∀ k : ℕ × Fin P.D.nNu, ∀ Y < 2 ^ P.D.lT, dJ P.D (P.rd (P.msg m)) k.1 k.2 Y = 0) ∧
        P.jg x (P.tS x m) m = 0 := Iff.rfl

/-- **Knowledge soundness of the own rounds at the value: no premise but the letters' fields.** -/
theorem own_knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (P.own.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ P.own.pT x m)
      (jt A0 (fun e => pr (P.own.toOwn.ch.back e)) (P.own.toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) (P.own.toOwn.ch.eps Ex) :=
  P.own.knowAt Ex A0 pr Dn

end FullPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.FullPar.own_knowAt
