-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TenOfPan.lean: the library's pair of a piece of a weight panel (tenAt,
Cb/Pv/Lay/At/TnSplit.lean) and the verifier's weight claim with the piece's number say the same of
every matrix W.

Both are worth, on W, the library's Pan.TnRow or Pan.TnPan: the pair by tenAt_row and
tenAt_pan, the claim by claim_of_panel (Johnson/Road/K4/ClaimsOfPan.lean). The number: the
verifier's number of a panel's first claim is v0Of D pn (placed_v0, Johnson/Road/K4/WalkV0.lean), so
the claim of piece pc has the number that numK D gives pc (Johnson/Road/K4/NumPieces.lean).

Main names:
  `sig_zeta`: SigFits at another letter for the batched sumcheck's point that reads the same
    challenges on the library's coordinates.
  `f2_right`: a member of the second list of a pairing has its partner.
  `ten_of_panel`: for one panel: the pair of piece i against claim number v0 + i.
  `ten_of_placed`: for every piece x: claim number (numK D).symm x of the verifier's list is there,
    and on every W it is worth what the pair of x is worth.
Limits. Premises: SigFits; the verifier's lists of panels and of claims have returned; the matrix
has room for all units (hH); each piece's layer is a layer of the model (hL). An identity on public
data and any matrix W: nothing on which matrix is committed, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.ClaimsOfPan
import Johnson.Road.K4.WalkV0
import Cb.Pv.Lay.At.TnSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World WsShape WsClaim)
open OnBytes.Model.Layer (SBlk Panels PanelEnv ClaimEnv panelsA panelsT placePanels)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Pan Rd pans lamS)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model.Layout (units off)
open Inst.Model.Layout.Tensor (matOf)

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv}
  {c : ClaimEnv} {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
  {lk L0 : ℕ} {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- SigFits at another letter for the batched sumcheck's point. -/
theorem sig_zeta (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) {ζ' : ℕ → K}
    (hζ : ∀ j, j < lamS D → ζ' j = ρ.val (c.rs.getD (lamS D - 1 - j) zeroE)) :
    SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ' tb :=
  { S with aim := { S.aim with claim := { S.aim.claim with zeta := hζ } } }

omit scl in
/-- A member of the second list of a pairing has its partner. -/
theorem f2_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ y ∈ l', ∃ x ∈ l, R x y
  | _, _, .nil, _, hy => absurd hy (List.not_mem_nil)
  | _, _, .cons (a := a) h1 t1, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨x, hx, hr⟩ := f2_right t1 y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- **One panel: the pair of piece i against claim number v0 + i.** -/
theorem ten_of_panel (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (r : Rd K) {hh : ℕ}
    (hH : off lk (units D.P) (units D.P).length ≤ hh) (W : Wm K) {TS : List ℕ}
    {cl : List WsClaim} {b : SBlk} {pn : Pan} (hI : IsPanelOf p c TS cl b pn)
    (hw : pn.weight = true) (hni : pn.three = false → b.ni = pn.nr D)
    (hL : ∀ i, i < cntB D pn → L0 + layerOfRow pn i < D.P.layers) :
    ∃ v0, b.v0 = some v0 ∧ ∀ i, i < cntB D pn → ∃ c0, cl[v0 + i]? = some c0 ∧
      tval (tenAt D tb L0 lk hh z zh ζ pn i) (matOf W) = claimVal ρ c.wsLay W c0 := by
  obtain ⟨v0, hv0, k⟩ := claim_of_panel S W r hI hw hni
  obtain ⟨q', cd, sg, F, -⟩ := S.qk
  have h64 : D.P.nq + D.P.nkv ≤ 64 := by
    rw [F.sized.nq, F.sized.nkv]
    exact F.heads
  refine ⟨v0, hv0, fun i hi => ?_⟩
  obtain ⟨c0, e0, e2, e3⟩ := k i hi
  refine ⟨c0, e0, ?_⟩
  cases h3 : pn.three with
  | false =>
    rw [e2 h3]
    exact tenAt_row D tb lk hh z zh ζ r S.aim.claim.even S.aim.f2 h64 pn hw h3 i (hL i hi) hH W
  | true =>
    have hi0 : i = 0 := by
      have e : cntB D pn = 1 := by
        unfold cntB
        rw [if_pos hw, if_pos h3]
      omega
    subst hi0
    rw [e3 h3]
    exact tenAt_pan D tb lk hh z zh ζ r S.aim.claim.even S.aim.f2 pn hw h3 (hL 0 hi) hH W

/-- **Every piece: its pair against the claim with its number.** -/
theorem ten_of_placed (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (r : Rd K) {hh : ℕ}
    (hH : off lk (units D.P) (units D.P).length ≤ hh) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl)
    (hL : ∀ x : Piece D, L0 + layerOfRow x.1.1 x.2 < D.P.layers) (x : Piece D) :
    ∃ c0, cl[((numK D).symm x).val]? = some c0 ∧ ∀ W : Wm K,
      tval (tenAt D tb L0 lk hh z zh ζ x.1.1 x.2) (matOf W) = claimVal ρ c.wsLay W c0 := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  have hne : p.v.y.LamM = D.ne := by
    rw [S.env]
    exact S.aim.claim.LamM
  have FE := placed_fields S hTS hp hc
  have FI := placed_are_pans p c S.env hp hc h3 hne S.lines hTS (D := D)
  have F0 := (placed_v0 hp FE).1
  obtain ⟨b', -, ⟨En, b, ⟨o, rfl⟩, hI⟩, hv⟩ := f2_right (f2_and (f2_and FE FI) F0) x.1.1 x.1.2
  have hw : x.1.1.weight = true := Cb.Pv.Lay.At.piece_weight x
  have hLp : ∀ i, i < cntB D x.1.1 → L0 + layerOfRow x.1.1 i < D.P.layers :=
    fun i hi => hL ⟨x.1, ⟨i, hi⟩⟩
  have key := fun W : Wm K => ten_of_panel S r hH W hI hw En.ni hLp
  obtain ⟨v0, hv0, k0⟩ := key 0
  have ev : v0 = v0Of D x.1.1 := Option.some.inj (hv0.symm.trans (hv hw))
  obtain ⟨c0, e0, -⟩ := k0 x.2 x.2.isLt
  refine ⟨c0, by rw [numK_val, ← ev]; exact e0, fun W => ?_⟩
  obtain ⟨v1, hv1, k1⟩ := key W
  obtain rfl : v0 = v1 := Option.some.inj (hv0.symm.trans hv1)
  obtain ⟨c1, e1, q⟩ := k1 x.2 x.2.isLt
  obtain rfl : c0 = c1 := Option.some.inj (e0.symm.trans e1)
  exact q

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sig_zeta
#print axioms OnBytes.Road.K4.ten_of_panel
#print axioms OnBytes.Road.K4.ten_of_placed
