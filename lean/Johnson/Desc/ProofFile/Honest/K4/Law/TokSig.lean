-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokSig.lean: CONDITIONAL.

What is here. At one token, the sum of products of the second token sumcheck's honest job (`tokSum`,
TermsTotal.lean) is the sum of the library's shares of the verifier's panels of the second pass,
laid at that token's corner and at the true values of what the sumcheck will show; and that is the
library's `Sig1` (Inst/Model/FF/Objects.lean).

  `tokSum_trips`   a token's sum of products is the sum over that token's own products
  `trips_share`   the products of all panels, in the library's shares
  `sum_claim1`, `panels_open`, `share_sig1`   two pairs of weights pick the second pass's panels:
     their shares make up Sig1
  `tok_sig`   **one token**

Limits. THE FULL SIZE ALONE for the second statement: it calls the library's `port_sig`
(Johnson/Road/FormsKeysPortSig.lean), whose structure `SigFits` cannot be met at the small public
example by that file's head. Both statements: at the reading `Reading.gl`; for a token's number
below the number of tokens. HYPOTHESES: the ties of TripShare.lean at every panel of the second
pass; for the second statement `SigFits` at the honest side's environment of the panels at that
token, the calls of the second walk are 0, 1, 2, 5, the verifier's list of claims returns, the
verifier's end function returns on the panels. The library's sum stands at its structure `rPort`: it
is not the library's true structure. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTotal
import Johnson.Desc.ProofFile.Honest.K4.Law.TripShare
import Johnson.Desc.ProofFile.Honest.K4.Law.PassSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading Aff World WsShape WsClaim eqTab)
open OnBytes.Model.Layer (SBlk ClaimEnv StackEnd stackEnd Panels panelsA panelsT placePanels)
open OnBytes.Road (shareP omK wvOf SigFits port_sig rPort Cells Wm)
open OnBytes.Road.K4.C (sidesEnv firstOf)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Sig0 Sig1 layerR)
open OnBytes.Desc.First.K4.Honest

/-- **A token's sum of products is the sum over that token's own products**, where the token's row
has the first token's weights and as many products. -/
theorem tokSum_trips (rows : TokRows) {t : ℕ} {sh : Array E} {tr : Array Trip}
    (ht : rows[t]? = some (sh, tr)) (hw : tr.map (·.1) = (firstOf rows).map (·.1)) :
    tokSum rows t = tripSum tr.toList := by
  have hsz : tr.size = (firstOf rows).size := by
    have := congrArg Array.size hw
    simpa using this
  have hrow : rows.getD t (#[], #[]) = (sh, tr) := by
    rw [Array.getD_eq_getD_getElem?, ht]
    rfl
  unfold tokSum tripSum
  rw [sum_by_number trip0, Array.length_toList, hsz]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e1 : tr.toList.getD k trip0 = tr.getD k trip0 := by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have ew : wAt rows k = (tr.getD k trip0).1 := by
    have a1 : ((firstOf rows).map (·.1)).getD k zeroE = ((firstOf rows).getD k trip0).1 := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem hk']
      rfl
    have a2 : (tr.map (·.1)).getD k zeroE = (tr.getD k trip0).1 := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem (by rw [hsz]; exact hk')]
      rfl
    show ((firstOf rows).getD k trip0).1 = _
    rw [← a1, ← hw, a2]
  rw [e1, ew]
  unfold aAt bAt
  rw [hrow]

/-- **The products of all panels of the second pass, in the library's shares.** CONDITIONAL: on the
ties at each of these panels. -/
theorem trips_share {S : OnBytes.Desc.First.K4.Honest.Sides} {R : Reads} {et : Array E}
    {hh : ℕ → ℕ → E} {sh : Array E} {tr : Array Trip} (h : S.trips R et hh sh = some tr)
    {Wo : World Cb.Gl.E} {hv wv : ℕ → ℕ → Cb.Gl.E} :
    ∃ bl places, S.panels sh = some (bl, places) ∧
      ((∀ b ∈ bl.toList, b.claim = 1 → TripTies S (fun a => valAff? S.v R (fun _ => zeroE) a)
        (S.weights et) hh Wo hv wv b) →
      tripSum tr.toList = ((bl.toList.filter fun b => b.claim == 1).map fun b =>
        shareP Reading.gl Wo S.v.y hv wv b).sum) := by
  unfold OnBytes.Desc.First.K4.Honest.Sides.trips at h
  obtain ⟨⟨bl, places⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  refine ⟨bl, places, hp, fun T => ?_⟩
  rw [Array.mapM_eq_mapM_toList] at hl
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hl
  rw [Array.toList_filter] at hL
  have key := sum_of_mapM (tripsOf S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights et) hh)
    (fun b => shareP Reading.gl Wo S.v.y hv wv b) 1 _ L hL (fun b hb tr' ht' => by
      rw [one_mul]
      have hb' := List.mem_filter.mp hb
      exact (trip_share (T b hb'.1 (by simpa using hb'.2)) ht').symm)
  rw [one_mul] at key
  rw [key, Array.toList_flatMap]
  rfl

/-- The weights 1, 1 count the panels of both passes. -/
theorem sum_claim1 (f : SBlk → Cb.Gl.E) (l : List SBlk) :
    (l.map fun b => omK Reading.gl #[oneE, oneE] b * f b).sum =
      ((l.filter fun b => b.claim == 0).map f).sum +
        ((l.filter fun b => b.claim == 1).map f).sum := by
  rw [sum_filter, sum_filter, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  unfold omK
  rcases hc : b.claim with _ | _ | n
  · show Reading.gl.val oneE * _ = _
    rw [Reading.gl.one, one_mul, if_pos (by decide), if_neg (by decide), add_zero]
  · show Reading.gl.val oneE * _ = _
    rw [Reading.gl.one, one_mul, if_neg (by decide), if_pos (by decide), zero_add]
  · show Reading.gl.val zeroE * _ = _
    rw [Reading.gl.zero, zero_mul, if_neg (by simp), if_neg (by simp), add_zero]

/-- The verifier's panels as the honest side lays them, opened. -/
theorem panels_open {S : OnBytes.Desc.First.K4.Honest.Sides} {sh : Array E} {bl : Array SBlk}
    {places : ℕ} (h : S.panels sh = some (bl, places)) :
    ∃ pans : Panels, panelsT (sidesEnv S sh) S.TS (panelsA (sidesEnv S sh) {}) = some pans ∧
      bl = (placePanels pans.bl).1 := by
  unfold OnBytes.Desc.First.K4.Honest.Sides.panels at h
  obtain ⟨pans, hp, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨pans, hp, ?_⟩
  split at h
  · cases h
  · exact (congrArg Prod.fst (Option.some.inj h)).symm

variable [scl : Scl]

/-- **The shares of the second pass's panels make up the library's Sig1.** THE FULL SIZE ALONE
(SF). -/
theorem share_sig1 {S : OnBytes.Desc.First.K4.Honest.Sides} {sh : Array E} {bl : Array SBlk}
    {places : ℕ} (hp : S.panels sh = some (bl, places)) {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low z zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv S sh) c h' pc s D lk L0 cc t low z zh ζ tb)
    (M : Wm Cb.Gl.E) (hv : ℕ → ℕ → Cb.Gl.E) (hTS : S.TS = [0, 1, 2, 5]) {cl : List WsClaim}
    (hc : c.weightClaims S.TS = some cl) {rs om H1 V : Array E} {lam : ℕ} {sA sB : E}
    {s' : StackEnd} (hst : stackEnd S.v.y bl rs lam om H1 V sA sB = some s') :
    ((bl.toList.filter fun b => b.claim == 1).map fun b =>
        shareP Reading.gl Wo S.v.y hv (wvOf Reading.gl c.wsLay M cl) b).sum =
      Sig1 D (rPort Reading.gl S.v.y sh hv D t z zh) tb L0 (fun l => layerR D.P lk M (L0 + l)) z
        zh := by
  obtain ⟨pans, hpp, hbl⟩ := panels_open hp
  obtain ⟨s0, hst0⟩ := stackEnd_any #[oneE, zeroE] hst
  obtain ⟨s1, hst1⟩ := stackEnd_any #[oneE, oneE] hst
  have e0 := port_sig SF M hv hTS hpp hc (om := #[oneE, zeroE])
    (show Reading.gl.val oneE = 1 from Reading.gl.one) (by rw [← hbl]; exact hst0)
  have e1 := port_sig SF M hv hTS hpp hc (om := #[oneE, oneE])
    (show Reading.gl.val oneE = 1 from Reading.gl.one) (by rw [← hbl]; exact hst1)
  rw [← hbl, sum_claim] at e0
  rw [← hbl, sum_claim1] at e1
  have z0 : Reading.gl.val ((#[oneE, zeroE] : Array E).getD 1 zeroE) = 0 := Reading.gl.zero
  have z1 : Reading.gl.val ((#[oneE, oneE] : Array E).getD 1 zeroE) = 1 := Reading.gl.one
  rw [z0, zero_mul, add_zero] at e0
  rw [z1, one_mul, e0] at e1
  exact add_left_cancel e1

/-- **ONE TOKEN: ITS SUM OF PRODUCTS IS THE LIBRARY's Sig1** at the values sh, which are the true
values at that token of what the sumcheck will show. CONDITIONAL: on every hypothesis named. THE
FULL SIZE ALONE (SF). -/
theorem tok_sig {S : OnBytes.Desc.First.K4.Honest.Sides} {rows : TokRows}
    (hrows : tokenRows S = some rows)
    (hsame : (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) = true) {i : ℕ}
    (hi : i < S.v.y.T) {R : Reads} {sh : Array E}
    (hR : S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R)
    (hsh : endsOn S R = some sh)
    {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low z zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv S sh) c h' pc s D lk L0 cc t low z zh ζ tb)
    (M : Wm Cb.Gl.E) (hv : ℕ → ℕ → Cb.Gl.E) (hTS : S.TS = [0, 1, 2, 5]) {cl : List WsClaim}
    (hc : c.weightClaims S.TS = some cl)
    (hst : ∀ bl places, S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd S.v.y bl rs lam om H1 V sA sB = some s')
    (T : ∀ bl places, S.panels sh = some (bl, places) → ∀ b ∈ bl.toList, b.claim = 1 →
      TripTies S (fun a => valAff? S.v R (fun _ => zeroE) a)
        (S.weights (eqTab (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i)))
        (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + i) zeroE) Wo hv
        (wvOf Reading.gl c.wsLay M cl) b) :
    tokSum rows i = Sig1 D (rPort Reading.gl S.v.y sh hv D t z zh) tb L0
      (fun l => layerR D.P lk M (L0 + l)) z zh := by
  obtain ⟨R', sh', tr, hR', hsh', htr, hrow⟩ := OnBytes.Road.K4.C.tokenRows_trips hrows hi
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  obtain rfl : sh' = sh := Option.some.inj (hsh'.symm.trans hsh)
  have hw : tr.map (·.1) = (firstOf rows).map (·.1) := by
    have hm : (sh', tr) ∈ rows := Array.mem_of_getElem? hrow
    have := (Array.all_eq_true'.mp hsame) (sh', tr) hm
    simpa using this
  obtain ⟨bl, places, hp, key⟩ := trips_share htr (Wo := Wo) (hv := hv)
    (wv := wvOf Reading.gl c.wsLay M cl)
  obtain ⟨rs, om, H1, V, lam, sA, sB, s', hst'⟩ := hst bl places hp
  rw [tokSum_trips rows hrow hw, key (T bl places hp)]
  exact share_sig1 hp SF M hv hTS hc hst'

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokSum_trips
#print axioms ProofFile.Honest.K4.trips_share
#print axioms ProofFile.Honest.K4.sum_claim1
#print axioms ProofFile.Honest.K4.panels_open
#print axioms ProofFile.Honest.K4.share_sig1
#print axioms ProofFile.Honest.K4.tok_sig
