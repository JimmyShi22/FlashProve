-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TripTiesOf.lean: CONDITIONAL.

What is here. The ties of TripShare.lean (`TripTies`: the honest side's letters against the
library's, at one panel of the batched sumcheck's second pass, at a token point) at three chosen
letters: in `tripTies_of` from public hypotheses and hup, in `tripTies_at` from public hypotheses
and hval. The world is any in which the honest value, on the reads R at the token point, of each of
the panel's own forms is the form's value. One such is the world of honest reads R' (`readsWorld`,
Johnson/Road/K4/C/StackTrue.lean: 0 under every slot) that hold more tables than R, where a form's
value on R is its value on R' (hup). So the world can be one in which the tables at the lookup's
point are true too, as the library's `SigFits` asks. Every world with the true entries is another
such world: HvalOf.lean's `hval_true`. The routed experts' never-sent vectors are read off the
honest function hh (`hvOfH`). The weight claims' vectors are the library's, at the matrix of the
honest input's words and at the claims made at that point. So the three clauses on forms hold by
hval (in `tripTies_of` by that file's `reads_val`), the one on the never-sent vectors by the choice,
the two on the weight claims' vectors by OpenSides.lean's `weights_are` and `weights_kk`.

  `hvOfH`   the never-sent vectors, read off the honest function
  `UnitsAt`, `TripPub`   the two public hypotheses on one panel
  `tripTies_at`   **the ties**, in any world in which the honest values of the panel's own forms are
     the forms' values
  `tripTies_of`   the same in the world of honest reads to which the values lift

Limits. At the reading `Reading.gl`. PUBLIC HYPOTHESES, SHOWN IN OTHER FILES (UnitsAtOf.lean's
`unitsAt_of`; PanelPubOf.lean's `tripPub_of`): `UnitsAt`: the units of the panel's weight claims:
found; with the group "e" just where the panel has the selector; the bits of a column; the extent of
"kk" at most the panel's number of columns; `TripPub`: a panel with the selector has a row for each
routed expert; the columns fit the bits. Beside them: the function that makes the shared data
returns; the verifier's function for the claims returns at the honest side's environment with
challenges and the point laid in; the layout of the weights is what the verifier's `wsLayOf` returns
for a model with routed experts. That the vectors `hvOfH` are the library's vectors of the routed
gated products is not said here: GatedOf.lean's `hhAt_gated` says it at a token's corner. No example
of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TripShare
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenSides
import Johnson.Road.K4.C.StackTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading World WsLay WsClaim WsShape wsLayOf eqTab)
open OnBytes.Model.Layer (SBlk ClaimEnv)
open OnBytes.Road (wvOf hasE wkOf)
open OnBytes.Road.K4.C (readsWorld reads_val)
open OnBytes.Desc.First.K4.Honest

/-- **The never-sent vectors, read off the honest function**: number k at a column. -/
noncomputable def hvOfH (hh : ℕ → ℕ → E) (k X : ℕ) : Cb.Gl.E := Reading.gl.val (hh (k - 1) X)

/-- **The units of one panel's weight claims.** This defines a hypothesis; the definition claims
nothing. -/
def UnitsAt (lay : WsLay) (cl : List WsClaim) (b : SBlk) : Prop :=
  ∀ v0, b.v0 = some v0 →
    (b.tri = true → ∃ x u, cl[v0]? = some x ∧ lay.U[x.ui]? = some u ∧ hasE u.g = true ∧
      wkOf u.g = b.wy ∧ ((u.g.find? fun g => g.name == "kk").map (·.R)).getD 0 ≤ b.ny) ∧
    (b.tri = false → ∀ i, i < b.ni → ∃ x u, cl[v0 + i]? = some x ∧ lay.U[x.ui]? = some u ∧
      hasE u.g = false ∧ ((u.g.find? fun g => g.name == "kk").map (·.R)).getD 0 ≤ b.ny)

/-- **Two public numbers of one panel.** This defines a hypothesis; the definition claims nothing.
-/
structure TripPub (S : OnBytes.Desc.First.K4.Honest.Sides) (b : SBlk) : Prop where
  /-- a panel with the selector has a row for each routed expert -/
  rows : b.tri = true → b.ni = S.v.y.h.NE
  /-- the columns fit the bits -/
  cols : b.ny ≤ 2 ^ b.wy

/-- **THE TIES AT A TOKEN POINT, IN ANY WORLD IN WHICH THE HONEST VALUE OF EACH OF THE PANEL's OWN
FORMS IS THE FORM's VALUE** (hval). CONDITIONAL: on every hypothesis named. -/
theorem tripTies_at {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rs rt : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (R : Reads)
    (Wo : World Cb.Gl.E) (hh : ℕ → ℕ → E) {b : SBlk}
    (hval : ∀ a, FormOf b a → ∀ y, valAff? S.v R (fun _ => zeroE) a = some y →
      Reading.gl.val y = a.value Reading.gl Wo)
    (U : UnitsAt Q.P.wsLay cl b) (B : TripPub S b) :
    TripTies S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights (eqTab rt)) hh
      Wo (hvOfH hh) (wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl) b where
  valX := fun yv y h1 hy => hval _ (Or.inl ⟨yv, h1, rfl⟩) y hy
  valA := fun A i yv f y h1 h2 hy => hval f (Or.inr (Or.inl ⟨A, i, yv, h1, h2⟩)) y hy
  valB := fun B i yv f y h1 h2 hy => hval f (Or.inr (Or.inr ⟨B, i, yv, h1, h2⟩)) y hy
  rows := B.rows
  cols := B.cols
  hvT := fun _ _ _ _ _ => rfl
  wvT := fun ht v0 h0 i yv _ hy => by
    obtain ⟨x, u, hx, hu, hE, hwk, hkk⟩ := (U v0 h0).1 ht
    have r := weights_are hS hcl hl v0 x u hx hu i yv (Or.inl ⟨hE, by rw [hwk]; exact hy⟩)
    rw [hwk] at r
    rw [← r]
    by_cases cy : yv < b.ny
    · rw [if_pos cy]
    · rw [if_neg cy]
      unfold at2
      rw [if_neg (by
        rw [weights_kk hS hcl v0 x u hx hu]
        exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
      exact Reading.gl.zero
  wvP := fun ht v0 h0 i yv hi _ => by
    obtain ⟨x, u, hx, hu, hE, hkk⟩ := (U v0 h0).2 ht i hi
    have r := weights_are hS hcl hl (v0 + i) x u hx hu 0 yv (Or.inr ⟨hE, rfl⟩)
    rw [Nat.zero_mul, Nat.zero_add] at r
    rw [← r]
    by_cases cy : yv < b.ny
    · rw [if_pos cy]
    · rw [if_neg cy]
      unfold at2
      rw [if_neg (by
        rw [weights_kk hS hcl (v0 + i) x u hx hu]
        exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
      exact Reading.gl.zero

/-- **The same in the world of honest reads R'** to which the values on R lift (hup). -/
theorem tripTies_of {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rs rt : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (R R' : Reads)
    (hup : ∀ a y, valAff? S.v R (fun _ => zeroE) a = some y →
      valAff? S.v R' (fun _ => zeroE) a = some y)
    (hh : ℕ → ℕ → E) {b : SBlk} (U : UnitsAt Q.P.wsLay cl b) (B : TripPub S b) :
    TripTies S (fun a => valAff? S.v R (fun _ => zeroE) a) (S.weights (eqTab rt)) hh
      (readsWorld S.v R') (hvOfH hh) (wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl) b :=
  tripTies_at hS hcl hl R _ hh (fun a _ y hy => reads_val S.v R' a y (hup a y hy)) U B

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tripTies_at
#print axioms ProofFile.Honest.K4.tripTies_of
