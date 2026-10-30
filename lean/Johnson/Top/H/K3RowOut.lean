-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RowOut.lean: the kind "lookup" (K3): THE ROW OUT: what stands behind a lookup's
block in the table of joints, GENERAL IN THE PLACE, cut into three items by sort; and the theorem
that at a written transcript's own rounds it is the proved block's out-claim. Definitions,
statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. A relation behind a block reads the record behind, the oracles and the witness: it cannot name
the transcript. The library's list of claims (claimsOf,
OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean:79) is made of the transcript's rounds. What the record
behind holds is what was heard, g, and the ledger F'. So the row out says its clause OF ALL ROUNDS
rs FOR WHICH THE HEARD RECORD STANDS (HeardIs ρ g F' at the end values of rs).

Main names. h, lm, first: the shape, the planes' packing, the lookup's first slot. ν: the reading of
the places (a mask, a cell of the planes' matrix). Kv c i: key number i of call c.
  K3Rows h lm first ν rs: THE FORMS THAT THE HEARING LEFT: every residue of the sumchecks' rows is 0
    (rows.map (rowRes ν)).
  K3Planes h lm first ν rs: PLANES-AT-POINTS: claimLeaves at the columns' own combinations of cells
    at the leaves' point, claimBits at the bits' point, countK at the counts' combinations: each 0.
  K3Keys h lm first ν Kv rs: KEYS-AT-POINTS: claimJoin at the extension of each call's key vector at
    that call's point is 0.
  k3_claims_iff: the three together are «every member of claimsOf is 0».
  K3OutRows, K3OutPlanes, K3OutKeys ρ g F' …: each item at all rs under HeardIs. K3Out: the three.
  k3Out_iff: K3Out is «for all rs under HeardIs, every member of claimsOf is 0».
  K3Stands ρ g F' h lm first: some rs has HeardIs: for the condition behind.
  out_iff_items: AT ANY CALLER r of the proved block whose layout meets (L1)'s two equations, at
    written rounds that meet the spec and hold no answers, at every statement and transcript: the
    block puts out x, and for all entries μ₀: x's out-claim holds of μ₀ IF AND ONLY IF the three
    items hold at the transcript's rounds, ν := μ₀ at the places, Kv := the layout's key vectors.
Limits. At a record whose g and F' no rounds could have left, K3Out holds of every witness for
nothing: K3Stands, in the condition behind, shuts that. IS IT PAYABLE: the laws on runs of claims
(K3RunIsWorth, Johnson/Top/H/K3LawKind.lean) hold at every rs under HeardIs: the claims' values are
one list: where they are 0, the members are 0 at every such rs. A tie with no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LawClaims
import Johnson.Top.H.K3LawKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

section
variable {K : Type} [CommRing K] (h : FoNums.Sh) (lm first : ℕ) (ν : _root_.Fo.Pl → K)
  (Kv : ℕ → ℕ → K)

/-- **The forms that the hearing left**: every residue of the sumchecks' rows is 0. -/
def K3Rows (rs : Rounds K) : Prop :=
  ∀ y ∈ (endsOf h lm first rs).rows.map (rowRes ν), y = 0

/-- **Planes-at-points.** -/
def K3Planes (rs : Rounds K) : Prop :=
  claimLeaves h lm first rs ν (colsK h lm (endsOf h lm first rs).zb0 ν) = 0 ∧
    claimBits h lm first rs ν (colsK h lm (endsOf h lm first rs).zb1 ν) = 0 ∧
    countK h lm (pinColK lm ν) = 0

/-- Each call's key vector at its point. -/
def keysAt (rs : Rounds K) (c : ℕ) : K := extL (Kv c) ((endsOf h lm first rs).zk.getD c [])

/-- **Keys-at-points.** -/
def K3Keys (rs : Rounds K) : Prop :=
  claimJoin h lm first rs ν (keysAt h lm first Kv rs) = 0

/-- The three items are the list's members, by name. -/
theorem k3_claims_iff (rs : Rounds K) :
    (∀ y ∈ claimsOf h lm first rs ν (colsK h lm (endsOf h lm first rs).zb0 ν)
      (colsK h lm (endsOf h lm first rs).zb1 ν) (pinColK lm ν) (keysAt h lm first Kv rs), y = 0) ↔
      K3Rows h lm first ν rs ∧ K3Planes h lm first ν rs ∧ K3Keys h lm first ν Kv rs := by
  unfold claimsOf K3Rows K3Planes K3Keys
  constructor
  · intro H
    refine ⟨fun y hy => H y (List.mem_append_left _ hy), ⟨?_, ?_, ?_⟩, ?_⟩ <;>
      exact H _ (List.mem_append_right _ (by simp))
  · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩ y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact h1 y hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact h2
      · exact h3
      · exact h4
      · exact h5

variable (ρ : OnBytes.Model.Reading K) (g : Forest.Heard) (F' : Fork)

/-- The heard record stands for some rounds. -/
def K3Stands : Prop := ∃ rs : Rounds K, HeardIs ρ g F' (endsOf h lm first rs)

/-- **The three items of the row out**, each at all rounds for which the heard record stands. -/
def K3OutRows : Prop :=
  ∀ rs : Rounds K, HeardIs ρ g F' (endsOf h lm first rs) → K3Rows h lm first ν rs
def K3OutPlanes : Prop :=
  ∀ rs : Rounds K, HeardIs ρ g F' (endsOf h lm first rs) → K3Planes h lm first ν rs
def K3OutKeys : Prop :=
  ∀ rs : Rounds K, HeardIs ρ g F' (endsOf h lm first rs) → K3Keys h lm first ν Kv rs

/-- **THE ROW OUT.** -/
def K3Out : Prop :=
  K3OutRows h lm first ν ρ g F' ∧ K3OutPlanes h lm first ν ρ g F' ∧
    K3OutKeys h lm first ν Kv ρ g F'

theorem k3Out_iff : K3Out h lm first ν Kv ρ g F' ↔
    ∀ rs : Rounds K, HeardIs ρ g F' (endsOf h lm first rs) →
      ∀ y ∈ claimsOf h lm first rs ν (colsK h lm (endsOf h lm first rs).zb0 ν)
        (colsK h lm (endsOf h lm first rs).zb1 ν) (pinColK lm ν) (keysAt h lm first Kv rs),
        y = 0 :=
  ⟨fun H rs hI => (k3_claims_iff h lm first ν Kv rs).2 ⟨H.1 rs hI, H.2.1 rs hI, H.2.2 rs hI⟩,
    fun H => ⟨fun rs hI => ((k3_claims_iff h lm first ν Kv rs).1 (H rs hI)).1,
      fun rs hI => ((k3_claims_iff h lm first ν Kv rs).1 (H rs hI)).2.1,
      fun rs hI => ((k3_claims_iff h lm first ν Kv rs).1 (H rs hI)).2.2⟩⟩

end

/-- **At a written transcript's own rounds the three items are the proved block's out-claim.** -/
theorem out_iff_items (L : List LookupCRCaller) (r : LookupCRCaller)
    (hok : FoNums.ok r.c.h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ r.c.h.kT + 5)
    (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀) (hmk : ∀ t, r.c.L.mkS t = mk (jLK + t))
    (hbc : ∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2)
    (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF r.c.h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (a : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds)) :
    ∃ x : TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀),
      ((kLookupCRN L).toKind.block r).R.red.out a
          ((mapsT ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
        some ((x, a.1.2), a.2) ∧
      ∀ μ₀ : r.c.J₀ → Cb.Gl.E,
        ((forA Cb.Gl.E r.c.h r.c.L).lk.out id id x (zext μ₀) ↔
          K3Rows r.c.h lm jLK (fun p => zext μ₀ (placeOf mk pl p)) (viewRounds ds τ) ∧
          K3Planes r.c.h lm jLK (fun p => zext μ₀ (placeOf mk pl p)) (viewRounds ds τ) ∧
          K3Keys r.c.h lm jLK (fun p => zext μ₀ (placeOf mk pl p))
            (forK Cb.Gl.E r.c.L a.1.1 (zext μ₀)) (viewRounds ds τ)) := by
  obtain ⟨x, hx, hiff⟩ := k3OutIsClaimsR L r hok lm jLK h5 hlm mk pl hmk hbc ds hM hA a τ
  refine ⟨x, hx, fun μ₀ => ?_⟩
  rw [← k3_claims_iff]
  have e := hiff (fun c => AffK.ofConst (keysAt r.c.h lm jLK (forK Cb.Gl.E r.c.L a.1.1 (zext μ₀))
    (viewRounds ds τ) c)) μ₀ (fun c _ => AffK.val_ofConst _ _)
  simpa only [AffK.val_ofConst] using e

#print axioms k3_claims_iff
#print axioms k3Out_iff
#print axioms out_iff_items

end VerifiableInference.OnPublicFiles
