-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsSame.lean.
The smallness test's record behind its claims, and the four hand-made claims under the law of the
rows in the state that the check's own routine leaves.

`tail_four_law` (FoTailLaw) asks the law of the rows in the state that `coefAll` makes at the record
from which `linJoin9` runs. The check runs `coefficients` at the record that `objectsF` returns,
which holds more (the weights of the ties and the reads). This file states that the two records
agree in what the lookup's rows read, and `tail_four_law` once more at a record that so agrees.

Main names:
  `SameZ a b`: b has a's numbers of the arrays, a's two calls, and a's record of the lookup.
  `same_linJoin9`, `same_linBits9`, `same_powersF`, `same_foldSums`, `same_weightsF`,
  `same_objectsF`: what each of these routines returns has `SameZ` with the record at which it ran.
  `SameZ.zOf`, `SameZ.pieces`: so the calls and the list of all pieces are the same.
  `tail_four_lawX`: `tail_four_law` with `CoefOK` and `RowsLaw` at a record tlX with `SameZ tl tlX`.

Under: for `tail_four_lawX`, all the other premises of `tail_four_law`, at the record tl, over a
field.

Limit: tlX is any record with `SameZ tl tlX`, and Fc is any state with `CoefOK tlX Fc` in which each
piece's rows lie inside its array: no premise ties tlX to a run of `objectsF`, or Fc to the states
of the two runs. That `coefAll tlX g Fc` is the state that a run of `coefficientsF` at tlX from Fc
leaves is `coefficientsF_ok` (FoCoef), not a statement of this file.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that `RowsLaw` holds of committed arrays, that `CoefOK` follows from the success
of the routines that make the record and the arrays, or that the check runs `coefficients` at such
a record from such a state.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedLook
import OnBytes.Tie.Pv.Lookup.Ends.FoTailLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset

/-- b has a's numbers of the arrays, a's two calls, and a's record of the lookup. -/
structure SameZ (a b : HTailF2) : Prop where
  ix : b.ix = a.ix
  z1 : b.z1 = a.z1
  z2 : b.z2 = a.z2
  heard : b.heard = a.heard

theorem SameZ.refl (a : HTailF2) : SameZ a a := ⟨rfl, rfl, rfl, rfl⟩

theorem SameZ.trans {a b c : HTailF2} (h : SameZ a b) (k : SameZ b c) : SameZ a c :=
  ⟨k.ix.trans h.ix, k.z1.trans h.z1, k.z2.trans h.z2, k.heard.trans h.heard⟩

theorem SameZ.zOf {a b : HTailF2} (h : SameZ a b) (q : ℕ) : b.zOf q = a.zOf q := by
  unfold HTailF2.zOf
  rw [h.z1, h.z2]

theorem SameZ.pieces {a b : HTailF2} (h : SameZ a b) : allPieces b = allPieces a := by
  unfold allPieces
  rw [h.zOf 0, h.zOf 1]

theorem same_linJoin9 (tl : HTailF2) : Yields tl.linJoin9 (SameZ tl) := by
  unfold HTailF2.linJoin9
  repeat' first
    | exact Yields.pure ⟨rfl, rfl, rfl, rfl⟩
    | (refine Yields.bind fun _ => ?_)

theorem same_linBits9 (tl : HTailF2) : Yields tl.linBits9 (SameZ tl) := by
  unfold HTailF2.linBits9
  repeat' first
    | exact Yields.pure ⟨rfl, rfl, rfl, rfl⟩
    | (refine Yields.bind fun _ => ?_)

theorem same_powersF {tl t : HTailF2} {F : Fork} (h : tl.powersF F = some t) : SameZ tl t := by
  unfold HTailF2.powersF at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rw [← Option.some.inj h]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem same_foldSums {tl t : HTailF2} {mu : ℕ} (h : tl.foldSums mu = some t) : SameZ tl t := by
  unfold HTailF2.foldSums at h
  dsimp only at h
  split_ifs at h <;>
    (rw [← Option.some.inj h]
     exact ⟨rfl, rfl, rfl, rfl⟩)

theorem same_folds : ∀ (l : List ℕ) (a b : HTailF2),
    l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) a = some b → SameZ a b
  | [], a, b, h => by
    obtain rfl : a = b := Option.some.inj h
    exact SameZ.refl a
  | mu :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (same_foldSums ht).trans (same_folds l t b h2)

theorem same_weightsF (tl : HTailF2) : Yields tl.weightsF (SameZ tl) := by
  intro F c a G c' hr
  unfold HTailF2.weightsF at hr
  obtain ⟨t, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨t', e1, r1⟩ := (ask_ok _ _ _ _).1 h1
  obtain rfl : t = t' := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) r1
  obtain ⟨a', e2, r2⟩ := (get_ok _ _ _ _).1 h2
  obtain rfl : a = a' := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) r2
  have k := same_folds _ _ _ e2
  exact (same_powersF e1).trans ⟨k.ix, k.z1, k.z2, k.heard⟩

/-- **The record that `objectsF` returns.** -/
theorem same_objectsF (tl : HTailF2) (funs : Array HFun) :
    Yields (tl.objectsF funs) (SameZ tl) := by
  unfold HTailF2.objectsF
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (same_linJoin9 tl) fun t1 h1 => ?_
  refine Yields.bind2 (same_linBits9 t1) fun t2 h2 => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (same_weightsF t2) fun t3 h3 => ?_
  have e := (h1.trans h2).trans h3
  repeat' first
    | exact Yields.pure ⟨e.ix, e.z1, e.z2, e.heard⟩
    | (refine Yields.bind fun _ => ?_)

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

/-- The four hand-made claims, under the law of the rows at a later record. -/
theorem tail_four_lawX (tl tl1 tl2 tlX : HTailF2) (hX : SameZ tl tlX) (F G1 G2 : Fork)
    (c c1 c2 : Ctx)
    (hJ : tl.linJoin9 F c = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F) (hLS : F.LS.size = F.ns)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : Later G2 H)
    (hL : RowsLaw ρ (coefAll tlX g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i))) :
    G2.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) =
      F.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) +
        ρ.val F.theta ^ F.nClaim * claimJoin g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀)) +
        ρ.val F.theta ^ (F.nClaim + 1) * claimLeaves g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 2) * claimBits g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 3) * Pin.countK g.shape 5
          (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tlX g Fc T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR _ _ hL _ _
    (show rdL ρ g.zb0 = _ from hI.zb0) (show rdL ρ g.zb1 = _ from hI.zb1) tl.bzColumns
  rw [hX.ix] at v0 v1 v2
  refine tail_four_dig ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK rsK F0 hI h0 hok hT hF hLS
    hfull h5 hn h63 hP hD en mk μ₀ entry v0 v1 v2 (fun q hq p hp i _ => ?_) H hH
  have e := virt_piece ρ tlX g Fc T (q, p) (hX.pieces ▸ mem_allPieces hq hp)
    (hRw _ (mem_allPieces hq hp)) _ _ hL (p.c0 + i)
  rw [hX.zOf] at e
  rw [(hP q hq p hp).tree] at e ⊢
  exact e

end
end Fo
