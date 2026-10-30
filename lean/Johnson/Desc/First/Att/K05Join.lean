-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Join.lean: the join of K05_law's two halves: the hearing's and the rows'
(Att/K05Law.lean) with the claims' (Att/Claims/SayAt.lean: say_at: under its own premises, every
form that the runs
"first" and "second" gather is worth 0 exactly if SayAt).

Where SayAt holds in the ledger's world, at a record whose points are pointsOf's of
what was heard and of leftP's rows (PointsAre), each sumcheck's debt in the proved chain's bill is
just
EndsMean (Att/K5Mean.lean).

Main names:
  `sumAt_len`: a sumcheck has heard as many end values as its stage says.
  `TailSeam`, `UnitsSeam`: the numbering's bounds and the places of the end values' mask entries.
  `tail_join`; `SlotsFrom`, `slots_of_index`, `slots_from`, `cntOf`, `UnitsMeans`, `units_join`.
  `K05_join`: UnitsBill and TailBill hold exactly if (UnitsLin and UnitsMeans) and (TailLin and the
    five
    EndsMean), at the written readers.

Premises: SayAt · PointsAre · Said, the data's ties · the place's three numbers are the plan's · the
two
seams (lemmas at the closed parameters: Att/K05Row.lean).
Limit: the score at the index's row and end values are not cancelled here: they stand inside owF.
Sources: Att/Claims/SayAt.lean and what it imports (oldOf is a plain record made of the kind's own;
it feeds
written lists alone). No routine that runs in a context is reached.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SayAt
import Johnson.Desc.First.Att.K5Mean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH)
open VerifiableInference.Desc.Part
open K5Law (SayAt PointsAre tail_rows tail_ends unit_at unitReader endsE endsV endsK endsH oldOf sum3Back)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

theorem sumAt_len {C : Aff} {vs : List MaskedSum.Var} {e : MaskedSum.Ends} {pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (.sum vs e) pre H hh G) : H.v.length = e.n := by
  obtain ⟨vs', e', F, G0, used, e1, sd, _⟩ := h
  injection e1 with _ e3
  rw [e3]
  exact sd.lenV

/-! ## The tail -/

/-- The numbering's bounds, and the places of the end values' mask entries. -/
structure TailSeam {X : Type} {T : Tail K M X} (a : TailAdd T) (x : Params.AttentionRounds) (h : Heard)
    (mask : ℕ → K) (m : M) : Prop where
  nE : ∀ y, a.aE.num y < 2 * x.pairs
  mE : ∀ y, T.sE.msg m (T.sE.T.cAt y) = mask (h.division.sEnd + a.aE.num y)
  nM : ∀ y, a.aM.num y < 2 * x.pairs
  mM : ∀ y, T.sVM.msg m (T.sVM.T.cAt y) = mask (h.below.sEnd + a.aM.num y)
  nVD : ∀ y, a.aVD.num y < 2 * x.pairs
  mVD : ∀ y, T.sVD.msg m (T.sVD.T.cAt y) = mask (h.on.sEnd + a.aVD.num y)
  nD : ∀ y, a.aD.num y < x.Lam + x.pairs * x.lt
  mD : ∀ y, T.sD.msg m (T.sD.T.cAt y) = mask (h.key.sEnd + a.aD.num y)
  nH : ∀ y, a.aH.num y < 2 * x.pairs
  mH : ∀ y, T.sH.msg m (T.sH.T.cAt y) = mask (h.cells.sEnd + a.aH.num y)

/-- **The tail's five debts, where K5's claims hold.** -/
theorem tail_join {X : Type} {T : Tail K M X} (dt : TailH ρ T) {x : Params.AttentionRounds} {h : Heard} {Gf : Fork}
    {Ls : Lists} (hs : Said x h Gf Ls) (ho : TailOfP dt x h Ls) (a : TailAdd T) (hv : TailVals dt a) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) (sm : TailSeam a x h mask m) {S : Attention.Shape} {gL : Forest.Heard}
    {i : Runs.In} {Kc : ℕ} {zk : Array (Array E)} {l : Left} (H : PointsAre i.g zk h l i.p)
    (Sy : SayAt ρ (Gf.worldOf ρ mask entry) S gL i Kc) (hNP : S.NP = x.pairs) (hLam : S.Lam = x.Lam)
    (hlt : S.cf.lt = x.lt) :
    TailPaid dt l (Gf.worldOf ρ mask entry) m ↔
      EndsMean T.sE dt.dE a.aE (endsE (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m ∧
      EndsMean T.sVM dt.dVM a.aM (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM)
        (Gf.worldOf ρ mask entry) m ∧
      EndsMean T.sVD dt.dVD a.aVD (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD)
        (Gf.worldOf ρ mask entry) m ∧
      EndsMean T.sD dt.dD a.aD (endsK (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m ∧
      EndsMean T.sH dt.dH a.aH (endsH (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m := by
  obtain ⟨r1, r2, r3, _, r5, r6⟩ := tail_rows H Sy
  obtain ⟨e1, e2, e3, _, e5, e6⟩ := tail_ends H Sy
  rw [hNP] at e1 e2 e3 e6
  rw [hNP, hLam, hlt] at e5
  unfold TailPaid
  rw [paid_iff_mean T.sE dt.dE ho.oE hs.sE a.aE hv.vE _ sm.nE (le_of_eq (sumAt_len hs.sE).symm) m mask entry sm.mE _ _ e1,
    paid_iff_mean T.sVM dt.dVM ho.oM hs.sM a.aM hv.vM _ sm.nM (le_of_eq (sumAt_len hs.sM).symm) m mask entry sm.mM _ _ e2,
    paid_iff_mean T.sVD dt.dVD ho.oVD hs.sVD a.aVD hv.vVD _ sm.nVD (le_of_eq (sumAt_len hs.sVD).symm) m mask entry
      sm.mVD _ _ e3,
    paid_iff_mean T.sD dt.dD ho.oD hs.sD a.aD hv.vD _ sm.nD (le_of_eq (sumAt_len hs.sD).symm) m mask entry sm.mD _ _ e5,
    paid_iff_mean T.sH dt.dH ho.oH hs.sH a.aH hv.vH _ sm.nH (le_of_eq (sumAt_len hs.sH).symm) m mask entry sm.mH _ _ e6]
  simp only [r1, r2, r3, r5, r6, true_and]

/-! ## The units -/

/-- The units' rows are worth 0 and their end values' slots are worth the readers' forms, one by
one, from number n on. -/
def SlotsFrom (W : World K) (ρ : Reading K) (rdr : ℕ → ℕ → Aff) (cnt : ℕ → ℕ) :
    List (ℕ × MaskedSum.Heard) → List Aff → ℕ → Prop
  | [], [], _ => True
  | o :: os, f :: fs, n =>
    f.value ρ W = 0 ∧ (∀ j < cnt n, W.slot (o.2.sEnd + j) = (rdr n j).value ρ W) ∧ SlotsFrom W ρ rdr cnt os fs (n + 1)
  | _, _, _ => False

omit [Fintype K] in
theorem slots_of_index (W : World K) (ρ : Reading K) (rdr : ℕ → ℕ → Aff) (cnt : ℕ → ℕ) :
    ∀ (os : List (ℕ × MaskedSum.Heard)) (fs : List Aff) (n0 : ℕ), os.length = fs.length →
      (∀ n o, os[n]? = some o → ∃ f, fs[n]? = some f ∧ f.value ρ W = 0 ∧
        ∀ j < cnt (n0 + n), W.slot (o.2.sEnd + j) = (rdr (n0 + n) j).value ρ W) →
      SlotsFrom W ρ rdr cnt os fs n0
  | [], [], _, _, _ => trivial
  | o :: os, f :: fs, n0, hl, h => by
    obtain ⟨f', e, h1, h2⟩ := h 0 o rfl
    have ef : f' = f := (Option.some.inj e).symm
    subst ef
    refine ⟨h1, h2, slots_of_index W ρ rdr cnt os fs (n0 + 1) (by simpa using hl) fun n o' ho => ?_⟩
    obtain ⟨f2, e2, k1, k2⟩ := h (n + 1) o' (by simpa using ho)
    refine ⟨f2, by simpa using e2, k1, ?_⟩
    rw [show n0 + 1 + n = n0 + (n + 1) by omega]
    exact k2
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- How many end values unit number n has, by the claims' record. -/
def cntOf (i : Runs.In) (n : ℕ) : ℕ := 2 * ((i.p.scores[n]?).map (·.pw.size)).getD 0

omit [Fintype K] in
theorem slots_from {W : World K} {S : Attention.Shape} {gL : Forest.Heard} {i : Runs.In} {Kc : ℕ}
    {zk : Array (Array E)} {h : Heard} {l : Left} (H : PointsAre i.g zk h l i.p) (Sy : SayAt ρ W S gL i Kc) :
    SlotsFrom W ρ (unitReader S gL i Kc) (cntOf i) h.scores.toList l.scores.toList 0 := by
  refine slots_of_index W ρ _ _ _ _ 0 (by simp [← H.nH, ← H.nL]) fun n o ho => ?_
  obtain ⟨k, f, a1, a2, _, _, a5, a6⟩ := unit_at H Sy n o (by simpa using ho)
  refine ⟨f, by simpa using a2, a5, ?_⟩
  rw [Nat.zero_add]
  unfold cntOf
  rw [a1]
  exact a6

/-- The numbering's bounds and the places of the end values' mask entries, unit by unit. -/
def UnitsSeam {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsAdd us → List (ℕ × ℕ) →
    List (ℕ × MaskedSum.Heard) → (ℕ → ℕ) → ℕ → (ℕ → K) → M → Prop
  | [], _, _, _, _, _, _, _ => True
  | u :: us, a, p :: ps, o :: os, cnt, n, mask, m =>
    (∀ y, a.1.num y < cnt n) ∧ cnt n ≤ 2 * p.2 ∧ (∀ y, u.msg m (u.T.cAt y) = mask (o.2.sEnd + a.1.num y)) ∧
      UnitsSeam us a.2 ps os cnt (n + 1) mask m
  | _, _, _, _, _, _, _, _ => False

def UnitsMeans {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → UnitsAdd us → ℕ → (ℕ → ℕ → Aff) →
    World K → M → Prop
  | [], _, _, _, _, _, _ => True
  | u :: us, d, a, n, rdr, W, m => EndsMean u d.1 a.1 (rdr n) W m ∧ UnitsMeans us d.2 a.2 (n + 1) rdr W m

/-- **The units' debts, where K5's claims hold.** -/
theorem units_join {X : Type} {Gf : Fork} (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) (rdr : ℕ → ℕ → Aff)
    (cnt : ℕ → ℕ) : ∀ (us : List (SumL K M (Seen K X))) (du : UnitsH ρ us) (a : UnitsAdd us) (ps : List (ℕ × ℕ))
    (os : List (ℕ × MaskedSum.Heard)) (pre : List E) (lst : List (List E × PscH)) (fs : List Aff) (n : ℕ),
    UnitsAt ps os pre lst Gf → UnitsOfP us du ps os pre lst → UnitsVals us du a →
    UnitsSeam us a ps os cnt n mask m → SlotsFrom (Gf.worldOf ρ mask entry) ρ rdr cnt os fs n →
    (UnitsPaid us du fs (Gf.worldOf ρ mask entry) m ↔ UnitsMeans us du a n rdr (Gf.worldOf ρ mask entry) m)
  | [], _, _, [], [], _, [], [], _, _, _, _, _, _ => Iff.rfl
  | u :: us, d, a, p :: ps, o :: os, pre, (v7, H) :: lst, f :: fs, n, ⟨_, _, a3, _, a5⟩, ⟨_, of, hn⟩, ⟨hv, hvs⟩,
      ⟨s1, s2, s3, s4⟩, ⟨z1, z2, z3⟩ => by
    have hp := paid_iff_mean u d.1 of a3 a.1 hv (cnt n) s1 (by rw [sumAt_len a3]; exact s2) m mask entry s3 f
      (rdr n) z2
    refine and_congr (hp.trans (by rw [z1]; simp))
      (units_join mask entry m rdr cnt us d.2 a.2 ps os [] lst fs (n + 1) a5 hn hvs s4 z3)
  | [], _, _, [], [], _, [], _ :: _, _, _, _, _, _, hz => hz.elim
  | [], _, _, [], [], _, _ :: _, _, _, _, ho, _, _, _ => ho.elim
  | [], _, _, [], _ :: _, _, _, _, _, _, ho, _, _, _ => ho.elim
  | [], _, _, _ :: _, _, _, _, _, _, _, ho, _, _, _ => ho.elim
  | _ :: _, _, _, [], _, _, _, _, _, _, ho, _, _, _ => ho.elim
  | _ :: _, _, _, _ :: _, [], _, _, _, _, _, ho, _, _, _ => ho.elim
  | _ :: _, _, _, _ :: _, _ :: _, _, [], _, _, _, ho, _, _, _ => ho.elim
  | _ :: _, _, _, _ :: _, _ :: _, _, _ :: _, [], _, _, _, _, _, hz => hz.elim

/-! ## The whole -/

/-- **THE JOIN.** Where K5's gathered claims all hold in the ledger's world, the proved chain's bill
is: the letters' linear
claims, and for each sumcheck that owes its output claims: what its end values' readers mean. -/
theorem K05_join {X : Type} (A : Cb.Pv.Att.AttOwn K M X) (du : UnitsH ρ A.units) (dt : TailH ρ A.tail)
    {x : Params.AttentionRounds} {h : Heard} {Gf : Fork} {Ls : Lists} (hs : Said x h Gf Ls)
    (hu : UnitsOfP A.units du x.score h.scores.toList Ls.planes.flatten Ls.units) (ht : TailOfP dt x h Ls)
    (au : UnitsAdd A.units) (at' : TailAdd A.tail) (vu : UnitsVals A.units du au) (vt : TailVals dt at')
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {S : Attention.Shape} {gL : Forest.Heard} {i : Runs.In} {Kc : ℕ}
    {zk : Array (Array E)} {l : Left} (H : PointsAre i.g zk h l i.p)
    (Sy : SayAt ρ (Gf.worldOf ρ mask entry) S gL i Kc) (hNP : S.NP = x.pairs) (hLam : S.Lam = x.Lam)
    (hlt : S.cf.lt = x.lt) (su : UnitsSeam A.units au x.score h.scores.toList (cntOf i) 0 mask m)
    (st : TailSeam at' x h mask m) (s0 : Seen K X) (s1 : Seen K X) :
    (UnitsBill A.units du s0 l.scores.toList (Gf.worldOf ρ mask entry) m ∧
        TailBill dt s1 l (Gf.worldOf ρ mask entry) m) ↔
      (UnitsLin A.units du s0 m ∧
        UnitsMeans A.units du au 0 (unitReader S gL i Kc) (Gf.worldOf ρ mask entry) m) ∧
      (TailLin dt s1 m ∧
        EndsMean A.tail.sE dt.dE at'.aE (endsE (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m ∧
        EndsMean A.tail.sVM dt.dVM at'.aM
          (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM) (Gf.worldOf ρ mask entry) m ∧
        EndsMean A.tail.sVD dt.dVD at'.aVD
          (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD) (Gf.worldOf ρ mask entry) m ∧
        EndsMean A.tail.sD dt.dD at'.aD (endsK (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m ∧
        EndsMean A.tail.sH dt.dH at'.aH (endsH (oldOf S gL i) Kc) (Gf.worldOf ρ mask entry) m) := by
  rw [unitsBill_iff, tailBill_iff,
    units_join mask entry m _ _ A.units du au _ _ _ _ _ 0 hs.units hu vu su (slots_from H Sy),
    tail_join dt hs ht at' vt mask entry m st H Sy hNP hLam hlt]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.units_join
#print axioms VerifiableInference.Desc.First.Att.P.K05_join
#print axioms VerifiableInference.Desc.First.Att.P.tail_join
