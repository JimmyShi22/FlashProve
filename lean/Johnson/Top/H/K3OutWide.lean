-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutWide.lean: the kind "lookup" (K3): the road from claims to the proved block's
out-claim, CUT IN TWO AT A MIDDLE STATEMENT, so that a caller that does not hand in a form for each
column of the planes' matrix can walk it too. Definitions and theorems with their proofs.

Why. K3ClaimsGiveOut (Johnson/Top/H/K3OutStatement.lean) takes the claims on the planes from forms
that the caller hands in, one for each column (K3HostLaw). The verifier program's smallness test
does not go that way at its lookup on the digits: it makes the four claims by hand, each as a form
plus runs on virtual rows (linJoin9, linBits9, OnBytes/Model/Tail.lean). Whether forms for single
columns could be given there at all, at entries of virtual rows that stand for committed arrays, has
not been settled; the cut spares the question.

Main names:
  `K3ClaimsAre`: THE MIDDLE: three lists of claims, of any type with a value, are worth: the
    residues of the record's rows; claimLeaves, claimBits and countK at the columns' own
    combinations of cells (colsK, pinColK); claimJoin at given values for the calls' key vectors.
  `out_of_claimsAre`: FROM THE MIDDLE ON: at every written transcript that meets the block's spec
    the block puts out x, and for all claims with K3ClaimsAre at the key vectors' extensions, if
    every claim is worth 0 then x's out-claim holds. By k3OutIsClaimsR alone.
  `claimsAre_of_runs`: ONE WAY TO THE MIDDLE: the kind's three runs with the law on runs, at later
    records (K3RanAt), with K3HostLaw.

Limits. A tie with no error term. Nothing here says at WHICH entries of virtual rows a claim's value
is taken: val is a letter; that these entries are what committed arrays give is a law on the world
(the library's RowsLaw), owed by whoever fills val. The second way to the middle, for claims made by
hand from totals under a law on virtual rows, is not here. out_of_claimsAre names no decide: that
the first slot jLK and the rounds are those of a decide's yes is the caller's to bring
(K3DecideHears gives it).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- **The middle: what the lookup's claims are worth.** val: the value of a claim. kf c: the value
for call c's key vector. -/
def K3ClaimsAre {Cl K : Type} [CommRing K] (val : Cl → K) (h : FoNums.Sh) (lm jLK : ℕ)
    (rs : Rounds K) (ν : _root_.Fo.Pl → K) (kf : ℕ → K) (clO clP clJ : List Cl) : Prop :=
  clO.map val = (endsOf h lm jLK rs).rows.map (rowRes ν) ∧
    clP.map val =
      [claimLeaves h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb0 ν),
        claimBits h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb1 ν),
        countK h lm (pinColK lm ν)] ∧
    clJ.map val = [claimJoin h lm jLK rs ν kf]

/-- With the middle, claims that are all worth 0 make every member of the list 0. -/
theorem claimsAre_zero {Cl K : Type} [CommRing K] {val : Cl → K} {h : FoNums.Sh} {lm jLK : ℕ}
    {rs : Rounds K} {ν : _root_.Fo.Pl → K} {kf : ℕ → K} {clO clP clJ : List Cl}
    (hA : K3ClaimsAre val h lm jLK rs ν kf clO clP clJ)
    (hz : ∀ c ∈ clO ++ clP ++ clJ, val c = 0) :
    ∀ y ∈ claimsOf h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb0 ν)
      (colsK h lm (endsOf h lm jLK rs).zb1 ν) (pinColK lm ν) kf, y = 0 := by
  obtain ⟨aO, aP, aJ⟩ := hA
  have zero : ∀ (cl : List Cl), (∀ c ∈ cl, c ∈ clO ++ clP ++ clJ) → ∀ y ∈ cl.map val, y = 0 := by
    intro cl hcl y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c (hcl c hc)
  have zO := zero clO (fun c hc => by simp [hc])
  have zP := zero clP (fun c hc => by simp [hc])
  have zJ := zero clJ (fun c hc => by simp [hc])
  rw [aO] at zO
  rw [aP] at zP
  rw [aJ] at zJ
  intro y hy
  unfold claimsOf at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact zO y hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact zP _ (by simp)
    · exact zP _ (by simp)
    · exact zP _ (by simp)
    · exact zJ _ (by simp)

/-- **From the middle to the proved block's out-claim.** -/
theorem out_of_claimsAre (L : List LookupCRCaller) (r : LookupCRCaller)
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
      ∀ (Cl : Type) (val : Cl → Cb.Gl.E) (clO clP clJ : List Cl) (μ₀ : r.c.J₀ → Cb.Gl.E),
        K3ClaimsAre val r.c.h lm jLK (viewRounds ds τ) (fun p => zext μ₀ (placeOf mk pl p))
          (fun c => extL (forK Cb.Gl.E r.c.L a.1.1 (zext μ₀) c)
            ((endsOf r.c.h lm jLK (viewRounds ds τ)).zk.getD c [])) clO clP clJ →
        (∀ c ∈ clO ++ clP ++ clJ, val c = 0) →
        (forA Cb.Gl.E r.c.h r.c.L).lk.out id id x (zext μ₀) := by
  obtain ⟨x, hx, hiff⟩ := k3OutIsClaimsR L r hok lm jLK h5 hlm mk pl hmk hbc ds hM hA a τ
  refine ⟨x, hx, fun Cl val clO clP clJ μ₀ hAre hz => ?_⟩
  refine (hiff (fun c => AffK.ofConst (extL (forK Cb.Gl.E r.c.L a.1.1 (zext μ₀) c)
    ((endsOf r.c.h lm jLK (viewRounds ds τ)).zk.getD c []))) μ₀
    (fun c _ => AffK.val_ofConst _ _)).2 ?_
  simpa only [AffK.val_ofConst] using claimsAre_zero hAre hz

/-- **One way to the middle: the kind's own runs, with a form for each column.** -/
theorem claimsAre_of_runs {S Cl K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard) (form : Cl → Aff) (lm : ℕ)
    (objects planes join : ℕ → S → Except String (List Cl × S))
    (bit : S → ℕ → ℕ → Aff) (pin : S → ℕ → Aff) (keys : S → Array Aff)
    (hO : K3RunIsWorth fork heard form lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)))
    (hP : K3RunIsWorthAt fork heard form lm planes
      (fun s _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit s 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit s 1 col),
          Pin.countK g.shape lm fun col => val (pin s col)]))
    (hJ : K3RunIsWorthAt fork heard form lm join
      (fun s _ _ g jLK rsK ν val =>
        [claimJoin g.shape lm jLK rsK ν fun k => val ((keys s).getD k (Aff.ofConst zeroE))]))
    (g : Forest.Heard) (F' : Fork) (jLK : ℕ) (rsK : Rounds K)
    (hI : HeardIs ρ g F' (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (sO sP sJ : S) (clO clP clJ : List Cl) (GO GP GJ H : Fork)
    (rO : K3RanAt fork heard g F' objects sO clO GO)
    (rP : K3RanAt fork heard g F' planes sP clP GP) (rJ : K3RanAt fork heard g F' join sJ clJ GJ)
    (lO : _root_.Fo.Later GO H) (lP : _root_.Fo.Later GP H) (lJ : _root_.Fo.Later GJ H)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) (Kv : ℕ → ℕ → K)
    (hH : K3HostLaw g.shape lm (endsOf g.shape lm jLK rsK).zb0 (endsOf g.shape lm jLK rsK).zb1
      (fun k => (endsOf g.shape lm jLK rsK).zk.getD k []) ν Kv
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) (bit sP) (pin sP)
      (keys sJ)) :
    K3ClaimsAre (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) g.shape lm
      jLK rsK ν (fun c => extL (Kv c) ((endsOf g.shape lm jLK rsK).zk.getD c [])) clO clP clJ := by
  obtain ⟨FO, fO, laO, szO⟩ := rO.later
  obtain ⟨nO, sO', runO, gO⟩ := rO.ran
  obtain ⟨GO', bO, _, _, _, _, vO⟩ :=
    hO K ρ g jLK rsK F' FO nO sO sO' clO rO.heard fO hI laO hok szO runO
  obtain rfl : GO = GO' := Option.some.inj (gO.symm.trans bO)
  have wO := vO H lO ν entry
  obtain ⟨FP, fP, laP, szP⟩ := rP.later
  obtain ⟨nP, sP', runP, gP⟩ := rP.ran
  obtain ⟨GP', bP, _, _, _, _, vP⟩ :=
    hP K ρ g jLK rsK F' FP nP sP sP' clP rP.heard fP hI laP hok szP runP
  obtain rfl : GP = GP' := Option.some.inj (gP.symm.trans bP)
  have wP := vP H lP ν entry
  obtain ⟨FJ, fJ, laJ, szJ⟩ := rJ.later
  obtain ⟨nJ, sJ', runJ, gJ⟩ := rJ.ran
  obtain ⟨GJ', bJ, _, _, _, _, vJ⟩ :=
    hJ K ρ g jLK rsK F' FJ nJ sJ sJ' clJ rJ.heard fJ hI laJ hok szJ runJ
  obtain rfl : GJ = GJ' := Option.some.inj (gJ.symm.trans bJ)
  have wJ := vJ H lJ ν entry
  beta_reduce at wO wP wJ
  refine ⟨wO, ?_, ?_⟩
  · rw [wP, claimLeaves_congr _ _ _ _ _ _ _ fun col hc => hH.bit0 col hc,
      claimBits_congr _ _ _ _ _ _ _ fun col hc => hH.bit1 col hc,
      Cb.Fo.PlaneClaims.countK_congr _ _ _ _ fun col hc => hH.pin col hc]
  · rw [wJ, claimJoin_congr _ _ _ _ _ _ _ fun c hc => hH.keys c hc]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.out_of_claimsAre
#print axioms VerifiableInference.OnPublicFiles.claimsAre_of_runs
