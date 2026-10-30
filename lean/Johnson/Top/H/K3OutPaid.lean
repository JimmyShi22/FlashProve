-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutPaid.lean: the kind "lookup" (K3): WHO PAYS THE ROW OUT: the five statements of
part (III) of Johnson/Top/H/K3LeftStatement.lean, proved: the rows, the planes and the keys, each
from its own run of claims under its own premises alone; the keys handed in by a calling kind that
calls no "join"; the three at K3's own runs. Theorems with their proofs.

How. The laws on the runs (Johnson/Top/H/K3RunsLaw.lean) say what each run's claims are worth at
every later ledger, at all rounds for which the heard record stands; objectsAre_of_run and
planesAre_of_run (Johnson/Top/H/K3OutParts.lean) have them as equations of lists. HeardIs pins the
points that the premises read (zb0, zb1, zk, theta, alpha, zy) to the heard record's own words: so
the premises name no round.

Main names: `zk_getD` · `k3RowsPaid_of` · `k3PlanesPaid_of` · `k3KeysPaid_of` · `k3KeysHanded` ·
`k3PaidAtSeat` · `k3Out_paid` (the three together are the row out).

Limits. Ties: no error term. That the claims ARE worth 0, the three clauses on the planes and the
keys' equations are premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin Cb.Fo.PlaneClaims

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- Call c's key point, read: off the list of read points, or off the array of points. -/
theorem zk_getD (zk : Array (Array OnBytes.E)) (c : ℕ) :
    (zk.toList.map (rdA ρ)).getD c [] = rdA ρ (zk.getD c #[]) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases zk[c]? <;> rfl

/-- What the form left for the join is worth at a later ledger. -/
theorem cEnd_worth (g : Forest.Heard) (F0 H : Fork) (lm first : ℕ) (rs : Rounds K)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm first rs)) (hL : _root_.Fo.Later F0 H)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm first rs).cEndF, (endsOf g.shape lm first rs).cEndC) ν := by
  rw [(hI.cEnd H hL).2 (fun j => ν (.mask j)) entry,
    evalL_muOf (onMasks_keyTop g.shape lm first rs) ν]
  show _ = evalL ν (scale (-1) (endsOf g.shape lm first rs).cEndInc) + _
  rw [evalL_scale]
  ring

end

section
variable {S Cl : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
  {form : Cl → Aff} {lm : ℕ}

/-- **The rows.** -/
theorem k3RowsPaid_of {objects : ℕ → S → Except String (List Cl × S)}
    (hO : K3RunIsWorth fork heard form lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν))) :
    K3RowsPaid fork heard form lm objects := by
  intro K _ ρ g F0 first sO clO GO H ν entry hok rO lO hz rs hI y hy
  rw [← objectsAre_of_run ρ fork heard form lm objects hO g F0 first rs hI hok sO clO GO H rO lO ν
    entry] at hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
  exact hz c hc

/-- **The planes.** -/
theorem k3PlanesPaid_of {planes : ℕ → S → Except String (List Cl × S)} {bit : S → ℕ → ℕ → Aff}
    {pin : S → ℕ → Aff}
    (hP : K3RunIsWorthAt fork heard form lm planes
      (fun s _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit s 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit s 1 col),
          Pin.countK g.shape lm fun col => val (pin s col)])) :
    K3PlanesPaid fork heard form lm planes bit pin := by
  intro K _ ρ g F0 first sP clP GP H ν entry hok rP lP hz b0 b1 pn rs hI
  have hA := planesAre_of_run ρ fork heard form lm planes bit pin hP g F0 first rs hI hok sP clP GP
    H rP lP ν entry (by rw [← hI.zb0]; exact b0) (by rw [← hI.zb1]; exact b1) pn
  have z : ∀ y ∈ clP.map (fun c =>
      (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)), y = 0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c hc
  rw [hA] at z
  exact ⟨z _ (by simp), z _ (by simp), z _ (by simp)⟩

/-- **The keys.** -/
theorem k3KeysPaid_of {join : ℕ → S → Except String (List Cl × S)} {keys : S → Array Aff}
    (hJ : K3RunIsWorthAt fork heard form lm join
      (fun s _ _ g jLK rsK ν val =>
        [claimJoin g.shape lm jLK rsK ν fun k => val ((keys s).getD k (Aff.ofConst zeroE))])) :
    K3KeysPaid fork heard form lm join keys := by
  intro K _ ρ g F0 first sJ clJ GJ H ν entry Kv hok rJ lJ hz hk rs hI
  obtain ⟨FJ, fJ, laJ, szJ⟩ := rJ.later
  obtain ⟨nJ, sJ', runJ, gJ⟩ := rJ.ran
  obtain ⟨GJ', bJ, _, _, _, _, vJ⟩ :=
    hJ K ρ g first rs F0 FJ nJ sJ sJ' clJ rJ.heard fJ hI laJ hok szJ runJ
  obtain rfl : GJ = GJ' := Option.some.inj (gJ.symm.trans bJ)
  have wJ := vJ H lJ ν entry
  beta_reduce at wJ
  have z : ∀ y ∈ clJ.map (fun c =>
      (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)), y = 0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c hc
  rw [wJ] at z
  have z0 := z _ (List.mem_singleton.2 rfl)
  show claimJoin g.shape lm first rs ν (keysAt g.shape lm first Kv rs) = 0
  rw [← z0]
  refine claimJoin_congr _ _ _ _ _ _ _ fun c hc => ?_
  unfold keysAt
  rw [hk c hc, ← hI.zk, zk_getD]

end

/-- **The keys, handed in.** -/
theorem k3KeysHanded : K3KeysHanded := by
  intro K _ ρ lm g F0 H first ν entry Kv hok hL hz rs hI
  show claimJoin g.shape lm first rs ν (keysAt g.shape lm first Kv rs) = 0
  unfold claimJoin
  rw [val_joinK] at hz ⊢
  simp only [AffK.val_ofConst] at hz ⊢
  rw [← cEnd_worth ρ g F0 H lm first rs hI hL ν entry, ← hI.theta, ← hI.alpha, ← hI.zy]
  have hk : ∀ c, keysAt g.shape lm first Kv rs c = extL (Kv c) (rdA ρ (g.zk.getD c #[])) := by
    intro c
    unfold keysAt
    rw [← hI.zk, zk_getD]
  simp only [hk]
  exact hz

/-- **The three at K3's own runs.** -/
theorem k3PaidAtSeat : K3PaidAtSeat := fun S Cl seat form hs lm readers keys =>
  ⟨k3RowsPaid_of (objects_worth seat form hs lm),
    k3PlanesPaid_of (planes_worth seat form hs lm readers),
    k3KeysPaid_of (join_worth seat form hs lm keys)⟩

/-- The three together are the row out. -/
theorem k3Out_paid {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : FoNums.Sh}
    {lm first : ℕ} {ν : _root_.Fo.Pl → K} {Kv : ℕ → ℕ → K} {g : Forest.Heard} {F0 : Fork}
    (h1 : K3OutRows h lm first ν ρ g F0) (h2 : K3OutPlanes h lm first ν ρ g F0)
    (h3 : K3OutKeys h lm first ν Kv ρ g F0) : K3Out h lm first ν Kv ρ g F0 := ⟨h1, h2, h3⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3RowsPaid_of
#print axioms VerifiableInference.OnPublicFiles.k3PlanesPaid_of
#print axioms VerifiableInference.OnPublicFiles.k3KeysPaid_of
#print axioms VerifiableInference.OnPublicFiles.k3KeysHanded
#print axioms VerifiableInference.OnPublicFiles.k3PaidAtSeat
