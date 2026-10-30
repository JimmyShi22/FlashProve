-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutProof.lean: the kind "lookup" (K3): the statement K3ClaimsGiveOut
(Johnson/Top/H/K3OutStatement.lean) follows from three laws: the law on decide's yes
(K3DecideHears), the law on the three runs of claims (K3RunIsWorth, K3RunIsWorthAt), and the law
that ties the proved block's out-claim to the library's list of claims (k3OutIsClaimsR). Theorems
with their proofs.

Main names:
  `k3ClaimsGiveOut_of`: at letters for the kind's functions, from the first two laws as premises.
  `k3ClaimsGiveOut`: at K3.block's own decide and runs, for a seat with the three laws on seats.
  `shapeOf_unique`, `claimLeaves_congr`, `claimBits_congr`, `claimJoin_congr`: small lemmas.

Limits. Those of the statement's file. A tie with no error term. The host's law stays a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutStatement
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.K3DecideHearsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- The public tests make one shape of the calls. -/
theorem shapeOf_unique {calls : Array Call} {pub : Array Nat} {lid : ℕ} {h h' : Forest.Shape}
    (a : ShapeOf calls pub lid h) (b : ShapeOf calls pub lid h') : h = h' := by
  obtain ⟨h0, e0, _, rfl⟩ := a
  obtain ⟨h1, e1, _, rfl⟩ := b
  have e : h0 = h1 := Except.ok.inj (e0.symm.trans e1)
  rw [e]

section
variable {K : Type} [CommRing K]

theorem claimLeaves_congr (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : _root_.Fo.Pl → K)
    (b b' : ℕ → K) (hb : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → b col = b' col) :
    claimLeaves h lm jLK rs ν b = claimLeaves h lm jLK rs ν b' := by
  unfold claimLeaves
  rw [Cb.Fo.PlaneClaims.planesK_congr h lm _ b b' hb]

theorem claimBits_congr (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : _root_.Fo.Pl → K)
    (b b' : ℕ → K) (hb : ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → b col = b' col) :
    claimBits h lm jLK rs ν b = claimBits h lm jLK rs ν b' := by
  unfold claimBits
  rw [Cb.Fo.PlaneClaims.planesK_congr h lm _ b b' hb]

theorem claimJoin_congr (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : _root_.Fo.Pl → K)
    (kf kf' : ℕ → K) (hk : ∀ c, c < h.NC → kf c = kf' c) :
    claimJoin h lm jLK rs ν kf = claimJoin h lm jLK rs ν kf' := by
  unfold claimJoin
  simp only [val_joinK, AffK.val_ofConst]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun c hc => by rw [hk c (Finset.mem_range.1 hc)]

end

/-- **From the laws on decide and on the runs.** -/
theorem k3ClaimsGiveOut_of {S Cl : Type} (fork : S → Option Fork)
    (heard : S → Option Forest.Heard) (form : Cl → Aff) (calls : Array Call) (pub : Array Nat)
    (lid lm : ℕ) (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S)
    (objects planes join : ℕ → S → Except String (List Cl × S))
    (bit : S → ℕ → ℕ → Aff) (pin : S → ℕ → Aff) (keys : S → Array Aff)
    (hD : K3DecideHears fork heard calls pub lid decide)
    (hO : K3RunIsWorth fork heard form lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)))
    (hP : K3RunIsWorthAt fork heard form lm planes
      (fun s _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit s 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit s 1 col),
          Pin.countK g.shape lm fun col => val (pin s col)]))
    (hJ : K3RunIsWorthAt fork heard form lm join
      (fun s _ _ g jLK rsK ν val =>
        [claimJoin g.shape lm jLK rsK ν fun k => val ((keys s).getD k (Aff.ofConst zeroE))])) :
    K3ClaimsGiveOut fork heard form calls pub lid lm decide objects planes join bit pin keys := by
  intro L r hSh h5 hlm s s₁ F hF hS mk pl hmk hbc ds hM hA a τ cols hw hdec
  obtain ⟨F1, F', g, e1, e2, e3, _, hlaw⟩ := hD Cb.Gl.E Reading.gl lm s s₁ _ cols hw hdec
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨hSg, _, hI⟩ := hlaw hS
  have hg : g.shape = r.c.h := shapeOf_unique hSg hSh
  have hok : FoNums.ok r.c.h = true := by
    obtain ⟨h0, a0, a1, a2⟩ := hSh
    rw [a2]
    exact Cb.Fo.shape_ok a0 a1
  have hokg : FoNums.ok g.shape = true := by rw [hg]; exact hok
  obtain ⟨x, hx, hiff⟩ := k3OutIsClaimsR L r hok lm F.next h5 hlm mk pl hmk hbc ds hM hA a τ
  refine ⟨x, F', g, hx, e2, e3, hg, ?_⟩
  intro sO sP sJ clO clP clJ GO GP GJ H rO rP rJ lO lP lJ μ₀ entry hz hH
  -- the three runs' laws, at the ledger H
  obtain ⟨FO, fO, laO, szO⟩ := rO.later
  obtain ⟨nO, sO', runO, gO⟩ := rO.ran
  obtain ⟨GO', bO, _, _, _, _, vO⟩ := hO Cb.Gl.E Reading.gl g F.next (viewRounds ds τ) F' FO nO sO
    sO' clO rO.heard fO hI laO hokg szO runO
  obtain rfl : GO = GO' := Option.some.inj (gO.symm.trans bO)
  have wO := vO H lO (fun p => zext μ₀ (placeOf mk pl p)) entry
  obtain ⟨FP, fP, laP, szP⟩ := rP.later
  obtain ⟨nP, sP', runP, gP⟩ := rP.ran
  obtain ⟨GP', bP, _, _, _, _, vP⟩ := hP Cb.Gl.E Reading.gl g F.next (viewRounds ds τ) F' FP nP sP
    sP' clP rP.heard fP hI laP hokg szP runP
  obtain rfl : GP = GP' := Option.some.inj (gP.symm.trans bP)
  have wP := vP H lP (fun p => zext μ₀ (placeOf mk pl p)) entry
  obtain ⟨FJ, fJ, laJ, szJ⟩ := rJ.later
  obtain ⟨nJ, sJ', runJ, gJ⟩ := rJ.ran
  obtain ⟨GJ', bJ, _, _, _, _, vJ⟩ := hJ Cb.Gl.E Reading.gl g F.next (viewRounds ds τ) F' FJ nJ sJ
    sJ' clJ rJ.heard fJ hI laJ hokg szJ runJ
  obtain rfl : GJ = GJ' := Option.some.inj (gJ.symm.trans bJ)
  have wJ := vJ H lJ (fun p => zext μ₀ (placeOf mk pl p)) entry
  beta_reduce at wO wP wJ
  rw [hg] at wO wP wJ
  -- every value on the left is 0
  have zO : ∀ y ∈ (endsOf r.c.h lm F.next (viewRounds ds τ)).rows.map
      (rowRes fun p => zext μ₀ (placeOf mk pl p)), y = 0 := by
    rw [← wO]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c (by simp [hc])
  have zP : ∀ y ∈ clP.map (fun c => (form c).value Reading.gl
      (H.worldOf Reading.gl (fun j => zext μ₀ (placeOf mk pl (.mask j))) entry)), y = 0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c (by simp [hc])
  have zJ : ∀ y ∈ clJ.map (fun c => (form c).value Reading.gl
      (H.worldOf Reading.gl (fun j => zext μ₀ (placeOf mk pl (.mask j))) entry)), y = 0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact hz c (by simp [hc])
  rw [wP] at zP
  rw [wJ] at zJ
  have z1 := zP _ (List.mem_cons_self)
  have z2 := zP _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have z3 := zP _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have z4 := zJ _ (List.mem_cons_self)
  refine (hiff (fun c => AffK.ofConst (((keys sJ).getD c (Aff.ofConst zeroE)).value Reading.gl
    (H.worldOf Reading.gl (fun j => zext μ₀ (placeOf mk pl (.mask j))) entry))) μ₀ ?_).2 ?_
  · intro c hc
    rw [AffK.val_ofConst]
    exact hH.keys c hc
  · intro y hy
    unfold claimsOf at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact zO y hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · rw [claimLeaves_congr _ _ _ _ _ _ _ fun col hc => (hH.bit0 col hc).symm]
        exact z1
      · rw [claimBits_congr _ _ _ _ _ _ _ fun col hc => (hH.bit1 col hc).symm]
        exact z2
      · rw [Cb.Fo.PlaneClaims.countK_congr _ _ _ _ fun col hc => (hH.pin col hc).symm]
        exact z3
      · rw [claimJoin_congr _ _ _ _ _ _ _ fun c _ => AffK.val_ofConst _ _]
        exact z4

/-- **At the kind's own text**: K3.block's decide, its run "objects", planesRun and joinRun, for a
seat that reads back what it lays. -/
theorem k3ClaimsGiveOut {S Cl : Type} (seat : Desc.K3.Seat S Cl) (form : Cl → Aff)
    (hs : SeatFits seat form) (hk : SeatKeeps seat) (hr : Desc.K3.SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (lm : ℕ) (readers : Desc.K3.Readers S)
    (keys : S → Option (Array Aff)) :
    K3ClaimsGiveOut seat.fork seat.heard form p.calls p.pub p.lid lm
      (Desc.K3.block seat piece laid before p guests).decide (objectsRun seat)
      (Desc.K3.planesRun seat lm readers) (Desc.K3.joinRun seat keys) (bitOf readers)
      (pinOf readers) (keysOf keys) :=
  k3ClaimsGiveOut_of _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (k3DecideHears seat piece laid before p guests hk hr) (objects_worth seat form hs lm)
    (planes_worth seat form hs lm readers) (join_worth seat form hs lm keys)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3ClaimsGiveOut_of
#print axioms VerifiableInference.OnPublicFiles.k3ClaimsGiveOut
