-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileWalkAtFlat.lean: WHO WRITES THE ROWS ON THE TABLE, BY NUMBER;
AND A MEMBER OF `PileWalk` (Johnson/Desc/K13/Honest/PileInduction.lean: the twelve premises of the
induction for the pile's filler) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN IN LEAN, AT
THE BORDER 355, IN FRONT OF K13's BATCHING: SIX OF THE TWELVE ARE SHOWN, SIX ARE PREMISES.
Conditional statements with their proofs.

Under: In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the proof
file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the first
chain); and hp: EVERY SUB-PROTOCOL OF THE CHAIN's LIST PASSES ITS OWN TEST ON THE PLAN (∀ b ∈
c.blocksInOrder, b.planOk = true): public.
Main names:
  `siteC_iff`: the test `siteC` (PileLengthReach.lean of this folder) is true just at the numbers c
    of the sites of `sitesAt c Z` (SitesAtFlat.lean).
  `rows_by_number`: **WHO WRITES THE ROWS, BY NUMBER, ON ITS OWN**: of every decision of a number k
    below 355: either k is the number c of a site σ of the list and the verifier's own row of what
    σ.left reads off the state in front (`rowBy`) is laid at the rows' end; or k is no site's c and
    the rows stay. By `cleared_by_sort` (ClearedBySort.lean) and `flat_stays` (PileAtFlat.lean).
  `pileWalk_at_flat`: **`PileWalk` at c.blocksInOrder, b := 355, the one layout, the shape of the test,
    `sitesAt c Z`, rd := `S.rows`**, at any start. SHOWN: `inList` (the library's `IM.places_scope`,
    `IM.places_len`) · `order` · `inside` · `clears` · `quiet` (both by `rows_by_number`) · `mark`
    (`layersSite_at_flat`, `headSite_at_flat`). PREMISES, each as `PileWalk` asks it: `sites` ·
    `reach` · `stays` · `reply` (at the numbers 347 to 354) · `empty` · `atEnd`.
  `pileIs_at_flat`: **so `PileIs` there at the filler over these sites**, under the same.

What is not claimed. Any of the six premises; that the six can be met together. That hp holds at any
public files (see ClearedBySort.lean). Nothing at another border. It is none of the library's goals.
Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.PileInduction
import Johnson.Desc.ProofFile.Honest.K13.ClearedBySort
import Johnson.Desc.ProofFile.Honest.K13.SitesAtFlat
import Johnson.Desc.ProofFile.Honest.K13.PileLengthReach
import Johnson.IMR.PlacesScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs ClaimsIs SiteClaims MergeSite
  FoldReaches pileBySites pileIs_of_claimsIs)
open ProofFile (Cl)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Law (rowBy)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf frameAt zeroAt pubOf rowOf headFrame_fv
  frameAt_att frameAt_lay zeroAt_some)
open Johnson.Desc.First.Walk.Props (planAtt_fv planLay_fv planLayZero_fv)

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The test `siteC` (PileLengthReach.lean) is true just at the numbers c of the list's sites. -/
theorem siteC_iff (c : Chain S Cl) (Z : ProofFile.Pub) (k : Nat) :
    siteC k = true ↔ ∃ σ ∈ sitesAt c Z, σ.c = k := by
  unfold siteC
  rw [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨g, hg, e⟩ | e)
    · exact ⟨layerSite c Z g, mem_sitesAt.2 (Or.inl ⟨g, List.mem_range.1 hg, rfl⟩), eq_of_beq e⟩
    · exact ⟨headSite c Z, mem_sitesAt.2 (Or.inr rfl), (eq_of_beq e).symm⟩
  · rintro ⟨σ, hσ, e⟩
    rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · exact Or.inl ⟨g, List.mem_range.2 hg, beq_iff_eq.2 e⟩
    · exact Or.inr (beq_iff_eq.2 e.symm)

/-- **WHO WRITES THE ROWS ON THE TABLE, BY NUMBER**: of every decision of a sub-protocol of a number
k below 355: either k is the number c of a site σ of the list, and the verifier's own row of what
σ.left reads off the state in front is laid at the rows' end; or k is no site's c, and the rows
stay. -/
theorem rows_by_number (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) (hk : k < 355) (blk : Block S Cl)
    (hb : c.blocksInOrder[k]? = some blk) (s t : S) (R : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s R gs = .ok t) :
    (∃ σ ∈ sitesAt c Z, σ.c = k ∧
        ∃ r, rowBy σ.left Z.p.X.layers.wsLay σ.m.ncl Z.first.lin s = some r ∧
          t.rows = s.rows ++ [r]) ∨
      ((∀ σ ∈ sitesAt c Z, σ.c ≠ k) ∧ t.rows = s.rows) := by
  have notSite : ∀ l, l < 25 → l % 2 = 1 → ∀ σ ∈ sitesAt c Z, σ.c ≠ 14 * l + IM.nAt l + 7 := by
    intro l hl ho σ hσ e
    have hn : IM.nAt l = 7 := by
      unfold IM.nAt
      rw [if_neg (by omega)]
    rcases mem_sitesAt.1 hσ with ⟨g, _, rfl⟩ | rfl
    · have e' : 28 * g + 14 = 14 * l + IM.nAt l + 7 := e
      omega
    · have e' : 352 = 14 * l + IM.nAt l + 7 := e
      omega
  by_cases hc : ∃ l < 25, k = 14 * l + IM.nAt l + 7
  · obtain ⟨l, hl, rfl⟩ := hc
    obtain ⟨Xl, hX, h⟩ := cleared_by_sort hS hR O hp l hl blk hb
    have hn : nclAt Z l = Xl.NCL := by
      unfold nclAt
      rw [hX]
      rfl
    rcases h with ⟨rfl, hq⟩ | ⟨he, h24, hq⟩ | ⟨ho, hq⟩
    · refine Or.inl ⟨headSite c Z, mem_sitesAt.2 (Or.inr rfl), rfl, ?_⟩
      show ∃ r, rowBy leftHead _ (nclAt Z 24) _ s = some r ∧ _
      rw [hn]
      exact hq s t R gs hd
    · have e2 : 2 * (l / 2) = l := by omega
      refine Or.inl ⟨layerSite c Z (l / 2), mem_sitesAt.2 (Or.inl ⟨l / 2, by omega, rfl⟩), ?_, ?_⟩
      · show 28 * (l / 2) + 14 = 14 * l + IM.nAt l + 7
        unfold IM.nAt
        rw [if_neg h24]
        omega
      · show ∃ r, rowBy leftLay _ (nclAt Z (2 * (l / 2))) _ s = some r ∧ _
        rw [e2, hn]
        exact hq s t R gs hd
    · exact Or.inr ⟨notSite l hl ho, hq s t R gs hd⟩
  · refine Or.inr ⟨fun σ hσ e => hc ?_,
      (flat_stays hS hR O k blk hb hk (fun l hl e => hc ⟨l, hl, e⟩) s t R gs hd).1⟩
    rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · refine ⟨2 * g, by omega, ?_⟩
      have e' : 28 * g + 14 = k := e
      unfold IM.nAt
      rw [if_neg (by omega)]
      omega
    · exact ⟨24, by decide, e.symm⟩

/-- **A MEMBER OF `PileWalk` AT THE PROOF FILE's OWN FIRST CHAIN**, at the border 355 (in front of
K13's batching), at the reading `S.rows`, where every sub-protocol of the chain passes its test on
the plan. Six of the twelve premises are shown; six are premises here, each as `PileWalk` asks
it. -/
theorem pileWalk_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (start : Xi → S) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z,
      ClaimsIs c.blocksInOrder start σ.j σ.m Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hstays : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.j < k → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s)
    (hreply : ∀ k blk, 346 < k → k < 355 → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → t.out.reply = s.out.reply)
    (hempty : ∀ x, (start x).rows = [])
    (hend : ∀ x rs cols s r cl, foldBlocks 0 (c.blocksInOrder.take 355) (start x) rs cols = .ok (s, r, cl) →
      s.failed = none → s.rows = s.out.pending) :
    PileWalk c.blocksInOrder start 355 n Z.p.X.layers.wsLay Z.first.lin (sitesAt c Z) claims asked
      S.rows where
  inList := by
    have hlen : c.blocksInOrder.length = 358 := by
      rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]
    omega
  sites := hsites
  order := sitesAt_order c Z
  inside := by
    intro σ hσ
    rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · exact ⟨by show 28 * g + 4 < 28 * g + 14; omega, by show 28 * g + 14 < 355; omega⟩
    · exact ⟨by show 346 < 352; omega, by show 352 < 355; omega⟩
  reach := hreach
  stays := hstays
  clears := by
    intro σ hσ blk hb x rs cols s cl _ R gs t hd
    have hk : σ.c < 355 := by
      rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
      · show 28 * g + 14 < 355
        omega
      · show 352 < 355
        omega
    rcases rows_by_number hS hR O hp σ.c hk blk hb s t R gs hd with ⟨τ, hτ, e, h⟩ | ⟨hne, _⟩
    · obtain rfl : τ = σ := by
        rcases mem_sitesAt.1 hτ with ⟨g, _, rfl⟩ | rfl <;>
          rcases mem_sitesAt.1 hσ with ⟨g', _, rfl⟩ | rfl
        · have e' : 28 * g + 14 = 28 * g' + 14 := e
          obtain rfl : g = g' := by omega
          rfl
        · have e' : 28 * g + 14 = 352 := e
          omega
        · have e' : 352 = 28 * g' + 14 := e
          omega
        · rfl
      exact h
    · exact absurd rfl (hne σ hσ)
  quiet := by
    intro k blk hk hne hb x rs cols s cl _ R gs t hd
    rcases rows_by_number hS hR O hp k hk blk hb s t R gs hd with ⟨τ, hτ, e, _⟩ | ⟨_, h⟩
    · exact absurd e (hne τ hτ)
    · exact h
  mark := by
    intro σ hσ blk hb x rs cols s cl _ R gs t hd
    rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · obtain ⟨_, _, _, _, _, hm, _⟩ := layersSite_at_flat hS hR O g hg
      exact hm blk hb s R gs t hd
    · exact (headSite_at_flat hS hR O).1 blk hb s R gs t hd
  reply := by
    intro σ hσ hh k blk hj hk hb
    rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · cases hh
    · exact hreply k blk hj hk hb
  empty := hempty
  atEnd := hend

/-- **So `PileIs` there, at the filler over these sites**, under the same premises. -/
theorem pileIs_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (start : Xi → S) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z,
      ClaimsIs c.blocksInOrder start σ.j σ.m Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hstays : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.j < k → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s)
    (hreply : ∀ k blk, 346 < k → k < 355 → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → t.out.reply = s.out.reply)
    (hempty : ∀ x, (start x).rows = [])
    (hend : ∀ x rs cols s r cl, foldBlocks 0 (c.blocksInOrder.take 355) (start x) rs cols = .ok (s, r, cl) →
      s.failed = none → s.rows = s.out.pending) :
    PileIs c.blocksInOrder start 355 n
      (pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims) asked :=
  pileIs_of_claimsIs
    (pileWalk_at_flat hS hR O hp start n claims asked hsites hreach hstays hreply hempty hend)

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.siteC_iff
#print axioms ProofFile.Honest.K13.rows_by_number
#print axioms ProofFile.Honest.K13.pileWalk_at_flat
#print axioms ProofFile.Honest.K13.pileIs_at_flat
