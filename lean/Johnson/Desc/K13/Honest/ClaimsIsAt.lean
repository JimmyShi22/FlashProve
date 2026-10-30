-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ClaimsIsAt.lean: `ClaimsIs` (PileDefs.lean of this folder) AT A LAYERS' SITE
AND AT THE HEAD's, EACH FROM NAMED PREMISES. One definition with code; five premises' forms; and
conditional statements with their proofs. It stands on this folder's MergeLayersJoin.lean,
MergeRounds.lean, FoldCut.lean and the library alone.

`ClaimsIs` is asked of the verifier's own fold over the chain's first j + 1 sub-protocols. The way
from the fold to the decision of number j (`fold_to_decision`): `foldCutAt` (FoldCut.lean), then the
library's `stepOk` (Johnson/Desc/Sound/FoldHeardProofs.lean); kin in the library: `decidedAt`
(Sound/FoldStepsProofs.lean). The second, third and fourth clauses then come from `layers_join`
(MergeLayersJoin.lean) and `headMerge_at_chain` (MergeRounds.lean). THE FIRST CLAUSE IS A PREMISE,
in the form of a law that runs from the hearing's own return.
Main names, the layers:
  `layersGateAt P hp g`: a number of a round of the layers' own sub-protocol, written as a sum of
    five stretches: the premise `ClaimsFromHearing` is asked at prefixes from it on. What stands at
    that round is not said here. `layersGateAt_le`: it is at most `layersSigmaAt`.
  `LayersSite bs j p m lay`: THE SITE: number j is there; its decision returns only where that of
    the layers' own sub-protocol at the verifier's state (`blockAtS p`) does, with the same state;
    the site's batching round is `roundsAhead bs j + layersSigmaAt`; the layout is p's.
  `LayersFront bs start j Szd Tie tokOf`: THREE SENTENCES ON THE FOLD's STATE IN FRONT OF NUMBER j,
    where it has failed = none: its ledger has Szd; what the lookup returned is tied to the instance
    and the challenges in front by Tie; its tokens are tokOf of the instance. Szd, Tie, tokOf:
    letters.
  `ClaimsFromHearing p link a claims Szd Tie tokOf`: THE LAW ON THE CLAIMS: from every return of
    `hear engFl` at tokens tk, from a ledger with Szd, on a tape whose round number n has sampled
    the elements of challenge number n of a list ds of at least `layersGateAt` challenges; at a list
    h of a challenges with Tie; tokOf x = tk: at every prefix of ds of at least `layersGateAt`
    challenges: the parameter at h, then that prefix, returns the claims that the hearing hands the
    merge (`mergeClaims`).
  `claimsIs_layers`: **`ClaimsIs` at the site, at left := `leftLay`, from the three.**
Main names, the head:
  `HeadSite bs j P m lay`: number j is there; its decision returns only where `headMergeDecide P`
    does; the site's batching round is `roundsAhead bs j`; the layout is P's.
  `HeadClaimIs bs start j link claims asked`: the law on the claim: at the fold's state in front of
    number j, where it has failed = none and holds the reply asked, and stands in the head's segment
    with a claim laid: the parameter at the challenges in front returns just that claim.
  `claimsIs_head`: **`ClaimsIs` at the head's site, at left := `leftHead`, from the two.**

What is not claimed. Any of the five premises, at any chain. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.K13.Honest.MergeLayersJoin
import Johnson.Desc.K13.Honest.FoldCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork WsClaim WsLay)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.P1 (drawnOf)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks noDigest stepOk)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (decide_iff)
open VerifiableInference.Desc.First.Close (leftHead)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open Johnson.Desc.First.Walk (leftLay)

variable {Xi Cl : Type}

/-! ## From the fold to the decision -/

/-- **From the fold over the first j + 1 sub-protocols to the decision of number j**: the fold over
the first j returns a state sj and leaves the rounds from number `roundsAhead bs j` on; number j's
decision returns the fold's own last state from sj, on its own slice without the digests. -/
theorem fold_to_decision {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    (hb : bs[j]? = some b) {s₀ s : S} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (bs.take (j + 1)) s₀ rs cols = .ok (s, r, c)) :
    ∃ sj c₀ gs, foldBlocks 0 (bs.take j) s₀ rs cols = .ok (sj, rs.drop (roundsAhead bs j), c₀) ∧
      b.decide sj (((rs.drop (roundsAhead bs j)).take b.rounds.length).map noDigest) gs =
        .ok s := by
  have hlt : j < bs.length := (List.getElem?_eq_some_iff.1 hb).1
  have hb' : (bs.take (j + 1))[j]? = some b := by
    rw [List.getElem?_take_of_lt (Nat.lt_succ_self j)]
    exact hb
  obtain ⟨sj, sj', c₀, n, h1, h2, h3⟩ := foldCutAt 0 (bs.take (j + 1)) j b hb' s₀ rs cols _ h
  rw [take_take_le bs (Nat.le_succ j), roundsAhead_take bs (Nat.le_succ j)] at h1
  rw [roundsAhead_take bs (Nat.le_succ j)] at h2
  have hnil : (bs.take (j + 1)).drop (j + 1) = [] :=
    List.drop_eq_nil_of_le (List.length_take_le _ _)
  rw [hnil] at h3
  have e : (s, r, c) = (sj', _, _) := (Except.ok.inj h3).symm
  obtain rfl : s = sj' := congrArg Prod.fst e
  obtain ⟨gs, hd⟩ := stepOk h2
  exact ⟨sj, c₀, gs, h1, hd⟩

/-! ## A layers' site -/

/-- A number of a round of the layers' own sub-protocol, written as a sum of five stretches: the law
on the claims is asked at prefixes from it on. -/
def layersGateAt (P : Pub) (hp : HPlan2) (g : Nat) : Nat :=
  k0 g + 2 + (P.rd.muV + 5) + (P.y.h.lt + 3) + (P.y.h.lt + 4) + (hp.lamS + 3)

/-- It stands in front of the merge's batching round. -/
theorem layersGateAt_le (P : Pub) (hp : HPlan2) (g : Nat) :
    layersGateAt P hp g ≤ layersSigmaAt P hp g := by
  rw [layersSigmaAt_eq]
  unfold layersGateAt
  omega

/-- **THE SITE.** -/
structure LayersSite (bs : List (Block S Cl)) (j : Nat) (p : Par) (m : MergeSite) (lay : WsLay) :
    Prop where
  /-- number j is there -/
  there : ∃ b, bs[j]? = some b
  /-- its decision returns only where `blockAtS p`'s does, with the same state -/
  back : ∀ b, bs[j]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
    (blockAtS p).decide s rs gs = .ok s'
  /-- the number of the site's batching round -/
  sigma : m.sigmaAt = roundsAhead bs j + layersSigmaAt p.P p.hp p.g
  /-- the layout -/
  lay : lay = p.P.wsLay

/-- **THREE SENTENCES ON THE FOLD's STATE IN FRONT OF NUMBER j.** Szd, Tie, tokOf: letters. -/
structure LayersFront (bs : List (Block S Cl)) (start : Xi → S) (j : Nat) (Szd : Fork → Prop)
    (Tie : Xi → List Fmt.Drawn → OnBytes.Model.Forest.Heard → Prop) (tokOf : Xi → Array Nat) :
    Prop where
  /-- its ledger -/
  sized : ∀ x rs cols sj c y,
    foldBlocks 0 (bs.take j) (start x) rs cols = .ok (sj, rs.drop (roundsAhead bs j), c) →
    sj.failed = none → sj.here = .lay y → Szd y.F
  /-- what the lookup returned -/
  tie : ∀ x rs cols sj c y fo,
    foldBlocks 0 (bs.take j) (start x) rs cols = .ok (sj, rs.drop (roundsAhead bs j), c) →
    sj.failed = none → sj.here = .lay y → y.fo = some fo →
    Tie x ((rs.take (roundsAhead bs j)).map (·.drawn)) fo
  /-- its tokens -/
  tokens : ∀ x rs cols sj c,
    foldBlocks 0 (bs.take j) (start x) rs cols = .ok (sj, rs.drop (roundsAhead bs j), c) →
    sj.failed = none → tokOf x = sj.tokv

/-- **THE LAW ON THE CLAIMS, FROM THE HEARING's OWN RETURN.** a: how many challenges stand in front
of the sub-protocol. -/
def ClaimsFromHearing (p : Par) (link a : Nat) (claims : SiteClaims Xi) (Szd : Fork → Prop)
    (Tie : Xi → List Fmt.Drawn → OnBytes.Model.Forest.Heard → Prop) (tokOf : Xi → Array Nat) :
    Prop :=
  ∀ (x : Xi) (tk : Array Nat) (fo : OnBytes.Model.Forest.Heard) (F G : Fork) (t u : Tape) (o : Own)
    (ds h : List Fmt.Drawn) (cl : Array WsClaim) (n : Nat),
    hear engFl { p.P with tokv := tk } p.hp p.g fo F t = some (o, G, u) → Szd F →
    (∀ (i : ℕ) (d : Fmt.Drawn), ds[i]? = some d → drawnOf (t.drop i) = d.elems.map E.ofTriple) →
    layersGateAt p.P p.hp p.g ≤ ds.length → h.length = a → Tie x h fo → tokOf x = tk →
    layersGateAt p.P p.hp p.g ≤ n → mergeClaims { p.P with tokv := tk } p.g o = some cl →
    claims link x (h ++ ds.take n) = some cl

/-- **`ClaimsIs` AT A LAYERS' SITE, FROM THE THREE.** -/
theorem claimsIs_layers {bs : List (Block S Cl)} {start : Xi → S} {j : Nat} {m : MergeSite}
    {lay : WsLay} {p : Par} {claims : SiteClaims Xi} {asked : Xi → E} {Szd : Fork → Prop}
    {Tie : Xi → List Fmt.Drawn → OnBytes.Model.Forest.Heard → Prop} {tokOf : Xi → Array Nat}
    (hS : LayersSite bs j p m lay) (hF : LayersFront bs start j Szd Tie tokOf)
    (hC : ClaimsFromHearing p m.link (roundsAhead bs j) claims Szd Tie tokOf) :
    ClaimsIs bs start j m lay leftLay claims asked false := by
  intro x rs cols s r c hfold hfail _
  obtain ⟨b, hb⟩ := hS.there
  obtain ⟨sj, c₀, gs, h1, hd⟩ := fold_to_decision hb hfold
  have hd' := hS.back b hb _ _ _ _ hd
  obtain ⟨y, fo, G, o, cl, sigma, hy, hfo, _, hh, hD, hlen, hsplit, hcl, _, hdr, hleft, hrec⟩ :=
    layers_join hd'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hR⟩ := heard_reads hd'
  have hf0 : sj.failed = none := by
    rw [← hR.failed]
    exact hfail
  have hg := layersGateAt_le p.P p.hp p.g
  have ha : ((rs.take (roundsAhead bs j)).map (·.drawn)).length = roundsAhead bs j := by
    simp only [List.length_map, List.length_take, List.length_drop] at hlen ⊢
    omega
  refine ⟨cl, sigma, o.wo, ?_, ?_, hleft, ?_⟩
  · rw [hS.sigma, hsplit]
    exact hC x sj.tokv fo y.F G _ [] o _ _ cl _ hh (hF.sized x rs cols sj c₀ y h1 hf0 hy) hD
      (by omega) ha (hF.tie x rs cols sj c₀ y fo h1 hf0 hy hfo) (hF.tokens x rs cols sj c₀ h1 hf0)
      hg hcl
  · rw [hS.sigma, hS.lay]
    exact hdr
  · rw [hS.lay]
    exact hrec

/-! ## The head's site -/

/-- **THE HEAD's SITE.** -/
structure HeadSite (bs : List (Block S Cl)) (j : Nat) (P : HeadMergeP) (m : MergeSite)
    (lay : WsLay) : Prop where
  /-- number j is there -/
  there : ∃ b, bs[j]? = some b
  /-- its decision returns only where `headMergeDecide P` does, with the same state -/
  back : ∀ b, bs[j]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
    headMergeDecide P s rs = .ok s'
  /-- the number of the site's batching round -/
  sigma : m.sigmaAt = roundsAhead bs j
  /-- the layout -/
  lay : lay = P.lay

/-- **THE LAW ON THE HEAD's CLAIM**, at the fold's state in front of number j. -/
def HeadClaimIs (bs : List (Block S Cl)) (start : Xi → S) (j link : Nat) (claims : SiteClaims Xi)
    (asked : Xi → E) : Prop :=
  ∀ x rs cols sj c o claim,
    foldBlocks 0 (bs.take j) (start x) rs cols = .ok (sj, rs.drop (roundsAhead bs j), c) →
    sj.failed = none → sj.out.reply = some (asked x) → sj.here = .head o →
    o.claim = some claim →
    claims link x ((rs.take (roundsAhead bs j)).map (·.drawn)) = some #[claim]

/-- **`ClaimsIs` AT THE HEAD's SITE, FROM THE TWO.** -/
theorem claimsIs_head {bs : List (Block S Cl)} {start : Xi → S} {j : Nat} {m : MergeSite}
    {lay : WsLay} {P : HeadMergeP} {claims : SiteClaims Xi} {asked : Xi → E}
    (hS : HeadSite bs j P m lay) (hC : HeadClaimIs bs start j m.link claims asked) :
    ClaimsIs bs start j m lay leftHead claims asked true := by
  intro x rs cols s r c hfold hfail hreply
  obtain ⟨b, hb⟩ := hS.there
  obtain ⟨sj, c₀, gs, h1, hd⟩ := fold_to_decision hb hfold
  have hd' := hS.back b hb _ _ _ _ hd
  obtain ⟨o, _, claim, wo, sigma, ho, hc, _, _, hleft, hdr, hrec⟩ := headMerge_at_chain hd'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := (decide_iff P sj s _).1 hd'
  have hf0 : sj.failed = none := by
    rw [e] at hfail
    exact hfail
  have hr0 : sj.out.reply = some (asked x) := by
    have q := hreply rfl
    rw [e] at q
    exact q
  refine ⟨#[claim], sigma, wo, ?_, ?_, hleft, ?_⟩
  · rw [hS.sigma]
    exact hC x rs cols sj c₀ o claim h1 hf0 hr0 ho hc
  · rw [hS.sigma, hS.lay]
    exact hdr
  · rw [hS.lay]
    exact hrec

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.fold_to_decision
#print axioms VerifiableInference.Desc.K13.Honest.layersGateAt_le
#print axioms VerifiableInference.Desc.K13.Honest.claimsIs_layers
#print axioms VerifiableInference.Desc.K13.Honest.claimsIs_head
