-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/StaysAtFlat.lean: THE PREMISE `stays` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN: SHOWN AT THE FOUR HEARING SUB-PROTOCOLS BETWEEN A LAYERS' SEGMENT's MERGE AND ITS BATCHING;
SO AT A LAYERS' SITE THE PREMISE IS NARROWED FROM NINE NUMBERS TO FIVE. AT THE HEAD's SITE NOTHING
OF IT IS SHOWN IN THIS FILE: its five numbers are all left here. (The closing's three of the five,
at every site: ClosersStay.lean of this folder.) Statements with their proofs.

THE LIBRARY HAS BOTH HALVES. The places by number: `IM.k1_reads_of`, `IM.k1_digits_of`
(Johnson/IMR/K1Scope.lean), `IM.k8_alone` (IMR/K8Seat.lean), `IM.k3_of` (IMR/K3Seat.lean),
`IM.hear_at_flat`, `IM.flatIx_scope`, `IM.yes_alone`. That these texts' decisions leave what a
layers' segment's own rounds returned: `SameOwn`, `sameOwn_stretch`, `quietLayers_sameOwn`
(Johnson/Desc/First/Link/Law/OwnStay.lean). Johnson/Desc/First/Link/Law/StretchBack.lean joins the
two for states that are REACHED (`back_of`, `stretch_back_layers`; at `SameOwn`: `own_from_k4`,
OwnStay.lean: the nearest kin: the same stretch, the same reading, of no named rounds). Here the
same join is made AT THE DECISION, step for step after that file's proofs, general in the relation
as there (`StretchKeeps`).
Main names. In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the
proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the
first chain):
  `decides_at_flat`: the tool: `back_of` at the decision.
  `stretch_decides_layers`: **for g < 12: every decision of a number 28 g + 5 … 28 g + 8 keeps R**,
    for every R with `StretchKeeps R` that the layers' step without a round keeps too.
  `leftLay_eq_own`: `leftLay` is read off `S.own?`. `stays_hear_layers`: **so these decisions leave
    `leftLay`.**
  `pileWalk_at_desc_five`, `pileIs_at_desc_five`: **`PileWalk`, and so `PileIs`, as in
    PileWalkAtDesc.lean of this folder, with `stays` asked at the five numbers in front of a site's
    laying alone** (c − 5 … c − 1): the batching, the sub-protocol behind it, and the closing's
    three: at a layers' site 28 g + 9 … 28 g + 13, at the head's 347 … 351.

What is not claimed. `stays` at these five numbers. Kin in the library: laws on two functions that
write the state there (`leftOf_set`, Johnson/Desc/First/Link/Law/DoorBlind.lean; `leftOf_putRec`,
Johnson/Desc/First/Close/Law/EPubAtK10.lean): they speak of `leftOf`, and leftOf t = leftOf s gives
leftLay t = leftLay s only where the arm of `here` stays. The library has laws on the decisions
there and on the runs of claims that the batching and the sub-protocol behind it call:
`K9.closeOf_keeps`, `K9.batch_keeps` (Johnson/Desc/First/Batch/Law/Keeps.lean),
`TailClaims.Law.claimsInBy_keeps` (Johnson/Desc/First/TailClaims/K8SitsFront.lean), `run_layers`,
`run_head` (Johnson/Desc/First/Link/Law/RunRel.lean): the first is called in ClosersStay.lean of
this folder. `sites`; `reach`. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.PileWalkAtDesc
import Johnson.Desc.First.Link.Law.OwnStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.LinkJoin (StretchKeeps SameOwn sameOwn_stretch quietLayers_sameOwn
  k8Ix k8_kind_at)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs ClaimsIs SiteClaims FoldReaches
  pileBySites pileIs_of_claimsIs)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile (Cl)

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {R : S → S → Prop}

/-- **The tool**: where the hearing sub-protocol number i of segment l is a text, alone, whose
decision keeps R: so does the decision of number 14 l + i + 2 of the chain's list. -/
theorem decides_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {l i : ℕ} (hl : l ≤ 24)
    {Lk : Link S Cl} {b b' : Block S Cl} {name : String} {a : Place}
    (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (hA : IM.LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7)
    (hD : Decides R b') (blk : Block S Cl) (hb : c.blocksInOrder[14 * l + i + 2]? = some blk) :
    Decides R blk := by
  intro s rs gs t hd
  have hf : c.blocksInOrder[14 * l + i + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O hl i]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = blk := Option.some.inj (hf.symm.trans hb)
  exact hD s rs gs t ((IM.yes_alone hA hk s t rs gs).1 hd).1

/-- **The four hearing sub-protocols between the layers' own and the batching keep R**, by their
numbers. -/
theorem stretch_decides_layers (K : StretchKeeps R)
    (hq : ∀ P : VerifiableInference.Desc.K8.ReadsQuiet.PG,
      Decides R (VerifiableInference.Desc.K8.ReadsQuiet.layers P))
    (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) (k : ℕ)
    (h1 : 28 * g + 5 ≤ k) (h2 : k ≤ 28 * g + 8) (blk : Block S Cl)
    (hb : c.blocksInOrder[k]? = some blk) : Decides R blk := by
  have n24 : 2 * g ≠ 24 := by omega
  have i3 : IM.k3Ix (2 * g) true = 6 := by
    show (if true = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 6
    simp [n24]
  have i1 : IM.k1Ix (2 * g) true = 5 := by
    show (if true = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 5
    simp [n24]
  have i8 : k8Ix (2 * g) = 4 := by
    show 4 + (if 2 * g = 24 then 1 else 0) = 4
    simp [n24]
  have i0 : IM.k1Ix (2 * g) false = 3 := by
    show (if false = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 3
    simp [n24]
  have hk0 : ∀ X, Bs.G₀.built[2 * g]? = some X → X.kind = 0 := by
    intro X hX
    obtain ⟨m, -, fm, km, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
    rw [← Option.some.inj (fm.symm.trans hX)]
    exact km
  have hcase : k = 14 * (2 * g) + 3 + 2 ∨ k = 14 * (2 * g) + 4 + 2 ∨ k = 14 * (2 * g) + 5 + 2 ∨
      k = 14 * (2 * g) + 6 + 2 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, _, e4⟩ :=
      IM.k1_reads_of hS hR O (2 * g) (by omega)
    rw [i0] at e2
    refine decides_at_flat hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) ?_ blk hb
    intro s rs gs t hd
    have hd' : (IM.k1Reads Z Bs.G₀ (2 * g) Xl (IM.k1Ix (2 * g) false + 1) reads).decide s rs gs =
        .ok t := hd
    unfold IM.k1Reads at hd'
    obtain ⟨m, a1, a2⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
    have q1 : R s m := K.k1 _ _ _ _ _ _ s _ _ m a1
    have q2 : R m t := by
      unfold IM.k1Quiet at a2
      rcases VerifiableInference.Desc.First.K8.Ready.quiet_arms Bs.G₀ (2 * g) Xl _ _ _ _ a2 with
        ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
      · rw [hk0 Xl hX] at k1
        exact absurd k1 (fun h => nomatch h)
      · rcases hc with ⟨_, hp, _, hq'⟩ | ⟨k2, _⟩
        · exact hq _ m _ _ t hq'
        · rw [hk0 Y hY] at k2
          exact absurd k2 (fun h => nomatch h)
    exact K.trans _ _ _ q1 q2
  · obtain ⟨Lk, b, Xl, e1, e2, _, _, e4⟩ := IM.k8_alone O (2 * g) (IM.subAt (2 * g))
      (IM.subs_scope hS hR O (2 * g) (by omega)) (k8Ix (2 * g)) (k8_kind_at (2 * g)) (by
        rw [i8]
        omega)
    rw [i8] at e2
    exact decides_at_flat hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) (K.k8 _) blk hb
  · obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, _, _, e4⟩ :=
      IM.k1_digits_of hS hR O (2 * g) (by omega)
    rw [i1] at e2
    exact decides_at_flat hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
      (fun s rs gs s' hd => K.k1 _ _ _ _ _ _ s rs gs s' hd) blk hb
  · obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O (2 * g) (by omega) true
    rw [i3] at e2
    exact decides_at_flat hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
      (K.k3 _ _ _ _ _ _ e3) blk hb

/-- What the merge left at a layers' segment is read off what the segment's own rounds returned. -/
theorem leftLay_eq_own (s : S) : leftLay s = s.own?.map (·.wo) := by
  unfold leftLay VerifiableInference.Desc.First.S.own?
  cases s.here <;> rfl

/-- **`stays` AT THE FOUR**: every decision of a number 28 g + 5 … 28 g + 8 leaves what the merge
left. -/
theorem stays_hear_layers (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) (k : ℕ)
    (h1 : 28 * g + 5 ≤ k) (h2 : k ≤ 28 * g + 8) (blk : Block S Cl)
    (hb : c.blocksInOrder[k]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    leftLay t = leftLay s := by
  have q : SameOwn s t := stretch_decides_layers sameOwn_stretch quietLayers_sameOwn hS hR O hg k
    h1 h2 blk hb s rs gs t hd
  rw [leftLay_eq_own, leftLay_eq_own, q]

/-- **THE MEMBER OF `PileWalk`, WITH `stays` ASKED AT FIVE NUMBERS A SITE ALONE**: the batching, the
sub-protocol behind it, and the closing's three. -/
theorem pileWalk_at_desc_five (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z, ClaimsIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) σ.j σ.m
      Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileWalk c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n Z.p.X.layers.wsLay Z.first.lin
      (sitesAt c Z) claims asked VerifiableInference.Desc.First.S.rows := by
  refine pileWalk_at_desc hS hR O hp pubOf n claims asked hsites hreach ?_
  intro σ hσ k blk hj hc hb x rs cols s cl hF R gs t hd
  by_cases h5 : σ.c ≤ k + 5
  · exact hfive σ hσ k blk h5 hc hb x rs cols s cl hF R gs t hd
  · rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
    · have a1 : 28 * g + 4 < k := hj
      have a2 : ¬ 28 * g + 14 ≤ k + 5 := h5
      exact stays_hear_layers hS hR O hg k (by omega) (by omega) blk hb s t R gs hd
    · have a1 : 346 < k := hj
      have a2 : ¬ 352 ≤ k + 5 := h5
      omega

/-- **So `PileIs` there.** -/
theorem pileIs_at_desc_five (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {Xi : Type} (pubOf : Xi → ProofFile.InstPub) (n : Nat)
    (claims : SiteClaims Xi) (asked : Xi → E)
    (hsites : ∀ σ ∈ sitesAt c Z, ClaimsIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) σ.j σ.m
      Z.p.X.layers.wsLay σ.left claims asked σ.head)
    (hreach : ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ n)
    (hfive : ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    PileIs c.blocksInOrder (fun x => ProofFile.startS Z (pubOf x)) 355 n
      (pileBySites Z.p.X.layers.wsLay Z.first.lin ((sitesAt c Z).map (·.m)) claims) asked :=
  pileIs_of_claimsIs
    (pileWalk_at_desc_five hS hR O hp pubOf n claims asked hsites hreach hfive)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.decides_at_flat
#print axioms ProofFile.Honest.K13.stretch_decides_layers
#print axioms ProofFile.Honest.K13.leftLay_eq_own
#print axioms ProofFile.Honest.K13.stays_hear_layers
#print axioms ProofFile.Honest.K13.pileWalk_at_desc_five
#print axioms ProofFile.Honest.K13.pileIs_at_desc_five
