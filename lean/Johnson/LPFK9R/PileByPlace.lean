-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/PileByPlace.lean:
A TOOL, GENERAL IN A SENTENCE P ON THE VERIFIER's STATE: "WHO WRITES THE PILE", BY
POSITION: for a sentence that link 0's "opened" keeps only where no row lies on the table.
WHY. The rule PileLaw (Johnson/LTPileR/PileSeat.lean) asks that P rides over link 0's "opened"
AT EVERY STATE. That step writes the index masks' number and never reads the old one: so a sentence
that ties the rows on the table to that number does not ride over it where a row lies. In the IOP's
own first chain that step runs once, in sub-protocol number 2, and no row lies there. Here that is
spent: by the walk over the 358 sub-protocols (flat_cases, Johnson/IMR/FlatCases.lean)
and "the pile stays" (PileStays, Johnson/Desc/First/Pile/PileMakers.lean) at every maker.
  PileLawZ P        same, push, batch as in PileLaw; zero: ASKED ONLY WHERE NO ROW LIES.
  seatKeeps_pile    every maker of the seat but the links' frames' rows leaves the pile.
  lot_pile, lot_rides   so does each lot's sub-protocol that is of a kind (K13's batching: P rides).
  frame_but         a row of the links' frames: "cleared": P rides; "opened": P rides at every link
                    but link 0, and at link 0 where no row lies.
  hear_runs_pile    the runs of claims of a link's hearing sub-protocols.
  flat_rides        in the goals' scope: over an accepting decision of sub-protocol number k of the
                    flat list P rides, if k is not 2 or no row lies.
  flat_rows         numbers 0 and 1 leave the rows.
  fold_ix           the fold's rule for a sentence that may read the number of the border.
  fold_rides        **IN SCOPE: P AT EVERY STATE THAT A FOLD OVER A FRONT STRETCH OF THE FIRST CHAIN
                    RETURNS, FROM A START THAT MEETS P AND HAS NO ROW.** No test on the list of
                    rounds is asked.
What is not claimed. No sentence is shown to meet PileLawZ here. Nothing on soundness.

-/
import Johnson.IMR.FlatCases
import Johnson.IMR.LinkRest
import Johnson.LTPileR.PileSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl Lot Ground)
open Johnson.Desc.First.Walk
open Meaning.K2

/-- **What is asked of a sentence P.** -/
structure PileLawZ (P : S → Prop) : Prop where
  /-- over a step that leaves the rows on the table, the index masks' number and the stand -/
  same : ∀ s s', PileStays s s' → P s → P s'
  /-- link 0's "opened", WHERE NO ROW LIES -/
  zero : ∀ (Q : LayPar) (fvs : List Bool) (kCol : Nat) (s t : S),
    openLayZero Q fvs kCol s = .ok t → s.rows = [] → P s → P t
  /-- "cleared": it lays a row at the pile's end -/
  push : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (lay : WsLay) (lin : Params.LinShape), Fn (Rides P) (clearWith X counts left
      fun masks w claims os => Pend.pendingRowO lay masks w claims lin os)
  /-- kind K13's batching: the pile becomes the one row -/
  batch : ∀ p : K13.Where, Decides (Rides P) (K13.atM3 (Cl := Unit) p)

/-- **Every maker of the seat but the frames' rows leaves the pile.** -/
theorem seatKeeps_pile : SeatKeeps PileStays (fun _ => False) where
  refl := pile_refl
  trans := pile_trans
  frames := fun hB => False.elim hB
  k1First := fun q gp _ => firstAtS_pile q gp
  k1Later := fun q gp l p m a _ => laterAt_pile q gp l p m a
  reads := fun h => readsQuietAt_pile h
  k3 := fun c r X cs' sh' a _ h => theStated_pile c r X cs' sh' a h
  k4 := fun p => blockAtC_pile p
  k5 := fun W l g bf _ h => k5AtN_pile W l g bf h
  k6 := fun h => seatedClaims_pile h
  k7 := fun W l => k7Of_pile W l
  k8 := fun p => k8Whole_pile p
  k11 := fun Q => headMerge11_pile Q
  closeOf := fun p Q b hb => closeOf_pile p Q b hb
  batch := fun p _ hf => batch_over pile_trans (fun _ _ h => h) p hf
  k2 := fun p _ => k2_pile p
  front := fun tl => headFrontQ_pile tl
  openQ := fun Q _ => headOpenQ_pile Q
  finFront := finishFrontQ_pile
  finBehind := finishBehindQ_pile

/-- **A lot's sub-protocol of a kind other than K13 leaves the pile.** -/
theorem lot_pile (Z : ProofFile.Pub) (h0 : Z.P.firstTree = 0) (G : Ground) {L : Lot}
    (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ L.blocks G)
    (hf : b.place.kind ≠ KindName.frame) (h13 : b.place.kind ≠ KindName.K13) :
    Whole PileStays b := by
  have H := seatKeeps_pile
  unfold ProofFile.onlineFirstChainBlockTables at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h
  · exact absurd (IM.kind_frames Z G b hb) hf
  · exact (k1Pure_keeps H Z h0 G).1 b hb
  · exact (k2Pure_keeps H Z h0 G fun _ _ _ => trivial).1 b hb
  · exact (k3Lot_keeps H Z G).1 b hb
  · exact (k4Lot_keeps H Z G).1 b hb
  · exact (k5LotN_keeps H Z G).1 b hb
  · exact (k8Lot_keeps H Z G).1 b hb
  · exact (k9Ninth_keeps H Z G).1 b hb
  · exact (k11Lot_keeps H Z G).1 b hb
  · rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
      obtain rfl := List.mem_singleton.1 h₀
      exact retype_whole (atFinish_pile _)
    · exact nomatch hb
  · exact absurd (IM.kind_K13 Z G b hb) h13
  · refine (lotAll_of (L := K13.lot4 Z) (G := G) (fun b hb => ?_) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h)).1 b hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
    have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
    unfold K13.wBlock K1.wAt at hw'
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
    exact atM4_pile _ _
  · exact absurd (IM.kind_K13_end Z G b hb) hf
  · unfold ProofFile.p4Pure at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact (k6Lot_keeps H Z G).1 b hb
    · refine (?K : LotAll PileStays _ G).1 b hb
      exact lotAll_of (fun b hb => h1_whole H G b hb) (fun _ hb => nomatch hb)
        (fun _ _ h => nomatch h)

variable {P : S → Prop}

/-- **Over a lot's sub-protocol of a kind P rides.** -/
theorem lot_rides (L : PileLawZ P) (Z : ProofFile.Pub) (h0 : Z.P.firstTree = 0) (G : Ground) {Lt : Lot}
    (hL : Lt ∈ ProofFile.onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ Lt.blocks G)
    (hf : b.place.kind ≠ KindName.frame) : Whole (Rides P) b := by
  by_cases h13 : b.place.kind = KindName.K13
  · obtain ⟨rfl, -⟩ := IM.lot_K13 hL hb h13
    refine (lotAll_of (L := K13.lot Z) (G := G) (fun b hb => ?_) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h)).1 b hb
    obtain rfl := List.mem_singleton.1 hb
    exact ⟨L.batch _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact whole_mono (fun s s' q => L.same s s' q) (lot_pile Z h0 G hL hb hf h13)

open Johnson.Desc.First.Walk.Seat in
/-- **A row of the links' frames.** -/
theorem frame_but (L : PileLawZ P) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) (i : Nat)
    (f : LinkFrame) (hi : fs[i]? = some f) :
    Fn (Rides P) f.clear ∧
      ∀ s t, f.opened s = .ok t → (i ≠ 0 ∨ s.rows = []) → P s → P t := by
  rcases IM.frames_arms h i f hi with ⟨X, -, -, rfl⟩ | ⟨rfl, Q, -, -, eo, ec⟩ |
    ⟨Q, n, -, -, eo, ec⟩ | ⟨Q, -, -, eo, ec⟩
  · exact ⟨L.push _ _ _ _ _, fun s t k _ I => by cases k; exact I⟩
  · refine ⟨ec ▸ L.push _ _ _ _ _, fun s t k hz I => ?_⟩
    rw [eo] at k
    rcases hz with hz | hz
    · exact absurd rfl hz
    · exact L.zero _ _ _ s t k hz I
  · refine ⟨ec ▸ L.push _ _ _ _ _, fun s t k _ I => ?_⟩
    rw [eo] at k
    exact L.same s t (openAtt_pile Q s t k) I
  · refine ⟨ec ▸ L.push _ _ _ _ _, fun s t k _ I => ?_⟩
    rw [eo] at k
    exact L.same s t (openLay_pile Q s t k) I

theorem hear_noframe {sub : ModelPart} {f : Bool} {i : Nat} {k : KindName}
    (h : (kindsBeforeBatching sub f)[i]? = some k) : k ≠ KindName.frame ∧ k ≠ KindName.K13 := by
  have hm := List.mem_of_getElem? h
  constructor <;> rintro rfl <;> revert hm <;> cases sub <;> cases f <;> decide

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The runs of claims of a link's hearing sub-protocols.** -/
theorem hear_runs_pile (L : PileLawZ P) (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) : ∀ b ∈ Lk.hear, RunsKeep (Rides P) b := by
  intro b hb
  have h0 : Z.P.firstTree = 0 := pub_firstTree O.pub
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hb
  have e : Lk.hear[j]? = some b := by rw [List.getElem?_eq_getElem hj, e']
  obtain ⟨Lk9, -, -, -, e9, -, -, -, -, -, -, -, -, -, -, -, -, hlen9, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk9 := Option.some.inj (eL.symm.trans e9)
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, e1, hn, -⟩ := hall l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1)
  have hn' : Lk.hear.length = IM.nAt l := hn
  have hn9 : IM.nAt l ≤ 9 := by unfold IM.nAt; split <;> omega
  obtain ⟨k1, hk1⟩ : ∃ k1, (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some k1 :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen9]; exact hj)⟩
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨Lk', b0, e1', e2, Lt, hLt, b', hb', ep, hjn⟩ := IM.first_sits hS hR O l hl k1 hk1
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1')
    obtain rfl : b = b0 := Option.some.inj (e.symm.trans e2)
    exact joined_runs rides_refl rides_trans hjn
      (lot_rides L Z h0 Bs.G₀ hLt hb' (by rw [ep]; exact (hear_noframe hk1).1)).2
  · obtain ⟨h9, h10⟩ := IM.hear_plain hk1
    obtain ⟨Lk', b0, e1', e2, sp, -, Lt, hLt, b', hb', -, ep, hla⟩ :=
      IM.chain_hear_alone O.made O.places O.chain l (IM.subAt l) (IM.subs_scope hS hR O l hl) j k1
        hk1 h9 h10 ⟨by omega, by omega⟩
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e1')
    obtain rfl : b = b0 := Option.some.inj (e.symm.trans e2)
    exact alone_runs rides_refl hla
      (lot_rides L Z h0 Bs.G₀ hLt hb' (by rw [ep]; exact (hear_noframe hk1).1)).2

/-- **Over sub-protocol number k of the flat list P rides, if k is not 2 or no row lies.** -/
theorem flat_rides (L : PileLawZ P) (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : Nat) (b : Block S Cl)
    (hb : c.blocksInOrder[k]? = some b) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok t)
    (hk : k ≠ 2 ∨ s.rows = []) (hP : P s) : P t := by
  have h0 : Z.P.firstTree = 0 := pub_firstTree O.pub
  cases IM.flat_cases hS hR O k b hb with
  | front b hr hd' =>
    obtain rfl := (hd' s rs gs t).1 hd
    exact hP
  | laid l hl b hr hd' => exact L.same _ _ (layFront_pile l s t ((hd' s rs gs t).1 hd).1) hP
  | first l hl k0 b b' hk0 lot hp hj =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    obtain ⟨fs, f, m, hfs, hf, y1, -, y2, -, -⟩ := hj.yes hd
    have q : PileStays s m := (lot_pile Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact (hear_noframe hk0).1)
      (by rw [hp]; exact (hear_noframe hk0).2)).1 s _ _ m y1
    refine (frame_but L hfs l f hf).2 m t y2 ?_ (L.same _ _ q hP)
    rcases hk with hk | hk
    · exact Or.inl (by omega)
    · exact Or.inr (q.1.trans hk)
  | hear l hl i hi k1 b b' name hk1 lot hp hla =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    have W := lot_rides L Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact (hear_noframe hk1).1)
    by_cases h7 : k1 = KindName.K7
    · exact W.1 s rs gs t ((IM.yes_alone_K7 hla h7 s t rs gs).1 hd).1 hP
    · exact W.1 s rs gs t ((IM.yes_alone hla h7 s t rs gs).1 hd).1 hP
  | batch l hl Lk p e1 hp hal =>
    have y := ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro q; cases q) s t rs gs).1 hd).1
    exact (batch_over rides_trans L.same p (link_claims_runs rides_refl rides_trans Lk
      (hear_runs_pile L hS hR O hl e1))).1 s rs gs t y hP
  | behind l hl Lk b e1 hr hd' =>
    rw [hd'] at hd
    exact link_behind_runs rides_refl rides_trans Lk (hear_runs_pile L hS hR O hl e1) s t hd hP
  | close l hl p Q j k' b x hp hQ hk' ex hla =>
    have h7 : (IM.cAt l (IM.subAt l) j k').kind ≠ KindName.K7 := by
      have hm := List.mem_of_getElem? hk'
      intro q
      have q' : k' = KindName.K7 := q
      subst q'
      revert hm
      decide
    exact L.same _ _ ((closeOf_pile p Q x (List.mem_of_getElem? ex)).1 s rs gs t
      ((IM.yes_alone hla h7 s t rs gs).1 hd).1) hP
  | cleared l hl fs f b hfs hf hr hd' =>
    exact (frame_but L hfs l f hf).1 s t ((hd' s rs gs t).1 hd).1 hP
  | back j kj b b' name hkj lot hp hla =>
    obtain ⟨Lt, hLt, hb'⟩ := lot
    have hm := List.mem_of_getElem? hkj
    have hfr : kj ≠ KindName.frame := by
      rintro rfl
      revert hm
      decide
    have h7 : kj ≠ KindName.K7 := by
      rintro rfl
      revert hm
      decide
    have hd2 : b.decide s rs gs = .ok t := hd
    exact (lot_rides L Z h0 Bs.G₀ hLt hb' (by rw [hp]; exact hfr)).1 s rs gs t
      ((IM.yes_alone hla h7 s t rs gs).1 hd2).1 hP
  | last lot hla =>
    have hd2 : c.last.decide s rs gs = .ok t := hd
    exact ((k13LotEnd_keeps (R := Rides P) rides_refl Z Bs.G₀).1 _ lot).1 s rs gs t
      ((IM.yes_alone hla (by intro q; cases q) s t rs gs).1 hd2).1 hP

/-- **Sub-protocols number 0 and 1 leave the rows.** -/
theorem flat_rows (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (k : Nat) (hk : k ≤ 1)
    (b : Block S Cl) (hb : c.blocksInOrder[k]? = some b) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok t) : t.rows = s.rows := by
  cases IM.flat_cases hS hR O k b hb with
  | front b hr hd' =>
    obtain rfl := (hd' s rs gs t).1 hd
    rfl
  | laid l hl b hr hd' => exact (layFront_pile l s t ((hd' s rs gs t).1 hd).1).1
  | first l hl k0 b b' hk0 lot hp hj => omega
  | hear l hl i hi k1 b b' name hk1 lot hp hla => omega
  | batch l hl Lk p e1 hp hal => omega
  | behind l hl Lk b e1 hr hd' => omega
  | close l hl p Q j k' b x hp hQ hk' ex hla => omega
  | cleared l hl fs f b hfs hf hr hd' => omega
  | back j kj b b' name hkj lot hp hla => omega
  | last lot hla => omega

end

/-- **The fold's rule for a sentence that may read the number of the border.** -/
theorem fold_ix {T C : Type} (I : Nat → T → Prop) (ft : Nat) : ∀ (bs : List (Block T C)) (j : Nat),
    (∀ k b, bs[k]? = some b → ∀ s rs gs t, b.decide s rs gs = .ok t → I (j + k) s →
      I (j + k + 1) t) →
    ∀ (s : T) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
      (r : T × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
      foldBlocks ft bs s rs cols = .ok r → I j s → I (j + bs.length) r.1 := by
  intro bs
  induction bs with
  | nil =>
    intro j _ s rs cols r h hI
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    exact hI
  | cons b l ih =>
    intro j hb s rs cols r h hI
    simp only [foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' _ cols k hs
        have h1 : I (j + 1) s' := hb 0 b rfl s rs' gs' s' hd hI
        have h2 := ih (j + 1) (fun k' b' e s rs gs t d hi => by
          have h3 := hb (k' + 1) b' (by simpa using e) s rs gs t d
            (by rwa [show j + (k' + 1) = j + 1 + k' by omega])
          rwa [show j + (k' + 1) + 1 = j + 1 + k' + 1 by omega] at h3) _ _ _ _ h h1
        rwa [show j + 1 + l.length = j + (b :: l).length by
          rw [List.length_cons]; omega] at h2

/-- **IN SCOPE: P AT EVERY STATE THAT A FOLD OVER A FRONT STRETCH OF THE FIRST CHAIN RETURNS.** -/
theorem fold_rides (L : PileLawZ P) {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (s₀ : S) (hP : P s₀)
    (h0 : s₀.rows = []) (ft : Nat) (l₁ l₂ : List (Block S Cl)) (hc : c.blocksInOrder = l₁ ++ l₂)
    (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (hf : foldBlocks ft l₁ s₀ rs cols = .ok r) : P r.1 := by
  refine (fold_ix (fun k s => P s ∧ (k ≤ 2 → s.rows = [])) ft l₁ 0 ?_ s₀ rs cols r hf
    ⟨hP, fun _ => h0⟩).1
  intro k b e s rs gs t d hi
  have hb : c.blocksInOrder[k]? = some b := by
    rw [hc, List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1]
    exact e
  refine ⟨flat_rides L hS hR O k b hb s t rs gs d ?_ hi.1, fun hk => ?_⟩
  · by_cases h2 : k = 2
    · exact Or.inr (hi.2 (by omega))
    · exact Or.inl h2
  · rw [flat_rows hS hR O k (by omega) b hb s t rs gs d]
    exact hi.2 (by omega)

end LPFK9

#print axioms LPFK9.seatKeeps_pile
#print axioms LPFK9.lot_pile
#print axioms LPFK9.lot_rides
#print axioms LPFK9.frame_but
#print axioms LPFK9.hear_runs_pile
#print axioms LPFK9.flat_rides
#print axioms LPFK9.flat_rows
#print axioms LPFK9.fold_ix
#print axioms LPFK9.fold_rides
