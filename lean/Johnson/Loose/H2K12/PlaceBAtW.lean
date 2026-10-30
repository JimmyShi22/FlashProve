-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/PlaceBAtW.lean:
THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's LAST CHAIN:
THE TEST WITH CODE ON A PLACE
AND ITS STRETCH's DATA (PlaceB, Johnson/Desc/K12/Coin/BoolsTests.lean) ACCEPTS: general in the
IOP as written in Lean, and at the proof file's own (FL, Johnson/LLT25R/LastSeat.lean), in the
letters of the field placeB of the last chain's ledger (Johnson/LLT25R/LastLedger.lean).
Statements and proofs. No evaluation by the kernel; no written value.

Why. The library has the way from the test's yes to the sentences (atPlace_of,
Johnson/Desc/K12/Coin/Bools.lean) and, apart, the sentences themselves at a stretch of the data
(AtPlace by atPlace_lastJ, Johnson/Desc/K12/Coin/AtDescJ.lean). Whoever holds the test as a premise
needs the way back. Of its ten clauses seven are AtPlace's own fields. The three others:
  likeOk_of       "the data are like the written rounds": the converse of like_of_ok.
  treesOk_of_planOk   "which written rounds send a tree": from the sub-protocol's own test on the
                  list of rounds (MasksFixed.made, Johnson/Desc/K12/Law/MasksFixed.lean; WShape,
                  Johnson/Desc/K12/Law/TreesMade.lean), by treesWalk_of_shape.
  wantsB_of_rel   "what the stretch opens is what the declared rounds open": from the facts, round
                  by round, in which rel_of (Johnson/Desc/Sound/WantsAtStretch.lean) ends.
                  rel_piece, rel_cut, rel_last: these facts at a stretch of the last chain's data:
                  the proofs of that file's wants_piece, wants_cut, wants_last, each one step
                  shorter.
Then:
  placeB_of_atPlace   the ten clauses together.
  placeB_last     at a stretch of the last chain's data, the declared rounds cut as a list.
  placeB_tile₃    the same where the flat list parts at a sub-protocol that declares the test's
                  rounds.
  placeB_at_FL    THE LEDGER's FIELD's OWN TEXT, general in the shared seat A.
Limits. (1) The first arm alone (the first fold sends no mask of its own), the last chain alone. (2)
placeB_at_FL's five premises are those of four_at_W (H2K12/LastRestAtW.lean): K12's files' structure
of tests at the place (ClosedL, Johnson/Desc/K12/Coin/LawAtLight.lean), of which the test on the
list of rounds and the test johOk alone are spent; no own mask; no root in front; FL has data; the
third stretch is dB :: dt. They are shown here of no files. (3) A test's yes is what it is worth in
atPlace_of: nothing is added to that. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.AtDescJ
import Johnson.Desc.K12.Coin.BoolsTests
import Johnson.Desc.K12.Law.MasksPlan
import Johnson.Desc.K12.Law.SpendMade
import Johnson.Desc.Sound.WantsAtStretch
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.K12.Coin.LawAtLight
import Johnson.LLT25R.LastNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open H2K.Pub (writtenOf WR spendOk johOk)
open Johnson.G.OfPlan (rootsOf)
open VerifiableInference.OnPublicFiles.Last
open LLT25 (FL c0 c1 c2 c3 last_flat_pure)

/-! ## 1 From the sentences back to the tests with code -/

theorem likeB_of {d : RDT} {w : WR} (h : Like d w) : likeB d w = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [likeB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem likeAllB_of : ∀ (ds : List RDT) (ws : List WR), List.Forall₂ Like ds ws →
    likeAllB ds ws = true
  | [], [], _ => rfl
  | d :: ds, w :: ws, h => by
    cases h with
    | cons h1 ht =>
      simp only [likeAllB, Bool.and_eq_true]
      exact ⟨likeB_of h1, likeAllB_of ds ws ht⟩

/-- Data that are like written rounds open no stored table. -/
theorem stored_of_like : ∀ (ds : List RDT) (ws : List WR), List.Forall₂ Like ds ws →
    ∀ d ∈ ds, d.stored = []
  | [], [], _, _, hd => by cases hd
  | d :: ds, w :: ws, h, x, hx => by
    cases h with
    | cons h1 ht =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h1.2.2.2.2
      · exact stored_of_like ds ws ht x hx

/-- The converse of like_of_ok (Johnson/Desc/K12/Coin/Bools.lean). -/
theorem likeOk_of (π : P12) (ds : List RDT)
    (h : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like ds (w0 :: l)) :
    likeOk π ds = true := by
  obtain ⟨w0, l, hw, hl⟩ := h
  unfold likeOk
  rw [hw]
  exact likeAllB_of _ _ hl

/-- Round by round: the facts in which rel_of (Johnson/Desc/Sound/WantsAtStretch.lean) ends are the
test's own, where no round's data open the stored table. -/
theorem wantsB_of_rel (a : ℕ) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) :
    ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound),
      List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
        d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
          (∀ s ∈ r.stored, s.sh.a = a) ∧ ∀ o ∈ r.opens, dep (num o.2) = some o.1.a) ds rs →
      (∀ d ∈ ds, d.stored = []) → wantsB dep num ds rs = true
  | [], [], _, _ => rfl
  | d :: ds, r :: rs, h, hs => by
    cases h with
    | cons h1 ht =>
      obtain ⟨e1, e2, -, e4⟩ := h1
      have s1 : d.stored = [] := hs d List.mem_cons_self
      simp only [wantsB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
        beq_iff_eq]
      exact ⟨⟨⟨⟨s1, e1 ▸ s1⟩, e2⟩, e4⟩,
        wantsB_of_rel a dep num ds rs ht fun e he => hs e (List.mem_cons_of_mem _ he)⟩

/-- Which written rounds send a tree, cut as the chain cuts them: the walk with code accepts. -/
theorem treesWalk_of_shape : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage) (l : List WR),
    H2K.Made.WShape none rest a l → treesWalk rest a l = true
  | [], _, _, _ => rfl
  | b :: rest, a, l, h => by
    obtain ⟨dE, dT, dS, dC, l', rfl, e1, e2, e3, e4, k1, k2, hW⟩ := h
    obtain ⟨n, hn⟩ : ∃ n, a.k = n + 1 := ⟨a.k - 1, by omega⟩
    have hk : H2K.Pub.kk a = n + 1 := by
      unfold H2K.Pub.kk
      omega
    have hd : (dT :: (List.replicate n dT ++ dS :: dC :: l')).drop (H2K.Pub.kk a) =
        dS :: dC :: l' := by
      rw [hk, List.drop_succ_cons]
      exact List.drop_left' (by simp)
    rw [hn, List.replicate_succ]
    show treesWalk (b :: rest) a (dE :: dT :: (List.replicate n dT ++ dS :: dC :: l')) = true
    unfold treesWalk
    dsimp only
    rw [hd]
    simp only [Bool.and_eq_true]
    exact ⟨⟨by rw [e1]; rfl, by rw [e2]; rfl⟩, ⟨e3, by rw [e4]; rfl⟩,
      treesWalk_of_shape rest b l' hW⟩

/-- **The test on which written rounds send a tree, from the sub-protocol's own test on the list of
rounds**, where the first fold sends no mask of its own. -/
theorem treesOk_of_planOk (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (ho : π.nums.ownMask = false) : treesOk π = true := by
  obtain ⟨a, b, rest, w0, w, hs, hw, hW, -⟩ := (H2K.Made.masksFixed_of_planOk π hp).made
  have e : ((H2K.Made.ownTold π.nums).map (·.1)).head? = none := by simp [H2K.Made.ownTold, ho]
  rw [e] at hW
  unfold treesOk
  rw [hs, hw]
  exact treesWalk_of_shape _ a w hW

/-! ## 2 The facts on what a stretch opens, at every IOP as written that has data -/

/-- One stretch: wants_piece's proof (Johnson/Desc/Sound/WantsAtStretch.lean), one step shorter. -/
theorem rel_piece (Fr : Frame) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ)
    (rs : List Fmt.DeclaredRound) (base : ℕ) (ds : List RDT) (hM : Matches Fr.a dep rs ds)
    (hN : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.opens = r.opens.map fun o => num o.2) ds rs)
    (hT : InTime base ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (Fr.all.filter (·.no == j)).map (·.a) = [a']) :
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
        (∀ s ∈ r.stored, s.sh.a = Fr.a) ∧
        ∀ o ∈ r.opens, (stg Fr base ds).depth (num o.2) = some o.1.a) ds rs :=
  rel_of Fr.a dep _ num rs ds hM hN
    (depth_agrees Fr dep base ds (inTime_below ds base hT) own listed
      (matches_dep Fr.a dep rs ds hM))

/-- The stretch behind pre, as long as mid: wants_cut's proof, with rel_piece at its end. -/
theorem rel_cut (Fr : Frame) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ)
    (pre mid post : List Fmt.DeclaredRound) (base₀ : ℕ) (ds : List RDT)
    (hM : Matches Fr.a dep (pre ++ (mid ++ post)) ds)
    (hN : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.opens = r.opens.map fun o => num o.2) ((ds.drop pre.length).take mid.length) mid)
    (hT : InTime base₀ ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base₀ + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (Fr.all.filter (·.no == j)).map (·.a) = [a']) :
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
        (∀ s ∈ r.stored, s.sh.a = Fr.a) ∧
        ∀ o ∈ r.opens, (stg Fr (base₀ + nTrees (ds.take pre.length))
          ((ds.drop pre.length).take mid.length)).depth (num o.2) = some o.1.a)
      ((ds.drop pre.length).take mid.length) mid := by
  have hM2 := (matches_split Fr.a dep pre (mid ++ post) ds hM).2
  have hM3 := (matches_split Fr.a dep mid post _ hM2).1
  have t1 := (inTime_append (ds.take pre.length) (ds.drop pre.length) base₀
    (by rw [List.take_append_drop]; exact hT)).2
  have t2 := (inTime_append ((ds.drop pre.length).take mid.length)
    ((ds.drop pre.length).drop mid.length) _ (by rw [List.take_append_drop]; exact t1)).1
  refine rel_piece Fr dep num mid _ _ hM3 hN t2 (fun n sh h => ?_) listed
  have lt := treeShT_lt _ n sh h
  have e1 : treeShT (ds.drop pre.length) n = some sh := by
    rw [← List.take_append_drop mid.length (ds.drop pre.length), treeShT_append, if_pos lt]
    exact h
  have e2 : treeShT ds (nTrees (ds.take pre.length) + n) = some sh := by
    rw [← List.take_append_drop pre.length ds, treeShT_append, if_neg (by
      rw [List.take_append_drop]; omega)]
    rw [List.take_append_drop, Nat.add_sub_cancel_left]
    exact e1
  rw [Nat.add_assoc]
  exact own _ sh e2

/-- **A stretch of the last chain**: wants_last's proof, with rel_cut at its end. -/
theorem rel_last {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (pre mid post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.2 = pre ++ (mid ++ post)) (k : ℕ → ℕ) (ft : ℕ) :
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.stored = r.stored ∧ d.opens = r.opens.map (fun o => numAt F.t₁ F.t₂ 2 o.2) ∧
        (∀ s ∈ r.stored, s.sh.a = (frameAt D (allOf D) k ft).a) ∧
        ∀ o ∈ r.opens, (stg (frameAt D (allOf D) k ft)
          (D.t₁ + D.t₂ + nTrees (D.ds₃.take pre.length))
          ((D.ds₃.drop pre.length).take mid.length)).depth (numAt F.t₁ F.t₂ 2 o.2) = some o.1.a)
      ((D.ds₃.drop pre.length).take mid.length) mid := by
  obtain ⟨-, -, f⟩ := chainFits_of_data F file D h ⟨[], ⟨[], [], [], none⟩⟩ k k k ft ft ft
  have hM := f.rounds
  rw [flat_blk, e] at hM
  have hN := forall₂_cut pre mid post (by rw [← e]; exact (opensOfData Xi F file D h).2.2)
  exact rel_cut _ D.depth _ pre mid post _ D.ds₃ hM (hN.imp fun _ _ x => x.2) f.inTime f.own
    f.listed

/-! ## 3 The test on a place and its stretch's data -/

/-- All ten clauses: seven are AtPlace's own fields (Johnson/Desc/K12/Coin/Sheet.lean). -/
theorem placeB_of_atPlace {F : Frame} {π : P12} {num : Fmt.TreeSource → ℕ}
    {L mC mS mW : OnBytes.Slice.Sg → ℕ → ℕ} {rad : OnBytes.Slice.Sg → ℕ} {base : ℕ} {dB : RDT}
    {dt : List RDT} {εt : Iop.Err (uLT (_root_.Run.ckP .two) dt)}
    (A : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hw : wantsB (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth num (dB :: dt)
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds = true) (ht : treesOk π = true) :
    PlaceB F π num base dB dt = true := by
  simp only [PlaceB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨A.early, A.answers⟩, A.planOk⟩, A.spend⟩, A.deal⟩, likeOk_of π _ A.like⟩,
    A.batNone⟩, A.own0⟩, hw⟩, ht⟩

/-- **THE TEST AT THE STRETCH THAT AN IOP AS WRITTEN's OWN DATA HOLD FOR THE PROXIMITY TEST ON THE
LAST CHAIN**, first arm. -/
theorem placeB_last {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.2 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post))
    (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt =
      (D.ds₃.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hj : johOk π r = true)
    (ho : π.nums.ownMask = false) :
    PlaceB (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2)
      (D.t₁ + D.t₂ + nTrees (D.ds₃.take pre.length)) dB dt = true := by
  obtain ⟨a, b, rest, w0, w, -, hw, -, -⟩ := (H2K.Made.masksFixed_of_planOk π hp).made
  have A := atPlace_lastJ F file D h key ft π r pre post e dB dt hcons hfree
    (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
    (H2K.Made.spendOk_of_planOk π hp) hj ho w0 w hw
  refine placeB_of_atPlace A ?_ (treesOk_of_planOk π hp ho)
  obtain ⟨w0', l', -, hl⟩ := A.like
  have R := rel_last h pre _ post e key ft
  rw [← hcons] at R
  exact wantsB_of_rel _ _ _ _ _ R (stored_of_like _ _ hl)

/-- **The same where the last chain's flat list parts at a sub-protocol that declares the test's
rounds**: atPlace_tile₃'s binders (Johnson/Desc/K12/Coin/LawAtTileThird.lean), less the chain at the
radii and the price of "BAT". -/
theorem placeB_tile₃ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre : List (Block F.S₃ F.Cl)) (B : Block F.S₃ F.Cl) (post : List (Block F.S₃ F.Cl))
    (hfl : F.second.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hj : johOk π r = true)
    (ho : π.nums.ownMask = false) (dB : RDT) (dt : List RDT)
    (hds : (D.ds₃.drop (pre.flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt) :
    PlaceB (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2)
      (D.t₁ + D.t₂ + nTrees (D.ds₃.take (pre.flatMap (·.rounds)).length)) dB dt = true := by
  have e : F.roundsDeclaredByBlocks.2.2 = pre.flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds)) := by
    show F.second.blocksInOrder.flatMap (·.rounds) = _
    rw [hfl, List.flatMap_append, List.flatMap_cons, hB]
  exact placeB_last F file D h key ft π r _ _ e dB dt hds.symm hfree hp hj ho

/-! ## 4 At the proof file's own IOP as written -/

/-- **THE LEDGER's FIELD placeB, IN ITS OWN TEXT**, general in the shared seat. -/
theorem placeB_at_FL (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
    (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (file : String)
    (D : WholeD)
    (r : Fmt.M1.Stage → ℕ) (ch b₁ b₂ : ℕ) (T : List (Fmt.TreeSource × ℕ)) (dB : RDT) (dt : List RDT)
    (hcl : ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r ch b₁ b₂ T)
    (ho : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false)
    (hfree : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free = 0)
    (h : (FL o mk Z A N c).data file = .ok D)
    (hds : ds₂ D.ds₃
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N))
      (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) =
        dB :: dt) :
    PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (numAt D.t₁ D.t₂ 2)
      (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt = true := by
  obtain ⟨-, k₁, k₂⟩ := opensShaped (FL o mk Z A N c) file D h
  have P := placeB_tile₃ (FL o mk Z A N c) file D h D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r [c0 Z, c1 N] (c2 N) [c3 Z N]
    (last_flat_pure o mk Z A N c) rfl hfree hcl.plan hcl.joh ho dB dt hds
  have hb : baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N) = D.t₁ + D.t₂ + nTrees (D.ds₃.take 0) := by
    rw [LLT25.baseTwo_pure]
    simp [nTrees]
  rw [← k₁, ← k₂] at P
  rw [hb]
  exact P

end H2K12

#print axioms H2K12.likeB_of
#print axioms H2K12.likeAllB_of
#print axioms H2K12.stored_of_like
#print axioms H2K12.likeOk_of
#print axioms H2K12.wantsB_of_rel
#print axioms H2K12.treesWalk_of_shape
#print axioms H2K12.treesOk_of_planOk
#print axioms H2K12.rel_piece
#print axioms H2K12.rel_cut
#print axioms H2K12.rel_last
#print axioms H2K12.placeB_of_atPlace
#print axioms H2K12.placeB_last
#print axioms H2K12.placeB_tile₃
#print axioms H2K12.placeB_at_FL
