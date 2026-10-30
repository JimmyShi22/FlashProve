-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHPublic.lean: the closed fields of `FirstPublic` (E2E/FirstHSeats.lean), in scope, by
evaluation at the written sizes.

  `sendRound_behind`, `sent_of_member`: the tree that a sending sends first is sent at the sending's
    first round.
  `sendFits_par`, `trees_par`: a sending's public test and its trees read its codes and messages alone.
  `SheetAt`: K's six senders are the sheet's and stand at the places: a premise, by rfl at the value.
  `first_public`: `FirstPublic`, from it and scope.

Limits. `decide +kernel` at the written sizes alone. Nothing on any property.
-/
import E2E.FirstHSeats
import E2E.KeyRangesTrees
import E2E.KeyShapeAtFull
import E2E.KeyBookHeldK1Jobs
import Johnson.RunOne.KeySeatScope

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block sendRound)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces sendingPar pieces)
open AtPublicFiles.KeyThread (D one₀ rootsOf rootsOf_cons rootsOf_append sentIn treesTo_roots decls_split
  trees_six trees15)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (oneF six_sourced)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending keyBatt constraintRowsAtClaimPoints firstW oneOf)
open AtPublicFiles.KeyBook (rideMsg rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob sendFits)

/-- **The round that sends a tree**, behind the rounds that send the trees in front of it. -/
theorem sendRound_behind : ∀ (pre : List Fmt.DeclaredRound) (r : Fmt.DeclaredRound)
    (rest : List Fmt.DeclaredRound) (i : Nat), i < r.entry.roots →
    sendRound (pre ++ r :: rest) (rootsOf pre + i) = some pre.length
  | [], r, rest, i, h => by
    show sendRound (r :: rest) (rootsOf [] + i) = some 0
    have e : rootsOf [] + i = i := Nat.zero_add i
    rw [e]
    unfold sendRound
    rw [if_pos h]
  | q :: pre, r, rest, i, h => by
    rw [List.cons_append, rootsOf_cons]
    unfold sendRound
    rw [if_neg (by omega)]
    have e : q.entry.roots + rootsOf pre + i - q.entry.roots = rootsOf pre + i := by omega
    rw [e, sendRound_behind pre r rest i h]
    rfl

/-- **A sending's tree is sent at the sending's first round.** -/
theorem sent_of_member {S Cl : Type} {bs : List (Block S Cl)} {b : Nat} {blk : Block S Cl}
    {r : Fmt.DeclaredRound} {l : List Fmt.DeclaredRound} (hb : bs[b]? = some blk) (hr : blk.rounds = r :: l)
    (h0 : 0 < r.entry.roots) (hl : ∀ x ∈ bs, ProofFile.Honest.Small.Listed x) :
    sentIn (bs.flatMap (·.rounds)) (treesTo bs b) = roundsTo bs b := by
  have e := AtPublicFiles.KeyThread.decls_split bs b
  obtain ⟨rest, hd⟩ : ∃ rest, (bs.drop b) = blk :: rest := by
    cases hdr : bs.drop b with
    | nil =>
      have h1 := (List.getElem?_eq_some_iff.1 hb).1
      have h2 := List.drop_eq_nil_iff.1 hdr
      omega
    | cons a t =>
      have e1 : (bs.drop b)[0]? = some blk := by
        rw [List.getElem?_drop, Nat.add_zero]
        exact hb
      rw [hdr] at e1
      obtain rfl : a = blk := Option.some.inj e1
      exact ⟨t, rfl⟩
  rw [hd, List.flatMap_cons, hr, List.cons_append] at e
  unfold sentIn
  rw [e, treesTo_roots bs hl b]
  have := sendRound_behind (declsTo bs b) r (l ++ rest.flatMap (·.rounds)) 0 h0
  rw [Nat.add_zero] at this
  rw [this]
  rfl

/-- A sending's public test reads its codes and its messages alone. -/
theorem sendFits_par (a a' : OneTime) (n n' : Nat) (w w' : String) (m : Array OracleNotice)
    (g g' : List (List Nat)) (hc : a.codes = a'.codes) (ride : Nat → Option ProofFile.Honest.K1.Ride) :
    sendFits (sendingPar a n w m g) ride = sendFits (sendingPar a' n' w' m g') ride := by
  unfold sendFits Johnson.Prover.Send.shapeAt
  simp only [AtPublicFiles.KeyLookup.sent_par]
  simp only [sendingPar, hc]

/-- Its trees likewise. -/
theorem trees_par (a a' : OneTime) (n n' : Nat) (w w' : String) (m : Array OracleNotice)
    (g g' : List (List Nat)) (hc : a.codes = a'.codes) :
    (sendingPar a n w m g).trees = (sendingPar a' n' w' m g').trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  simp only [AtPublicFiles.KeyLookup.sent_par]
  simp only [sendingPar, hc]

/-! ## At the written sizes -/

def idxFull : VerifiableInference.Desc.K1.Par := sendingPar oneF 0 "" #[oneF.indexMasks] []
def msgFull : VerifiableInference.Desc.K1.Par := sendingPar oneF 0 "" (Wf.messageOf oneF.ranges) []

theorem fits_idx : sendFits idxFull (fun _ => none) = true := by decide +kernel
theorem fits_msg : sendFits msgFull rideMsg = true := by decide +kernel
theorem fits_w : ∀ m, linMessageW oneF.lin = some m → sendFits (sendingPar oneF 0 "" m []) rideW = true := by
  decide +kernel
theorem trees_idx : idxFull.trees.length = 1 := by decide +kernel
theorem trees_msg : msgFull.trees.length = 1 := by decide +kernel
theorem trees_w : ∀ m, linMessageW oneF.lin = some m → (sendingPar oneF 0 "" m []).trees.length = 1 := by
  decide +kernel
theorem message_size : 0 < (Wf.messageOf oneF.ranges).size := by decide +kernel
theorem first_is : 1 + (Wf.messageOf oneF.ranges).size +
    ((AtPublicFiles.TreeReads.sentOfTest oneF.given.plan.samples true oneF.ranges.stages).map
      List.length).sum = 1 + 2 * oneF.ranges.stages.length := by decide +kernel
theorem stages_one : 1 ≤ oneF.ranges.stages.length := by decide +kernel
theorem lookups_two : oneF.ranges.lookups.length = 2 := by decide +kernel

/-! ## In scope -/

section
variable {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Z : PublicFiles}

/-- **K's senders are the sheet's and stand at the first chain's places.** By rfl at the value. -/
structure SheetAt (Xs : Source) (N : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X' Wk)
    (f : W₀ → Weights) : Prop where
  places : K.AtPlaces
  idx : K.idx = indexMaskSending Xs
  msg : K.msg = multiplicitiesSending f Xs
  w : K.w = batchedRowsSending f Xs N
  batt : K.batt = keyBatt Xs
  pile : K.pile = constraintRowsAtClaimPoints Xs N
  weights : K.weights = f

theorem some_of_map {α β : Type} {o : Option α} {g : α → β} {b : β} (h : o.map g = some b) :
    o.isSome = true := by
  cases o with
  | none => cases h
  | some _ => rfl

/-- As many oracle messages as the sending has trees. -/
theorem oracles_count {S Cl : Type} {blk : Block S Cl} {P : VerifiableInference.Desc.K1.Par}
    (h : blk.oracles = VerifiableInference.Desc.K1.oracles P) :
    (blk.oracles.flatMap id).length = P.trees.length := by
  rw [h]
  simp [VerifiableInference.Desc.K1.oracles]

/-- A list of nineteen at its last. -/
theorem last_at {α : Type} (pre : List α) (a b c d : α) (h : (pre ++ [a, b, c, d]).length = 19) :
    (pre ++ [a, b, c, d])[18]? = some d := by
  have hl : pre.length = 15 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  rw [List.getElem?_append_right (by omega), hl]
  rfl

/-- The first chain declares six trees in all. -/
theorem trees_all (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    treesTo (D Xs N Pl).first.blocksInOrder 19 = 6 := by
  have hl := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  have hlist : ∀ x ∈ (D Xs N Pl).first.blocksInOrder, ProofFile.Honest.Small.Listed x := fun x hx =>
    ProofFile.Honest.Small.lists_of_shaped ((planOk_all hs.named.plan).1 x hx).2
  rw [treesTo_roots _ hlist 19]
  have e : declsTo (D Xs N Pl).first.blocksInOrder 19 = (D Xs N Pl).first.blocksInOrder.flatMap (·.rounds) := by
    unfold declsTo
    rw [List.take_of_length_le (by rw [hl])]
  rw [e]
  exact trees_six hs scope

/-- The last member. -/
theorem seal_at (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {bw : Block FirstState Claim} (hw : AtPublicFiles.AtFiles.sendWAt (AtPublicFiles.AtFiles.pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 = some bw) :
    (D Xs N Pl).first.blocksInOrder[18]? = some (D Xs N Pl).first.last.asBare := by
  have e : (D Xs N Pl).first.blocksInOrder = _ :=
    AtPublicFiles.AtFiles.flat₁_cut (AtPublicFiles.AtFiles.pubOf Xs) Xs.Y.D.1 Xs.Y.told.1 N bw hw
  have hl := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  rw [e] at hl ⊢
  exact last_at _ _ _ _ _ hl

/-- The last member states no oracle message. -/
theorem seal_none : (((D Xs N Pl).first.last.asBare).oracles.flatMap id).length = 0 := by
  have e : (D Xs N Pl).first.last.oracles = [[]] := rfl
  show ((D Xs N Pl).first.last.oracles.flatMap id).length = 0
  rw [e]
  rfl

/-- **The closed fields of `FirstPublic`, in scope.** -/
theorem first_public (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : SheetAt Xs N K f) : FirstPublic (Pl := Pl) Xs N K f := by
  have six := six_sourced hs scope
  have hc : (oneOf Xs).codes = oneF.codes := six.codes
  have hi : (oneOf Xs).indexMasks = oneF.indexMasks := six.indexMasks
  have hr : (oneOf Xs).ranges = oneF.ranges := six.ranges
  have hl : (oneOf Xs).lin = oneF.lin := six.lin
  have hsm : (oneOf Xs).given.plan.samples = oneF.given.plan.samples := six.samples
  obtain ⟨bw, hw⟩ := w_there hs scope
  have hw' : VerifiableInference.Desc.Key.sendW (oneOf Xs) pieces (AtPublicFiles.AtFiles.sentAt Xs.Y.D.1)
      (AtPublicFiles.AtFiles.groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hw
  obtain ⟨msg, hm, -⟩ := w_yes hw'
  have hm' : linMessageW oneF.lin = some msg := by
    rw [← hl]
    exact hm
  obtain ⟨hJ, -⟩ := keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hw
  have hP : (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P = sendingPar (oneOf Xs) pieces.w
      "W and what rides with it" msg (AtPublicFiles.AtFiles.groupsW Xs.Y.D.1 Xs.Y.told.1) := by
    unfold AtPublicFiles.Key.wJob at hJ
    rw [hm] at hJ
    exact (congrArg SendJob.P (Option.some.inj hJ)).symm
  have hride : (batchedRowsSending (X := X') (Rc := Rc) f Xs N).ride = rideW := by
    unfold AtPublicFiles.Key.wJob at hJ
    rw [hm] at hJ
    exact (congrArg SendJob.ride (Option.some.inj hJ)).symm
  have hlist : ∀ x ∈ (D Xs N Pl).first.blocksInOrder, ProofFile.Honest.Small.Listed x := fun x hx =>
    ProofFile.Honest.Small.lists_of_shaped ((planOk_all hs.named.plan).1 x hx).2
  have hlen := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  have ht19 := trees_all hs scope
  -- the three members
  have b0 := member0 (N := N) (Pl := Pl) hw
  have b1 := member1 (N := N) (Pl := Pl) hw
  have b17 := (member_back hs scope hw).2
  have hidxT : (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.trees.length = 1 := by
    show (sendingPar (oneOf Xs) _ _ _ _).trees.length = 1
    rw [trees_par _ oneF _ 0 _ "" _ _ [] hc, hi]
    exact trees_idx
  have hmsgT : (multiplicitiesSending (W₀ := W₀) (Rc := Rc) (X := X') f Xs).P.trees.length = 1 := by
    show (sendingPar (oneOf Xs) _ _ _ _).trees.length = 1
    rw [trees_par _ oneF _ 0 _ "" _ _ [] hc, hr]
    exact trees_msg
  have hwT : (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P.trees.length = 1 := by
    rw [hP, trees_par _ oneF _ 0 _ "" _ _ [] hc]
    exact trees_w msg hm'
  have h1 : treesTo (D Xs N Pl).first.blocksInOrder 1 = 1 := by
    have e := treesTo_succ b0
    have hc0 := (oracles_count (AtPublicFiles.Key.idx_seat (β := VerifiableInference.Desc.Key.LookupRecord)
      (Cl := Claim) (W := In1 W₀ Rc) (X := X') (oneOf Xs) pieces
      (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1 0
        (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1 0)) 0).2.2).trans hidxT
    exact e.trans (congrArg (fun z => treesTo (D Xs N Pl).first.blocksInOrder 0 + z) hc0)
  have h17 : treesTo (D Xs N Pl).first.blocksInOrder 17 = 5 := by
    have e18 := treesTo_succ b17
    have e19 := treesTo_succ (seal_at hs scope hw)
    rw [seal_none] at e19
    have hsh := (keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hw).2
    have hw1 : (bw.asBare.oracles.flatMap id).length = 1 := by
      rw [show bw.asBare.oracles = bw.oracles from rfl, oracles_count hsh.2.2]
      exact hwT
    rw [hw1] at e18
    have e19' : treesTo (D Xs N Pl).first.blocksInOrder 19 = treesTo (D Xs N Pl).first.blocksInOrder 18 := e19
    have e18' : treesTo (D Xs N Pl).first.blocksInOrder 18 = treesTo (D Xs N Pl).first.blocksInOrder 17 + 1 := e18
    omega
  refine
    { places := hK.places, idx := hK.idx, msg := hK.msg, w := hK.w, batt := hK.batt, pile := hK.pile
      weights := hK.weights, fitsIdx := ?_, fitsMsg := ?_, fitsW := ?_, sentMsg := ?_
      firstIsPlans := ?_, stages := ?_, lookupsTwo := ?_, toldThree := ?_, treesIdx := ?_
      treesMsg := ?_, treesW := ?_, treesAt1 := ?_, treesAt17 := ?_, sentAt0 := ?_, sentAt1 := ?_
      sentAt5 := ?_ }
  · rw [hK.idx]
    show sendFits (sendingPar (oneOf Xs) _ _ _ _) _ = true
    rw [sendFits_par _ oneF _ 0 _ "" _ _ [] hc, hi]
    exact fits_idx
  · rw [hK.msg]
    show sendFits (sendingPar (oneOf Xs) _ _ _ _) rideMsg = true
    rw [sendFits_par _ oneF _ 0 _ "" _ _ [] hc, hr]
    exact fits_msg
  · rw [hK.w, hP, hride, sendFits_par _ oneF _ 0 _ "" _ _ [] hc]
    exact fits_w msg hm'
  · rw [hr]
    exact message_size
  · unfold firstW
    rw [hr, hsm]
    exact first_is
  · rw [hr]
    exact stages_one
  · rw [hr]
    exact lookups_two
  · have hcs : (oneOf Xs).codes = Johnson.Top.H.csKey := six.codes
    have hn := Johnson.RunOne.KeyLetters.nums_front Xs N Pl hcs six.indexMasks six.ranges
    refine ⟨some_of_map hn.1, some_of_map hn.2, ?_⟩
    have h6 : (VerifiableInference.Desc.oraclesOf (D Xs N Pl).first.blocksInOrder).length = 6 := by
      have e := ht19
      unfold treesTo at e
      rw [List.take_of_length_le (by rw [hlen])] at e
      exact e
    show ((VerifiableInference.Desc.oraclesOf (D Xs N Pl).first.blocksInOrder ++ VerifiableInference.Desc.oraclesOf (D Xs N Pl).shared.blocksInOrder ++
      VerifiableInference.Desc.oraclesOf (D Xs N Pl).second.blocksInOrder)[5]?).isSome = true
    rw [List.append_assoc, List.getElem?_append_left (by rw [h6]; decide)]
    rw [List.getElem?_eq_getElem (by rw [h6]; decide)]
    rfl
  · rw [hK.idx]
    exact hidxT
  · rw [hK.msg]
    exact hmsgT
  · rw [hK.w]
    exact hwT
  · exact h1
  · exact h17
  · exact sent_of_member (r := _) (l := _) b0 rfl (by
      show 0 < (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X') Xs).P.trees.length
      rw [hidxT]
      decide) hlist
  · have e := sent_of_member (r := _) (l := _) b1 rfl (by
      show 0 < (multiplicitiesSending (W₀ := W₀) (Rc := Rc) (X := X') f Xs).P.trees.length
      rw [hmsgT]
      decide) hlist
    rw [h1] at e
    exact e
  · have hsh := (keyW_job (X' := X') (W₀ := W₀) (Rc := Rc) (f := f) (N := N) hw).2
    have e := sent_of_member (r := _) (l := _) b17 (show bw.rounds = _ from hsh.2.1) (by
      show 0 < (batchedRowsSending (X := X') (Rc := Rc) f Xs N).P.trees.length
      rw [hwT]
      decide) hlist
    rw [h17] at e
    exact e

end

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.first_public
#print axioms AtPublicFiles.FirstH.sendRound_behind
#print axioms AtPublicFiles.FirstH.sent_of_member
#print axioms AtPublicFiles.FirstH.sendFits_par
#print axioms AtPublicFiles.FirstH.trees_par
#print axioms AtPublicFiles.FirstH.fits_idx
#print axioms AtPublicFiles.FirstH.fits_msg
#print axioms AtPublicFiles.FirstH.fits_w
#print axioms AtPublicFiles.FirstH.trees_idx
#print axioms AtPublicFiles.FirstH.trees_msg
#print axioms AtPublicFiles.FirstH.trees_w
#print axioms AtPublicFiles.FirstH.message_size
#print axioms AtPublicFiles.FirstH.first_is
#print axioms AtPublicFiles.FirstH.stages_one
#print axioms AtPublicFiles.FirstH.lookups_two
