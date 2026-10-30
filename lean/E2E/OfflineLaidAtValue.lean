-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineLaidAtValue.lean: in scope, at the written book, the sixteen halves of the offline prover
are laid (`OfflineRowsLaid`, E2E/OfflineLaying.lean), and they have the numbers of parts that the
book's cuts have (`OfflineParts`).

  `send_laid`, `look_laid`, `batching_laid`, `quiet_laid`, `test_laid`, `guarded_laid`   by kind
  `offline_rows_laid`, `offline_parts`   the two statements

What is taken from the public files: `KeySourced` and scope. The written numbers are held by the
kernel lines of E2E/OfflineLaying.lean. Limits: those of that file. Nothing on any property.
-/
import E2E.OfflineLaying

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob proverSideOfProximityTest firstPart restPart)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces pieces)
open OnBytes.Slice (GF)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first sharedChainProverSidesInOrder)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull full_two chainPlaces Stated OneFull
  idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace locPlace omegaPlace
  zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace idxJob_stated msgJob_stated
  wJob_stated k13_stated k14_stated k14_sends_stated rides_full)
open AtPublicFiles.KeyValues (WitK oneOf)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced later_sourced)
open VerifierAndGoals (InScope)

section Kinds
variable {V W Y : Type} {K₀ : KeyPub}

/-- The written book's cut at a place of its table. -/
theorem cut_of (hK : fullPub = some K₀) {p : Place} {c : List Nat} (hm : (p, c) ∈ cutsTable) :
    (keyBook K₀).cuts.lookup p = some c :=
  beq_iff_eq.1 (List.all_eq_true.1 (of_atFull cuts_full hK) _ hm)

/-- **A sending of the first chain is laid.** -/
theorem send_laid (hK : fullPub = some K₀) (J : K1.SendJob W Y) {p : Place} (hp : J.P.place = p)
    (ha : (chainPlaces 0).contains p = true) (hn : partsAt p = 1) (hc : (p, [2]) ∈ cutsTable)
    (hs : Stated (keyBook K₀) (keyBook K₀).first ⟨p, 0⟩ (K1.sendPart (V := V) J)) :
    RowLaid (keyBook K₀) 0 (K1.proverSideOfSending J : Placed V W Y) := by
  subst hp
  refine laid_of_stated hK (Or.inl rfl) ha hn ⟨cut_of hK hc, ?_⟩
  intro i q hq
  match i, hq with
  | 0, hq =>
    obtain rfl := Option.some.inj hq
    exact hs
  | i + 1, hq => cases hq

/-- The written source's face is the written face. -/
theorem face_of_one {Xs : Source} (one : OneFull (oneOf Xs)) (i : Nat) :
    AtPublicFiles.KeyValues.faceAt Xs i = writtenFace i := by
  unfold AtPublicFiles.KeyValues.faceAt AtPublicFiles.KeyValues.lookAt writtenFace
    VerifiableInference.Desc.Key.lookupsOf
  rw [one.ranges, one.lin]

/-- A list's pairs with their numbers, read at the first alone. -/
theorem zipIdx_first {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    (l.zipIdx n).map (fun x => g x.1) = l.map g
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_first g l (n + 1)]

/-- The numbers of moves of a seated row at owners are its stages' numbers of rounds. -/
theorem seat_moves {V₁ W₁ X₁ Wk : Type} (o : K3.Owners) (R : K3.Reads) (J : K3.LookJobs Wk)
    (wit : W₁ → Wk) (a : K3.At) :
    (K3.proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts.map (·.moves.length) =
      (K3.stages a.face).map (K3.Stage.rounds a.face) := by
  show (((K3.lookRowOwned (V := Unit) o R J a).map
      (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)).map (·.moves.length)) = _
  rw [List.map_map]
  have e : ((fun p : Part V₁ W₁ X₁ => p.moves.length) ∘
      (Part.lift (V' := Unit) (Y := Unit) (fun _ => ()) wit (fun _ => ()) fun x _ => x)) =
      fun p : Part Unit Wk Unit => p.moves.length := by
    funext p
    exact List.length_map _
  rw [e, K3.lookRowOwned_moves]
  unfold K3.lookRow
  rw [List.map_map]
  have e2 : ((fun p : Part Unit Wk Unit => p.moves.length) ∘
      fun x : K3.Stage × Nat => (K3.partOf R J a x.1 x.2 : Part Unit Wk Unit)) =
      fun x => K3.Stage.rounds a.face x.1 := by
    funext x
    exact K3.partOf_moves R J a x.1 x.2
  rw [e2]
  exact zipIdx_first _ _ 0

/-- **A lookup is laid.** a: the lookup's place, the written face, and any rounds in front. hs: its
parts state what the book has for them. -/
theorem look_laid {V₁ W₁ X₁ Wk : Type} (hK : fullPub = some K₀) (i n : Nat)
    (ha : (chainPlaces 0).contains (lookPlace i) = true)
    (hf : lookupFits K₀ i n = true) (R : K3.Reads) (J : K3.LookJobs Wk) (wit : W₁ → Wk)
    (a : K3.At) (hp : a.place = lookPlace i) (hface : a.face = writtenFace i)
    (hn : partsAt (lookPlace i) = n)
    (hs : ∀ j q, (K3.proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (K3.keyOwners a.face) R J wit a).parts[j]? =
      some q → Stated (keyBook K₀) (keyBook K₀).first ⟨a.place, j⟩ q) :
    RowLaid (keyBook K₀) 0
      (K3.proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (K3.keyOwners a.face) R J wit a) := by
  obtain ⟨pl, fa, ba⟩ := a
  obtain rfl : pl = lookPlace i := hp
  obtain rfl : fa = writtenFace i := hface
  unfold lookupFits at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨h1, h2⟩ := hf
  have hlen : (K3.proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (K3.keyOwners (writtenFace i)) R J wit
      ⟨lookPlace i, writtenFace i, ba⟩).parts.length = n := by
    have e := congrArg List.length (seat_moves (V₁ := V₁) (X₁ := X₁) (K3.keyOwners (writtenFace i))
      R J wit ⟨lookPlace i, writtenFace i, ba⟩)
    rw [List.length_map, List.length_map] at e
    exact e.trans h2
  refine laid_of_stated hK (Or.inl rfl) ha ?_ ⟨?_, hs⟩
  · show partsAt (lookPlace i) = _
    rw [hlen]
    exact hn
  · show _ = some ((K3.proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) (K3.keyOwners (writtenFace i)) R J wit
      ⟨lookPlace i, writtenFace i, ba⟩).parts.map (·.moves.length))
    rw [seat_moves]
    exact h1

/-- **A test's half is laid**, at a job that agrees with a written one. -/
theorem test_laid {W' X' : Type} (hK : fullPub = some K₀) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) (J : TestJob W' X') (J₀ : TestJob Unit Unit)
    (hp : J.p = J₀.p) (hm : J.members = J₀.members) (hf : J.fresh = J₀.fresh)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J₀.p.nums.stages = s :: t :: rest)
    (hT : testStated (keyBook K₀) ch J₀ = true) (ha : (chainPlaces ch).contains J₀.p.place = true)
    (hn : partsAt J₀.p.place = 2) : RowLaid (keyBook K₀) ch (proverSideOfProximityTest J : Placed V W' X') := by
  have hs : RowStated (keyBook K₀) ch (proverSideOfProximityTest J : Placed V W' X') :=
    stated_of_test J s t rest (by rw [hp]; exact hst)
      (by rw [testStated_same _ _ J J₀ hp hm hf]; exact hT)
  refine laid_of_stated hK hch ?_ ?_ hs
  · show (chainPlaces ch).contains J.p.place = true
    rw [hp]
    exact ha
  · show partsAt J.p.place = 2
    rw [hp]
    exact hn

/-- The like behind the guard. -/
theorem guarded_laid {W' X' : Type} (hK : fullPub = some K₀) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) (J : TestJob W' X') (J₀ : TestJob Unit Unit)
    (hp : J.p = J₀.p) (hm : J.members = J₀.members) (hf : J.fresh = J₀.fresh)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J₀.p.nums.stages = s :: t :: rest)
    (hT : testStated (keyBook K₀) ch J₀ = true) (ha : (chainPlaces ch).contains J₀.p.place = true)
    (hn : partsAt J₀.p.place = 2) :
    RowLaid (keyBook K₀) ch (proverSideOfProximityTest J : Placed V W' X').needsField := by
  have hs : RowStated (keyBook K₀) ch (proverSideOfProximityTest J : Placed V W' X') :=
    stated_of_test J s t rest (by rw [hp]; exact hst)
      (by rw [testStated_same _ _ J J₀ hp hm hf]; exact hT)
  refine laid_of_stated hK hch ?_ ?_ hs.needsField
  · show (chainPlaces ch).contains J.p.place = true
    rw [hp]
    exact ha
  · show partsAt J.p.place = 2
    rw [hp]
    exact hn

/-- A half of the table of cuts is laid. -/
theorem row_of_table (hK : fullPub = some K₀) {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2)
    {h : Placed V W Y} {p : Place} {c : List Nat} {n : Nat} (hp : h.place = p)
    (hm : h.parts.map (·.moves.length) = c) (hl : h.parts.length = n) (hc : (p, c) ∈ cutsTable)
    (ha : (chainPlaces ch).contains p = true) (hn : partsAt p = n)
    (hs : ∀ i q, h.parts[i]? = some q → Stated (keyBook K₀) ((keyBook K₀).rowsOf ch) ⟨h.place, i⟩ q) :
    RowLaid (keyBook K₀) ch h := by
  refine laid_of_stated hK hch (by rw [hp]; exact ha) (by rw [hp, hl]; exact hn) ⟨?_, hs⟩
  rw [hp, hm]
  exact cut_of hK hc

/-- What `sharedChainProverSidesInOrder` lays is of the two lists. -/
theorem mem_weave {W₀ Rc X₀ : Type} {own send : List (Placed Empty (AtPublicFiles.KeyFile.In2 W₀ Rc) X₀)}
    {g : Placed Empty (AtPublicFiles.KeyFile.In2 W₀ Rc) X₀} (h : g ∈ sharedChainProverSidesInOrder own send) : g ∈ own ∨ g ∈ send := by
  unfold sharedChainProverSidesInOrder at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inr (Or.inr h))
  · exact List.mem_append.1 h

end Kinds

/-! ## The written lines of the three tests of the later chains -/

/-- The members of the test on the folded row's group. By evaluation. -/
theorem folded_members_full :
    [K12.AtProof.msgOf K12.AtProof.senderU (K14.jobU ⟨QK, 0⟩) 0,
      K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨QK, 0⟩) 1] =
      AtPublicFiles.KeyTest.jobFolded.members := by decide +kernel

/-- The members of the test on Omega's group. By evaluation. -/
theorem omega_members_full :
    [K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨QK, 0⟩) 0,
      K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨QK, 0⟩) 1] =
      AtPublicFiles.KeyTest.jobOmega.members := by decide +kernel

/-- The numbers of the test on Omega's group. By evaluation. -/
theorem omega_place_full : H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U) = H2K.Member.piKOFull := by
  first
    | decide +kernel
    | rfl

/-- The numbers of the last chain's test. By evaluation. -/
theorem own_place_full : AtPublicFiles.KeyLay.pWK PF = H2K.Member.piKWFull := by
  first
    | decide +kernel
    | rfl

/-- The members of the last chain's test, at the written notices. -/
def ownMembersAt (wNotices : Array OnBytes.OracleNotice) : List (Addr × Nat × Due) :=
  [(AtPublicFiles.KeyTest.sIdx, 0, K1.dueMsg keyFull.codes keyFull.once.input.shape none),
    (AtPublicFiles.KeyTest.sW, 0, K1.dueMsg keyFull.codes (wNotices.getD 0 default).shape
      (AtPublicFiles.KeyBook.rideW 0)),
    K12.AtProof.msgOf K12.AtProof.senderO (K14.jobOmega ⟨QK, 0⟩) 0]

/-- They are the written job's. By evaluation. -/
theorem own_members_full :
    ownMembersAt ((OnBytes.linMessageW keyFull.once.shape).getD #[]) =
      AtPublicFiles.KeyTest.jobOwn.members := by decide +kernel

/-- The written shape has a message W, of two notices, and it splits; the batching has 18 variables.
By evaluation. -/
theorem shape_full : (OnBytes.linMessageW keyFull.once.shape).map Array.size = some 2 ∧
    keyFull.once.shape.sharedSplitNeeded = true ∧ keyFull.once.shape.kCol = 18 := by decide +kernel

/-- The written book has 18 such variables too. By evaluation. -/
theorem kCol_full : atFull (fun K => K.kCol == 18) = true := by decide +kernel

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.send_laid
#print axioms AtPublicFiles.OfflineRows.look_laid
#print axioms AtPublicFiles.OfflineRows.test_laid
#print axioms AtPublicFiles.OfflineRows.guarded_laid
