-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/DoorOnShapes.lean: CONDITIONAL: on the head at a return of the maker and on
TWO NAMED PREMISES, NOT PROVED HERE, one on each of the two earlier chains. THE FULL SIZE ALONE.
The shared chain's is had under the head (AtFullSide/LaterThreads/SharedEndShape.lean), the first
chain's from a closed run on shapes (AtFullSide/LaterThreads/FirstEndShapeOfRun.lean).

What is here. THE PREMISE door OF AtFullSide/LaterThreads/FramesOfTheLastThread.lean (DoorHasTheShape:
the last chain's first state has one shape) BROUGHT DOWN TO ONE SENTENCE ON THE FIRST CHAIN's END AND
ONE ON THE SHARED CHAIN's END, each on the verifier's own fold over that chain alone.

  HandedShape, handedShape     what the last chain's start reads of the first chain's end, without a
                               field element: the statement's and the book's shapes, the count of
                               roots, the mark on the statement, the numbers of W, of the own group
                               and of the mask, the mark on the one pending row's weights
  sharedOutShape               the like of the shared chain's end (the library's SharedSh,
                               E2E/KeyShapeDoor.lean)
  doorShape                    the last chain's first shape, of these two
  shape_of_the_start           **what start₃E returns has that shape**: no premise but its return
  FirstEndHasTheShape          THE FIRST CHAIN's SHARE: a definition, meant as a hypothesis
  SharedEndHasTheShape         THE SHARED CHAIN's SHARE: a definition, meant as a hypothesis
  sharedEnd_of_sharedSh        that share, from the library's own reader sharedSh at the last state
  door_of_the_two_ends         **the two shares give DoorHasTheShape at doorShape of the two values**

Not shown here. The two shares, at any value. One value serves every instance that passes okStart and
whose key has the plan's sizes, at the shared chain by `shared_end_at_the_head`, at the first chain by
`first_end_shape_of_run`, given the whole run on shapes and one closed line at its end: if that run
refused at one member, that law would be empty.
Each names the verifier's fold alone: no thread, no prover, no coin. Nothing on soundness, on
completeness, on hiding or on any other property.
No property is claimed.
-/
import AtFullSide.LaterThreads.FramesOfTheLastThread
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor
import Johnson.Desc.Third.Law.AtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open OnBytes
open OnBytes.Params (LinShape)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SharedSh weightsB)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Third (S₃ SharedOut FirstEnd₃ start₃E firstOutFrom firstOfS
  sharedOfEnd)
open ToldDesc (p14At)

/-- **What the last chain's start reads of the first chain's end, without a field element.** -/
structure HandedShape where
  st : StSh
  book : BookSh
  roots : Nat
  /-- the mark on the statement -/
  tidy : Bool
  w : Nat
  own : Nat
  mask : Option Nat
  /-- the mark on the one pending row's weights -/
  weights : Bool
  deriving DecidableEq, Repr

/-- The reader, of the seven things one by one. Nothing unless just one row is pending. -/
def handedShapeOf (S : LinShape) (st : Statement) (book : TreeBook) (roots w own : Nat)
    (mask : Option Nat) (pile : List TensorRow) : Option HandedShape :=
  match pile with
  | [r] => some ⟨stSh st, bookSh book, roots, stTidyB st, w, own, mask,
      weightsB S (linLayOmega st.codes S) r.g⟩
  | _ => none

/-- **The reader.** -/
def handedShape (S : LinShape) (f : FirstEnd₃) : Option HandedShape :=
  handedShapeOf S f.st f.book f.roots f.w f.own f.mask f.pending

/-- **The reader at the shared chain's end.** -/
def sharedOutShape (o : SharedOut) : SharedSh :=
  ⟨stTidyB o.st, stSh o.st, bookSh o.book, o.psi.length, o.omega⟩

/-- **The last chain's first shape, of the two ends' shapes.** -/
def doorShape (a : HandedShape) (b : SharedSh) : Sh₃ :=
  (⟨a.st, a.book, 0⟩,
    ⟨a.tidy, a.w, a.own, a.mask, some ⟨a.weights, b.tidy, b.st, b.book, b.psi, b.omega⟩, noId,
      a.roots + 1⟩)

/-- **WHAT THE START RETURNS HAS THE SHAPE doorShape OF THE TWO ENDS' SHAPES.** -/
theorem shape_of_the_start (codes : Codes) (S : LinShape) (st : Statement) (book : TreeBook)
    (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (returns : start₃E codes S st book roots w own mask pile o = .ok s₀) :
    ∃ a, handedShapeOf S st book roots w own mask pile = some a ∧
      sh₃ S s₀ = doorShape a (sharedOutShape o) := by
  obtain ⟨g, made, started⟩ :=
    VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ returns
  obtain ⟨-, -, rfl⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ started
  unfold firstOutFrom at made
  split at made
  · rename_i r
    try dsimp only at made
    repeat' (split at made)
    all_goals first
      | (cases made; exact ⟨_, rfl, rfl⟩)
      | (cases made)
  · cases made

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **THE FIRST CHAIN's SHARE**: at an instance that passes okStart and whose key has the
plan's sizes, what is handed of a state that the
verifier's fold over the first chain returns has the shape a. A definition, meant as a hypothesis. -/
def FirstEndHasTheShape (h : HeadAtReturn files A) (a : HandedShape) : Prop :=
  ∀ (x : ProofFile.Inst) (rounds : List Fmt.RoundView) (columns : List VerifiableInference.Desc.OpenedColumn)
    (last : h.description.S₁) (handed : FirstEnd₃), h.description.okStart x = true →
    KeyHasTheSizes h x →
    VerifiableInference.Desc.foldBlocks 0 h.description.first.blocksInOrder
      (h.description.start₁ (h.description.pub x)) rounds columns = .ok (last, [], []) →
    firstOfS last = some handed → handedShape (p14At A.Z).S handed = some a

/-- **THE SHARED CHAIN's SHARE**: at an instance that passes okStart and whose key has the
plan's sizes, the end of a state that the
verifier's fold over the shared chain returns has the shape b. A definition, meant as a hypothesis.
-/
def SharedEndHasTheShape (h : HeadAtReturn files A) (b : SharedSh) : Prop :=
  ∀ (x : ProofFile.Inst) (rounds : List Fmt.RoundView) (columns : List VerifiableInference.Desc.OpenedColumn)
    (last : h.description.S₂) (ending : OnBytes.Proof.SharedEnd), h.description.okStart x = true →
    KeyHasTheSizes h x →
    VerifiableInference.Desc.foldBlocks 0 h.description.shared.blocksInOrder
      (h.description.start₂ (h.description.pub x)) rounds columns = .ok (last, [], []) →
    Desc.K14.ended last = some ending → sharedOutShape (sharedOfEnd ending) = b

/-- What the last chain takes of the shared chain's end has the shape that the library's reader
sharedSh (E2E/KeyShapeDoor.lean) reads off that chain's last state. -/
theorem sharedOutShape_of_ended {last : Desc.K14.St} {ending : OnBytes.Proof.SharedEnd}
    (isEnded : Desc.K14.ended last = some ending) :
    sharedOutShape (sharedOfEnd ending) = AtPublicFiles.AtFiles.sharedSh last := by
  unfold Desc.K14.ended at isEnded
  split at isEnded
  · cases isEnded
    rfl
  · cases isEnded

/-- **The shared chain's share, from the library's own reader at the last state**: the form in which
a run on shapes over that chain gives it (sharedOf_eq, E2E/KeyShapeSharedChain.lean). -/
theorem sharedEnd_of_sharedSh (h : HeadAtReturn files A) {b : SharedSh}
    (reads : ∀ (x : ProofFile.Inst) (rounds : List Fmt.RoundView) (columns : List VerifiableInference.Desc.OpenedColumn)
      (last : h.description.S₂), h.description.okStart x = true → KeyHasTheSizes h x →
      VerifiableInference.Desc.foldBlocks 0 h.description.shared.blocksInOrder
        (h.description.start₂ (h.description.pub x)) rounds columns = .ok (last, [], []) →
      AtPublicFiles.AtFiles.sharedSh last = b) : SharedEndHasTheShape h b :=
  fun x rounds columns last _ fit sizes fold isEnded =>
    (sharedOutShape_of_ended isEnded).trans (reads x rounds columns last fit sizes fold)

/-- CONDITIONAL on the two shares. **THE LAST CHAIN's FIRST STATE HAS THE SHAPE doorShape a b.** -/
theorem door_of_the_two_ends (h : HeadAtReturn files A) {a : HandedShape} {b : SharedSh}
    (first : FirstEndHasTheShape h a) (shared : SharedEndHasTheShape h b) :
    DoorHasTheShape h (doorShape a b) := by
  intro x r₁ r₂ c₁ c₂ e₁ e₂ s₀ fit sizes fold₁ fold₂ started
  obtain ⟨handed, ending, -, isHanded, isEnded, returns⟩ :=
    K14.start_at_last A.Z h.places h.firstChain _ e₁ e₂ s₀ started
  obtain ⟨a', read, shape⟩ := shape_of_the_start _ _ _ _ _ _ _ _ _ _ _ returns
  obtain rfl : a' = a :=
    Option.some.inj (read.symm.trans (first x r₁ c₁ e₁ handed fit sizes fold₁ isHanded))
  rw [shape, shared x r₂ c₂ e₂ ending fit sizes fold₂ isEnded]

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.shape_of_the_start
#print axioms AtFullSide.LaterThreads.sharedEnd_of_sharedSh
#print axioms AtFullSide.LaterThreads.door_of_the_two_ends
