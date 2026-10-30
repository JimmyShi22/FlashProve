-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/PileSeat.lean
(it stands on Johnson/IMR/SeatKeeps.lean): ONE INDUCTION ALONG THE FOLD
ON "WHO WRITES THE PILE", GENERAL IN A SENTENCE P ON THE VERIFIER'S STATE.

Main names (namespace `Meaning.K2`).
  `Rides P s s'` := P s → P s'. **`PileLaw P`**: WHAT IS ASKED OF P: same: it rides over whatever
    leaves the pile (`PileStays`) · zero: over link 0's "opened" (`openLayZero`: it writes the index
    masks' number) · push: over "cleared" (`clearWith` at the row's function `Pend.pendingRowO lay …
    lin`: the form of both the frames' `rowOf` and `Close.tailHead`: read at
    Johnson/Top/H0/Walk/FrameLot.lean:60 and Johnson/Desc/First/Close/TailHead.lean:64) · batch:
    over kind K13's batching (`K13.atM3`).
  `readsQuietAt_pile`; `framesOf_rides`; **`seatKeeps_rides`** : `SeatKeeps (Rides P)`;
    **`seatBack_rides`** : `SeatBack (Rides P)`: every field of the two structures.
  **`descPure_rides`**: at the IOP as written in Lean for the proof file (`ProofFile.onlineDescription`'s value F =
    `fileDescBy … c`): if every sub-protocol of `c.blocksInOrder` passes its own test on the list of rounds
    (`Block.planOk`): whatever state `foldBlocks ft (c.blocksInOrder.take k) s rs cols` returns meets P if s
    does.

Every "there is", walked. Z, A, B, c: tied by `pureRoad.pub … = .ok Z` and F's equation, as in the
machine's own tops.
CAN THE PREMISE ON `planOk` BE MET? It is each sub-protocol's own field, not other files' list of
named tests. A measure, over a trial build,
printed "planOk true" for the proof file at the small and at the full size [not run here].
Limits. THE SEAT is the harness's (Johnson/Desc/ProofFile/…; Johnson/IMR/SeatKeeps.lean's head).
The step from "reached" to such a fold is another file's lemma. Nothing on soundness or on hiding.

-/
import Johnson.IMR.SeatKeeps
import Johnson.Desc.First.Pile.PileSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)
open Johnson.Desc.First.Walk

/-! ## The quiet step behind the reads, at the seat -/

theorem readsBlockAt_pile {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole PileStays b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_pile _
  · split at h
    · cases h
      exact headReads_pile _
    · cases h

theorem readsQuietAt_pile {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : Whole PileStays b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtO_pile h
    | exact readsBlockAt_pile h
    | cases h

/-! ## A sentence on the pile, along the whole first chain -/

/-- The relation of a sentence P on the verifier's state: P goes on. -/
def Rides (P : S → Prop) (s s' : S) : Prop := P s → P s'

/-- **WHAT IS ASKED OF A SENTENCE P**: it rides over whatever leaves the pile, and over the three
writers. -/
structure PileLaw (P : S → Prop) : Prop where
  /-- over a step that leaves the rows on the table, the index masks' number and the stand -/
  same : ∀ s s', PileStays s s' → P s → P s'
  /-- link 0's "opened": it writes the index masks' number -/
  zero : ∀ (Q : LayPar) (fvs : List Bool) (kCol : Nat), Fn (Rides P) (openLayZero Q fvs kCol)
  /-- "cleared": it lays a row at the pile's end -/
  push : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (lay : WsLay) (lin : Params.LinShape), Fn (Rides P) (clearWith X counts left
      fun masks w claims os => Pend.pendingRowO lay masks w claims lin os)
  /-- kind K13's batching: the pile becomes the one row -/
  batch : ∀ p : K13.Where, Decides (Rides P) (K13.atM3 (Cl := Unit) p)

variable {P : S → Prop}

theorem rides_refl (s : S) : Rides P s s := fun h => h

theorem rides_trans (a b c : S) (h : Rides P a b) (k : Rides P b c) : Rides P a c :=
  fun x => k (h x)

theorem whole_rides (L : PileLaw P) {Cl : Type} {b : Block S Cl} (W : Whole PileStays b) :
    Whole (Rides P) b := whole_mono (fun s s' q => L.same s s' q) W

theorem fn_rides (L : PileLaw P) {f : S → Except String S} (h : Fn PileStays f) :
    Fn (Rides P) f := fun s t k => L.same s t (h s t k)

open Johnson.Desc.First.Walk.Seat in
/-- Every row of the links' frames. -/
theorem framesOf_rides (L : PileLaw P) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (Rides P) f.lay ∧ Fn (Rides P) f.opened ∧ Fn (Rides P) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_rides L (layFront_pile l), fun s t k I => by cases k; exact I, L.push _ _ _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_rides L (layFront_pile 0), L.zero _ _ _, L.push _ _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_rides L (layFront_pile l), fn_rides L (openAtt_pile _), L.push _ _ _ _ _⟩
      · cases e
        exact ⟨fn_rides L (layFront_pile l), fn_rides L (openLay_pile _), L.push _ _ _ _ _⟩

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE SUB-PROTOCOLS BEHIND THE LAST LINK.** -/
theorem seatKeeps_rides (L : PileLaw P) : SeatKeeps (Rides P) where
  refl := rides_refl
  trans := rides_trans
  frames := fun _ h => framesOf_rides L h
  k1First := fun q gp _ => whole_rides L (firstAtS_pile q gp)
  k1Later := fun q gp l p m a _ => whole_rides L (laterAt_pile q gp l p m a)
  reads := fun h => whole_rides L (readsQuietAt_pile h)
  k3 := fun c r X cs' sh' a _ h => whole_rides L (theStated_pile c r X cs' sh' a h)
  k4 := fun p => whole_rides L (blockAtC_pile p)
  k5 := fun W l g bf _ h => whole_rides L (k5AtN_pile W l g bf h)
  k6 := fun h => whole_rides L (seatedClaims_pile h)
  k7 := fun W l => whole_rides L (k7Of_pile W l)
  k8 := fun p => whole_rides L (k8Whole_pile p)
  k11 := fun Q => whole_rides L (headMerge11_pile Q)
  closeOf := fun p Q b hb => whole_rides L (closeOf_pile p Q b hb)
  batch := fun p _ hf => batch_over rides_trans L.same p hf
  k2 := fun p _ => whole_rides L (k2_pile p)
  front := fun tl => fn_rides L (headFrontQ_pile tl)
  openQ := fun Q _ => fn_rides L (headOpenQ_pile Q)
  finFront := fn_rides L finishFrontQ_pile
  finBehind := fn_rides L finishBehindQ_pile

/-- **THE MAKERS BEHIND THE LAST LINK.** -/
theorem seatBack_rides (L : PileLaw P) : SeatBack (Rides P) where
  k12 := fun _ _ => whole_rides L (atFinish_pile _)
  k13M3 := fun p => ⟨L.batch p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p Q _ => whole_rides L (atM4_pile p Q)

/-- **THE FOLD's FACT, GENERAL IN THE SENTENCE**: at the IOP as written in Lean for the proof file
(`ProofFile.onlineDescription`'s value): where every sub-protocol of the request's own chain passes its test on
the list of rounds: whatever state a fold over a front stretch of that chain returns, from the
chain's own start at any public part, meets P if the start does. -/
theorem descPure_rides (L : PileLaw P) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (k ft : Nat) (s : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn)
        (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
        foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r → P s → P r.1) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ :=
    descPure_flat (seatKeeps_rides L) (seatBack_rides L) (fun _ _ => trivial) h
  refine ⟨Z, A, B, c, h1, h2, fun hp n ft s rs cols r hf => ?_⟩
  exact Keeps.foldBlocks_keeps (Rides P) rides_refl rides_trans ft (c.blocksInOrder.take n)
    (fun b hb => k b (List.mem_of_mem_take hb) (hp b (List.mem_of_mem_take hb))) s rs cols r hf

#print axioms readsBlockAt_pile
#print axioms readsQuietAt_pile
#print axioms rides_refl
#print axioms rides_trans
#print axioms whole_rides
#print axioms fn_rides
#print axioms framesOf_rides
#print axioms seatKeeps_rides
#print axioms seatBack_rides
#print axioms descPure_rides

end Meaning.K2
