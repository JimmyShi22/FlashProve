-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SegmentAlike.lean: the kind "the code switch" (K2): THE NAMED
STEP OF THE LAW ON THE CLOSING's REFUSALS, PROVED (`SegmentAlike`, Honest/K2/Law/ReturnsTop.lean),
AND SO THE LAW ITSELF (`ReturnsLaw`, Honest/K2/Exact.lean). Definitions; statements with their
proofs. The law says nothing on what a run shows: it is on refusals alone.

  `Laid`, `SameShapes`   a message's shape with what stands in its main rows; two lists of such with
                    the same shapes, member by member
  `SameShapes.append`, `same_map`, `map_fst_same`, `zipIdx_same`   tools on such lists
  `dataAtOf`, `inFirstOf`, `laterStep`, `laterOf`   the two lists that `segmentGroupRows`
                    (Honest/K2/Closing.lean) makes of a segment's messages, by name
  `rowsCore`        that text again, with the two lists as letters; `segmentRows_eq`: it is that
                    text
  `inFirst_same`, `later_fold`, `later_same`   at two runs the two lists have the same shapes
  `rowsM_alike`     the rows of a list of messages are made, or refused, alike
  `rowsCore_alike`, `segmentRows_alike`   so for a segment's group's rows: with the same members
  `segmentAlike`    THE NAMED STEP
  `returnsLaw`      THE LAW: where a place passes the public test `closingOk`, the lot's closing
                    returns, at every input, list of challenges and carried coins, just where
                    `publicOk` says yes at the input's public instance

Limits. THAT THE TEST `closingOk` SAYS YES, at the table at which the law stands (`freshTable`), IS
PROVED FOR NO PLACE IN THIS FILE; under the head, `closing_at_head`
(Honest/K2/Law/ClosingAtHead.lean) proves that it says yes at each place of the plan. At a made-up
place, and at a table written out for the test in that table's stead, a test says yes, and no at two
bent places (Honest/K2/ToySim.lean). Nothing on what the closing leaves. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MessageAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.ReturnsTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows zeroG)

/-! ## Lists of messages with the same shapes -/

/-- A message's shape, with what stands in its main rows. -/
abbrev Laid : Type := OnBytes.OracleShape × (Nat → Nat → Cb.Gl.E)

/-- The same shapes, member by member. -/
def SameShapes (A A' : List Laid) : Prop := List.Forall₂ (fun a b : Laid => a.1 = b.1) A A'

theorem SameShapes.append {A A' B B' : List Laid} (h : SameShapes A A') (g : SameShapes B B') :
    SameShapes (A ++ B) (A' ++ B') := by
  induction h with
  | nil => exact g
  | cons h₁ _ ih => exact List.Forall₂.cons h₁ ih

theorem same_map {ι : Type} (sh : ι → OnBytes.OracleShape) (f g : ι → Nat → Nat → Cb.Gl.E) :
    ∀ l : List ι, SameShapes (l.map fun x => (sh x, f x)) (l.map fun x => (sh x, g x))
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons rfl (same_map sh f g l)

theorem map_fst_same {A A' : List Laid} (h : SameShapes A A') :
    A.map (·.1) = A'.map (·.1) := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => rw [List.map_cons, List.map_cons, h₁, ih]

theorem zipIdx_same {A A' : List Laid} (h : SameShapes A A') : ∀ n : Nat,
    List.Forall₂ (fun x y : Laid × Nat => x.1.1 = y.1.1 ∧ x.2 = y.2) (A.zipIdx n)
      (A'.zipIdx n) := by
  induction h with
  | nil => exact fun _ => List.Forall₂.nil
  | cons h₁ _ ih =>
    intro n
    rw [List.zipIdx_cons, List.zipIdx_cons]
    exact List.Forall₂.cons ⟨h₁, rfl⟩ (ih (n + 1))

/-! ## The two lists, by name -/

/-- What stands in the main rows of the message number n of a segment's first sending. -/
def dataAtOf (S : SegmentPub) (prev : Option Left) (own : Nat → Nat → Nat → Cb.Gl.E) (n : Nat) :
    Nat → Nat → Cb.Gl.E :=
  match prev with
  | some W => mainRows S.sizes W own n
  | none => own n

/-- The members in the first sending. -/
def inFirstOf (S : SegmentPub) (prev : Option Left) (own : Nat → Nat → Nat → Cb.Gl.E) :
    List Laid :=
  (((S.sent.headD #[]).toList.take ((S.sent.headD #[]).size - 1)).zipIdx.map fun x =>
    (x.1.shape, dataAtOf S prev own x.2))

/-- One later sending. -/
def laterStep (own : Nat → Nat → Nat → Cb.Gl.E) (s : List Laid × Nat)
    (a : Array OnBytes.OracleNotice) : List Laid × Nat :=
  (s.1 ++ a.toList.zipIdx.map fun x => (x.1.shape, own (s.2 + x.2)), s.2 + a.size)

/-- The members in the later sendings. ps: a fold stands in front. -/
def laterOf (S : SegmentPub) (ps : Bool) (own : Nat → Nat → Nat → Cb.Gl.E) : List Laid × Nat :=
  (S.sent.drop 1).foldl (laterStep own)
    ([], (S.sent.headD #[]).size - 1 - if ps then 1 + S.sizes.kept.length else 0)

/-- `segmentGroupRows`' text, with the two lists as letters. -/
def rowsCore (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    Except String GroupRows := do
  let codes := S.sizes.codes
  let first := S.sent.headD #[]
  if first.isEmpty then throw "a segment's first sending holds no message"
  if ps && S.sizes.kept.length != S.sizes.target.kept.size then
    throw "a switch has not one target for each kept member"
  if ps && S.sizes.kept != prevKept then
    throw "a switch's kept members are not those that the fold in front left"
  if ps && !S.sizes.roomy then
    throw "the sizes do not fit a switch"
  let freshNo := first.size - 1
  let flags :=
    (if ps then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept
  if flags.length != A.length + B.1.length then
    throw "a segment's own messages are not marked one by one"
  let skip := if withFresh then 1 else 0
  let rows₀ ← A.zipIdx.mapM fun x =>
    (k (base + x.2)).bind (messageRows table codes x.1.1 none x.1.2)
  let fresh ←
    if withFresh then
      ((k (base + freshNo)).bind
        (messageRows table codes (first.getD freshNo default).shape (some S.foldVars)
          fun _ _ => zeroG)).map some
    else pure none
  let rows₁ ← B.1.zipIdx.mapM fun x =>
    (k (base + freshNo + skip + x.2)).bind (messageRows table codes x.1.1 none x.1.2)
  pure ⟨(((A ++ B.1).map (·.1)).zip flags).map fun x => ⟨x.1, x.2⟩, rows₀ ++ rows₁, fresh⟩

theorem segmentRows_eq (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Cb.Gl.E)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    segmentGroupRows table S prev prevKept own k base withFresh =
      rowsCore table S prev.isSome prevKept (inFirstOf S prev own) (laterOf S prev.isSome own) k
        base withFresh := rfl

theorem inFirst_same (S : SegmentPub) (prev prev' : Option Left)
    (own own' : Nat → Nat → Nat → Cb.Gl.E) :
    SameShapes (inFirstOf S prev own) (inFirstOf S prev' own') :=
  same_map (fun x : OnBytes.OracleNotice × Nat => x.1.shape) _ _ _

theorem later_fold (own own' : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (l : List (Array OnBytes.OracleNotice)) (s s' : List Laid × Nat),
      SameShapes s.1 s'.1 → s.2 = s'.2 →
        SameShapes (l.foldl (laterStep own) s).1 (l.foldl (laterStep own') s').1
  | [], _, _, h, _ => h
  | a :: l, s, s', h, e =>
    later_fold own own' l (laterStep own s a) (laterStep own' s' a)
      (h.append (same_map (fun x : OnBytes.OracleNotice × Nat => x.1.shape) _ _ _))
      (congrArg (· + a.size) e)

theorem later_same (S : SegmentPub) (ps : Bool) (own own' : Nat → Nat → Nat → Cb.Gl.E) :
    SameShapes (laterOf S ps own).1 (laterOf S ps own').1 :=
  later_fold own own' _ _ _ List.Forall₂.nil rfl

/-! ## Alike -/

theorem rowsM_alike (table : FreshTable) (codes : OnBytes.Codes)
    {k k' : Nat → Except String Stretch} (hk : CoinsAlike k k') {A A' : List Laid}
    (h : SameShapes A A') (off : Nat) :
    Alike Any
      (A.zipIdx.mapM fun x => (k (off + x.2)).bind (messageRows table codes x.1.1 none x.1.2))
      (A'.zipIdx.mapM fun x =>
        (k' (off + x.2)).bind (messageRows table codes x.1.1 none x.1.2)) := by
  refine Alike.mono (fun _ _ _ => trivial) (Alike.mapM (R := Any) ?_)
  refine List.Forall₂.imp ?_ (zipIdx_same h 0)
  rintro ⟨⟨sa, da⟩, na⟩ ⟨⟨sb, db⟩, nb⟩ ⟨h₁, h₂⟩
  obtain rfl : sa = sb := h₁
  obtain rfl : na = nb := h₂
  exact Alike.bind (hk _) fun _ _ hs => messageRows_alike table codes sa none da db hs

theorem rowsCore_alike (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) {A A' : List Laid} {B B' : List Laid × Nat}
    (hA : SameShapes A A') (hB : SameShapes B.1 B'.1) {k k' : Nat → Except String Stretch}
    (hk : CoinsAlike k k') (base : Nat) (withFresh : Bool) :
    Alike (fun R R' : GroupRows => R.members = R'.members)
      (rowsCore table S ps prevKept A B k base withFresh)
      (rowsCore table S ps prevKept A' B' k' base withFresh) := by
  have hm : (A ++ B.1).map (·.1) = (A' ++ B'.1).map (·.1) := map_fst_same (hA.append hB)
  have lA : A.length = A'.length := List.Forall₂.length_eq hA
  have lB : B.1.length = B'.1.length := List.Forall₂.length_eq hB
  unfold rowsCore
  dsimp only
  rw [hm, lA, lB]
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.bind (rowsM_alike table _ hk hA _) fun _ _ _ => ?_
  refine Alike.ite ?_ ?_
  · refine Alike.bind (R := Any)
      (Alike.map (Alike.bind (hk _) fun _ _ hs => messageRows_alike table _ _ _ _ _ hs)
        fun _ _ _ => trivial) fun _ _ _ => ?_
    refine Alike.bind (rowsM_alike table _ hk hB _) fun _ _ _ => ?_
    exact rfl
  · refine Alike.bind (R := Any) (Alike.ok trivial) fun _ _ _ => ?_
    refine Alike.bind (rowsM_alike table _ hk hB _) fun _ _ _ => ?_
    exact rfl

theorem segmentRows_alike (table : FreshTable) (S : SegmentPub) (prev prev' : Option Left)
    (prevKept : List OnBytes.OracleShape) (own own' : Nat → Nat → Nat → Cb.Gl.E)
    {k k' : Nat → Except String Stretch} (hp : prev.isSome = prev'.isSome)
    (hk : CoinsAlike k k') (base : Nat) (withFresh : Bool) :
    Alike (fun R R' : GroupRows => R.members = R'.members)
      (segmentGroupRows table S prev prevKept own k base withFresh)
      (segmentGroupRows table S prev' prevKept own' k' base withFresh) := by
  rw [segmentRows_eq, segmentRows_eq, hp]
  exact rowsCore_alike table S _ prevKept (inFirst_same S prev prev' own own')
    (later_same S _ own own') hk base withFresh

/-- **The named step.** -/
theorem segmentAlike : SegmentAlike := by
  intro table S prev prev' prevKept own own' heard heard' k k' base hp hk
  have hγ : (challengesOr0 heard S.gamma).length = (challengesOr0 heard' S.gamma).length := by
    simp [challengesOr0]
  unfold segmentLeft
  dsimp only
  refine Alike.bind (segmentRows_alike table S prev prev' prevKept own own' hp hk base true)
    fun R R' hR => ?_
  rw [hR, hγ]
  split
  · exact Alike.error _
  · simp only [pure_bind]
    split
    · exact Alike.error _
    · exact rfl

variable {W₀ Rc Xi Tr : Type}

/-- **THE LAW.** -/
theorem returnsLaw (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace) :
    ReturnsLaw D readers lay segs p :=
  returnsLaw_of segmentAlike D readers lay segs p

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.Laid
#print axioms ProofFile.Honest.K2.Law.SameShapes
#print axioms ProofFile.Honest.K2.Law.SameShapes.append
#print axioms ProofFile.Honest.K2.Law.same_map
#print axioms ProofFile.Honest.K2.Law.map_fst_same
#print axioms ProofFile.Honest.K2.Law.zipIdx_same
#print axioms ProofFile.Honest.K2.Law.dataAtOf
#print axioms ProofFile.Honest.K2.Law.inFirstOf
#print axioms ProofFile.Honest.K2.Law.laterStep
#print axioms ProofFile.Honest.K2.Law.laterOf
#print axioms ProofFile.Honest.K2.Law.rowsCore
#print axioms ProofFile.Honest.K2.Law.segmentRows_eq
#print axioms ProofFile.Honest.K2.Law.inFirst_same
#print axioms ProofFile.Honest.K2.Law.later_fold
#print axioms ProofFile.Honest.K2.Law.later_same
#print axioms ProofFile.Honest.K2.Law.rowsM_alike
#print axioms ProofFile.Honest.K2.Law.rowsCore_alike
#print axioms ProofFile.Honest.K2.Law.segmentRows_alike
#print axioms ProofFile.Honest.K2.Law.segmentAlike
#print axioms ProofFile.Honest.K2.Law.returnsLaw
