-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/KeepsOfMeans.lean: SIX LINES OF K4's ROW's STRUCTURE `K4Keeps`
(K4PromiseBehind.lean; in the form in which `k4Keeps_at`, K4AtMg.lean, takes them) AS THEOREMS OUT
OF THE STRUCTURE OF EQUATIONS `K4Means` (K4Means.lean): dec · inOrder · keepP · restP · restQ (the
public items of other kinds that are open across K4's sub-protocol) · keepT (the public items that
are tied to open items). Definitions (two tests on the public parameters), statements and proofs:
the sorts, then a call a sort (Riders/PubKept.lean).

  `pubSort`, `k4PubFit`: WHICH PUBLIC ITEMS OF OTHER KINDS ARE OPEN ACROSS K4 (by reading the
    promise's table's rows and the layers' doors; the test says it with code): linkFresh m · lookOut
    m 2 · "ledger.treesAre" at m · AND EVERY NAME AT THE DOOR OF THE SORT rest, A PARAMETER: no name
    of another kind stands in this file (the list, and the line `K4Kept` at it:
    Riders/KeptNames.lean).
  `tiedSort`, `k4TiedFit`: WHICH ARE TIED TO ITEMS OPEN IN FRONT: indexIs · indexThere (pinI) ·
    formsInT m 2 "objects".
  **`dec_of_means`** (under hdecT) · **`inOrder_of_means`** (under hbase: the base letter's conjunct
    rides).
  `linkFreshB_kept` · `liveIsB_kept` · `k3OnOutAt_kept`: the lookups' three tests ride past an
    accept of K4's.
  **`restQ_of_means`**: under the test, and hpc (the lookup on the calls stands at piece 2 of
    segment m).
  **`keepP_of_means`** (under the test) · **`restP_of_means`** (under hDoorP): the sentences without
    a test: they read no state at every item but left | leftOn.
  **`keepT_of_means`**: under the test, and ONE LINE: formsInT m 2 "objects" rides past an accept:
    the lookup's own runs' test at a later ledger: THE TWIN OF THE LINE objects: owed.

Limits. The tests are premises here (Riders/PlanFull.lean evaluates them by Lean's kernel at the
full size's written lists). The names that only
carry a fact on every reached state across many kinds' sub-protocols HAVE LEFT the composed
meaning's door: THIRTEEN (the weights' one · the proximity test's door's four · the pile's three ·
"pile.room" · "frame.liveIs" · "K8.lay7" · "K8.onThird" · "K8.funsThird"), and four conjuncts of "in
order": a theorem here that spends, keeps or makes one of them stands at a WIDER meaning than the
composed one (a bridge's side), and is carried to it by a bridge under facts on reached states that
are owed. hpc and the line on the lookup's run "objects" are premises. make is not here. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Reads
import Johnson.Desc.First.K4PlanFit
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.K4PubBehind
import Johnson.Road.K4.LookOutKept
import Johnson.Road.K4.K4KeepKeeper
import Johnson.Road.K4.Slots.HearTrees
import Johnson.Road.K4.Riders.PubKept
import Johnson.Road.K4.SameReadSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Riders (weightsB_kept atFirstBook_kept atFirstSeats_kept
atFirstShapes_kept
  indexIsC_kept indexThereC_kept)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Strs)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub More Meaning start openSets pubSets
pubRowM
  pubOfItems keeperItem eqsB reqIsB)
open VerifiableInference.Desc.First.FillK4 (isK4At k4Item)
open VerifiableInference.Desc.K13.Law (inOrderK13)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ MsgT decodesOf)
open VerifiableInference.Desc.First.Look (liveItem liveIsB k3OnOutAt placeAt)
open VerifiableInference.OnPublicFiles (linkFreshB digitsUnheardB)
open OnBytes.Desc.First.K4 (Rest)
open OnBytes.Desc.First.K4.Slots (hear_trees)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB treesAreB)
open VerifiableInference.Desc.First (pubFit ledgerB moreItem)

/-- The public items of other kinds that are open across K4's sub-protocol at a feed-forward
segment m. -/
def pubSort (rest : Option ℕ → String → Bool) (m : ℕ) : Pub → Bool
  | .linkFresh j => j == m
  | .lookOut j k => j == m && k == 2
  | .more seg n => rest seg n || (seg == some m && n == "ledger.treesAre")
  | _ => false

/-- A TEST ON THE PROMISE's TABLE, at a filling of the door: at every place of K4's, whatever is
open in
front is dropped by the row, or K4's own layer's, or the table's own layer's, or of these sorts. -/
def k4PubFit (rest : Option ℕ → String → Bool) (M : More) (links : List ModelPart) (ps : List Place) :
    Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | none => true
    | some pl =>
      !isK4At links pl ||
        ((pubSets M links ps)[k]?.getD []).all fun x =>
          (pubRowM M links pl).drops.contains x || k4Item links x || keeperItem x ||
            pubSort rest (pl.link.getD 0) x

/-- The public items that are tied to items open in front of K4's sub-protocol. -/
def tiedSort (m : ℕ) : Pub → Bool
  | .indexIs => true
  | .indexThere => true
  | .formsInT j k r => j == m && k == 2 && r == "objects"
  | _ => false

/-- A TEST ON THE TABLE: at every place of K4's the tied public items in front are of these sorts.
-/
def k4TiedFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | none => true
    | some pl =>
      !isK4At links pl ||
        (pubOfItems ((openSets links ps (start links))[k]?.getD [])).all (tiedSort (pl.link.getD 0))

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- The lookups' test "nothing is heard at the digits' seat; the table of arrays is the public
parameters'"
reads
what K4's accept leaves. -/
theorem linkFreshB_kept {s s' : S} (R : Rest s s') (arrs : Array (ℕ × String)) :
    linkFreshB arrs s' = linkFreshB arrs s := by
  unfold linkFreshB digitsUnheardB
  rw [R.tl, R.link]

/-- So does "the live request's shape and layout are the public parameters'". -/
theorem liveIsB_kept {s s' : S} (R : Rest s s') (D3 : VerifiableInference.Desc.First.Look.Sent) :
    liveIsB D3 s' = liveIsB D3 s := by
  unfold liveIsB S.live
  rw [R.link, R.check]

/-- "The open segment's frame is the public parameters'" reads the open segment alone. -/
theorem sentIsB_kept {s s' : S} (R : Rest s s') (d : SentData) (j : ℕ) :
    sentIsB d j s' = sentIsB d j s := by
  unfold sentIsB
  rw [R.link]

/-- "The ledger's arrays have the public parameters' look": K4's hearing turns no array of the
ledger. -/
theorem treesAreB_kept {p : Par} {s s' : S} (K : KeptAtS p s s') (hl : ledgerB s = true)
    (d : SentData) (j : ℕ) : treesAreB d j s' = treesAreB d j s := by
  obtain ⟨a, fo, o, G, ha, _, hG, _, _, _, _, _, _, _, _, t, u, hh⟩ := K
  have hF : s.fork? = some a.F := by simp only [S.fork?, ha]
  have hS : PscRun.Sized a.F := by
    obtain ⟨F, e, z⟩ := (ledgerB_iff s).1 hl
    obtain rfl : F = a.F := Option.some.inj (e.symm.trans hF)
    exact (sized_iff _).1 z
  unfold treesAreB
  rw [hG, hF, Option.any_some, Option.any_some, hear_trees hS hh]

/-- "The index masks' ledger has just so many entries left" reads the statement and what is handed
out: an accept of K4's leaves both. -/
theorem roomIsB_kept {s s' : S} (R : Rest s s') (free0 : ℕ) (fvs : List Bool) (j : ℕ) :
    Johnson.Desc.First.Walk.Tied.roomIsB free0 fvs j s' =
      Johnson.Desc.First.Walk.Tied.roomIsB free0 fvs j s := by
  unfold Johnson.Desc.First.Walk.Tied.roomIsB Johnson.Desc.First.Walk.Tied.leftIsB
    Johnson.Desc.First.Walk.Law.ledgerAt
  rw [R.st, R.out]

/-- The lookup's promise behind it rides past an accept of K4's. -/
theorem k3OnOutAt_kept {p : Par} {s s' : S} (K : KeptAtS p s s') {X3 : Verify.Public} {i : ℕ}
    {dg : Bool} (h : k3OnOutAt X3 i dg s = true) : k3OnOutAt X3 i dg s' = true := by
  unfold k3OnOutAt at h ⊢
  cases hp : placeAt X3 i dg with
  | none => simp [hp] at h
  | some x =>
    simp only [hp, Option.any_some] at h ⊢
    exact k3OnOut_of_kept K x h

theorem isK4At_of (H : AtK4 links ps k m pl) : isK4At links pl = true := by
  simp [isK4At, H.link, H.sub, H.piece]

/-- **The line dec.** -/
theorem dec_of_means (E : K4Means Mg D)
    (hdecT : ∀ a τ fo o G', Yes seatS par q a τ fo o G' →
      ∀ c, (D.decT c (Z, a.1)).isSome = true →
        (D.decT c (Z, (behindOf seatS q a τ o G').1)).isSome = true) :
    ∀ a τ fo o G', Yes seatS par q a τ fo o G' → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
      Mg.decodes (Z, (behindOf seatS q a τ o G').1)
        (strsOf Fr (behindOf seatS q a τ o G').2) := by
  intro a τ fo o G' y hx
  rw [E.decodes] at hx ⊢
  unfold decodesOf at hx ⊢
  rw [cell_same (sameRead_of_yes y)]
  exact hdecT a τ fo o G' y _ hx

/-- **The line inOrder**, wherever `SameRead`. -/
theorem inOrder_of_means (E : K4Means Mg D) {base : ℕ} {x y : S × Fr.E.Str}
    (h : SameRead base x y) (hbase : D.base (Z, x.1) = true → D.base (Z, y.1) = true)
    (hx : Mg.inOrder (Z, x.1) = true) : Mg.inOrder (Z, y.1) = true := by
  rw [E.inOrder] at hx ⊢
  simp only [Bool.and_eq_true] at hx ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hx
  refine ⟨⟨⟨⟨hbase h1, ?_⟩, ?_⟩, ?_⟩, h5⟩
  · unfold eqsB at h2 ⊢
    rw [h.rest.st, h.rest.check]
    exact h2
  · unfold reqIsB at h3 ⊢
    rw [h.rest.req]
    exact h3
  · unfold inOrderK13 at h4 ⊢
    rw [h.rest.st, h.rest.check]
    exact h4

/-- **The line restQ**: the other kinds' public items that are open across K4's sub-protocol ride.
-/
theorem restQ_of_means (E : K4Means Mg D) {rest : Option ℕ → String → Bool}
    (Kp : K4Kept Mg rest Z) (H : AtK4 links ps k m pl)
    (hpf : pubFit Mg.more links ps = true) (hfit : k4PubFit rest Mg.more links ps = true)
    (hpc : VerifiableInference.Desc.K3.pieceAt X m false = 2) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], x ∉ (pubRowM Mg.more links pl).drops →
      k4Item links x = false → keeperItem x = false → Mg.pub x (Z, a.1) = true →
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y x hx hd h4 hkp hp
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp H.here).1
  have h2 := List.all_eq_true.1 hfit k (List.mem_range.2 hk)
  rw [H.here] at h2
  simp only [isK4At_of H, Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.1 h2 x hx
  have hdc : (pubRowM Mg.more links pl).drops.contains x = false := by simpa using hd
  rw [hdc, h4, hkp, H.link] at h3
  have hs : pubSort rest m x = true := by simpa using h3
  have hR := (rest_of_yes y).1
  obtain ⟨b1, _, _⟩ := bools_of_onQ D.N Mg Z ha hu
  rw [H.here] at b1
  obtain ⟨al, hal⟩ := lay_of_shape H b1
  cases x with
  | linkFresh j =>
    have e : j = m := by simpa [pubSort] using hs
    subst e
    rw [E.linkFresh] at hp ⊢
    rw [linkFreshB_kept hR]
    exact hp
  | lookOut j k' =>
    have e : j = m ∧ k' = 2 := by simpa [pubSort] using hs
    obtain ⟨rfl, rfl⟩ := e
    rw [← hpc, E.lookOut] at hp ⊢
    exact k3OnOutAt_kept (kept_of_yes y) hp
  | more sg n =>
    have e : rest sg n = true ∨ (sg = some m ∧ n = "ledger.treesAre") := by
      simpa [pubSort] using hs
    rcases e with e | ⟨rfl, rfl⟩
    · rw [Kp.kept sg n e a.1 _ ⟨⟨al, hal⟩, hR⟩]
      exact hp
    · have f1 := k4_pub_front D.N Mg Z H hpf ha hu (.ledger m) (by simp)
      rw [E.ledger] at f1
      rw [E.treesAre] at hp ⊢
      rw [treesAreB_kept (kept_of_yes y) f1]
      exact hp
  | _ => simp [pubSort] at hs

/-- **The line keepT**: the public items that are tied to items open in front ride. -/
theorem keepT_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl)
    (hfit : k4TiedFit links ps = true)
    (hObj : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → Mg.pub (.formsInT m 2 "objects") (Z, a.1) = true →
      Mg.pub (.formsInT m 2 "objects") (Z, (behindOf seatS q a τ o G').1) = true) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []),
      Mg.pub x (Z, a.1) = true → Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y x hx hp
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp H.here).1
  have h2 := List.all_eq_true.1 hfit k (List.mem_range.2 hk)
  rw [H.here] at h2
  simp only [isK4At_of H, Bool.not_true, Bool.false_or] at h2
  have hs := List.all_eq_true.1 h2 x hx
  rw [H.link] at hs
  have hR := (rest_of_yes y).1
  cases x with
  | indexIs =>
    rw [E.indexIs] at hp ⊢
    rw [indexIsC_kept hR]
    exact hp
  | indexThere =>
    rw [E.indexThere] at hp ⊢
    rw [indexThereC_kept hR]
    exact hp
  | formsInT j k' r =>
    have e : (j = m ∧ k' = 2) ∧ r = "objects" := by simpa [tiedSort] using hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact hObj a τ fo o G' ha hu y hp
  | _ => simp [tiedSort] at hs

/-- **The line keepP**: the sentences without a Bool of the public items that are open across K4's
sub-protocol: none of these items is left | leftOn (the test), so each reads no state. -/
theorem keepP_of_means (E : K4Means Mg D) {rest : Option ℕ → String → Bool}
    (H : AtK4 links ps k m pl)
    (hfit : k4PubFit rest Mg.more links ps = true) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [],
      x ∉ (pubRowM Mg.more links pl).drops → Mg.pubP x (Z, a.1) →
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1) := by
  intro a τ fo o G' _ _ _ x hx hd hP
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp H.here).1
  have h2 := List.all_eq_true.1 hfit k (List.mem_range.2 hk)
  rw [H.here] at h2
  simp only [isK4At_of H, Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.1 h2 x hx
  have hdc : (pubRowM Mg.more links pl).drops.contains x = false := by simpa using hd
  rw [hdc, Bool.false_or] at h3
  exact E.pubPRides x Z _ _ (fun j e => by subst e; simp [k4Item, keeperItem, pubSort] at h3)
    (fun j e => by subst e; simp [k4Item, keeperItem, pubSort] at h3) hP

/-- **The line restP**: of what K4's row makes, all but leftOn m: lookIn m 7 and whatever names the
door's filling lets it make: the first by the structure; the others under hDoorP. -/
theorem restP_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl)
    (hDoorP : ∀ nm ∈ (Mg.more.rows links pl).makes, ∀ a, Mg.pubP (moreItem nm) a) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes, x ≠ .leftOn m →
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1) := by
  intro a τ fo o G' _ _ _ x hx hne
  rw [k4_makes H] at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hx
  rcases hx with (rfl | rfl) | ⟨nm, hnm, rfl⟩
  · exact E.pubPLookIn m 7 _
  · exact absurd rfl hne
  · exact hDoorP nm hnm _

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.keepP_of_means
#print axioms OnBytes.Road.K4.Riders.restP_of_means
#print axioms OnBytes.Road.K4.Riders.dec_of_means
#print axioms OnBytes.Road.K4.Riders.inOrder_of_means
#print axioms OnBytes.Road.K4.Riders.restQ_of_means
#print axioms OnBytes.Road.K4.Riders.keepT_of_means
