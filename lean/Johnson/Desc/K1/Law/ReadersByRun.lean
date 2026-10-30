-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersByRun.lean: k01_law's BINDER hRd
(what a reader answers in front of a later sub-protocol of kind K1 it answers behind) CUT RUN BY RUN:
at each of the fifty later places it is Fwd
(Johnson/Desc/Reads/FormsPass.lean) at a written list of the driver's runs, by the sort of the
segment. Tests with code, what an accept of each says, their evaluations, and statements with
their proofs.

Why. hRd speaks of every public item formsIn | formsInT that stands in front of the place. Each run's
files owe their own run alone: the cut says which runs, at which places.

OBJECT. The table's own lists at First.flatPlacesOf linksFull true, at the numbers noL l d, l < 25;
the door's list is a letter M (closed: mwMore, Johnson/Desc/K1/Law/DoorAtPlus13.lean).
USER. Whoever pays hRd: hRd_of_runs gives hRd in hPub_at's own letters at one place.
Main names:
  runsOfSort · runsL      the written lists: a segment of the sort "layers": (1, objects) (1, guests)
                          (2, front) (2, back); "attention": (1, objects) (1, guests) (2, first)
                          (2, keys) (2, second) (1, planes) (2, join); the output head: (2, objects)
                          (2, guests) (3, norm) (3, policy) (3, logits) (2, planes) (3, join); at a
                          digits' place (d = true) the approximate range proof's one run as well.
  runsFitB · runsFit_of   the test: each such item in front of the place is the segment's own, and
                          each run that it stands for is on the list; what an accept says.
  namedB                  the test the other way: each run on the list is named by such an item.
  runsFit_mw · named_mw   [kernel] both at all fifty places, at the closed door.
  runsTests_fail          [kernel] THE TESTS CAN FAIL: a run struck from the list; a run added.
  hRd_of_runs             **hRd at one place, from Fwd at the list's runs.**
  runsFit_mw1             the test at the wider meaning mw1's own door.
  tl_rest · funs_rest · pairStays_small    **the approximate range proof's run is PAID at the digits'
                          places**: its reader (K9.smallReader) reads two parts of the state which a
                          commitment does not write (K9.smallReader_same, ReadersAt.lean).
  pairStays_of_respects   away from the output head the second reader is silent: PairStays is
                          Respects of the run that the segment states under the name.
  fwd_digits              **Fwd over the accept of a digits' place, from PairStays.**
PREMISES THAT STAY, BY NAME. hruns (the letter's map of names is the table's own, Sound.runsAt) ·
hF (Fwd, run by run, behind the accept and the promise in front).
What is not claimed. Fwd of any run but the one named. Anything at the reads' places. Nothing on
soundness, on an honest prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000), as in Johnson/Desc/K1/Law/FormsAtFifty.lean:
for the kernel's evaluations' elaboration alone.

-/
import Johnson.Desc.K1.Law.CallsF
import Johnson.Desc.K1.Law.MemberMw1
import Johnson.Desc.K1.Law.ReadersStayAt
import Johnson.Desc.First.Batch.ReadersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Readers LinkHoles statesOfLink readersOfLink holesAt smallReader
  smallReader_same)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 The lists, the tests, and what an accept of each says -/

/-- The driver's runs whose readers are asked across a later place of kind K1, by the sort of the
segment; d: the digits' place. -/
def runsOfSort (sub : ModelPart) (d : Bool) : List (ℕ × String) :=
  match sub with
  | .layers => [(1, "objects"), (1, "guests"), (2, "front"), (2, "back")] ++
      (if d then [(4, "K8.equations")] else [])
  | .attention => [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "second"),
      (1, "planes"), (2, "join")] ++ (if d then [(4, "K8.equations")] else [])
  | .head => [(2, "objects"), (2, "guests"), (3, "norm"), (3, "policy"), (3, "logits"),
      (2, "planes"), (3, "join")] ++ (if d then [(5, "K8.equations")] else [])

/-- The same at segment l of the full size. -/
def runsL (l : ℕ) (d : Bool) : List (ℕ × String) :=
  ((linksFull[l]?).map fun sub => runsOfSort sub d).getD []

/-- The public items in front of the place (l, d), at the door's list M. -/
def pubsL (M : More) (l : ℕ) (d : Bool) : List Pub :=
  (First.pubSets M linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
    First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))

/-- Each formsIn | formsInT in front of the place is segment l's, and each run that it stands for is
on the list L. -/
def runsFitB (M : More) (l : ℕ) (d : Bool) (L : List (ℕ × String)) : Bool :=
  (pubsL M l d).all fun q =>
    match q with
    | .formsIn m j r => m == l && (runsAt linksFull m j r).all fun p => L.contains p
    | .formsInT m j r => m == l && (runsAt linksFull m j r).all fun p => L.contains p
    | _ => true

/-- Each run on the list L is named by a formsIn | formsInT in front of the place. -/
def namedB (M : More) (l : ℕ) (d : Bool) (L : List (ℕ × String)) : Bool :=
  L.all fun p => (pubsL M l d).any fun q =>
    match q with
    | .formsIn m j r => (runsAt linksFull m j r).contains p
    | .formsInT m j r => (runsAt linksFull m j r).contains p
    | _ => false

theorem runsFit_of {M : More} {l : ℕ} {d : Bool} {L : List (ℕ × String)}
    (h : runsFitB M l d L = true) (m j : ℕ) (r : String)
    (hq : Pub.formsIn m j r ∈ pubsL M l d ∨ Pub.formsInT m j r ∈ pubsL M l d) :
    m = l ∧ ∀ p ∈ runsAt linksFull m j r, p ∈ L := by
  unfold runsFitB at h
  have key : (m == l && (runsAt linksFull m j r).all fun p => L.contains p) = true := by
    rcases hq with hq | hq
    · exact List.all_eq_true.1 h _ hq
    · exact List.all_eq_true.1 h _ hq
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) key
  exact ⟨eq_of_beq h1, fun p hp => List.contains_iff_mem.1 (List.all_eq_true.1 h2 p hp)⟩

/-! ## 2 At the full size, at the closed door, by evaluation in Lean's kernel -/

theorem runsFit_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    runsFitB mwMore l d (runsL l d)) = true := by
  decide +kernel

theorem named_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    namedB mwMore l d (runsL l d)) = true := by
  decide +kernel

/-- **The tests can fail**: a run struck from the list (at each sort of segment); a run added. -/
theorem runsTests_fail :
    runsFitB mwMore 2 false ((runsL 2 false).erase (2, "back")) = false ∧
    runsFitB mwMore 3 true ((runsL 3 true).erase (4, "K8.equations")) = false ∧
    runsFitB mwMore 24 false ((runsL 24 false).erase (3, "join")) = false ∧
    runsFitB mwMore 3 true (runsL 4 true) = false ∧
    namedB mwMore 2 false (runsL 2 true) = false ∧
    namedB mwMore 24 true ((8, "the merge") :: runsL 24 true) = false := by
  decide +kernel

/-! ## 3 hRd at one place, from Fwd run by run -/

section
variable {Pp Cells Tok : Type}

/-- **hRd in hPub_at's own letters, at one later place.** -/
theorem hRd_of_runs (N : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (Dp : PubData)
    (hruns : Dp.runs = runsAt linksFull) (B : Block S Unit) (l : ℕ) (d : Bool)
    (L : List (ℕ × String)) (hfit : runsFitB Mg.more l d L = true)
    (hF : ∀ x x' y, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      ∀ p ∈ L, Fwd (Dp.Rd l) p.1 p.2 x.2 x'.2) :
    ∀ x x' y m j r, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        Pub.formsInT m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay Dp m j r x.2 x'.2 := by
  intro x x' y m j r hy hIn hq
  obtain ⟨rfl, hsub⟩ := runsFit_of hfit m j r hq
  intro p hp
  rw [hruns] at hp
  exact hF x x' y hy hIn p (hsub p hp)

end

/-- The test at the wider meaning's own door. -/
theorem runsFit_mw1 {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
    (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (h : Mg₀.more = {}) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    runsFitB (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more l d (runsL l d) = true := by
  show runsFitB (K13.Law.plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more l d (runsL l d) = true
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact List.all_eq_true.1 (List.all_eq_true.1 runsFit_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp)

/-! ## 4 The digits' places: payers by the form of the reader -/

theorem tl_rest (s : S) : (restOf s).tl? = s.tl? := by
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [restOf, hereRest, S.tl?, hh, ho]
  | _ => simp [restOf, hereRest, S.tl?, hh]

theorem funs_rest (s : S) : (restOf s).funs? = s.funs? := by
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [restOf, hereRest, S.funs?, hh, ho]
  | _ => simp [restOf, hereRest, S.funs?, hh]

/-- **The approximate range proof's one run**, at the term that is meant for the first hole. -/
theorem pairStays_small (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (lk : Link S Claim) (b : ℕ) :
    PairStays (holesAt X mH m lk) lk (b, "K8.equations") := by
  unfold PairStays
  have e : (((b, "K8.equations") : ℕ × String).2 == "K8.equations") = true := beq_self_eq_true _
  rw [if_pos e]
  intro s s' hA
  exact smallReader_same s s' (by rw [← tl_rest s', ← tl_rest s, hA])
    (by rw [← funs_rest s', ← funs_rest s, hA])

/-- Away from the output head's segment the second reader is silent. -/
theorem pairStays_of_respects (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (hm : m ≠ mH)
    (lk : Link S Claim) (p : ℕ × String) (hn : (p.2 == "K8.equations") = false)
    (hr : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → Respects r.2) :
    PairStays (holesAt X mH m lk) lk p := by
  unfold PairStays
  rw [hn]
  refine ⟨hr, fun s s' _ => ?_⟩
  unfold holesAt
  have e : (m == mH) = false := by simpa using hm
  simp only [e]
  rfl

/-- **Fwd over the accept of a digits' place.** -/
theorem fwd_digits {Pp : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (arrs : Option (List ℕ)) (Rd : Readers) (H : LinkHoles) (lk : Link S Claim)
    (hD : Rd = readersOfLink H lk) (p : ℕ × String) (hp : PairStays H lk p) (x x' : Pp × S)
    (hy : YesOf (blkL Z G₀ l true X arrs) x x') : Fwd Rd p.1 p.2 x.2 x'.2 := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  have hd' : (laterAt G₀.first (gpOf Z) l (k1Ix l true + 1) 2 arrs : Block S Unit).decide x.2
      (rs.map noDigest) gs = .ok x'.2 := hd
  intro R hR
  rw [hD] at hR ⊢
  rw [readersOfLink_alike H lk p hp (commitAtS_alike _ _ _ _ x.2 x'.2 _ gs hd')]
  exact hR

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.runsFit_of
#print axioms VerifiableInference.Desc.K1.runsFit_mw
#print axioms VerifiableInference.Desc.K1.named_mw
#print axioms VerifiableInference.Desc.K1.runsTests_fail
#print axioms VerifiableInference.Desc.K1.hRd_of_runs
#print axioms VerifiableInference.Desc.K1.runsFit_mw1
#print axioms VerifiableInference.Desc.K1.tl_rest
#print axioms VerifiableInference.Desc.K1.funs_rest
#print axioms VerifiableInference.Desc.K1.pairStays_small
#print axioms VerifiableInference.Desc.K1.pairStays_of_respects
#print axioms VerifiableInference.Desc.K1.fwd_digits
