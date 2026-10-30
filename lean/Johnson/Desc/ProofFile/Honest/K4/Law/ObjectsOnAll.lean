-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ObjectsOnAll.lean: CONDITIONAL.

What is here. THE SENTENCE OF THE ITEM formsT m 2 "objects", AT THE COMPOSED MEANING's OWN DATA, IS
CARRIED FORWARD: from the state in front of a step with K4's clause of `keeps` to the state behind
it, at the same tables of the witness. The sentence is written out as the first clause of the
library's `mgAll_formsT` (Johnson/Desc/Sound/MgAll.lean): at each run for which the item stands,
`formsTQ` at the segment's readers, the stated data and the first sending's seats; that clause does
not read the meaning's argument for the files' strings. (The second clause speaks of the name
"weights" alone.) At a feed-forward segment the runs are (1, "objects") and (1, "guests")
(`runs_layers`, Johnson/Desc/Sound/MgAt/Runs.lean). For the first: `objects_on_keeps`
(Law/ObjectsOnKeeps.lean); its three tests with code come out of hE, the promise's public test in
front (`ePubAt`: the tests of all public items that are open or asked at a border), as the library's
`eleven_at_all` draws its own (Johnson/Road/K4/More/ElevenAtAll.lean): the items ledger m, freeAbove
m and the name "K4.rowsBare" are asked in front of each of K4's places (`has_ledger`,
`has_freeAbove`, `has_rowsBare`, Johnson/Road/K4/More/FrontList.lean: comparisons by Lean's own
kernel, which no independent checker has replayed), and the wider meaning's equations, used inside
the proof alone, name each test. For the second: the library's `guests_holds` at the state behind.
The stated data's mask row is one at both states by unfolding. The statement names no thread. One
statement with its proof: calls. Words: Law/ObjectsOn.lean's head.

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: no example is known to us. NO HYPOTHESIS OF
ITS OWN SPEAKS OF THE ROWS' ENTRIES, YET THE FACT IS STILL ASKED: hE holds that no row which the
lookup heard names an entry (the public name "K4.rowsBare"). Who makes that test true is not shown
here: the library has it behind an accept of the lookup on the calls' own decision, under premises
on the shape, the fork and the state behind (`rowsBare_lay_made`,
Johnson/Desc/First/Look/K3CallsMade.lean), not at the seated sub-protocol. hH, hli, hlk, fO, oRun,
fG and gRun speak of the data: Law/ElevenHead.lean (`nine_head`) has all but hli under the library's
hypothesis on the public files and `LaidK4`; hli is the field links of the library's `k4Fill_all`
(Johnson/Road/K4/K4FillAll.lean). K (`K4Keeps`): Law/Keeps.lean, wherever the kind's sub-protocol
accepts; at the seated member: Law/KeepsStep.lean. hE: Law/FrontHead.lean (`thr_tests`,
`ePubAt_of_held`), wherever the thread stands. E is any value: neither the hypotheses nor the
conclusion read it; the proof uses the wider meaning at E to name the tests. THE LIBRARY's `K4Fence`
IS NOT ASKED. Nothing says that a form is worth 0 anywhere. THE FULL SIZE ALONE (`linksFull`). A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/, as those of Law/ObjectsOnKeeps.lean do.
No property is claimed.

  `k4_objects_on_all`   **the item's sentence forward.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ObjectsOnKeeps
import Johnson.Road.K4.More.ElevenAtAll
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun guests_holds reader_guests)
open OnBytes.Road.K4 (AtK4 CellsK k4DataWide k4Means_mgWide)
open OnBytes.Road.K4.Riders (link_forms)
open OnBytes.Road.K4.More (PS front_mem hasAtK4 has_ledger has_freeAbove has_rowsBare)
open VerifiableInference.Desc (Place Wit Claim Link K9.statesOfLink K9.readersOfLink K9.holesAt
  K9.readersAt_some)
open VerifiableInference.Desc.First (S pubAll ePubAt pubWide_hand freeAboveB)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT MsgQ formsTQ mgWide MgData WideData mgBase linksFull
  moreAll runsAt runsAt_of runs_layers)

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- CONDITIONAL: on every hypothesis named. **THE ITEM's SENTENCE FORWARD OVER A STEP WITH
`K4Keeps`**, where the promise's public test accepts in front. -/
theorem k4_objects_on_all (E : WideData P) {k m : ℕ} {pl : Place}
    (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (hli : Dm.links = linksFull) {l : Link S Claim} (hlk : Dm.lk m = some l) {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) {z : P} {s s' : S} (K : K4Keeps s s')
    (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    {rd : ℕ × ℕ → MsgQ}
    (h : ∀ p ∈ Dm.runs m 2 "objects",
      formsTQ (Dm.Rd m) Dm.St (Dm.N.sent m 0) p.1 p.2 s rd) :
    ∀ p ∈ Dm.runs m 2 "objects", formsTQ (Dm.Rd m) Dm.St (Dm.N.sent m 0) p.1 p.2 s' rd := by
  have Em := k4Means_mgWide Dm E Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hand : ∀ (q : PubI), VerifiableInference.Desc.First.classA q = false → ∀ a,
      (mgWide Dm E Bm).pub q a = pubAll Dm.pubD (Bm).pub q a := fun q hq a =>
    pubWide_hand E.d12 E.dP Dm.pubD (Bm).pub q hq a
  have fr : ∀ {f : ℕ → PubI}, hasAtK4 moreAll linksFull PS f = true →
      VerifiableInference.Desc.First.classA (f m) = false →
      (mgWide Dm E Bm).pub (f m) (z, s) = true := fun {f} hf hc => by
    rw [hand _ hc]
    exact List.all_eq_true.1 hE _ (front_mem H hf)
  have hl : isLay (k4DataWide Dm E Bm).links m = true := by
    show isLay Dm.links m = true
    rw [hli]
    unfold isLay
    rw [H.sub]
    rfl
  have f1 := fr (f := fun m => .ledger m) has_ledger rfl
  have f2 := fr (f := fun m => .freeAbove m) has_freeAbove rfl
  have f8 := fr (f := fun m => .more (some m) "K4.rowsBare") has_rowsBare rfl
  rw [Em.ledger] at f1
  rw [Em.freeAbove] at f2
  rw [Em.rowsBare m _ hl] at f8
  have hruns : Dm.runs m 2 "objects" = [(1, "objects"), (1, "guests")] := by
    show runsAt Dm.links m 2 "objects" = _
    rw [hli, runsAt_of linksFull m .layers H.sub]
    exact runs_layers.1
  have hRd : Dm.Rd m = K9.readersOfLink (K9.holesAt X (headLink X) m l) l :=
    K9.readersAt_some Dm.lk X _ m l hlk
  cases hn : (k4DataWide Dm E Bm).nsOf m with
  | none =>
    rw [hn] at f2
    cases f2
  | some n =>
    rw [hn] at f2
    have f2' : freeAboveB n s = true := f2
    intro p hp
    rw [hruns] at hp h
    rw [hRd] at h ⊢
    rcases List.mem_cons.1 hp with rfl | hp
    · exact objects_on_keeps K f1 f2' f8 fO oRun (fun _ _ => rfl) (h (1, "objects") (by simp))
    · rcases List.mem_cons.1 hp with rfl | hp
      · obtain ⟨R, a, _, _, ha, _⟩ := K
        obtain ⟨a', ha', _⟩ := R.here a ha
        exact guests_holds ha' fG gRun (link_forms (by decide) (reader_guests fG gRun ha'))
      · cases hp

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_objects_on_all
