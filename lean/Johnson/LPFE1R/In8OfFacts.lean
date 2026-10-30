-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/In8OfFacts.lean: HitemsLeft's FIELD in8 (LPFE1R/HitemsAtConst.lean): THE PUBLIC TEST
K9.formsIn AT THE ENTRY "K8.equations", AT EVERY STATE OF THE CONDITION IN FRONT OF A LINK's
BATCHING, AT THE CLOSED CONSTANT. WHAT PARTS formsIn FROM formsInA: an entry may name a cell of an
array that is still ahead; in front of the batching nothing is ahead. Statements and proofs.

  formsInA_of_promise   the sister of formsIn_of_promise (LPFE1R/HinOfPromise.lean): at a run that
                        is read ahead (𝔇.ah) the promise holds K9.formsInA
  formsIn_of_none_ahead where nothing is ahead at the state's open segment, formsInA gives formsIn
                        (affInA_none, Johnson/Desc/First/Batch/Ahead.lean)
  small8B · small8_full BY THE KERNEL: at each of the 25 links the entry (4 + shift, "K8.equations")
                        is a run of the item forms m (5 + shift) "small", which is open at the
                        batching's border · small8_no: a control: behind the batching it is not
  in8_at                (h : AtMgA secondHashFunction …) (hm : m < 25) z Rz (FF : FoldFacts Rz (fun a => (z,
                        a.1)) d reqW fullLinks At.ps) (hall) a (ho : onTR … (batchAt fullLinks At.ps
                        m) a) : K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) (4 + shift (subAt m))
                        "K8.equations" a.1 = true: "nothing is ahead":
                        ahead_none_of_facts (Link/Law/FrameFullOf.lean) at its place_batch
                        (K09Places.lean)

Limits. FoldFacts and hall (the closed test on the plan's numbers of FrameFullOf.lean) are premises
here: where in8_at is called (Johnson/P5J/K09LastC.lean | K09EndC.lean) they are fed by foldFacts_at
and LPFK9.hall_of_moments. The head is a premise. The full size alone. No soundness statement.

-/
import Johnson.LPFE1R.HinOfPromise
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Desc.First.Link.Law.FrameFullOf
import Johnson.Desc.First.Link.Law.K09Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubOfItems
  pubHeld runsOf shift pubAll_formsIn FoldFacts FoldData shiftAt)
open IM (subAt)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The weaker public test at a run that is read ahead, out of the promise.** -/
theorem formsInA_of_promise {A : Type} {F : Frame} (links : List ModelPart) (ps : List Place)
    (get : A → P × S) (k : ℕ) (a : A × F.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg) links ps get k a) (hm : (get a.1).2.failed = none)
    {m kk : ℕ} {r : String}
    (hO : Item.forms m kk r ∈ (openSets links ps (start links))[k]?.getD [])
    {e : ℕ × String} (he : e ∈ 𝔇.runs m kk r) (hah : 𝔇.ah e.1 e.2 = true) :
    K9.formsInA (𝔇.Rd m) (𝔇.N.sent m) (𝔇.N.group m) e.1 e.2 (get a.1).2 = true := by
  rcases hon.2 with hx | ⟨hb, -, -, -⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at hb
    have hp := hb.1.2
    unfold pubHeld at hp
    have hq : Pub.formsIn m kk r ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []) :=
      List.mem_flatMap.2 ⟨_, hO, List.mem_singleton.2 rfl⟩
    have h1 := List.all_eq_true.1 hp _ (List.mem_append_right _ hq)
    rw [mgAll_pub, pubAll_formsIn] at h1
    have h2 := List.all_eq_true.1 h1 e he
    have ea : 𝔇.pubD.ah e.1 e.2 = true := hah
    rw [ea] at h2
    simpa using h2

end

/-- **Where nothing is ahead the weaker test is the stronger.** -/
theorem formsIn_of_none_ahead (Rd : K9.Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))
    (piece : ℕ) (run : String) (s : S)
    (hn : ∀ a, K9.segAt? s = some a → ∀ b, K9.aheadIn sent own a b = none)
    (h : K9.formsInA Rd sent own piece run s = true) : K9.formsIn Rd own piece run s = true := by
  unfold K9.formsInA at h
  unfold K9.formsIn
  cases ea : K9.segAt? s with
  | none =>
    rw [ea] at h
    exact nomatch h
  | some a =>
    rw [ea] at h
    cases eR : Rd.forms piece run s with
    | none =>
      rw [eR] at h
      exact nomatch h
    | some R =>
      rw [eR] at h
      simpa only [K9.affInA_none sent own _ _ a (hn a ea)] using h

/-- The entry "K8.equations" of link m is a run of the item "small", which is open at border k. -/
def small8B (k m : ℕ) : Bool :=
  (P5J.oAt k).contains (Item.forms m (5 + shift (subAt m)) "small") &&
    (runsOf (subAt m) (5 + shift (subAt m)) "small").contains
      (4 + shift (subAt m), "K8.equations")

set_option maxRecDepth 1000000 in
theorem small8_full : ((List.range 25).all fun m =>
    small8B (batchAt P5J.fullLinks P5J.At.ps m) m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: behind the batching, which closes the item, the test says no at every link. -/
theorem small8_no : ((List.range 25).any fun m =>
    small8B (batchAt P5J.fullLinks P5J.At.ps m + 1) m) = false := by decide +kernel

theorem fullLinks_25 : P5J.fullLinks.length = 25 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **HitemsLeft's FIELD in8, AT THE CLOSED CONSTANT.** -/
theorem in8_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {F : Frame}
    (z : ProofFile.InstPub) (Rz : ℕ → S × F.E.Str → Prop) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW P5J.fullLinks P5J.At.ps)
    (hall : ∀ ms, (d.sent.shape.link[m]?).map (·.messages) = some ms →
      ms.length ≤ (d.ownAt m 3).size) (a : S × F.E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) P5J.fullLinks P5J.At.ps (fun s : S => (z, s)) Rz
      (batchAt P5J.fullLinks P5J.At.ps m) a) :
    K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) (4 + shift (subAt m)) "K8.equations" a.1 = true := by
  have h1 := List.all_eq_true.1 small8_full m (List.mem_range.2 hm)
  unfold small8B at h1
  rw [Bool.and_eq_true] at h1
  have hO := List.contains_iff_mem.1 h1.1
  have he : ((4 + shift (subAt m), "K8.equations") : ℕ × String) ∈
      h.𝔇.runs m (5 + shift (subAt m)) "small" :=
    mem_runsAt P5J.fullLinks m (subAt m) (LPFK9.fullLinks_sub m hm) _ _ _
      (List.contains_iff_mem.1 h1.2)
  have hf : a.1.failed = none := Classical.not_not.1 ho.1.2
  have hA := formsInA_of_promise h.𝔇 mgBase P5J.fullLinks P5J.At.ps (fun s : S => (z, s))
    (batchAt P5J.fullLinks P5J.At.ps m) a ho.1.1 hf hO he rfl
  obtain ⟨p, hp, hl, h7, h11⟩ := place_batch P5J.fullLinks P5J.At.ps placesFit_links m
    (by rw [fullLinks_25]; exact hm)
  exact formsIn_of_none_ahead _ _ _ _ _ _
    (fun y hy => ahead_none_of_facts FF _ a p m y ho.2 hf hp hl hy h7 h11 hall _ _) hA

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.formsInA_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.formsIn_of_none_ahead
#print axioms VerifiableInference.Desc.LinkJoin.small8_full
#print axioms VerifiableInference.Desc.LinkJoin.small8_no
#print axioms VerifiableInference.Desc.LinkJoin.fullLinks_25
#print axioms VerifiableInference.Desc.LinkJoin.in8_at
