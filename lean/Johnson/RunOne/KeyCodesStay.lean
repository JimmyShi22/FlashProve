-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCodesStay.lean: THEOREMS. **AT EVERY RECORD THAT THE KEY FILE's FIRST CHAIN REACHES FROM ITS START THE STATEMENT HAS GROWN OUT OF THE START's; SO THE CARRIED CODES ARE THE PLAN's THERE** (the first chain's third of the row «the carried
codes are the plan's at every step of Key.descriptionFromSource's chains»). GIVEN ONE PREMISE, a theorem in other files: the proximity test's seat at the ranges only grows the statement.
OBJECT. (Key.descriptionFromSource X N P).first = Key.firstChain …: its flat list, as a piece holds it, and its start; «reached» is LPFD.Hist₁ (Johnson/Top/Fire/Code/RowsWoven.lean · Reached.lean).
USER. The pairs (an older test · a caller in the description that hands it the RECORD's codes) on chain 1: linOk at K13.quiet (batt.1.batt's last quarter) · layPile's line on the index-mask message's ledger · Wf.admitted at Key.openRangesGroup (at the one-time chain's own codes: admitted_of_fileOkD,
Johnson/Top/Fire/Code/PublicOfFileOkD.lean); at door T: through
KeepsAt.reached the history's half of every On is free. LETTERS. R with GroundKeeps R · X · N · P · D.
  flat_keeps          every block of Key.firstChain's flat list keeps By R st₁ (chain1_keeps through the frame's chain_flat_keeps)
  reached_inv         a rule on Reached: what the start lays and every block's decide keeps holds at every reached record
  reached_rel₁        Hist₁ (Key.descriptionFromSource X N P) D k a → R (the start's statement) a.2.d.st, for every k
  grows_reached₁      at R := Grows · codes_reached₁   **a.2.d.st.codes = X.Y.k.oneTime.codes, FOR EVERY k**
What is not claimed. The premise. Chains 2 | 3. That the groups' members are those that the plan tells (Grows: a group keeps its two codes and only gains members). That a block accepts rightly. Nothing on soundness.

-/
import Johnson.RunOne.KeyKeepsAt
import Johnson.Desc.Key.Desc
import Johnson.Top.Fire.Code.RowsWoven

set_option autoImplicit false

namespace Johnson.RunOne.KeyCodes

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block Chain Grows)
open VerifiableInference.Desc.Ground (GroundKeeps By groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps chain_flat_keeps)
open LPFD (Hist₁ Reached)

variable {R : Statement → Statement → Prop}

theorem flat_keeps (H : GroundKeeps R) (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums)
    (h12 : Decides (By R st₁) (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim)) : ∀ b ∈ (firstChain one D told set N).blocksInOrder, Decides (By R st₁) b :=
  chain_flat_keeps (By R st₁) (fun _ => H.refl _) (fun _ _ _ h k => H.trans h k) _ (chain1_keeps H one D told set N h12)

/-- A rule on Reached: what the start lays and every block's decide keeps holds at every reached record. -/
theorem reached_inv {S Cl : Type} (ft : ℕ) (bs : List (Block S Cl)) (st₀ : S → Prop) (I : S → Prop) (h0 : ∀ a, st₀ a → I a)
    (hs : ∀ b ∈ bs, ∀ a rs gs a', I a → b.decide a rs gs = .ok a' → I a') : ∀ (k : ℕ) (a : S), Reached ft bs st₀ k a → I a
  | 0, a, h => h0 a h
  | k + 1, a, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, -⟩ := Reached.last h
    exact hs b (List.mem_of_getElem? hb) a' _ _ a (reached_inv ft bs st₀ I h0 hs k a' hr) hd

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- The statement in a record of the first chain, as a piece holds it. -/
def stAt (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) : Statement := st₁ (show FirstState from a.2)

/-- **Every reached record's statement is related to the start's.** -/
theorem reached_rel₁ (H : GroundKeeps R) (D : OnBytes.Maker.WholeD)
    (h12 : Decides (By R st₁) (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim)) (k : ℕ)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : R { codes := X.Y.k.oneTime.codes } (stAt a) := by
  refine reached_inv _ _ _ (fun a => R { codes := X.Y.k.oneTime.codes } (stAt a)) (fun a ha => ?_) (fun b hb a rs gs a' hI hd => ?_) k a h
  · have e : a.2 = (descriptionFromSource X N P).start₁ a.1 := ha
    have e2 : stAt a = { codes := X.Y.k.oneTime.codes } := congrArg (fun s : (descriptionFromSource X N P).S₁ => st₁ (show FirstState from s)) e
    show R _ (stAt a)
    rw [e2]
    exact H.refl _
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    have h2 := (VerifiableInference.Desc.Plain.held_decide b₀ a rs gs a' hd).2
    exact H.trans hI (flat_keeps H _ _ _ _ _ h12 b₀ hb₀ _ _ _ _ h2)

theorem grows_reached₁ (D : OnBytes.Maker.WholeD)
    (h12 : Decides (By Grows st₁) (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim)) (k : ℕ)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : Grows { codes := X.Y.k.oneTime.codes } (stAt a) :=
  reached_rel₁ groundKeeps_grows D h12 k a h

/-- **The carried codes are the plan's at every record that the first chain reaches.** -/
theorem codes_reached₁ (D : OnBytes.Maker.WholeD)
    (h12 : Decides (By Grows st₁) (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim)) (k : ℕ)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : (stAt a).codes = X.Y.k.oneTime.codes :=
  (grows_reached₁ D h12 k a h).1

end Johnson.RunOne.KeyCodes

#print axioms Johnson.RunOne.KeyCodes.flat_keeps
#print axioms Johnson.RunOne.KeyCodes.reached_inv
#print axioms Johnson.RunOne.KeyCodes.reached_rel₁
#print axioms Johnson.RunOne.KeyCodes.grows_reached₁
#print axioms Johnson.RunOne.KeyCodes.codes_reached₁
