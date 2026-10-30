-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyWalkAny.lean: THEOREMS. **THE WALK ALONG Key.descriptionFromSource's THREE CHAINS, ONCE, GENERAL IN THE RELATION, WITH NO PREMISE ON THE PLAN: every relation R on statements that the ground's ten routines keep (GroundKeeps R, Johnson/Desc/GroundKeeps.lean) and that the beginning of a proximity test
keeps (BeginKeeps R) is kept by every block of the three chains, the four tests' seats among them; it holds from border to border of one history and across the seam from chain 1's end into chain 3; and an invariant I, read as «if it holds before it holds behind», holds at every record that a chain reaches.**
AT I := OpenKinds («no open row is marked as a sample row», Johnson/Desc/Means/Holds.lean): openKinds_at_reached₁ | ₂ | ₃. AT R := K1.SmpStay: KeySmpStay.lean's and KeySmpWalk.lean's laws WITHOUT planOk.
THE TEST ITSELF IS CROSSED IN ANOTHER FILE: k12_keeps | ranges_keeps (Johnson/RunOne/Law/K12Keeps.lean: over K12's files' k12_calls: a yes of the test is a run of the ground's routines and of beginRunP): CALLED. KeySmpStay.lean's own k12_kept | k12_smpStay (early · one answer, over K12's files' stages_st) are the lesser twins: they yield.
OBJECT. Key.firstChain | sharedChain | thirdChain · LPFD.Hist₁ | Hist₂ | Hist₃ (Key.descriptionFromSource X N P) D. USER. grows_of_run (declared nowhere in this library) at 1.15 (and 2.9 | 2.10 | 3.2) · a member at a later border. LETTERS. R · I; X · N · P · D; m · j · k; x · x0 · a.
  BeginKeeps R          a yes of the ground's beginRunP keeps R
  three_keeps           **GroundKeeps R → BeginKeeps R → ChainKeeps (By R ·) of each of the three chains of Key.descriptionFromSource X N P, AT EVERY X N P** · flat_keeps₁' | ₂' | ₃': every block of the flat lists
  hist₁_rel | ₂ | ₃     **Hist (m + j) x → ∃ x0, Hist m x0 ∧ x0.1 = x.1 ∧ R (the statement at x0) (the statement at x)** · hist₃_from₁_rel: from chain 1's end, as handed, to every record of chain 3
  inv_at_reached₁ | ₂ | ₃    **at R a b := (I a → I b), with I at a statement without message and group: Hist_j k a → I (the statement at a)**
  openKinds_at_reached₁ | ₂ | ₃   **OpenKinds at every reached record: FROM THE HISTORY ALONE**
  three_smp · flat_smp₁ | ₂ | ₃ · seedIs_later | sealed_later · seedIs_into   **the laws on the sampled messages, WITHOUT planOk** (groundKeeps_smpStay · beginRun_smpStay: Johnson/Desc/K1/Law/SmpStay.lean:53 | :79)
  three_grows           «a statement only grows» on all three chains, with the test crossed by k12_calls, which lies in the files below: K12's files' k12_grows is not called for it (the file's import cone still holds it)
What is not claimed. InOrder is no such relation (Johnson/Desc/Means/FrameKeeps.lean's own head). From chain 2 into chain 3 (Omega comes by a copy). That SeedIs holds at border m. Nothing on soundness.

-/
import Johnson.RunOne.KeySmpWalk
import Johnson.RunOne.Law.K12Keeps

set_option autoImplicit false

namespace Johnson.RunOne.KeyWalk

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySmp
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Ground (GroundKeeps By beginRunP)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps chain_flat_keeps)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (SmpStay SeedIs Sealed groundKeeps_smpStay beginRun_smpStay)
open Johnson.RunOne.KeyCodes (reached_inv)
open Johnson.RunOne.Law.K12Keeps (k12_keeps ranges_keeps)
open LPFD (Hist₁ Hist₂ Hist₃)

variable {R : Statement → Statement → Prop}

/-- The beginning of a proximity test keeps R. -/
def BeginKeeps (R : Statement → Statement → Prop) : Prop :=
  ∀ (d d' : H2K.Out.DS) (g : Nat) (run : RunInput), beginRunP d g = some (run, d') → R d.st d'.st

theorem k12_decides_any (H : GroundKeeps R) (hb : BeginKeeps R) (p : P12) : Decides (By R fun t : T12 => t.st) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) :=
  fun t rs gs t' h => k12_keeps H hb p t t' rs gs h

theorem shared_keeps (H : GroundKeeps R) (hb : BeginKeeps R) (c : Model.Verify.Chains) (N : LaterPlaces) : ChainKeeps (By R st₂) (sharedChain c N) := by
  refine ⟨fun d _ _ d' hd => ?_, fun b hb' => (by cases hb'), fun L hL => (by cases hL), fun b hb' => ?_, end_keeps' H.refl _ _ _ _ _ _⟩
  · cases hd
    exact H.refl _
  · rcases List.mem_append.1 hb' with hb' | hb'
    · exact blocksOr_keep H _ b hb'
    · rcases List.mem_append.1 hb' with hb' | hb'
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · exact VerifiableInference.Desc.K12.Seat.onGu_keeps (R := fun a b => R a.st b.st) _ (k12_decides_any H hb _)
        · cases hb'
      · obtain ⟨nO, _, rfl⟩ := List.mem_map.1 hb'
        exact VerifiableInference.Desc.K12.Seat.onGomega_keeps (R := fun a b => R a.st b.st) _ (k12_decides_any H hb _)

theorem third_keeps (H : GroundKeeps R) (hb : BeginKeeps R) (c : Model.Verify.Chains) (N : LaterPlaces) : ChainKeeps (By R st₃) (thirdChain c N) := by
  refine ⟨k14Second_keeps H _, fun b hb' => (by cases hb'), fun L hL => (by cases hL), fun b hb' => ?_, end_keeps' H.refl _ _ _ _ _ _⟩
  rcases List.mem_cons.1 hb' with rfl | hb'
  · intro s rs gs s' h
    rw [VerifiableInference.Desc.Third.Law.takenSources_same _ s s' rs gs h]
    exact H.refl _
  · rcases List.mem_cons.1 hb' with rfl | hb'
    · exact VerifiableInference.Desc.K12.Seat.onOwn_keeps (R := fun a b => R a.st b.st) _ (k12_decides_any H hb _)
    · cases hb'

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **All three chains keep R: at every X N P.** -/
theorem three_keeps (H : GroundKeeps R) (hb : BeginKeeps R) :
    ChainKeeps (By R (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first ∧ ChainKeeps (By R st₂) (descriptionFromSource X N P).shared ∧ ChainKeeps (By R st₃) (descriptionFromSource X N P).second :=
  ⟨chain1_keeps H _ _ _ _ _ (fun s rs gs s' h => ranges_keeps H hb _ N s s' rs gs h), retype_keeps (shared_keeps H hb X.chains P), retype_keeps (third_keeps H hb X.chains P)⟩

theorem flat_keeps₁' (H : GroundKeeps R) (hb : BeginKeeps R) : ∀ b ∈ (descriptionFromSource X N P).first.blocksInOrder, Decides (By R (st₁ (β := LookupRecord))) b :=
  chain_flat_keeps (By R (st₁ (β := LookupRecord))) (fun _ => H.refl _) (fun _ _ _ x y => H.trans x y) _ (three_keeps H hb).1

theorem flat_keeps₂' (H : GroundKeeps R) (hb : BeginKeeps R) : ∀ b ∈ (descriptionFromSource X N P).shared.blocksInOrder, Decides (By R st₂) b :=
  chain_flat_keeps (By R st₂) (fun _ => H.refl _) (fun _ _ _ x y => H.trans x y) _ (three_keeps H hb).2.1

theorem flat_keeps₃' (H : GroundKeeps R) (hb : BeginKeeps R) : ∀ b ∈ (descriptionFromSource X N P).second.blocksInOrder, Decides (By R st₃) b :=
  chain_flat_keeps (By R st₃) (fun _ => H.refl _) (fun _ _ _ x y => H.trans x y) _ (three_keeps H hb).2.2

/-- **From border m to border m + j on one history.** -/
theorem hist₁_rel (H : GroundKeeps R) (hb : BeginKeeps R) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ R (st₁ (show FirstState from x0.2)) (st₁ (show FirstState from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).first.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By R (st₁ (β := LookupRecord))) (fun _ => H.refl _) (fun _ _ _ p q => H.trans p q) _ (fun b hm => flat_keeps₁' H hb b (List.mem_of_mem_drop hm)) _ j _ hw⟩

theorem hist₂_rel (H : GroundKeeps R) (hb : BeginKeeps R) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂, Hist₂ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ R (st₂ (show _root_.Desc.K14.St from x0.2)) (st₂ (show _root_.Desc.K14.St from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).shared.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By R st₂) (fun _ => H.refl _) (fun _ _ _ p q => H.trans p q) _ (fun b hm => flat_keeps₂' H hb b (List.mem_of_mem_drop hm)) _ j _ hw⟩

theorem hist₃_rel (H : GroundKeeps R) (hb : BeginKeeps R) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃, Hist₃ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ R (st₃ (show S₃ from x0.2)) (st₃ (show S₃ from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).second.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By R st₃) (fun _ => H.refl _) (fun _ _ _ p q => H.trans p q) _ (fun b hm => flat_keeps₃' H hb b (List.mem_of_mem_drop hm)) _ j _ hw⟩

/-- **Across the seam: from chain 1's end, as handed, to every record that chain 3 reaches.** -/
theorem hist₃_from₁_rel (H : GroundKeeps R) (hb : BeginKeeps R) (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    R (st₁ (show FirstState from a.1.2.1)) (st₃ (show S₃ from a.2)) := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₃_rel H hb D 0 k a (by rw [Nat.zero_add]; exact h)
  have e : ((descriptionFromSource X N P).start₃ x0.1.1 x0.1.2.1 x0.1.2.2).toOption = some x0.2 := (show LPFD.st₃ (descriptionFromSource X N P) D x0 from h0).2
  cases hq : (descriptionFromSource X N P).start₃ x0.1.1 x0.1.2.1 x0.1.2.2 with
  | error w => rw [hq] at e; cases e
  | ok s =>
    rw [hq] at e
    have e' : s = x0.2 := Option.some.inj e
    rw [e'] at hq
    rw [← e0, ← start₃_same hq]
    exact hs

/-- **From a border of chain 1 into chain 3.** -/
theorem hist₃_from_border_rel (H : GroundKeeps R) (hb : BeginKeeps R) (D : OnBytes.Maker.WholeD) (m j : ℕ) (hm : m + j = (descriptionFromSource X N P).first.blocksInOrder.length) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = a.1.1 ∧ R (st₁ (show FirstState from x0.2)) (st₃ (show S₃ from a.2)) := by
  have h1 := LPFD.hist₂_handed (descriptionFromSource X N P) D _ _ (LPFD.hist₃_handed (descriptionFromSource X N P) D k a h)
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_rel H hb D m j (a.1.1, a.1.2.1) (by rw [hm]; exact h1)
  exact ⟨x0, h0, e0, H.trans hs (hist₃_from₁_rel H hb D k a h)⟩

section Invariant
variable {I : Statement → Prop}

/-- **An invariant at every record that chain 1 reaches.** -/
theorem inv_at_reached₁ (H : GroundKeeps fun a b => I a → I b) (hb : BeginKeeps fun a b => I a → I b) (h0 : ∀ cs : Codes, I { codes := cs, oracles := #[], groups := #[] })
    (D : OnBytes.Maker.WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : I (st₁ (show FirstState from a.2)) := by
  obtain ⟨x0, hx, _, hs⟩ := hist₁_rel H hb D 0 k a (by rw [Nat.zero_add]; exact h)
  have e : x0.2 = (descriptionFromSource X N P).start₁ x0.1 := hx
  have e2 : st₁ (show FirstState from x0.2) = { codes := X.Y.k.oneTime.codes, oracles := #[], groups := #[] } := congrArg (fun s : (descriptionFromSource X N P).S₁ => st₁ (show FirstState from s)) e
  exact hs (e2 ▸ h0 _)

theorem inv_at_reached₂ (H : GroundKeeps fun a b => I a → I b) (hb : BeginKeeps fun a b => I a → I b) (h0 : ∀ cs : Codes, I { codes := cs, oracles := #[], groups := #[] })
    (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D k a) : I (st₂ (show _root_.Desc.K14.St from a.2)) := by
  obtain ⟨x0, hx, _, hs⟩ := hist₂_rel H hb D 0 k a (by rw [Nat.zero_add]; exact h)
  have e : x0.2 = (descriptionFromSource X N P).start₂ x0.1.1 := (show LPFD.st₂ (descriptionFromSource X N P) D x0 from hx).2
  have e2 : st₂ (show _root_.Desc.K14.St from x0.2) = { codes := X.chains.made.sized.key.codes, oracles := #[], groups := #[] } := congrArg (fun s : (descriptionFromSource X N P).S₂ => st₂ (show _root_.Desc.K14.St from s)) e
  exact hs (e2 ▸ h0 _)

theorem inv_at_reached₃ (H : GroundKeeps fun a b => I a → I b) (hb : BeginKeeps fun a b => I a → I b) (h0 : ∀ cs : Codes, I { codes := cs, oracles := #[], groups := #[] })
    (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) : I (st₃ (show S₃ from a.2)) :=
  hist₃_from₁_rel H hb D k a h (inv_at_reached₁ H hb h0 D _ (a.1.1, a.1.2.1) (LPFD.hist₂_handed (descriptionFromSource X N P) D _ _ (LPFD.hist₃_handed (descriptionFromSource X N P) D k a h)))

end Invariant

open OnBytes.Means (OpenKinds groundKeeps_openKinds beginRunP_kinds)

theorem begin_openKinds : BeginKeeps fun a b => OpenKinds a → OpenKinds b := fun _ _ _ _ h => beginRunP_kinds h

/-- **No open row is marked as a sample row, at every record that a chain of Key.descriptionFromSource reaches: from the history alone.** -/
theorem openKinds_at_reached₁ (D : OnBytes.Maker.WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : OpenKinds (show FirstState from a.2).d.st :=
  inv_at_reached₁ groundKeeps_openKinds begin_openKinds OpenKinds.start D k a h

theorem openKinds_at_reached₂ (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D k a) : OpenKinds (show _root_.Desc.K14.St from a.2).st :=
  inv_at_reached₂ groundKeeps_openKinds begin_openKinds OpenKinds.start D k a h

theorem openKinds_at_reached₃ (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) : OpenKinds (show S₃ from a.2).st :=
  inv_at_reached₃ groundKeeps_openKinds begin_openKinds OpenKinds.start D k a h

/-! ## The sampled messages, without planOk -/

theorem begin_smp : BeginKeeps SmpStay := fun d d' g run h => beginRun_smpStay d d' g run h

theorem three_smp : ChainKeeps (By SmpStay (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first ∧ ChainKeeps (By SmpStay st₂) (descriptionFromSource X N P).shared ∧ ChainKeeps (By SmpStay st₃) (descriptionFromSource X N P).second :=
  three_keeps groundKeeps_smpStay begin_smp

theorem flat_smp₁ : ∀ b ∈ (descriptionFromSource X N P).first.blocksInOrder, Decides (By SmpStay (st₁ (β := LookupRecord))) b := flat_keeps₁' groundKeeps_smpStay begin_smp
theorem flat_smp₂ : ∀ b ∈ (descriptionFromSource X N P).shared.blocksInOrder, Decides (By SmpStay st₂) b := flat_keeps₂' groundKeeps_smpStay begin_smp
theorem flat_smp₃ : ∀ b ∈ (descriptionFromSource X N P).second.blocksInOrder, Decides (By SmpStay st₃) b := flat_keeps₃' groundKeeps_smpStay begin_smp

/-- **The call: the sending kind's row at border m stands at border m + j: from the history alone.** -/
theorem seedIs_later (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∀ cs s o ρ y, SeedIs cs s (show FirstState from x0.2).d.st o ρ y → SeedIs cs s (show FirstState from x.2).d.st o ρ y := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_rel groundKeeps_smpStay begin_smp D m j x h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ k => k.stays hs⟩

theorem sealed_later (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∀ cs s e f o, Sealed cs s e f (show FirstState from x0.2).d.st o → Sealed cs s e f (show FirstState from x.2).d.st o := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_rel groundKeeps_smpStay begin_smp D m j x h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ k => k.stays hs⟩

theorem seedIs_into (D : OnBytes.Maker.WholeD) (m j : ℕ) (hm : m + j = (descriptionFromSource X N P).first.blocksInOrder.length) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = a.1.1 ∧
      ∀ cs s o ρ y, SeedIs cs s (show FirstState from x0.2).d.st o ρ y → SeedIs cs s (show S₃ from a.2).st o ρ y := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₃_from_border_rel groundKeeps_smpStay begin_smp D m j hm k a h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ q => q.stays hs⟩

/-! ## «A statement only grows», over the base's own law on the test -/

theorem begin_grows : BeginKeeps VerifiableInference.Desc.Grows := fun d d' g run h => VerifiableInference.Desc.Ground.beginRunP_grows d d' g run h

/-- KeyCodesLater.lean's three_grow again: here the test is crossed by k12_calls (Johnson/Desc/K12/Law/Calls.lean), through k12_keeps (Johnson/RunOne/Law/K12Keeps.lean), not by K12's files' k12_grows. BY PROOF, NOT YET BY IMPORT: this file imports KeySmpWalk.lean, whose cone holds three of K12's files. -/
theorem three_grows : ChainKeeps (By VerifiableInference.Desc.Grows (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first ∧ ChainKeeps (By VerifiableInference.Desc.Grows st₂) (descriptionFromSource X N P).shared ∧
    ChainKeeps (By VerifiableInference.Desc.Grows st₃) (descriptionFromSource X N P).second :=
  three_keeps VerifiableInference.Desc.Ground.groundKeeps_grows begin_grows

end Johnson.RunOne.KeyWalk
