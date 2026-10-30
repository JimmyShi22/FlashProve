-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsSeated.lean: THE SUB-PROTOCOLS AS THE SEAT LAYS THEM.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksSeated.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.First.Link.Law.LooksK2
import Johnson.Desc.First.Link.Law.SlotsK2
import Johnson.Desc.First.Link.Law.LooksK3
import Johnson.Desc.First.Link.Law.LooksK4
import Johnson.Desc.First.Link.Law.SlotsK4
import Johnson.Desc.First.Link.Law.LooksK5
import Johnson.Desc.First.Link.Law.SlotsK5
import Johnson.Desc.First.Link.Law.LooksK6
import Johnson.Desc.First.Link.Law.SlotsK6
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.K1.Places
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Top.H0.Walk.FrameLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **The term off the plan**: link m's number of slots BY THE FRAME's OWN LETTERS (off the built
links and the program's public data W); nH where the frame has no letters: the output head's link.
-/
def nsW (built : Array Stages.LinkH) (W : Verify.Public) (nH m : ℕ) : ℕ :=
  if m = 0 then ((zeroAt built W).map (·.ns)).getD nH
  else match frameAt built W m with
    | some (.att P _) => P.ns
    | some (.lay P) => P.ns
    | none => nH

/-- Both numbers. -/
def nsOfBuilt (built : Array Stages.LinkH) (W : Verify.Public) (nH m : ℕ) : ℕ × ℕ :=
  (nsW built W nH m, nsW built W nH m)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- The letters of link l. -/
theorem frameAt_lettersS {built : Array Stages.LinkH} {W : Verify.Public} (nH : ℕ) {l : ℕ}
    {x : Par} (h : frameAt built W l = some x) :
    match x with
    | .att P _ => P.l = l ∧ nsOfBuilt built W nH l = (P.ns, P.ns)
    | .lay P => P.l = l ∧ nsOfBuilt built W nH l = (P.ns, P.ns) := by
  have hl : l ≠ 0 := by
    rintro rfl
    unfold frameAt at h
    obtain ⟨X, _, h⟩ := Option.bind_eq_some_iff.1 h
    simp at h
  have h0 := frameAt_letters h
  cases x with
  | att P n => exact ⟨h0.1, by unfold nsOfBuilt nsW; rw [if_neg hl, h]⟩
  | lay P => exact ⟨h0.1, by unfold nsOfBuilt nsW; rw [if_neg hl, h]⟩

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
theorem zeroAt_lettersS {built : Array Stages.LinkH} {W : Verify.Public} (nH : ℕ) {P : LayPar}
    (h : zeroAt built W = some P) : nsOfBuilt built W nH 0 = (P.ns, P.ns) := by
  unfold nsOfBuilt nsW
  rw [if_pos rfl, h]
  rfl

/-- The end of the head's link is the frame's one clearing. -/
theorem tailHead_keepsS (nsOf : ℕ → ℕ × ℕ) {X : Johnson.Desc.First.Walk.LinkPub} {lay : WsLay}
    {lin : Params.LinShape} {s t : S} (h : First.Close.tailHead X lay lin s = .ok t) :
    KeepsSlots nsOf s t :=
  cleared_keepsS nsOf (X := X) (counts := First.Close.countsHead) (left := First.Close.leftHead)
    (row := fun masks w claims os => First.Pend.pendingRowO lay masks w claims lin os) h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **EVERY ROW OF THE FRAME, LINK BY LINK.** -/
theorem frames_keepS {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (nH : ℕ) (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    (∀ s t, f.lay s = .ok t → KeepsSlots (nsOfBuilt built W nH) s t) ∧
      (∀ s t, f.opened s = .ok t → KeepsSlots (nsOfBuilt built W nH) s t) ∧
      ∀ s t, f.clear s = .ok t → KeepsSlots (nsOfBuilt built W nH) s t := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fun _ _ k => laid_keepsS _ k, fun s t k => by cases k; exact keeps_reflS _ s,
        fun _ _ k => tailHead_keepsS _ k⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        exact ⟨fun _ _ k => laid_keepsS _ k,
          fun _ _ k => openLayZero_makesS _ k (zeroAt_lettersS nH hP),
          fun _ _ k => cleared_keepsS _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_lettersS nH hP
        exact ⟨fun _ _ k => laid_keepsS _ k, fun _ _ k => openAtt_makesS _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keepsS _ (X := P.X) (counts := countsAtt nLin)
            (left := fun _ => none) (row := rowOf W first) k⟩
      · rename_i P hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_lettersS nH hP
        exact ⟨fun _ _ k => laid_keepsS _ k, fun _ _ k => openLay_makesS _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keepsS _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩

/-! ## The kinds' makers as the lots seat them -/

section
variable (nsOf : ℕ → ℕ × ℕ)

theorem k4C_stepsS (p : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p).Steps (KeepsSlots nsOf) :=
  fun s rs gs s' h => k4_stepsS nsOf p s rs gs s' h

theorem k8W_stepsS (p : First.K8.ParW) : (First.K8.whole p).Steps (KeepsSlots nsOf) :=
  fun s rs gs s' h => k8_stepsS (Cl := Claim) nsOf p.toPar s rs gs s' h

theorem k1Later_stepsS {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps (KeepsSlots nsOf) :=
  k1_stepsS nsOf _ link moment arrays

theorem readsLay_stepsS (P : K8.ReadsQuiet.PG) :
    (K8.ReadsQuiet.layers P).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact keeps_sameS nsOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsHead_stepsS (P : K8.ReadsQuiet.PH) :
    (K8.ReadsQuiet.head P).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact keeps_sameS nsOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsAtt_stepsS {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : b.Steps (KeepsSlots nsOf) := by
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq (A := A) e
  exact keeps_sameS nsOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

/-- The steps without a round behind a lookup. -/
theorem quietAt_keepsS {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : KeepsSlots nsOf s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsSlots nsOf s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, hF, k⟩ := K9L.ok_bind k
    obtain ⟨G, hG, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    have hF' := named_some hF
    have hG' := named_some hG
    unfold First.Look.slotsTaken at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      refine keeps_of_casesS nsOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF', ?_, rfl, ?_⟩
      · rw [← link_putFork s]
        exact e2
      · rw [fork_putFork s F hF'] at e1
        rw [← Option.some.inj e1]
        rfl
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsSlots nsOf s t := by
    intro k
    unfold K3.quietHead at k
    split at k
    · rename_i a ha
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain rfl := Except.ok.inj k
      exact keeps_sameS nsOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → KeepsSlots nsOf s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact keeps_reflS nsOf s
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lk _ h)
    | cases hf

end

end VerifiableInference.Desc.LinkJoin
