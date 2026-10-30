-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastCore.lean (each premise and conclusion of the form "∀ a …, the
promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds beside
the promise; at the ledger: the layer on the last chain's own state; members may
also spend the game's own conclusion `NTuple` at whatever the state fixes: by
`fixes_unique`): THE SEAM's CORE AT THE LAST CHAIN's OWN TEST (the field
core of `LastOwed`: `CoreFacts` under the seated block's yes): WHAT IS ASKED OF THE
GROUP IS PAID; WHAT IS LEFT IS ASKED MEMBER BY MEMBER.
  `placeB_gives`: the ledger's test placeB holds, among its clauses, that the place is "early" and
    the block's own test on the plan.
  `found_all`: AT ANY NUMBER OF MEMBERS: at whatever the state fixes, where the state's statement
    is in order: the layout finds each member's number at the member's own place, and every member
    of the group is one of the data's: by `made_of`, `layout_eq`, `find_of_nodup` (`found_of_ids`
    is this at two members).
  `decide_of_yes`: the seated block's yes is the kind's decision's yes at what the seat's door
    returns, at the type of claims Unit.
  `groupFacts_W`: **`GroupFacts` at W**: inside the book-keeping's yes at border 2, at a yes of the
    kind's decision, from johOk and placeB: the codes by `codes_fixed` and `start_codes`; the four
    on the stage and the layout by `yes_facts`; the last two by `found_all`.
  `core_of_members`: **the field core FROM johOk, placeB AND members**: at whatever the state
    fixes: a tuple xs of members of the lists, one to each of the data's members, no one twice,
    every one of mine among them, and radii es, with `MemberFacts` at each. By
    `coreFacts_all`.
Limits. members is shown at no state; its seven clauses are left to files of several kinds, in forms
general in the seat. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeamRows
import Johnson.LLT25R.LastYesLays
import Johnson.Desc.Sound.SeamMembersAll
import Johnson.Desc.Sound.SeamFactsQ
import Johnson.Desc.Sound.SeamGroup
import Johnson.Desc.K12.Coin.YesFacts
import Johnson.Desc.K12.Coin.BoolsTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open Cb Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Johnson.Pack
open OnBytes.Means H2K.ClaimSays H2K.Pin
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open _root_.Desc.K14.Law.Fence (CoreFacts GroupFacts MemberFacts coreFacts_all codes_fixed
  fixes_unique)
open H2K.JointK
open H2K.First (Plain made_of)
open H2K.Pub (sgOf johOk)
open _root_.Run

/-- Two clauses of the ledger's test on the place. -/
theorem placeB_gives {F : Frame} {π : P12} {num : Fmt.TreeSource → ℕ} {base : ℕ} {dB : RDT}
    {dt : List RDT} (h : PlaceB F π num base dB dt = true) :
    π.early = true ∧ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true := by
  unfold PlaceB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a, _⟩, c⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ⟨a, c⟩

/-- **The layout finds the members, and the data hold them all: at any number of members.** -/
theorem found_all (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) (hI : InOrder t.st) :
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  have hL : Ly = layoutOf t.st G0 :=
    Option.some.inj (hf.2.2.1.symm.trans (layout_eq t.st t.g G0 hf.2.1))
  have hmem : Ly.members = G0.members := by rw [hL]; rfl
  have hnd : Ly.members.toList.Nodup := by rw [hmem]; exact (hI.groups _ _ hf.2.1).nodup
  refine ⟨fun j => ?_, fun o ho => ?_⟩
  · rw [hm.lay]
    exact find_of_nodup hnd (hm.mem j).1
  · rw [← hmem] at ho
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem ho
    have hi' : i < D.mems.length := by rw [← hm.size]; simpa using hi
    refine ⟨⟨i, hi'⟩, ?_⟩
    have h1 := (hm.mem ⟨i, hi'⟩).1
    have h2 : Ly.members[i]? = some o := by
      rw [← e]
      simp [Array.getElem?_eq_getElem (show i < Ly.members.size by simpa using hi)]
    exact Option.some.inj (h1.symm.trans h2)

/-- The seated block's yes is the kind's decision's. -/
theorem decide_of_yes {Cl' : Type} (π : P12) (s s' : S₃) (t : T12) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (ht : enterOwn s = .ok t)
    (hd : (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide s rs gs = .ok s') :
    ∃ tE, (proximityTestKind guardedProximityTestParts π : Blk').decide t rs gs = .ok tE := by
  have h' : ((enterOwn s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts π : Block T12 Cl').decide t rs gs).bind (leaveOwn s)) = .ok s' := hd
  obtain ⟨t0, ht0, h2⟩ := bindOk h'
  obtain ⟨tE, hE, -⟩ := bindOk h2
  obtain rfl : t0 = t := Except.ok.inj (ht0.symm.trans ht)
  refine ⟨tE, ?_⟩
  rw [(k12_alike (Cl' := Unit) (Cl := Cl') guardedProximityTestParts π).2.2]
  exact hE

/-- **WHAT IS ASKED OF THE GROUP, AT W.** -/
theorem groupFacts_W (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed) (o : SharedOut) (s : S₃)
    (t tE : T12) (π : P12) (r : Fmt.M1.Stage → ℕ) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hk : shapeAt p R 2 f o s = true)
    (ht : enterOwn s = .ok t) (hy : (proximityTestKind guardedProximityTestParts π : Blk').decide t rs gs = .ok tE)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) : GroupFacts p.codes (fun s => r s.st) t a G0 Ly D := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨-, hc⟩ := start_codes B.start
  have e0 : t.st = s.st := by
    obtain rfl : _ = t := Except.ok.inj ht
    rfl
  obtain ⟨h1, h2, h3, h4⟩ := yes_facts π r (fun s => r s.st) (fun _ => rfl) hj he hp t tE rs gs hy a
    rest G0 Ly D hf
  obtain ⟨h5, h6⟩ := found_all π t a rest G0 Ly D hf (by rw [e0]; exact B.tidy.inOrder)
  exact ⟨by rw [codes_fixed π t a rest G0 Ly D hf, e0, L.codes, hc], h1, h2, h3, h4, h5, h6⟩

variable {P S₁ S₂ Cells Tok Cl' : Type} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound)
  (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)
  {Xi : Type} (G : FileDescription Xi)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf p.codes s.l).om i).Smp)
  (mine : List Mem) (π : P12) (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
  (mem : ((P × S₁ × S₂) × S₃) → ℕ → Option Mem)

/- what holds beside the promise at border 2: a letter -/
variable {E : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop}

/-- **THE FIELD core, FROM TWO TESTS AND WHAT IS ASKED MEMBER BY MEMBER.** -/
theorem core_of_members {F' : Frame} {num : Fmt.TreeSource → ℕ} {base : ℕ} {dB : RDT} {dt : List RDT}
    (hj : johOk π r = true) (hB : PlaceB F' π num base dB dt = true)
    (members : ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised p.codes G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide a.1.2 rs gs = .ok s') →
      ∀ st rest G0 Ly D, Fixes π t st rest G0 Ly D →
      NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D →
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, z ∈ mine → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length, MemberFacts p.codes G Fr no (fun s => r s.st) smp (mem a.1) a.2 a.1
          (strsOf Fr a.2) st D j (xs j) (es j)) :
    ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → E a →
      Promised p.codes G smp mine a.1 (strsOf Fr a.2) → enterOwn a.1.2 = .ok t →
      (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide a.1.2 rs gs = .ok s') →
      QN π (NTuple Fr π no (fun s => r s.st) rd) (t, a.2) →
      CoreFacts p.codes G Fr π no (fun s => r s.st) smp (mem a.1) (· ∈ mine) t a.2 a.1
        (strsOf Fr a.2) := by
  intro a t hon hE hP ht hY hQ
  obtain ⟨f, o, -, -, hk⟩ := shapeAt_of_onL Nn Mg Pm Oc p R hand ended hon
  obtain ⟨rs, gs, s', hd⟩ := hY
  obtain ⟨tE, hy⟩ := decide_of_yes π a.1.2 s' t rs gs ht hd
  obtain ⟨he, hp⟩ := placeB_gives hB
  exact coreFacts_all p.codes G Fr π no (fun s => r s.st) smp (mem a.1) a.2 a.1 (strsOf Fr a.2)
    (· ∈ mine) t fun st rest G0 Ly D hf =>
      ⟨groupFacts_W p R f o a.1.2 t tE π r rs gs hk ht hy hj he hp st rest G0 Ly D hf,
        members a t hon hE hP ht ⟨rs, gs, s', hd⟩ st rest G0 Ly D hf (by
          obtain ⟨st', rest', G0', Ly', D', hf', hN⟩ := hQ
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_unique hf hf'
          exact hN)⟩

end LLT25

#print axioms LLT25.found_all
#print axioms LLT25.groupFacts_W
#print axioms LLT25.core_of_members
