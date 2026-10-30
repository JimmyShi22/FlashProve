-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/CoreBehindQ.lean: the seam's core behind our game's relations: from `QW` |
`QWO` (GameOut.lean | GameOutOwn.lean: what the proximity test's law with a key concludes, with the
test's own decision's yes laid in) to «one tuple of typed messages of which all rows taken in hold,
a candidate at every member that sits»: general in the description, the frame, the place, the doors,
the sample's reader and the list of members: NO FILE, NO SEAT AND NO TABLE IS NAMED. Statements;
each proof is two calls.

Called: `QW.places` | `QWO.places` (LabelsAtRecordOwn.lean: from the numbering by labels to the
numbering by the book's places) · `core_at`
(Johnson/Desc/Sound/SeamFacts.lean).
  `core_behind_QW` (the first arm) · `core_behind_QWO` (the second arm).
`CoreLeft` (the bundle but six clauses) · `coreFacts_of_yes` ·
`core_behind_QW'` | `core_behind_QWO'`: the relations hold the test's own decision's «accept»: it
pays six clauses of the bundle (with three tests on the plan: johOk · early · planOk): so the caller
owes `CoreLeft` alone. `core_behind_QWn`: the first arm at ANY numbering
by labels nl, at
no := nuOf π nl t: nothing is asked of the book.
`groupFacts_of_yes` · `coreLeft_of_members`: KIN, NAMED:
another file cuts `CoreFacts` in two (Johnson/Desc/Sound/SeamMembers.lean:
`GroupFacts`: the codes' equation and just the six clauses that `CoreLeft` leaves out ·
`MemberFacts`: seven clauses a
member;
SeamMembersAll.lean: `coreFacts_all`): in matter `CoreLeft` is the codes' equation and the members'
half of `coreFacts_all`'s premise, written out. These two lemmas tie the two forms.
What it is not. `CoreFacts` (the bundle of plain facts on the
verifier's state behind the
door in), «the statement is in order» and «the book is in order» ARE PREMISES: no member of them is
shown here. It pays no clause of a rule's premise and no field of a table: it is what their payer
calls. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LabelsAtRecordOwn
import Johnson.Desc.Sound.SeamFacts
import Johnson.Desc.Sound.SeamMembers
import Johnson.Desc.K12.Coin.YesFacts
import Johnson.Desc.K12.Coin.CoreAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law.Fence (CoreFacts core_at GroupFacts MemberFacts)
open H2K.Pin (tabP)
open H2K.ClaimSays
open H2K.Pub (johOk)

/-- **The first arm.** -/
theorem core_behind_QW {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs)
    (h : QW Fr π (nlAt π lo) r rdN enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t → t.mask.isSome = true ∧ BookOrd π.nums.firstTree t.book)
    (facts : ∀ t, enter a.1.2 = .ok t →
      CoreFacts cs G Fr π (fun z => lo + z) (fun s => r s.st) smp mem sits t a.2 a0 Y)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨t, ht, hq⟩ := h.places hB
  obtain ⟨_, _, G0, _, _, hf, _⟩ := id hq
  exact ⟨t, G0, ht, hf.2.1, core_at cs G Fr π _ _ rdN smp mem sits rd hrd t a.2 a0 Y (facts t ht)
    (hI t ht) hq G0 hf.2.1⟩

/-- **The second arm** (the first fold sends its own mask). -/
theorem core_behind_QWO {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (t₁ t₂ ch : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs)
    (h : QWO Fr π t₁ t₂ ch r rdN enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t →
      t.mask = none ∧ BookStep π.nums.firstTree t.book t.roots)
    (facts : ∀ t, enter a.1.2 = .ok t →
      CoreFacts cs G Fr π (noAt t₁ t₂ ch) (fun s => r s.st) smp mem sits t a.2 a0 Y)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨t, ht, hq⟩ := h.places hB
  obtain ⟨_, _, G0, _, _, hf, _⟩ := id hq
  exact ⟨t, G0, ht, hf.2.1, core_at cs G Fr π _ _ rdN smp mem sits rd hrd t a.2 a0 Y (facts t ht)
    (hI t ht) hq G0 hf.2.1⟩

/-! ## What the test's own «accept», which the relations hold, pays of the bundle -/

section
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc.Shared
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok made_of oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- **What is left of `CoreFacts` behind an «accept» of the test's decision**: its clauses but six:
the chain at the first stage's radius, the test `combineAt`, the layout's two lengths, «each member
is found at its own number» and «every member of the group is a member of the plain data» are gone.
The text is `CoreFacts`' own, copied from Johnson/Desc/Sound/SeamFacts.lean:
if that definition turns, `coreFacts_of_yes` goes red. -/
def CoreLeft (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
    (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop) (t : T12) (y : Fr.E.Str) (a0 : A) (Y : Strs) :
    Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    D.st.codes = cs ∧
    (∀ j : Fin D.mems.length, H2K.Pin.ok (siteL cs a (D.mems.get j)) = true) ∧
    (∀ j : Fin D.mems.length, ∃ x, D.st.oracles[(D.mems.get j).id]? = some x ∧
      H2K.Pin.ok (sampleL cs (D.mems.get j) x) = true) ∧
    ∃ (e0s : Fin D.mems.length → ℕ) (memJ : Fin D.mems.length → Mem),
      (∀ j : Fin D.mems.length,
        rad (sgOf a) < (e0s j + 1) * 2 ^ ((sgOf a).C.a - aOf cs (D.mems.get j).sh)) ∧
      Function.Injective memJ ∧ (∀ x, sits x → ∃ j, memJ j = x) ∧
      (∀ j, (memJ j).1.l.get (memJ j).2 = ((D.mems.get j).sh, e0s j)) ∧
      (∀ j, mem (D.mems.get j).id = some (memJ j)) ∧
      (∀ j : Fin D.mems.length, ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row)
        (tt : E) (β : GEˣ), D.st.oracles[(D.mems.get j).id]? = some x ∧
        Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
        x.sampleRows.toList = [{ row0 with target := tt }] ∧
        bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
        ∃ (z σ' : ((sigOf cs (memJ j).1.l).om (memJ j).2).Smp),
          smp a0 (memJ j).1 (memJ j).2 = some z ∧
          HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
            (portOmZ cs (D.mems.get j).sh (e0s j)).Smp) σ' ∧ z.2 = σ'.2 ∧
          ((sigOf cs (memJ j).1.l).om (memJ j).2).Z.val z.1 =
            ((sigOf cs (memJ j).1.l).om (memJ j).2).Z.val σ'.1) ∧
      ∀ j : Fin D.mems.length,
        HEq (strOf cs (D.mems.get j).sh (e0s j) (layOf (D.mems.get j))
            (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
          (VerifiableInference.Desc.Sound.wordsOf G cs (memJ j).1.l (memJ j).1.seat Y (memJ j).2)

/-- **The bundle from what is left, behind an «accept».** By `yes_facts`
(YesFacts.lean) and our `found_of_decide` (CoreAtYes.lean). -/
theorem coreFacts_of_yes (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop) (t tE : T12) (y : Fr.E.Str) (a0 : A) (Y : Strs)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE)
    (left : CoreLeft cs G Fr π no (fun s => r s.st) smp mem sits t y a0 Y) :
    CoreFacts cs G Fr π no (fun s => r s.st) smp mem sits t y a0 Y := by
  intro a rest G0 Ly D hf
  obtain ⟨hcs, hS, hQ, tail⟩ := left a rest G0 Ly D hf
  obtain ⟨hJ, ht, hk, hh⟩ :=
    yes_facts π r (fun s => r s.st) (fun _ => rfl) hj he hp t tE rs gs h a rest G0 Ly D hf
  obtain ⟨hfind, hmem⟩ := found_of_decide π t tE rs gs h a rest G0 Ly D hf
  exact ⟨hcs, hJ, ht, hk, hh, hS, hQ, hfind, hmem, tail⟩

/-- **`GroupFacts` (Johnson/Desc/Sound/SeamMembers.lean), general in the
seat: from the codes' equation and an «accept» of the test's own decision.** `GroupFacts` is that
equation and just the six clauses that `CoreLeft` leaves out. Kin: `group_nine` |
`group_ten` (SeamGroup.lean): the same at the proof file's two seats, from the seat's «accept» and
its test on the
state. -/
theorem groupFacts_of_yes (cs : Codes) (π : P12) (r : Fmt.M1.Stage → ℕ) (t tE : T12)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (hcs : D.st.codes = cs) :
    GroupFacts cs (fun s => r s.st) t a G0 Ly D := by
  obtain ⟨hJ, ht, hk, hh⟩ :=
    yes_facts π r (fun s => r s.st) (fun _ => rfl) hj he hp t tE rs gs h a rest G0 Ly D hf
  obtain ⟨hfind, hmem⟩ := found_of_decide π t tE rs gs h a rest G0 Ly D hf
  exact ⟨hcs, hJ, ht, hk, hh, hfind, hmem⟩

/-- **`CoreLeft`, paid member by member**: from the codes' equation and `MemberFacts`
(seven clauses a member) at an injective list of members that holds all that sit: the members' half
of the premise of `coreFacts_all` (SeamMembersAll.lean). So whoever pays `MemberFacts`' clauses
by name pays `CoreLeft`. -/
theorem coreLeft_of_members (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop) (t : T12) (y : Fr.E.Str) (a0 : A) (Y : Strs)
    (H : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout)
      (D : Plain), Fixes π t a rest G0 Ly D →
      D.st.codes = cs ∧
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, sits z → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length, MemberFacts cs G Fr no rad smp mem y a0 Y a D j (xs j) (es j)) :
    CoreLeft cs G Fr π no rad smp mem sits t y a0 Y := by
  intro a rest G0 Ly D hf
  obtain ⟨hcs, xs, es, hinj, hs, hM⟩ := H a rest G0 Ly D hf
  exact ⟨hcs, fun j => (hM j).1, fun j => (hM j).2.1, es, xs, fun j => (hM j).2.2.1, hinj, hs,
    fun j => (hM j).2.2.2.1, fun j => (hM j).2.2.2.2.1, fun j => (hM j).2.2.2.2.2.1,
    fun j => (hM j).2.2.2.2.2.2⟩

end

/-- **The first arm, asking of the bundle only what the relation's own «accept» does not give.**
-/
theorem core_behind_QW' {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs)
    (h : QW Fr π (nlAt π lo) r rdN enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t → t.mask.isSome = true ∧ BookOrd π.nums.firstTree t.book)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, enter a.1.2 = .ok t →
      CoreLeft cs G Fr π (fun z => lo + z) (fun s => r s.st) smp mem sits t a.2 a0 Y)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨t0, tE, h1, _, _, rs, gs, hy⟩ := id h
  refine core_behind_QW cs G Fr π lo r rdN smp mem sits rd hrd enter leave a b a0 Y h hB
    (fun t ht => ?_) hI
  obtain rfl : t0 = t := Except.ok.inj (h1.symm.trans ht)
  exact coreFacts_of_yes cs G Fr π _ r smp mem sits t0 tE a.2 a0 Y hj he hp rs gs hy (left t0 ht)

/-- **The second arm, the like.** -/
theorem core_behind_QWO' {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (t₁ t₂ ch : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs)
    (h : QWO Fr π t₁ t₂ ch r rdN enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t →
      t.mask = none ∧ BookStep π.nums.firstTree t.book t.roots)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, enter a.1.2 = .ok t →
      CoreLeft cs G Fr π (noAt t₁ t₂ ch) (fun s => r s.st) smp mem sits t a.2 a0 Y)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨t0, tE, h1, _, _, rs, gs, hy⟩ := id h
  refine core_behind_QWO cs G Fr π t₁ t₂ ch r rdN smp mem sits rd hrd enter leave a b a0 Y h hB
    (fun t ht => ?_) hI
  obtain rfl : t0 = t := Except.ok.inj (h1.symm.trans ht)
  exact coreFacts_of_yes cs G Fr π _ r smp mem sits t0 tE a.2 a0 Y hj he hp rs gs hy (left t0 ht)

/-- **At any numbering by labels nl: no carriage to the book's places.** FIRST LIMIT: THE BOOK's
PRICE IS NOT GONE: IT HAS MOVED INTO `CoreLeft`'s LAST CLAUSE: whoever shows the members' words at
no := nuOf π nl t must know which label each of the book's trees bears. `core_at` is general in its
letter no: here it is called at no := nuOf π nl t outright: so no binder speaks of the book. For a
test whose openings are taken over from earlier chains, where «the book is in order» has not the own
trees' form. -/
theorem core_behind_QWn {P S Xi A : Type} (cs : Codes) (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × Fr.E.Str) (a0 : A) (Y : Strs) (h : QW Fr π nl r rdN enter leave a b)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, enter a.1.2 = .ok t →
      CoreLeft cs G Fr π (nuOf π nl t) (fun s => r s.st) smp mem sits t a.2 a0 Y)
    (hI : ∀ t, enter a.1.2 = .ok t → InOrder t.st) :
    ∃ t G0, enter a.1.2 = .ok t ∧ t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT cs mem rd m) ∧
        ∀ x, sits x → CandAt cs G smp x a0 Y (m x) := by
  obtain ⟨t, tE, h1, _, hq, rs, gs, hy⟩ := h
  obtain ⟨_, _, G0, _, _, hf, _⟩ := id hq
  exact ⟨t, G0, h1, hf.2.1, core_at cs G Fr π _ _ rdN smp mem sits rd hrd t a.2 a0 Y
    (coreFacts_of_yes cs G Fr π _ r smp mem sits t tE a.2 a0 Y hj he hp rs gs hy (left t h1))
    (hI t h1) hq G0 hf.2.1⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QW
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QWO
#print axioms VerifiableInference.Desc.K12.Coin.coreFacts_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QW'
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QWO'
#print axioms VerifiableInference.Desc.K12.Coin.core_behind_QWn
#print axioms VerifiableInference.Desc.K12.Coin.groupFacts_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.coreLeft_of_members
