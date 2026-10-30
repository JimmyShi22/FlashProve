-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyCaller.lean: THE KEY FILE's FIRST CHAIN AT THE KEY FILE's DESCRIPTION (descriptionFromSource, Johnson/Desc/Key/Desc.lean): THE CALLER OF A LOOKUP (look‹l›.1.caller): THE NINTH AND TENTH OF THE TEN: ITS LAW «Keeps» (borders 3 → 4 · 9 → 10) FROM NAMED FACTS ON ITS YES.
  withCall s d' Fk hm   the state behind: the statement's part d', a ledger Fk opened, nothing heard, the homes hm
  CallGround s d'       WHAT THE GROUND's takeMasksP (Johnson/Desc/First/Base/Ground.lean; called twice) IS ASKED TO GIVE: the tables' sizes, the codes and the groups are not turned · every oracle message is the same BUT FOR ITS LEDGER
  ForkReady n Fk hm     the ledger that the caller opens is ready: its count at 0 · its size n · its three arrays of that size · no slot got · as many homes as slots (ready_slots | homeIs_of_size, in Johnson/Desc/First/Look/KeyLaw/Caller.lean, say this of the caller's text)
  CallerYes n b         the caller's yes: OWED BY WHOEVER HAS THE CALLER's CONTENT
  (Where this and lean/THEOREM.md differ, the page holds.)
  ReadsL G              a premise on the reading: of the chain's state it reads the statement's oracle messages, their ledgers left out, THE BOOK AND THE CODES (these two are let in: all ten blocks leave both, by reading). IT IS THE ONE PREMISE ON G FOR ALL TEN (ReadsL.readsO | readsD: PROVED). MET BY EVERY READING WHOSE smp | recOf ARE
                        FUNCTIONS OF WHAT WAS HANDED AND OF THE ORACLE MESSAGES WITHOUT THEIR LEDGERS (a ledger says which mask entries are handed out: no part of a sample): that the reading meant is such is owed by whoever fills it.
                        (Where this and lean/THEOREM.md differ, the page holds.)
  rides_call · c_3_4 | sh_3_4 · c_9_10 | sh_9_10 · keeps_caller0 | keeps_caller1   **PROVED** from these
Nothing on soundness.
-/
import Johnson.RunOne.KeyThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

/-- The state behind a caller. -/
def withCall (s : FirstState) (d' : PlainState) (Fk : Fork) (hm : Array Slot) : FirstState := { s with d := d', base := { s.base with fork := some Fk, heard := none, home := hm } }

/-- An oracle message, its ledger left out. -/
def unl (x : OnBytes.Oracle) : OnBytes.Oracle := { x with ledger := none }

/-- **What the ground's takeMasksP is asked to give.** -/
structure CallGround (s : FirstState) (d' : PlainState) : Prop where
  tables : SameTables d'.st s.d.st
  codes : d'.st.codes = s.d.st.codes
  groups : d'.st.groups = s.d.st.groups
  book : d'.book = s.d.book
  oracle : ∀ o : Nat, (d'.st.oracles[o]?).map unl = (s.d.st.oracles[o]?).map unl
  /-- the count of roots is not turned -/
  roots : d'.roots = s.d.roots

/-- **The ledger that the caller opens is ready.** -/
structure ForkReady (n : Nat) (Fk : Fork) (hm : Array Slot) : Prop where
  home : hm.size = n
  next : Fk.next = 0
  ns : Fk.ns = n
  vp : Fk.vp.size = n
  mf : Fk.mf.size = n
  got : Fk.gotF.size = n
  free : ∀ j, j < n → Fk.gotF.getD j true = false

theorem ForkReady.free_all {n : Nat} {Fk : Fork} {hm : Array Slot} (H : ForkReady n Fk hm) : ((List.range (Fk.ns - Fk.next)).all fun j => !Fk.gotF.getD (Fk.next + j) true) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' : j < n := by have := List.mem_range.1 hj; rw [H.ns, H.next] at this; omega
  rw [H.next, Nat.zero_add, H.free j hj']; rfl

/-- **The caller's yes.** -/
def CallerYes (n : Nat) (b : Block FirstState Claim) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ d' Fk hm, s' = withCall s d' Fk hm ∧ CallGround s d' ∧ ForkReady n Fk hm

section
variable {Cells M Smp Rec : Type} (G : Reading (Xi × FirstState) Cells M Smp Rec) (one : OneTime)

/-- **A premise on the reading**: of the chain's state it reads the statement's oracle messages, their ledgers left out. -/
def ReadsL : Prop := ∀ (p : Xi) (s s' : FirstState), (∀ o : Nat, (s'.d.st.oracles[o]?).map unl = (s.d.st.oracles[o]?).map unl) → s'.d.book = s.d.book → s'.d.st.codes = s.d.st.codes → SamePins G (p, s) (p, s')

/-- ONE PREMISE ON THE READING SERVES ALL TEN: ReadsL gives ReadsO (rng.0.rows) and ReadsD («cleared»). -/
theorem ReadsL.readsO (h : ReadsL G) : ReadsO G := fun p s s' e eb ec => h p s s' (fun o => by rw [e]) eb ec

theorem ReadsL.readsD (h : ReadsL G) : ReadsD G := fun p s s' e => h p s s' (fun o => by rw [e]) (by rw [e]) (by rw [e])

variable (s : FirstState) (d' : PlainState) (Fk : Fork) (hm : Array Slot)

theorem oracle_call (H : CallGround s d') (o : Nat) (x' : OnBytes.Oracle) (h : d'.st.oracles[o]? = some x') :
    ∃ x, s.d.st.oracles[o]? = some x ∧ x.sampled = x'.sampled ∧ x.sampleRows = x'.sampleRows := by
  have e := H.oracle o
  rw [h] at e
  cases hx : s.d.st.oracles[o]? with
  | none => rw [hx] at e; cases e
  | some x =>
    rw [hx] at e
    have e' : unl x' = unl x := Option.some.inj e
    exact ⟨x, rfl, (congrArg (·.sampled) e').symm, (congrArg (·.sampleRows) e').symm⟩

theorem sampleIn_call (H : CallGround s d') (o : Nat) (h : KeyRows23.SampleIn s.d.st o) : KeyRows23.SampleIn d'.st o :=
  sampleIn_of s.d.st d'.st H.codes (fun o' => by
    have q := congrArg (Option.map fun x : OnBytes.Oracle => (x.shape, x.sampleRows)) (H.oracle o')
    simpa [Option.map_map, Function.comp_def, unl] using q) o h

/-- **Means.InOrder rides past a caller**: the groups and the codes stay; of a message its ledger alone turns. By InOrder.sameGroups | samples_of. -/
theorem order_call (H : CallGround s d') (h : Means.InOrder s.d.st) : Means.InOrder d'.st := by
  have hE : Means.Extends s.d.st d'.st := ⟨H.codes, fun o x hx => by
    have q := H.oracle o
    rw [hx] at q
    cases hx' : d'.st.oracles[o]? with
    | none => rw [hx'] at q; cases q
    | some x' =>
      rw [hx'] at q
      exact ⟨x', rfl, congrArg (·.shape) (Option.some.inj q : unl x' = unl x)⟩⟩
  exact h.sameGroups hE H.groups (h.samples_of hE fun o => by
    have q := congrArg (Option.map fun x : OnBytes.Oracle => x.sampleRows) (H.oracle o)
    simpa [Option.map_map, Function.comp_def, unl] using q)

theorem sentB_call (H : CallGround s d') (k : Nat) : sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) k = sentB (plan₁ one) (readers₁ one) s k := by
  unfold sentB
  cases ho : (plan₁ one).orc k with
  | none => rfl
  | some o =>
    show (match d'.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false) = (match s.d.st.oracles[o]? with | some x => x.sampled && x.sampleRows.size != 0 | none => false)
    have e := H.oracle o
    cases h1 : d'.st.oracles[o]? with
    | none =>
      rw [h1] at e
      cases h2 : s.d.st.oracles[o]? with
      | none => rfl
      | some x => rw [h2] at e; cases e
    | some x' =>
      obtain ⟨x, hx, e1, e2⟩ := oracle_call s d' H o x' h1
      rw [hx]
      show (x'.sampled && x'.sampleRows.size != 0) = (x.sampled && x.sampleRows.size != 0)
      rw [e1, e2]

theorem groupB_call (H : CallGround s d') (ir : Bool) (n : Nat) : groupB (readers₁ one) (withCall s d' Fk hm) ir n = groupB (readers₁ one) s ir n := by
  unfold groupB
  show (match ((readers₁ one).grpB s).bind fun g => d'.st.groups[g]? with | some Gr => Gr.inRun == ir && Gr.rows.size == n | none => false) = _
  rw [H.groups]
  rfl

/-- **KeyQuiet.Rides around a caller**, at every open set without «grows»-turning: the groups are the same. -/
theorem rides_call (hG : ReadsL G) (H : CallGround s d') (O : List KItem) (p : Xi) : Rides G (readers₁ one) O p s (withCall s d' Fk hm) :=
  { marked := rfl, pins := hG p s (withCall s d' Fk hm) H.oracle H.book H.codes
    stmt := fun _ => ⟨H.tables, fun o x' h => oracle_call s d' H o x' h⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun g G' h => ⟨G', (show s.d.st.groups[g]? = some G' from H.groups ▸ h), rfl⟩⟩ }

/-- The ties' step across a caller: border 3 → 4. -/
theorem tA_3_4 (H : CallGround s d') (h : tiesA one 3 s = true) : tiesA one 4 (withCall s d' Fk hm) = true := by
  have h' : ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (s.d.st.codes = one.codes) && s.idx == 0 && ((s.d.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (s.d.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨e, f⟩, g⟩ := h'
  have g' : (d'.st.oracles[2]?).any (fun x => !x.sampled && !x.spentAsMask) = true := by
    have q := H.oracle 2
    cases h2 : s.d.st.oracles[2]? with
    | none => rw [h2] at g; cases g
    | some x =>
      rw [h2] at g q
      cases h1 : d'.st.oracles[2]? with
      | none => rw [h1] at q; cases q
      | some x' =>
        rw [h1] at q
        have q' : unl x' = unl x := Option.some.inj q
        show (!x'.sampled && !x'.spentAsMask) = true
        rw [show x'.sampled = x.sampled from congrArg (·.sampled) q', show x'.spentAsMask = x.spentAsMask from congrArg (·.spentAsMask) q']
        exact g
  show ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (d'.st.codes = one.codes) && s.idx == 0 && ((d'.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (d'.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true
  rw [H.codes, H.groups, a, b, c, d, e, f, g']; rfl

/-- The ties' step across a caller: border 9 → 10. -/
theorem tA_9_10 (H : CallGround s d') (h : tiesA one 9 s = true) : tiesA one 10 (withCall s d' Fk hm) = true := by
  have h' : ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (s.d.st.codes = one.codes) && s.idx == 0 && ((s.d.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (s.d.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨e, f⟩, g⟩ := h'
  have g' : (d'.st.oracles[2]?).any (fun x => !x.sampled && !x.spentAsMask) = true := by
    have q := H.oracle 2
    cases h2 : s.d.st.oracles[2]? with
    | none => rw [h2] at g; cases g
    | some x =>
      rw [h2] at g q
      cases h1 : d'.st.oracles[2]? with
      | none => rw [h1] at q; cases q
      | some x' =>
        rw [h1] at q
        have q' : unl x' = unl x := Option.some.inj q
        show (!x'.sampled && !x'.spentAsMask) = true
        rw [show x'.sampled = x.sampled from congrArg (·.sampled) q', show x'.spentAsMask = x.spentAsMask from congrArg (·.spentAsMask) q']
        exact g
  show ((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (d'.st.codes = one.codes) && s.idx == 0 && ((d'.st.groups[s.grp]?).any (fun G => G.members.toList == [1]) && s.rider == some 2 && (d'.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)) = true
  rw [H.codes, H.groups, a, b, c, d, e, f, g']; rfl

theorem sz_call (H : CallGround s d') (x y : Nat) (hx : counts₁ one y = counts₁ one x) (h2x : 2 ≤ x) (h2y : 2 ≤ y) (h8x : x < 18) (h8y : y < 18) (h7x : x < 17) (h7y : y < 17) : sizesB one y (withCall s d' Fk hm) = sizesB one x s := by
  unfold sizesB
  show (d'.st.oracles.size == (counts₁ one y).1 && d'.st.groups.size == (counts₁ one y).2.1 && d'.book.trees.size == (counts₁ one y).2.2 && d'.book.place.size == d'.st.oracles.size && (decide (2 ≤ y) || _) && (decide (y < 17) || _) && (decide (y < 18) || _) && (decide (y < 17) || _)) = _
  rw [H.tables.1, H.groups, H.book, hx, decide_eq_true h2x, decide_eq_true h2y, decide_eq_true h8x, decide_eq_true h8y, decide_eq_true h7x, decide_eq_true h7y]
  rfl

theorem t_3_4 (H : CallGround s d') (h : ties₁ one 3 s = true) : ties₁ one 4 (withCall s d' Fk hm) = true := by
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 (show (tiesA one 3 s && moreB 3 s && sizesB one 3 s) = true from h)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨tA_3_4 one s d' Fk hm H h1, (show moreB 4 (withCall s d' Fk hm) = moreB 3 s from by unfold moreB; rw [show (withCall s d' Fk hm).d.book = s.d.book from H.book, show (withCall s d' Fk hm).d.roots = s.d.roots from H.roots]; rfl).trans h2⟩, (sz_call one s d' Fk hm H 3 4 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3⟩

theorem t_9_10 (H : CallGround s d') (h : ties₁ one 9 s = true) : ties₁ one 10 (withCall s d' Fk hm) = true := by
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 (show (tiesA one 9 s && moreB 9 s && sizesB one 9 s) = true from h)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨tA_9_10 one s d' Fk hm H h1, (show moreB 10 (withCall s d' Fk hm) = moreB 9 s from by unfold moreB; rw [show (withCall s d' Fk hm).d.book = s.d.book from H.book, show (withCall s d' Fk hm).d.roots = s.d.roots from H.roots]; rfl).trans h2⟩, (sz_call one s d' Fk hm H 9 10 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3⟩

/-- core₁'s step across the caller of lookup 0: border 3 → 4. -/
theorem c_3_4 (H : CallGround s d') (Hf : ForkReady (slots₁ one 0) Fk hm) (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 3 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 (withCall s d' Fk hm) = true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) && _) = true := h
  have h1 : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) = true := (Bool.and_eq_true_iff.1 h').1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h1
  have a' := (sentB_call one s d' Fk hm H 0).trans a
  have b' := (sentB_call one s d' Fk hm H 1).trans b
  have c' : (!sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 2) = true := by rw [sentB_call one s d' Fk hm H 2]; exact c
  have d'' := (groupB_call one s d' Fk hm H false 0).trans d
  show (sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 0 && sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 1 && !sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 2 && groupB (readers₁ one) (withCall s d' Fk hm) false 0 && doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone &&
    (!false && hm.size == slots₁ one 0 && (Fk.next == 0 && Fk.ns == slots₁ one 0 && (Fk.vp.size == Fk.ns && Fk.mf.size == Fk.ns && Fk.gotF.size == Fk.ns) && ((List.range (Fk.ns - Fk.next)).all fun j => !Fk.gotF.getD (Fk.next + j) true)))) = true
  rw [a', b', c', d'', e, f, Hf.free_all]
  simp [Hf.home, Hf.next, Hf.ns, Hf.vp, Hf.mf, Hf.got]

theorem sh_3_4 (H : CallGround s d') (Hf : ForkReady (slots₁ one 0) Fk hm) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 3 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 (withCall s d' Fk hm) = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 3 4 s (withCall s d' Fk hm) (t_3_4 one s d' Fk hm H) (c_3_4 one s d' Fk hm H Hf) h

/-- core₁'s step across the caller of lookup 1: border 9 → 10. -/
theorem c_9_10 (H : CallGround s d') (Hf : ForkReady (slots₁ one 1) Fk hm) (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 9 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 (withCall s d' Fk hm) = true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) && _) = true := h
  have h1 : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) = true := (Bool.and_eq_true_iff.1 h').1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h1
  have a' := (sentB_call one s d' Fk hm H 0).trans a
  have b' := (sentB_call one s d' Fk hm H 1).trans b
  have c' : (!sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 2) = true := by rw [sentB_call one s d' Fk hm H 2]; exact c
  have d'' := (groupB_call one s d' Fk hm H false 0).trans d
  show (sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 0 && sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 1 && !sentB (plan₁ one) (readers₁ one) (withCall s d' Fk hm) 2 && groupB (readers₁ one) (withCall s d' Fk hm) false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone &&
    (!false && hm.size == slots₁ one 1 && (Fk.next == 0 && Fk.ns == slots₁ one 1 && (Fk.vp.size == Fk.ns && Fk.mf.size == Fk.ns && Fk.gotF.size == Fk.ns) && ((List.range (Fk.ns - Fk.next)).all fun j => !Fk.gotF.getD (Fk.next + j) true)))) = true
  rw [a', b', c', d'', e, f, Hf.free_all]
  simp [Hf.home, Hf.next, Hf.ns, Hf.vp, Hf.mf, Hf.got]

theorem sh_9_10 (H : CallGround s d') (Hf : ForkReady (slots₁ one 1) Fk hm) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 9 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 (withCall s d' Fk hm) = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 9 10 s (withCall s d' Fk hm) (t_9_10 one s d' Fk hm H) (c_9_10 one s d' Fk hm H Hf) h

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- **Border 3 → 4: the caller of lookup 0.** -/
theorem keeps_caller0 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : CallerYes (slots₁ one 0) b)
    (hbase : ∀ j ∈ pinned (open₁ 2 3), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 3) (on₁ F Fr G at_ one R coll 4) (L₁ F Fr G at_ one R 3) (L₁ F Fr G at_ one R 4) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 3 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    obtain ⟨d', Fk, hm, e, H, Hf⟩ := hb s rs gs s' h
    subst e
    exact ⟨fun p => rides_call G one s d' Fk hm hG H _ p, sh_3_4 one s d' Fk hm H Hf, H.book, fun h18 => absurd h18 (by decide), fun o => sampleIn_call s d' H o, order_call s d' H⟩

/-- **Border 9 → 10: the caller of lookup 1.** -/
theorem keeps_caller1 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hb : CallerYes (slots₁ one 1) b)
    (hbase : ∀ j ∈ pinned (open₁ 2 9), (at_ j).1 < pc.base) (hcoll : CollCell coll) (hG : ReadsL G) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 9) (on₁ F Fr G at_ one R coll 10) (L₁ F Fr G at_ one R 9) (L₁ F Fr G at_ one R 10) pc.err :=
  keeps_empty_at F Fr G at_ one R coll pc b hheld 9 (by decide) (by decide) hbase hcoll fun s rs gs s' h => by
    obtain ⟨d', Fk, hm, e, H, Hf⟩ := hb s rs gs s' h
    subst e
    exact ⟨fun p => rides_call G one s d' Fk hm hG H _ p, sh_9_10 one s d' Fk hm H Hf, H.book, fun h18 => absurd h18 (by decide), fun o => sampleIn_call s d' H o, order_call s d' H⟩

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.keeps_caller0
#print axioms Johnson.RunOne.KeyRows1.keeps_caller1
