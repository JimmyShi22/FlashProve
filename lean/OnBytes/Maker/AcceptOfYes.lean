-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/AcceptOfYes.lean: tools for the yes of the reduction of a whole file
(OnBytes/Maker/Whole.lean): three of its five kinds of test, five of the nine, one by one.

The verifier of that reduction (`reductionOfWholeFile`) makes nine tests: the proofs of work of the three
chains; that no stored table's part of a round's draws is shortened, chain by chain; that each
symbol read of the stored table carries its position; the test on what the three silent rounds send;
and the run on the three views. OnBytes/Maker/ViewsAlike.lean puts them together.

Main theorems.
  `fullOf_of_within`: the test on the parts, from `PartsWithin` (OnBytes/Maker/ReadFacts.lean).
  `mem_wantsOf_table`: what a want of the stored table comes from.
  `carries_chain`, `carriesOf_append`: the test on the symbols' positions.
  `silentOf_yes`, `silentOf_file`: the test on the silent rounds (`silentOf`,
    OnBytes/Maker/SilentParts.lean) says yes where the front and the joining round hold the
    instance's answers and the front its number.

What is not claimed. None of the hypotheses. Nothing on soundness.


-/
import OnBytes.Maker.TypingViews
import OnBytes.Maker.Files
import OnBytes.Maker.Decide3Laws
import OnBytes.Maker.SilentParts

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ

/-! ## The parts of the draws -/

/-- No part is shortened. -/
theorem fullOf_of_within : ∀ (dl : List Three.RDL) (ros : List Fmt.RoundOut), PartsWithin dl ros →
    fullOf (dl.map rdtOf) (ros.map (·.drawn)) = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: dl, ro :: ros, h => by
    show ((d.stored.all fun s => (Fmt.partOf s ro.drawn.poss).length == s.count) &&
      fullOf (dl.map rdtOf) (ros.map (·.drawn))) = true
    rw [fullOf_of_within dl ros fun p hp =>
      h p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp), Bool.and_true,
      List.all_eq_true]
    intro s hs
    have h1 : s.lo + s.count ≤ ro.drawn.poss.length :=
      h (d, ro) (by rw [List.zip_cons_cons]; exact List.mem_cons_self) s hs
    rw [beq_iff_eq]
    unfold Fmt.partOf
    rw [List.length_take, List.length_drop]
    omega

/-! ## The symbols' positions -/

/-- A want of the stored table comes from a round, one of its stored tables, and the list of that
table's part of the round's draws. -/
theorem mem_wantsOf_table (a : ℕ) (dep : ℕ → Option ℕ) (item x : ℕ) :
    ∀ (ds : List RDT) (Rs : List Fmt.Drawn), Want.table item x ∈ wantsOf a dep ds Rs →
    ∃ p ∈ ds.zip Rs, ∃ s ∈ p.1.stored,
      x ∈ Fmt.listOf ((Fmt.partOf s p.2.poss).map (· % 2 ^ a))
  | [], _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, R :: Rs, h => by
    rw [wantsOf_cons, List.mem_append, List.mem_append] at h
    rcases h with (h | h) | h
    · obtain ⟨s, hs, hx⟩ := List.mem_flatMap.1 h
      obtain ⟨x', hx', e⟩ := List.mem_map.1 hx
      cases e
      exact ⟨(d, R), by rw [List.zip_cons_cons]; exact List.mem_cons_self, s, hs, hx'⟩
    · obtain ⟨j, -, hx⟩ := List.mem_flatMap.1 h
      unfold treeWants at hx
      split at hx
      · cases hx
      · obtain ⟨_, -, e⟩ := List.mem_map.1 hx
        cases e
    · obtain ⟨p, hp, r⟩ := mem_wantsOf_table a dep item x ds Rs h
      exact ⟨p, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp, r⟩

/-- A member of a list has a partner in a list no shorter. -/
theorem exists_zip_right {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (x : α), x ∈ l₁ →
    l₁.length ≤ l₂.length → ∃ c, (x, c) ∈ l₁.zip l₂
  | [], _, _, h, _ => by cases h
  | _ :: _, [], _, _, hl => by simp at hl
  | a :: l₁, b :: l₂, x, h, hl => by
    rcases List.mem_cons.1 h with e | h'
    · exact ⟨b, by rw [List.zip_cons_cons, e]; exact List.mem_cons_self⟩
    · obtain ⟨c, hc⟩ := exists_zip_right l₁ l₂ x h' (by simpa using hl)
      exact ⟨c, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hc⟩

section
variable (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) (etab : List (ℕ × Row3))
  (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str)

/-- **Each symbol that one chain reads of the stored table carries its position.** -/
theorem carries_chain (hext : ExtHolds a W r etab)
    (hy : ∀ (x : ℕ) (hx : x < 2 ^ a) c s pt, etab.lookup x = some (c, s, pt) →
      y ⟨x, hx⟩ = (x, c))
    (dl : List Three.RDL) (ros : List Fmt.RoundOut)
    (hop : ∀ p ∈ dl.zip ros, p.2.opens.length = p.1.stored.length + p.1.opens.length)
    (hsto : ∀ p ∈ dl.zip ros, ∀ q ∈ p.1.stored.zip p.2.opens, q ∈ storedRowsW W r)
    (hlist : ListedAsDrawn a dl ros) :
    carriesOf (WholeD.of a W) y
      (wantsOf a (WholeD.of a W).depth (dl.map rdtOf) (ros.map (·.drawn))) = true := by
  unfold carriesOf
  rw [List.all_eq_true]
  intro w hw
  cases w with
  | tree j x => rfl
  | table item x =>
    obtain ⟨p, hp, s, hs, hx⟩ := mem_wantsOf_table a _ item x _ _ hw
    rw [List.zip_map, List.mem_map] at hp
    obtain ⟨⟨d, ro⟩, hdr, rfl⟩ := hp
    have hs' : s ∈ d.stored := hs
    have h2 : ro.opens.length = d.stored.length + d.opens.length := hop (d, ro) hdr
    obtain ⟨z, hz⟩ := exists_zip_right d.stored ro.opens s hs' (by omega)
    have hl := (hlist (d, ro) hdr).1 (s, z) hz
    obtain ⟨e1, e2, -, hok⟩ := hext.row s z (hsto (d, ro) hdr _ hz)
    have hx' : x ∈ z.2.1 := by
      rw [hl]
      exact hx
    obtain ⟨c, hc⟩ := exists_zip_right z.2.1 z.2.2.cols x hx'
      (Nat.le_of_eq (TieTree.ok_spec (asOpenB z) _ _ hok).1.symm)
    obtain ⟨sl, pt, hlk⟩ := hext.look s z (hsto (d, ro) hdr _ hz) x c hc
    have hlt : x < 2 ^ a := by
      have := (TieTree.ok_list (asOpenB z) _ _ hok).2.1 x hx'
      rw [show (asOpenB z).a = z.1.a from rfl, e1, e2] at this
      exact this
    show (if h : x < 2 ^ a then (y ⟨x, h⟩).1 == x else false) = true
    rw [dif_pos hlt, hy x hlt c sl pt hlk]
    exact beq_self_eq_true x

end

/-- The test on the symbols' positions, of two lists of wants laid behind each other. -/
theorem carriesOf_append (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (u v : List Want) :
    carriesOf D y (u ++ v) = (carriesOf D y u && carriesOf D y v) := by
  unfold carriesOf
  rw [List.all_append]

/-! ## The silent rounds -/

/-- The test on the silent rounds says yes where the front and the joining round hold the instance's
answers, and the front the instance's number. -/
theorem silentOf_yes {Xi A : Type} [DecidableEq A] (ans : Xi → A) (copy : Xi → ℕ) (x : Xi)
    (f : FrontMsg A) (j : Compile.Joined.JoinMsg A ByteArray) (t : ByteArray)
    (h1 : f.answers = ans x) (h2 : f.copy = copy x) (h3 : j.answers = ans x) :
    silentOf ans copy x f j t = true := by
  unfold silentOf
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The same where the front and the joining round are laid from the instance's own answers and
number. Of the file only the second chain's run's value enters, which the test does not read; t is
any string. -/
theorem silentOf_file {Xi A : Type} [DecidableEq A] (ans : Xi → A) (copy : Xi → ℕ) (x : Xi)
    (r : Proof.TailRead) (j : Compile.Joined.JoinMsg A ByteArray) (t : ByteArray)
    (hj : joinOf (ans x) r = some j) :
    silentOf ans copy x (frontOf (ans x) (copy x)) j t = true := by
  unfold joinOf at hj
  obtain ⟨run, -, rfl⟩ := Option.map_eq_some_iff.1 hj
  exact silentOf_yes ans copy x _ _ t rfl rfl rfl

end OnBytes.Maker
