-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SentRows.lean: the code switch: WHAT A YES OF THE SENDING LAYS AS THE
NEW MESSAGES' STORED SAMPLE ROWS.

SentKeeps.lean's sent_ok says what the sending that K2 runs leaves as it was, which numbers it
returns and which shapes it lays. Here: which SAMPLE ROWS stand in the statement behind it at each
new message that has an answer.
  RowsAre      rows are the sample rows of the message o of the shape s at the seeds: as many as s
               has answers; number i is the program's Send.form at seed number i, with some element
               as its target
  rowsFor_are  the ground's rowsFor makes such rows
  incr_lt, incr_tail  in a list that Fmt.increasing passes the first number is below all others; its
               tail passes too
  loop_rows    the ground's loop over the messages to sample, whose numbers differ: behind it each
               of them has the rows that rowsFor made for it
  seedsOf_len, seedsOf_head  what the program's Send.seedsOf cuts
  SentRows     what stands behind a sending: there are seeds, read by the program's Send.seedsOf off
               round 1's drawn elements, none with the factor 0, such that every new message with an
               answer has RowsAre at them, and its cube has at most as many coordinates as a seed's
               point; a new message without an answer has no stored row
  sendP_rows, sendOpen_rows, sent_rows  of the plain ground's sendP, of Send.sendOpen, of the
               sending that K2 runs
  rowsFor_spec, admit_rows, mapM_zip, mem_zip_of, foldl_max_ge  tools: what rowsFor returns; what
               admitting lays; three on lists
Kin: OnBytes/Slice/BlkSendRun.lean, and Admitted (OnBytes/Tie/Pv/Switch/LocAnswers.lean; spent in
Johnson/Top/H/LocPlace.lean), have the like for a run of the programs' routine.
The plain ground's sendP (Johnson/Desc/Ground/Calls.lean) calls the own-text seedsMade, formMade,
allZero and rising (Johnson/Desc/Own/); this file's statements speak of the program's Send.seedsOf,
Send.form, isZeroE and Fmt.increasing. Two lines of proof take the first and the last back by
Own/SendAgree.lean's seedsMade_eq and Own/RisingAgree.lean's rising_agrees; the two others unfold.
LIMITS. WHICH of round 2's answers is a row's target: SentTargets.lean. The library's typed sample
matrix: SeedBehind.lean. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.SentKeeps
import Johnson.Desc.Own.SendAgree
import Johnson.Desc.Own.RisingAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain VerifiableInference.Desc.Ground

/-- The sample rows of the message o of the shape s, at the seeds. -/
def RowsAre (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed)
    (rows : Array OnBytes.Row) : Prop :=
  rows.size = s.answers ∧ ∀ i, i < s.answers → ∃ seed row y, seeds[i]? = some seed ∧
    Send.form codes s o seed i = some row ∧ rows[i]? = some { row with target := y }

theorem rowsFor_spec (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) :
    ∀ (is : List Nat) (ys : List E) (acc rows : Array OnBytes.Row) (ys' : List E),
      rowsFor codes s o seeds is ys acc = some (rows, ys') →
      rows.size = acc.size + is.length ∧ (∀ j, j < acc.size → rows[j]? = acc[j]?) ∧
      ∀ j (hj : j < is.length), ∃ seed row y, seeds[is[j]]? = some seed ∧
        Send.form codes s o seed is[j] = some row ∧
        rows[acc.size + j]? = some { row with target := y }
  | [], ys, acc, rows, ys', h => by
    simp only [rowsFor, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | i :: is, [], acc, rows, ys', h => by simp [rowsFor] at h
  | i :: is, y :: ys, acc, rows, ys', h => by
    unfold rowsFor at h
    split at h
    · cases h
    · rename_i seed hseed
      split at h
      · cases h
      · rename_i row hrow
        obtain ⟨h1, h2, h3⟩ := rowsFor_spec codes s o seeds is ys _ rows ys' h
        rw [Array.size_push] at h1 h2 h3
        refine ⟨by rw [h1, List.length_cons]; omega, fun j hj => ?_, fun j hj => ?_⟩
        · rw [h2 j (by omega), Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]
        · cases j with
          | zero =>
            refine ⟨seed, row, y, hseed, hrow, ?_⟩
            rw [Nat.add_zero, h2 acc.size (by omega), Array.getElem?_push_size]
          | succ j =>
            obtain ⟨sd, rw', y', a, b, c⟩ := h3 j (by simpa using hj)
            refine ⟨sd, rw', y', a, b, ?_⟩
            rw [← c]
            congr 1
            omega

theorem rowsFor_are {codes : Codes} {s : OracleShape} {o : Nat} {seeds : List SampleSeed}
    {ys ys' : List E} {rows : Array OnBytes.Row}
    (h : rowsFor codes s o seeds (List.range s.answers) ys #[] = some (rows, ys')) :
    RowsAre codes s o seeds rows := by
  obtain ⟨h1, -, h3⟩ := rowsFor_spec codes s o seeds _ ys #[] rows ys' h
  refine ⟨by simpa using h1, fun i hi => ?_⟩
  obtain ⟨sd, rw', y', a, b, c⟩ := h3 i (by simpa using hi)
  simp only [List.getElem_range] at a b
  exact ⟨sd, rw', y', a, b, by simpa using c⟩

theorem incr_lt : ∀ (a : Nat) (l : List Nat), Fmt.increasing (a :: l) = true → ∀ b ∈ l, a < b
  | a, [], _, b, hb => by cases hb
  | a, c :: l, h, b, hb => by
    simp only [Fmt.increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact Nat.lt_trans h.1 (incr_lt c l h.2 b hb)

theorem incr_tail : ∀ (a : Nat) (l : List Nat), Fmt.increasing (a :: l) = true →
    Fmt.increasing l = true
  | a, [], _ => rfl
  | a, c :: l, h => by
    simp only [Fmt.increasing, Bool.and_eq_true] at h
    exact h.2

/-- What admitting lays. -/
theorem admit_rows {L : Type} {o : Nat} {d d' : DState L} {rows : Array OnBytes.Row}
    (h : admitP d o rows = some d') :
    (d'.st.oracles[o]?).map (·.sampleRows) = some rows ∧
      ∀ o', o ≠ o' → d'.st.oracles[o']? = d.st.oracles[o']? := by
  unfold admitP at h
  split at h
  · obtain ⟨x, hx, h⟩ := optBind h
    obtain ⟨places, -, h⟩ := optBind h
    cases h
    have ho : o < d.st.oracles.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hx
      cases hx
    exact ⟨OnBytes.Slice.admitted_sampleRows _ _ _ _ _ ho,
      fun o' ho' => OnBytes.Slice.admitted_other _ _ _ _ _ o' ho'⟩
  · cases h

/-- **Behind the loop each message has the rows that were made for it.** -/
theorem loop_rows {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      Fmt.increasing (l.map (·.1)) = true →
      sampleLoop groundG p codes seeds l ys d = some (d', left) →
      (∀ x ∈ l, ∃ rows, (d'.st.oracles[x.1]?).map (·.sampleRows) = some rows ∧
        RowsAre codes x.2 x.1 seeds rows) ∧
      ∀ o', (∀ x ∈ l, x.1 ≠ o') → d'.st.oracles[o']? = d.st.oracles[o']?
  | [], ys, d, d', left, _, h => by
    cases h
    exact ⟨fun x hx => (by cases hx), fun _ _ => rfl⟩
  | (o, s) :: l, ys, d, d', left, hi, h => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' hr
      split at h
      · cases h
      · rename_i d1 h1
        have hi' : Fmt.increasing (o :: l.map (·.1)) = true := hi
        obtain ⟨ha, hb⟩ := admit_rows (show admitP d o rows = some d1 from h1)
        obtain ⟨hc, hd⟩ := loop_rows p codes seeds l ys' d1 d' left (incr_tail _ _ hi') h
        refine ⟨fun x hx => ?_, fun o' ho' => ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine ⟨rows, ?_, rowsFor_are hr⟩
            rw [hd o fun z hz => Nat.ne_of_gt (incr_lt _ _ hi' z.1 (List.mem_map_of_mem hz))]
            exact ha
          · exact hc x hx
        · rw [hd o' fun z hz => ho' z (List.mem_cons_of_mem _ hz)]
          exact hb o' (ho' (o, s) (List.mem_cons_self ..))

/-- **What stands behind a sending, of the new messages' sample rows.** -/
def SentRows (S : Statement) (notices : Array OracleNotice) (r₁ : Fmt.RoundView) (S' : Statement) : Prop :=
  ∃ (bits answers : Nat) (seeds : List SampleSeed),
    Send.seedsOf bits answers (r₁.drawn.elems.map E.ofTriple) = some seeds ∧
    (∀ sd ∈ seeds, isZeroE sd.beta = false) ∧
    (∀ (i : Nat) (n : OracleNotice), notices[i]? = some n → n.shape.answers ≠ 0 →
      (Send.cube S.codes n.shape).bits ≤ bits ∧
      ∃ rows, (S'.oracles[S.oracles.size + i]?).map (·.sampleRows) = some rows ∧
        RowsAre S.codes n.shape (S.oracles.size + i) seeds rows) ∧
    ∀ (i : Nat) (n : OracleNotice), notices[i]? = some n → n.shape.answers = 0 →
      (S'.oracles[S.oracles.size + i]?).map (·.sampleRows) = some #[]

theorem mapM_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (ks : List β),
    l.mapM f = some ks → ks.length = l.length ∧ ∀ p ∈ l.zip ks, f p.1 = some p.2
  | [], ks, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun p hp => by simp at hp⟩
  | a :: l, ks, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        obtain ⟨e, hz⟩ := mapM_zip f l bs hl
        refine ⟨by simp [e], fun p hp => ?_⟩
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ha
        · exact hz p hp

theorem mem_zip_of {α β : Type} : ∀ (l : List α) (ks : List β), ks.length = l.length →
    ∀ a ∈ l, ∃ b, (a, b) ∈ l.zip ks
  | [], _, _, a, ha => by cases ha
  | x :: l, [], h, _, _ => by simp at h
  | x :: l, k :: ks, h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨k, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_of l ks (by simpa using h) a ha
      exact ⟨b, by simp [hb]⟩

theorem foldl_max_ge {α : Type} (f : α → Nat) : ∀ (l : List α) (b : Nat) (x : α), x ∈ l →
    f x ≤ l.foldl (fun b s => max b (f s)) b
  | [], _, x, h => by cases h
  | a :: l, b, x, h => by
    have mono : ∀ (l : List α) (b : Nat), b ≤ l.foldl (fun b s => max b (f s)) b := by
      intro l
      induction l with
      | nil => exact fun b => Nat.le_refl b
      | cons a l ih => exact fun b => Nat.le_trans (Nat.le_max_left _ _) (ih _)
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (mono l _)
    · exact foldl_max_ge f l _ x h

/-- What Send.seedsOf cuts: each seed's point has «bits» coordinates; the first seed is the first
«bits»
elements and the element behind them. -/
theorem seedsOf_len (bits : Nat) : ∀ (n : Nat) (l : List E) (seeds : List SampleSeed),
    Send.seedsOf bits n l = some seeds → ∀ sd ∈ seeds, sd.z.length = bits
  | 0, [], seeds, h, sd, hs => by
    simp only [Send.seedsOf, Option.some.injEq] at h
    subst h
    cases hs
  | 0, _ :: _, seeds, h, _, _ => by simp [Send.seedsOf] at h
  | n + 1, l, seeds, h, sd, hs => by
    unfold Send.seedsOf at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hs with rfl | hs
      · have : bits < l.length := by
          by_contra hc
          rw [List.drop_eq_nil_of_le (by omega)] at hd
          cases hd
        simp
        omega
      · exact seedsOf_len bits n rest t ht sd hs

theorem seedsOf_head (bits n : Nat) (l : List E) (seeds : List SampleSeed) (sd : SampleSeed)
    (h : Send.seedsOf bits n l = some seeds) (h0 : seeds[0]? = some sd) :
    sd.z = l.take bits ∧ l[bits]? = some sd.beta := by
  cases n with
  | zero =>
    cases l with
    | nil =>
      simp only [Send.seedsOf, Option.some.injEq] at h
      subst h
      cases h0
    | cons a l => simp [Send.seedsOf] at h
  | succ n =>
    unfold Send.seedsOf at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      refine ⟨rfl, ?_⟩
      have := congrArg (·[0]?) hd
      simpa using this

theorem sendP_rows {L : Type} {p : GPar} {own : Bool} {d : DState L} {sent : Array OracleNotice}
    {r₁ r₂ : Fmt.RoundView} {x : Array Nat × List E × List E × Nat × DState L}
    (h : sendP groundG p own d sent r₁ r₂ = some x) : SentRows d.st sent r₁ x.2.2.2.2.st := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := optBind h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := optBind h
  obtain ⟨seeds, hseeds, h⟩ := optBind h
  rw [VerifiableInference.Desc.Own.seedsMade_eq] at hseeds
  obtain ⟨an, -, h⟩ := optBind h
  split at h
  · rename_i hc
    obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBind h
    dsimp only at h
    split at h
    · cases h
      have hr : recvP p.firstTree d sent = some (ids, d₁) := h1
      unfold recvP at hr
      split at hr
      · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 hr
        cases e
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hlen, hz⟩ := mapM_zip _ _ _ hsh
        have hinc := hc.1.1.1.1.1.1.1.1.2
        rw [← VerifiableInference.Desc.Own.rising_agrees] at hinc
        have hbeta := hc.1.1.2
        obtain ⟨hrows, hoth⟩ := loop_rows p _ seeds _ an _ d₂ left
          (by rw [List.map_fst_zip (by omega)]; exact hinc) h2
        refine ⟨_, _, seeds, hseeds, fun sd hsd => ?_, fun i n hn ha => ?_, fun i n hn ha => ?_⟩
        · have := List.all_eq_true.1 hbeta sd hsd
          simpa using this
        · have hnew := OnBytes.Slice.stSent_new d.st sent i
          rw [hn] at hnew
          have hi : i < sent.size := by
            by_contra hcon
            rw [Array.getElem?_eq_none (by omega)] at hn
            cases hn
          obtain ⟨s, hs⟩ := mem_zip_of _ shapes hlen (d.st.oracles.size + i) (by
            refine List.mem_filter.2 ⟨?_, ?_⟩
            · simp only [Array.toList_map, List.mem_map]
              exact ⟨i, by simpa using hi, Nat.add_comm _ _⟩
            · rw [hnew]
              simpa using ha)
          have e := hz _ hs
          dsimp only at e
          rw [hnew] at e
          have e' : n.shape = s := Option.some.inj e
          subst e'
          exact ⟨foldl_max_ge (fun s => (Send.cube d.st.codes s).bits) _ 0 _ (List.of_mem_zip hs).2,
            hrows _ hs⟩
        · have hnew := OnBytes.Slice.stSent_new d.st sent i
          rw [hn] at hnew
          rw [hoth (d.st.oracles.size + i) fun z hz he => by
            have h5 := (List.mem_filter.1 (List.of_mem_zip hz).1).2
            rw [he, hnew] at h5
            simp [ha] at h5, hnew]
          rfl
      · cases hr
    · cases h
  · cases h

theorem sendOpen_rows {L : Type} {p : GPar} {owed : Option Nat} {sent : Array OracleNotice}
    {e₁ : Fmt.Entry} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {took : Nat}
    (h : VerifiableInference.Desc.First.Send.sendOpen groundG p owed sent e₁ d r₁ r₂ =
      some (ids, took, d')) : SentRows d.st sent r₁ d'.st := by
  unfold VerifiableInference.Desc.First.Send.sendOpen at h
  split at h
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact sendP_rows hx
  · cases h

attribute [local irreducible] SentRows

/-- **The sending that K2 runs.** -/
theorem sent_rows {P : _root_.Tw.K2.Par9} {S : Statement} {B : TreeBook} {roots : Nat}
    {settled : Bool} {notices : Array OracleNotice} {rS rL : Fmt.RoundView} {y : _root_.Tw.K2.Sent}
    (h : _root_.Tw.K2.sendByL8 P S B roots settled notices rS rL = .ok y) :
    SentRows S notices rS y.st := by
  unfold _root_.Tw.K2.sendByL8 at h
  split at h
  · rename_i ids took d hd
    cases h
    exact sendOpen_rows hd
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sent_rows
#print axioms VerifiableInference.Desc.First.K2.rowsFor_are
#print axioms VerifiableInference.Desc.First.K2.loop_rows
