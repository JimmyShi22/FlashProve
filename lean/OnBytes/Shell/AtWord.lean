-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtWord.lean: a passing line is printed only where the checks passed.

The program is the value `call C args` (OnBytes/Shell/Call.lean); a run of it is a list of steps
(OnBytes/Shell/Ends.lean). If printing fails, a run can hand a passing line to standard output and
still end with another result, so the theorems here start from the line. A line is one string handed
to the operation that prints a line; it holds no line feed (OnBytes/Shell/AtLine.lean [not in this library]).

Five lines say that a call passed, or a part of one; only `YES` and `WITHIN LIMITS` are a
verification. Four are a call's last line: `YES`, `TEST FILES PASSED`, and the lines that begin with
`WITHIN LIMITS: ` and `PART PASSED: `. No other line begins with Y, W, T or P, except
`PLAN ONLY: no proof was checked`. The fifth is the line for programs, if it begins with
`result-v1 status=0`; it is printed directly before the last line.

Main definitions: `Line.first`, `Cap`, `Pass`, `Result0`, `readEvents`, `saidAll`, `saidLast`.
Main theorems, for all checks C and whether or not printing succeeded.
- `hd_text`: the first character of every line.
- `finish_said`: in a run of `finish`, a line that begins with Y, W, P, N or T is the result's last.
- `said_yes`: `YES` comes only from a whole call, after its eight reads, and `Checks.wholeCall` on
  the call's options and the eight answers is a yes.
- `said_within`: the same for a line that begins with W and a result within limits.
- `said_part`: a line that begins with P, other than the `PLAN ONLY` line, comes from a call, whole
  or on one file alone, whose own check gave the result that a part passed.
- `said_test`: a line that begins with T comes from a call on test files that were accepted.
- `said_result`: `result-v1 status=0` comes only from a whole call with a yes or within limits.

What is not claimed. Nothing about the checks themselves. Nothing about compiled code, Lean's
run-time or the operating system. For proofs only; the program does not import this file.
-/
import OnBytes.Shell.AtCall

namespace OnBytes.Shell

open OnBytes.Model
open OnBytes.Model.Stages (CallEnd StageName Covered Closing)

/-! ## Strings -/

/-- The first character of a string. -/
def hd (s : String) : Option Char := s.toList.head?

/-- The first character of a ++ b is that of a, if a has one. -/
theorem hd_append {a : String} {c : Char} (b : String) (h : hd a = some c) :
    hd (a ++ b) = some c := by
  unfold hd at *
  rw [String.toList_append]
  cases hl : a.toList with
  | nil =>
    rw [hl] at h
    cases h
  | cons x t =>
    rw [hl] at h
    exact h

/-! ## The first character of a line -/

/-- The first character of a chain's name. -/
def ChainIx.initial : ChainIx → Char
  | .keyOneTime => 'k'
  | .keyShared => 'k'
  | .keySecond => 'k'
  | .entry => 'e'
  | .first => 'f'
  | .shared => 's'
  | .second => 's'

/-- The first character of a line's text. -/
def Line.first : Line → Char
  | .commitmentId _ => 'c'
  | .idCompared _ => 'i'
  | .hPar _ => 'h'
  | .keyNotChecked => 'k'
  | .weightHiding => 'w'
  | .covered _ => 'c'
  | .stageWork _ _ => 's'
  | .work _ _ => 'p'
  | .commitment _ _ => 'c'
  | .result _ _ _ _ _ => 'r'
  | .theCall => '-'
  | .callCause _ => 't'
  | .refusedBy _ _ => 'r'
  | .otherId1 => 'i'
  | .otherId2 => 'i'
  | .policyWhy _ => 'p'
  | .note (.bits _) => 't'
  | .note .keyFile => 'n'
  | .note .tableFile => 'n'
  | .planLine c _ => c.initial
  | .noPlan c => c.initial
  | .unreadable _ _ => 'i'
  | .yes => 'Y'
  | .withinLimits _ => 'W'
  | .partPassed _ => 'P'
  | .notVer => 'N'
  | .no _ => 'N'
  | .notChecked _ => 'N'
  | .testPassed => 'T'
  | .planOnly => 'P'

/-- The first character of a chain's name is what `ChainIx.initial` says. -/
theorem hd_chain (c : ChainIx) : hd c.text = some c.initial := by
  cases c <;> decide

/-- Under all lists L, the text of a line x begins with `x.first`. -/
theorem hd_text (L : Lists) (x : Line) : hd (x.text L) = some x.first := by
  cases x with
  | commitmentId o =>
    cases o with
    | none =>
      show hd "commitment ID: not-shown-without-id" = some 'c'
      decide
    | some h => exact hd_append (c := 'c') _ (by decide)
  | idCompared b =>
    cases b with
    | true =>
      show hd "id: named by the caller and equal" = some 'i'
      decide
    | false =>
      show hd "id: not compared: the call named none" = some 'i'
      decide
  | hPar h => exact hd_append (c := 'h') _ (by decide)
  | keyNotChecked => exact hd_append (c := 'k') _ (by decide)
  | weightHiding =>
    show hd "weight hiding: NOT CHECKED BY THIS CALL (it rests on how the commitment was made)" =
      some 'w'
    decide
  | covered a =>
    simp only [Line.text, Line.first]
    repeat (first | decide | apply hd_append)
  | stageWork s w =>
    simp only [Line.text, Line.first]
    repeat (first | decide | apply hd_append)
  | work o least =>
    cases o with
    | none =>
      show hd "proof of work: none counted" = some 'p'
      decide
    | some w =>
      simp only [Line.text, Line.first]
      repeat (first | decide | apply hd_append)
  | commitment n record =>
    simp only [Line.text, Line.first]
    apply hd_append
    split <;> repeat (first | decide | apply hd_append)
  | result st b lf a c =>
    simp only [Line.text, Line.first]
    repeat (first | decide | apply hd_append)
  | theCall =>
    show hd "---- the call ----" = some '-'
    decide
  | callCause c =>
    cases c with
    | idNamed => exact hd_append (c := 't') _ (by decide)
    | noProofOfWork n =>
      simp only [Line.text, CallCause.text, Line.first]
      repeat (first | decide | apply hd_append)
  | refusedBy s o =>
    cases o with
    | none => exact hd_append (c := 'r') _ (by decide)
    | some why =>
      simp only [Line.text, Line.first]
      split <;> repeat (first | decide | apply hd_append)
  | otherId1 =>
    simp only [Line.text, Line.first]
    decide
  | otherId2 => exact hd_append (c := 'i') _ (by decide)
  | policyWhy w => exact hd_append (c := 'p') _ (by decide)
  | note n =>
    cases n with
    | bits k => exact hd_append (c := 't') _ (by decide)
    | keyFile =>
      show hd "not checked in this call: the key file's own proofs" = some 'n'
      decide
    | tableFile =>
      show hd "not checked in this call: the file that names the table" = some 'n'
      decide
  | planLine c h => exact hd_append _ (hd_append _ (hd_chain c))
  | noPlan c => exact hd_append _ (hd_chain c)
  | unreadable role u =>
    simp only [Line.text, Line.first]
    repeat (first | decide | apply hd_append)
  | yes =>
    show hd "YES" = some 'Y'
    decide
  | withinLimits a =>
    simp only [Line.text, Line.first]
    repeat (first | decide | apply hd_append)
  | partPassed s => exact hd_append (c := 'P') _ (by decide)
  | notVer =>
    show hd "NOT-A-VERIFICATION" = some 'N'
    decide
  | no n => exact hd_append (c := 'N') _ (by decide)
  | notChecked n => exact hd_append (c := 'N') _ (by decide)
  | testPassed =>
    show hd "TEST FILES PASSED" = some 'T'
    decide
  | planOnly =>
    show hd "PLAN ONLY: no proof was checked" = some 'P'
    decide

/-- The line that a part passed is not the last line of a planning call. -/
theorem partPassed_ne_planOnly (L : Lists) (s : StageName) :
    (Line.partPassed s).text L ≠ Line.planOnly.text L := by
  cases s with
  | key =>
    show ("PART PASSED: " ++ "key" : String) ≠ "PLAN ONLY: no proof was checked"
    decide
  | leaf =>
    show ("PART PASSED: " ++ "leaf" : String) ≠ "PLAN ONLY: no proof was checked"
    decide
  | request =>
    show ("PART PASSED: " ++ "request" : String) ≠ "PLAN ONLY: no proof was checked"
    decide

/-- The capital letters with which a call's last line can begin. -/
def Cap (c : Char) : Prop := c = 'Y' ∨ c = 'W' ∨ c = 'P' ∨ c = 'N' ∨ c = 'T'

/-- True for the lines that can be a call's last line. -/
def Line.isLast : Line → Bool
  | .unreadable _ _ => true
  | .yes => true
  | .withinLimits _ => true
  | .partPassed _ => true
  | .notVer => true
  | .no _ => true
  | .notChecked _ => true
  | .testPassed => true
  | .planOnly => true
  | _ => false

/-- A line that cannot be a call's last line begins with no letter of `Cap`. -/
theorem middle_not_cap {x : Line} (h : x.isLast = false) : ¬ Cap x.first := by
  have no : ∀ c : Char, c ≠ 'Y' → c ≠ 'W' → c ≠ 'P' → c ≠ 'N' → c ≠ 'T' → ¬ Cap c := by
    intro c h1 h2 h3 h4 h5 hc
    rcases hc with e | e | e | e | e
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 e
    · exact h5 e
  have ch : ∀ c : ChainIx, ¬ Cap c.initial := by
    intro c
    cases c <;> first
      | exact no 'k' (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact no 'e' (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact no 'f' (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact no 's' (by decide) (by decide) (by decide) (by decide) (by decide)
  cases x with
  | commitmentId o => exact no 'c' (by decide) (by decide) (by decide) (by decide) (by decide)
  | idCompared b => exact no 'i' (by decide) (by decide) (by decide) (by decide) (by decide)
  | hPar s => exact no 'h' (by decide) (by decide) (by decide) (by decide) (by decide)
  | keyNotChecked => exact no 'k' (by decide) (by decide) (by decide) (by decide) (by decide)
  | weightHiding => exact no 'w' (by decide) (by decide) (by decide) (by decide) (by decide)
  | covered a => exact no 'c' (by decide) (by decide) (by decide) (by decide) (by decide)
  | stageWork s w => exact no 's' (by decide) (by decide) (by decide) (by decide) (by decide)
  | work o l => exact no 'p' (by decide) (by decide) (by decide) (by decide) (by decide)
  | commitment n record =>
    exact no 'c' (by decide) (by decide) (by decide) (by decide) (by decide)
  | result st b lf a c =>
    exact no 'r' (by decide) (by decide) (by decide) (by decide) (by decide)
  | theCall => exact no '-' (by decide) (by decide) (by decide) (by decide) (by decide)
  | callCause c => exact no 't' (by decide) (by decide) (by decide) (by decide) (by decide)
  | refusedBy s o => exact no 'r' (by decide) (by decide) (by decide) (by decide) (by decide)
  | otherId1 => exact no 'i' (by decide) (by decide) (by decide) (by decide) (by decide)
  | otherId2 => exact no 'i' (by decide) (by decide) (by decide) (by decide) (by decide)
  | policyWhy w => exact no 'p' (by decide) (by decide) (by decide) (by decide) (by decide)
  | note n =>
    cases n with
    | bits k => exact no 't' (by decide) (by decide) (by decide) (by decide) (by decide)
    | keyFile => exact no 'n' (by decide) (by decide) (by decide) (by decide) (by decide)
    | tableFile => exact no 'n' (by decide) (by decide) (by decide) (by decide) (by decide)
  | planLine c s => exact ch c
  | noPlan c => exact ch c
  | unreadable role u => cases h
  | yes => cases h
  | withinLimits a => cases h
  | partPassed s => cases h
  | notVer => cases h
  | no n => cases h
  | notChecked n => cases h
  | testPassed => cases h
  | planOnly => cases h

/-- If the test that a line cannot be last holds of a whole list, it holds of each of its lines. -/
theorem all_middle {xs : List Line} (key : xs.all (fun x => !x.isLast) = true) :
    ∀ x ∈ xs, x.isLast = false := by
  intro x hx
  have h := List.all_eq_true.1 key x hx
  cases hl : x.isLast with
  | false => rfl
  | true =>
    rw [hl] at h
    cases h

/-- No closing line of a call on one file alone before the verdict can be a call's last line. -/
theorem closingPart_middle (why : List CallCause) (leaf : Bool) (c : Closing) :
    ∀ x ∈ closingPart why leaf c, x.isLast = false :=
  all_middle (by cases leaf <;> simp [closingPart, Line.isLast, List.all_append, List.all_map])

/-- No closing line of a whole call before the verdict can be a call's last line. -/
theorem closingWhole_middle (p : Fields) (why : List CallCause) (status : Nat) (a : Covered)
    (c : Closing) : ∀ x ∈ closingWhole p why status a c, x.isLast = false :=
  all_middle (by simp [closingWhole, Line.isLast, List.all_append, List.all_map])

/-- No line before a result's last line can be a call's last line. -/
theorem before_middle (p : Fields) (e : CallEnd) : ∀ x ∈ before p e, x.isLast = false := by
  cases e with
  | yes a c => exact closingWhole_middle _ _ _ _ _
  | withinLimits a c => exact closingWhole_middle _ _ _ _ _
  | partPassed s c => exact closingPart_middle _ _ _
  | notVer cs o c =>
    cases o with
    | none => exact closingPart_middle _ _ _
    | some a => exact closingWhole_middle _ _ _ _ _
  | refusedBy s w n =>
    intro x hx
    cases hx with
    | head => rfl
    | tail _ h =>
      cases h with
      | head => rfl
      | tail _ h2 => cases h2
  | wrongId =>
    intro x hx
    cases hx with
    | head => rfl
    | tail _ h =>
      cases h with
      | head => rfl
      | tail _ h2 => cases h2
  | policy w =>
    intro x hx
    cases hx with
    | head => rfl
    | tail _ h => cases h
  | no n => exact fun _ h => by cases h
  | notChecked n => exact fun _ h => by cases h
  | unreadable role => exact fun _ h => by cases h
  | usage w => exact fun _ h => by cases h

/-- Of the fields of `Fields`, the lines before a result's last line depend only on `bits`, `leaf`
and `leafCall`. -/
theorem before_same {p q : Fields} (hb : p.bits = q.bits) (hl : p.leaf = q.leaf)
    (hc : p.leafCall = q.leafCall) (e : CallEnd) : before p e = before q e := by
  cases e with
  | yes a c => simp only [before, closingWhole, hb, hl]
  | withinLimits a c => simp only [before, closingWhole, hb, hl]
  | notVer cs o c => cases o <;> simp only [before, closingWhole, hb, hl, hc]
  | partPassed s c => rfl
  | refusedBy s w n => rfl
  | wrongId => rfl
  | policy w => rfl
  | no n => rfl
  | notChecked n => rfl
  | unreadable role => rfl
  | usage w => rfl

/-- So `before p e` is the same if all other fields of p are set to their defaults. -/
theorem before_eq (p : Fields) (e : CallEnd) :
    before p e = before { bits := p.bits, leaf := p.leaf, leafCall := p.leafCall } e :=
  before_same rfl rfl rfl e

variable {L : Lists}

/-- A line that begins with a letter of `Cap` is not among lines that cannot be last. -/
theorem not_middle {l : String} {c : Char} (hc : hd l = some c) (hcap : Cap c) (xs : List Line)
    (hx : ∀ x ∈ xs, x.isLast = false) : l ∉ xs.map (Line.text L) := by
  intro hm
  obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hm
  rw [hd_text] at hc
  rw [← Option.some.inj hc] at hcap
  exact middle_not_cap (hx x hxm) hcap

/-! ## Runs in which a line is handed over -/

/-- The words on standard error if the answer cannot be written. -/
def unwrittenWords : String :=
  "verify-on-bytes: the answer could not be written to standard output: take this call as " ++
    "not made"

/-- The last steps of a run that hands over l as its last line: the line, and, if it could not be
written, the words on standard error. -/
def saidLast (l : String) (ok : Bool) : List Event :=
  .say l ok :: (if ok then [] else [.err unwrittenWords])

/-- A fault hands no line over. -/
theorem faultWith_said {w : String} {evs : List Event} {r : Ending} {l : String} {ok : Bool}
    (h : (faultWith w).Ends evs r) (hm : Event.say l ok ∈ evs) : False := by
  obtain ⟨t, rfl, h2⟩ := ends_err h
  obtain ⟨rfl, _⟩ := ends_done h2
  cases hm with
  | tail _ h3 => cases h3

/-- Every run of `unwritten` is its words on standard error, and ends in `.unwritten`. -/
theorem unwritten_ends {evs : List Event} {r : Ending} (h : unwritten.Ends evs r) :
    evs = [.err unwrittenWords] ∧ r = .unwritten := by
  obtain ⟨t, rfl, h2⟩ := ends_err h
  obtain ⟨rfl, rfl⟩ := ends_done h2
  exact ⟨rfl, rfl⟩

/-- A run of `lastSay l0 r0` is `saidLast l0 ok`; it ends with r0 if ok, else in `.unwritten`. -/
theorem lastSay_ends {l0 : String} {r0 r : Ending} {evs : List Event}
    (h : (lastSay l0 r0).Ends evs r) :
    ∃ ok, evs = saidLast l0 ok ∧ r = (if ok then r0 else .unwritten) := by
  obtain ⟨ok, t, rfl, h2⟩ := ends_say h
  cases ok with
  | true =>
    obtain ⟨rfl, rfl⟩ := ends_done h2
    exact ⟨true, rfl, rfl⟩
  | false =>
    obtain ⟨rfl, rfl⟩ := unwritten_ends h2
    exact ⟨false, rfl, rfl⟩

/-- The only line that a run of `lastSay l0 r0` hands over is l0. -/
theorem lastSay_said {l0 l : String} {r0 r : Ending} {evs : List Event} {ok : Bool}
    (h : (lastSay l0 r0).Ends evs r) (hm : Event.say l ok ∈ evs) :
    l = l0 ∧ evs = saidLast l ok ∧ r = (if ok then r0 else .unwritten) := by
  obtain ⟨ok', rfl, rfl⟩ := lastSay_ends h
  cases hm with
  | head => exact ⟨rfl, rfl, rfl⟩
  | tail _ h3 =>
    cases ok' with
    | true => cases h3
    | false =>
      cases h3 with
      | tail _ h4 => cases h4

/-- If a run of `sayAll ls next` hands over a line not in ls, all of ls was printed before it. -/
theorem sayAll_said {next : Ask Ending} {r : Ending} {l : String} {ok : Bool} :
    ∀ (ls : List String) {evs : List Event}, l ∉ ls → (sayAll ls next).Ends evs r →
    Event.say l ok ∈ evs →
    ∃ t, evs = ls.map (fun x => Event.say x true) ++ t ∧ next.Ends t r ∧ Event.say l ok ∈ t
  | [], evs, _, h, hm => ⟨evs, rfl, h, hm⟩
  | x :: ls, evs, hn, h, hm => by
    obtain ⟨ok', t, rfl, h2⟩ := ends_say h
    have hm2 : Event.say l ok ∈ t := by
      cases hm with
      | head => exact absurd List.mem_cons_self hn
      | tail _ h3 => exact h3
    cases ok' with
    | false =>
      obtain ⟨rfl, _⟩ := unwritten_ends h2
      cases hm2 with
      | tail _ h3 => cases h3
    | true =>
      obtain ⟨t', rfl, h3, hm3⟩ :=
        sayAll_said ls (fun hx => hn (List.mem_cons_of_mem _ hx)) h2 hm2
      exact ⟨t', rfl, h3, hm3⟩

/-- The steps in which the lines xs are printed with success. -/
def saidAll (L : Lists) (xs : List Line) : List Event :=
  xs.map fun x => Event.say (x.text L) true

/-- If a run of `finish L p e` hands over a line that begins with a letter of `Cap`, the line is the
last line of the result e, and the run is e's lines in their order. -/
theorem finish_said {p : Fields} {e : CallEnd} {evs : List Event} {r : Ending} {l : String}
    {ok : Bool} {c : Char} (hc : hd l = some c) (hcap : Cap c)
    (h : (finish L p e).Ends evs r) (hm : Event.say l ok ∈ evs) :
    l = (verdict p e).text L ∧ evs = saidAll L (before p e) ++ saidLast l ok ∧
      r = (if ok then .ended e else .unwritten) := by
  have step : (sayAll ((before p e).map (Line.text L))
      (lastSay ((verdict p e).text L) (.ended e))).Ends evs r →
      l = (verdict p e).text L ∧ evs = saidAll L (before p e) ++ saidLast l ok ∧
        r = (if ok then .ended e else .unwritten) := by
    intro hs
    obtain ⟨t, rfl, h2, m2⟩ := sayAll_said _ (not_middle hc hcap _ (before_middle p e)) hs hm
    obtain ⟨e1, rfl, e3⟩ := lastSay_said h2 m2
    refine ⟨e1, ?_, e3⟩
    unfold saidAll
    rw [List.map_map]
    rfl
  cases e with
  | usage w => exact (faultWith_said h hm).elim
  | yes a c => exact step h
  | withinLimits a c => exact step h
  | partPassed s c => exact step h
  | notVer cs o c => exact step h
  | refusedBy s w n => exact step h
  | wrongId => exact step h
  | policy w => exact step h
  | no n => exact step h
  | notChecked n => exact step h
  | unreadable role => exact step h

/-- The first letters of the four passing last lines. `PLAN ONLY` begins with P too. -/
def Pass (c : Char) : Prop := c = 'Y' ∨ c = 'W' ∨ c = 'P' ∨ c = 'T'

/-- A letter of `Pass` is a letter of `Cap`. -/
theorem Pass.cap {c : Char} (h : Pass c) : Cap c := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- A letter of `Pass` is not N. -/
theorem Pass.notN {c : Char} (h : Pass c) : c ≠ 'N' := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- If a run of `fetch` hands over a line that begins with a passing letter, the call did not end at
the test of the length: the run is the read and then a run of `next`, which hands over the line.
That the answer was short is not stated here: see `pass_sizes` (OnBytes/Shell/AtSize.lean). -/
theorem fetch_said {m : Nat} {p : String} {next : FileRead → Ask Ending} {evs : List Event}
    {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (fetch L m p next).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ got t, evs = .read p (m + 1) got :: t ∧ (next got).Ends t r ∧
      Event.say l ok ∈ t := by
  obtain ⟨got, t, rfl, h2⟩ := ends_read h
  have hm2 : Event.say l ok ∈ t := by
    cases hm with
    | tail _ h3 => exact h3
  refine ⟨got, t, rfl, ?_, hm2⟩
  cases got with
  | bytes b =>
    have h3 : (if b.size ≤ m then next (.bytes b)
      else finish L {} (.no "file-too-long")).Ends t r := h2
    split at h3
    · exact h3
    · exfalso
      have e1 := (finish_said hc hp.cap h3 hm2).1
      rw [e1, hd_text] at hc
      exact hp.notN (Option.some.inj hc).symm
  | absent => exact h2
  | unreadable u => exact h2

/-- As `fetch_said`, for `need`: the read gave bytes. -/
theorem need_said {p : String} {next : ByteArray → Ask Ending} {evs : List Event} {r : Ending}
    {l : String} {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (need L p next).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ b t, evs = .read p (listLimit + 1) (.bytes b) :: t ∧ (next b).Ends t r ∧
      Event.say l ok ∈ t := by
  obtain ⟨got, t, rfl, h2, hm2⟩ := fetch_said hc hp h hm
  cases got with
  | bytes b => exact ⟨b, t, rfl, h2, hm2⟩
  | absent => exact (faultWith_said h2 hm2).elim
  | unreadable u => exact (faultWith_said h2 hm2).elim

/-- The reads of the paths ps with the answers bs. -/
def readEvents : List String → List ByteArray → List Event
  | p :: ps, b :: bs => .read p (listLimit + 1) (.bytes b) :: readEvents ps bs
  | _, _ => []

/-- As `fetch_said`, for `needAll`: every read gave bytes. -/
theorem needAll_said {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c)
    (hp : Pass c) : ∀ (ps : List String) (got : List ByteArray)
      (next : List ByteArray → Ask Ending) {evs : List Event},
    (needAll L ps got next).Ends evs r → Event.say l ok ∈ evs →
    ∃ bs t, bs.length = ps.length ∧ evs = readEvents ps bs ++ t ∧
      (next (got ++ bs)).Ends t r ∧ Event.say l ok ∈ t
  | [], got, next, evs, h, hm => ⟨[], evs, rfl, rfl, by rw [List.append_nil]; exact h, hm⟩
  | p :: ps, got, next, evs, h, hm => by
    obtain ⟨b, t, rfl, h2, hm2⟩ := need_said hc hp h hm
    obtain ⟨bs, t', hlen, rfl, h3, hm3⟩ := needAll_said hc hp ps (got ++ [b]) next h2 hm2
    refine ⟨b :: bs, t', by rw [List.length_cons, List.length_cons, hlen], rfl, ?_, hm3⟩
    rw [List.append_assoc] at h3
    exact h3

/-! ## Results and their last lines -/

/-- True for the three results whose last line is a passing line. -/
def passes : CallEnd → Bool
  | .yes _ _ => true
  | .withinLimits _ _ => true
  | .partPassed _ _ => true
  | _ => false

/-- A result whose last line begins with a passing letter passes, and the letter is not T. -/
theorem verdict_pass {p : Fields} {e : CallEnd} {c : Char} (hp : Pass c)
    (h : (verdict p e).first = c) : passes e = true ∧ c ≠ 'T' := by
  have nN : ¬ Pass 'N' := by
    intro k
    exact k.notN rfl
  have ni : ¬ Pass 'i' := by
    intro k
    rcases k with k | k | k | k <;> exact absurd k (by decide)
  have hY : ('Y' : Char) ≠ 'T' := by decide
  have hW : ('W' : Char) ≠ 'T' := by decide
  have hP : ('P' : Char) ≠ 'T' := by decide
  subst h
  cases e with
  | yes a cl => exact ⟨rfl, hY⟩
  | withinLimits a cl => exact ⟨rfl, hW⟩
  | partPassed s cl => exact ⟨rfl, hP⟩
  | notVer cs o cl => exact absurd hp nN
  | refusedBy s w n => exact absurd hp nN
  | wrongId => exact absurd hp nN
  | policy w => exact absurd hp nN
  | no n => exact absurd hp nN
  | notChecked n => exact absurd hp nN
  | unreadable role => exact absurd hp ni
  | usage w => exact absurd hp nN

/-- The last line of a passing result does not depend on the call's `Fields`. -/
theorem verdict_same {e : CallEnd} (h : passes e = true) (p q : Fields) :
    verdict p e = verdict q e := by
  cases e <;> first | rfl | cases h

/-- An early end does not pass. -/
theorem earlyEnd_passes (e : CallEnd) : passes (earlyEnd e) = false := by
  cases e <;> rfl

/-- If the result of a call on one file alone passes, it is what the checks gave, and it says that
a part passed. -/
theorem partEnd_pass {x : CallEnd} (h : passes (partEnd x) = true) :
    ∃ s c, x = .partPassed s c := by
  cases x with
  | partPassed s c => exact ⟨s, c, rfl⟩
  | yes a c => cases h
  | withinLimits a c => cases h
  | notVer cs o c => cases h
  | refusedBy s w n => cases h
  | wrongId => cases h
  | policy w => cases h
  | no n => cases h
  | notChecked n => cases h
  | unreadable role => cases h
  | usage w => cases h

/-- If a run of `finish L p e` hands over a line that begins with a passing letter, e passes, the
line is e's last line, and the run is e's lines in their order. -/
theorem finish_pass {p : Fields} {e : CallEnd} {evs : List Event} {r : Ending} {l : String}
    {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (finish L p e).Ends evs r) (hm : Event.say l ok ∈ evs) :
    passes e = true ∧ c ≠ 'T' ∧ l = (verdict {} e).text L ∧
      evs = saidAll L (before p e) ++ saidLast l ok ∧
      r = (if ok then .ended e else .unwritten) := by
  obtain ⟨e1, e2, e3⟩ := finish_said hc hp.cap h hm
  have hf : (verdict p e).first = c := by
    rw [e1, hd_text] at hc
    exact Option.some.inj hc
  obtain ⟨k1, k2⟩ := verdict_pass hp hf
  exact ⟨k1, k2, by rw [e1, verdict_same k1 p {}], e2, e3⟩

/-! ## The whole call and the calls on one file alone -/

/-- The files of a whole call except the entry, from the answers of the first seven reads. -/
def filesOf (pol kl lay key req yy prf : FileRead) : Verify.Files :=
  { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn key,
    request := fileIn req, y := fileIn yy, proof := fileIn prf }

/-- The files of a call on a key file alone, from the answers of its four reads. -/
def keyFiles (pol kl lay kb : FileRead) : Verify.Files :=
  { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn kb,
    request := none, y := none, proof := none }

/-- The files of a call on an entry file alone, from the answers of its five reads. -/
def leafFiles (pol kl lay kb ent : FileRead) : Verify.Files :=
  { policy := fileIn pol, KL := fileIn kl, layout := layoutIn lay, key := fileIn kb,
    request := none, y := none, proof := none, entry := fileIn ent }

/-- If a run of a whole call hands over a line that begins with a passing letter, the run is eight
reads and the lines of a passing result e, the line is e's last, and `Checks.wholeCall` on the eight
answers is e. -/
theorem whole_word {C : Checks} {config ivk request y proof : String} {a : Asked}
    {evs : List Event} {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c)
    (hp : Pass c) (h : (whole C config ivk request y proof a).Ends evs r)
    (hm : Event.say l ok ∈ evs) :
    ∃ (pol kl lay key req yy prf ent : FileRead) (k : Nat) (e : CallEnd),
      C.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      C.wholeCall a.options { filesOf pol kl lay key req yy prf with entry := fileIn ent } = e ∧
      passes e = true ∧ l = (verdict {} e).text C.lists ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay,
        .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
        .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
        .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
        (saidAll C.lists (before { bits := a.options.bits, leaf := k } e) ++ saidLast l ok) ∧
      r = (if ok then .ended e else .unwritten) := by
  obtain ⟨pol, t1, rfl, h1, m1⟩ := fetch_said hc hp h hm
  obtain ⟨kl, t2, rfl, h2, m2⟩ := fetch_said hc hp h1 m1
  obtain ⟨lay, t3, rfl, h3, m3⟩ := fetch_said hc hp h2 m2
  obtain ⟨key, t4, rfl, h4, m4⟩ := fetch_said hc hp h3 m3
  obtain ⟨req, t5, rfl, h5, m5⟩ := fetch_said hc hp h4 m4
  obtain ⟨yy, t6, rfl, h6, m6⟩ := fetch_said hc hp h5 m5
  obtain ⟨prf, t7, rfl, h7, m7⟩ := fetch_said hc hp h6 m6
  dsimp only at h7
  cases hk : C.entryNumber a.options (filesOf pol kl lay key req yy prf) with
  | error e0 =>
    unfold filesOf at hk
    rw [hk] at h7
    have h8 := (finish_pass hc hp h7 m7).1
    rw [earlyEnd_passes] at h8
    cases h8
  | ok k =>
    unfold filesOf at hk
    rw [hk] at h7
    obtain ⟨ent, t8, rfl, h8, m8⟩ := fetch_said hc hp h7 m7
    obtain ⟨k1, _, k3, k4, k5⟩ := finish_pass hc hp h8 m8
    rw [before_eq] at k4
    rw [k4]
    exact ⟨pol, kl, lay, key, req, yy, prf, ent, k, _, hk, rfl, k1, k3, rfl, k5⟩

/-- As `whole_word`, for the call on a key file alone. The result is that a part passed. -/
theorem keyPart_word {C : Checks} {config key : String} {a : Asked} {evs : List Event}
    {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (keyPart C config key a).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ (pol kl lay kb : FileRead) (s : StageName) (cl : Closing),
      C.keyCall a.options (keyFiles pol kl lay kb) = .partPassed s cl ∧
      l = (Line.partPassed s).text C.lists ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay, .read key (fileLimit + 1) kb] ++
        (saidAll C.lists (before {} (.partPassed s cl)) ++ saidLast l ok) ∧
      r = (if ok then .ended (.partPassed s cl) else .unwritten) := by
  obtain ⟨pol, t1, rfl, h1, m1⟩ := fetch_said hc hp h hm
  obtain ⟨kl, t2, rfl, h2, m2⟩ := fetch_said hc hp h1 m1
  obtain ⟨lay, t3, rfl, h3, m3⟩ := fetch_said hc hp h2 m2
  obtain ⟨kb, t4, rfl, h4, m4⟩ := fetch_said hc hp h3 m3
  obtain ⟨k1, _, k3, k4, k5⟩ := finish_pass hc hp h4 m4
  obtain ⟨s, cl, hx⟩ := partEnd_pass k1
  have hx2 : C.keyCall a.options (keyFiles pol kl lay kb) = .partPassed s cl := hx
  unfold keyFiles at hx2
  rw [hx2] at k3 k4 k5
  exact ⟨pol, kl, lay, kb, s, cl, hx, k3, by rw [k4]; rfl, k5⟩

/-- As `whole_word`, for the call on an entry file alone. The result is that a part passed. -/
theorem leafPart_word {C : Checks} {config key entry : String} {a : Asked} {evs : List Event}
    {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (leafPart C config key entry a).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ (pol kl lay kb ent : FileRead) (s : StageName) (cl : Closing),
      C.leafCall a.options (leafFiles pol kl lay kb ent) = .partPassed s cl ∧
      l = (Line.partPassed s).text C.lists ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay, .read key (fileLimit + 1) kb,
        .read entry (fileLimit + 1) ent] ++
        (saidAll C.lists (before {} (.partPassed s cl)) ++ saidLast l ok) ∧
      r = (if ok then .ended (.partPassed s cl) else .unwritten) := by
  obtain ⟨pol, t1, rfl, h1, m1⟩ := fetch_said hc hp h hm
  obtain ⟨kl, t2, rfl, h2, m2⟩ := fetch_said hc hp h1 m1
  obtain ⟨lay, t3, rfl, h3, m3⟩ := fetch_said hc hp h2 m2
  obtain ⟨kb, t4, rfl, h4, m4⟩ := fetch_said hc hp h3 m3
  obtain ⟨ent, t5, rfl, h5, m5⟩ := fetch_said hc hp h4 m4
  obtain ⟨k1, _, k3, k4, k5⟩ := finish_pass hc hp h5 m5
  obtain ⟨s, cl, hx⟩ := partEnd_pass k1
  have hx2 : C.leafCall a.options (leafFiles pol kl lay kb ent) = .partPassed s cl := hx
  unfold leafFiles at hx2
  rw [hx2] at k3 k4 k5
  exact ⟨pol, kl, lay, kb, ent, s, cl, hx, k3, by rw [k4]; rfl, k5⟩

/-! ## The calls on test files and the planning call -/

/-- If a run of a call on test files hands over a line that begins with a passing letter, the line
is `TEST FILES PASSED`; the run has read the call's paths in their order; the verdict on the bytes
read is `accepted`; and the notes and the line on proof of work are printed before the line. -/
theorem toy_word {C : Checks} {paths : List String} {notes : List Note}
    {v : List ByteArray → Option Verdict} {w : List ByteArray → Work}
    {evs : List Event} {r : Ending} {l : String} {ok : Bool} {c : Char} (hc : hd l = some c)
    (hp : Pass c) (h : ((Kind.toy paths notes v w).run C).Ends evs r)
    (hm : Event.say l ok ∈ evs) :
    ∃ bs o least, bs.length = paths.length ∧ v bs = some .accepted ∧ w bs = .ok (o, least) ∧
      l = Line.testPassed.text C.lists ∧
      evs = readEvents paths bs ++
        (saidAll C.lists (notes.map Line.note ++ [.work o least]) ++ saidLast l ok) ∧
      r = (if ok then .testPassed else .unwritten) := by
  obtain ⟨bs, t, hlen, rfl, k2, m2⟩ := needAll_said hc hp paths [] _ h hm
  rw [List.nil_append] at k2
  have k3 : (match v bs with
    | some x => sayAll (notes.map fun n => (Line.note n).text C.lists)
        (finishTest C.lists (w bs) x)
    | none => faultWith "verify-on-bytes: internal fault").Ends t r := k2
  cases hv : v bs with
  | none =>
    rw [hv] at k3
    exact (faultWith_said k3 m2).elim
  | some x =>
    rw [hv] at k3
    have hn : l ∉ notes.map fun n => (Line.note n).text C.lists := by
      have h0 := not_middle (L := C.lists) hc hp.cap (notes.map Line.note) (by
        intro y hy
        obtain ⟨n, _, rfl⟩ := List.mem_map.1 hy
        rfl)
      rw [List.map_map] at h0
      exact h0
    obtain ⟨t', rfl, k4, m4⟩ := sayAll_said _ hn k3 m2
    cases x with
    | refused q =>
      have k5 : (finish C.lists {} (.no q.check)).Ends t' r := k4
      have k6 := (finish_pass hc hp k5 m4).1
      cases k6
    | accepted =>
      have k5 : (finishWork C.lists (w bs)).Ends t' r := k4
      cases hw : w bs with
      | error name =>
        rw [hw] at k5
        have k6 := (finish_pass hc hp (e := .no name) k5 m4).1
        cases k6
      | ok ow =>
        rw [hw] at k5
        obtain ⟨o, least⟩ := ow
        have hn2 : l ∉ [(Line.work o least).text C.lists] :=
          not_middle (L := C.lists) hc hp.cap [.work o least] (by
            intro y hy
            cases hy with
            | head => rfl
            | tail _ h6 => cases h6)
        obtain ⟨t5, rfl, k6, m6⟩ := sayAll_said _ hn2 k5 m4
        obtain ⟨e1, rfl, e3⟩ := lastSay_said k6 m6
        refine ⟨bs, o, least, hlen, hv, hw, e1, ?_, e3⟩
        unfold saidAll
        rw [List.map_append, List.map_map, List.map_map, List.append_assoc]
        rfl

/-- If a run of a planning call hands over a line that begins with a passing letter, the line is the
last line of a planning call. -/
theorem plan_word {C : Checks} {config : String} {bits : Nat} {evs : List Event} {r : Ending}
    {l : String} {ok : Bool} {c : Char} (hc : hd l = some c) (hp : Pass c)
    (h : (planCall C config bits).Ends evs r) (hm : Event.say l ok ∈ evs) :
    l = Line.planOnly.text C.lists := by
  obtain ⟨pol, _, rfl, h1, m1⟩ := fetch_said hc hp h hm
  obtain ⟨kl, _, rfl, h2, m2⟩ := fetch_said hc hp h1 m1
  obtain ⟨lay, _, rfl, h3, m3⟩ := fetch_said hc hp h2 m2
  cases hq : C.plan bits (fileIn pol) (fileIn kl) (layoutIn lay) with
  | error e0 =>
    rw [hq] at h3
    have h8 := (finish_pass hc hp h3 m3).1
    rw [earlyEnd_passes] at h8
    cases h8
  | ok x =>
    rw [hq] at h3
    have hn : l ∉ (planLines x).map (Line.text C.lists) :=
      not_middle hc hp.cap _ (by
        intro y hy
        obtain ⟨ch, _, rfl⟩ := List.mem_map.1 hy
        split <;> rfl)
    obtain ⟨t, rfl, h4, m4⟩ := sayAll_said _ hn h3 m3
    exact (lastSay_said h4 m4).1

/-! ## The program -/

/-- The word `YES`. If a run of the program hands the line `YES` to standard output, whether or not
that succeeds, the call is a whole call, the run is its eight reads and the lines of a yes, and
`Checks.wholeCall` on the call's options and the answers of the eight reads is that yes. -/
theorem said_yes {C : Checks} {args : List String} {evs : List Event} {r : Ending} {ok : Bool}
    (h : (call C args).Ends evs r) (hm : Event.say "YES" ok ∈ evs) :
    ∃ (config ivk request y proof : String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (about : Covered) (cl : Closing),
      kindOf args = .whole config ivk request y proof a ∧
      C.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      C.wholeCall a.options
        { filesOf pol kl lay key req yy prf with entry := fileIn ent } = .yes about cl ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay,
        .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
        .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
        .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
        (saidAll C.lists (before { bits := a.options.bits, leaf := k } (.yes about cl)) ++
          saidLast "YES" ok) ∧
      r = (if ok then .ended (.yes about cl) else .unwritten) := by
  have hc : hd "YES" = some 'Y' := by decide
  have hp : Pass 'Y' := Or.inl rfl
  have nP : ∀ (x : Line) (d : Char), x.first = d → d ≠ 'Y' → "YES" ≠ x.text C.lists := by
    intro x d hd0 hx e
    rw [e, hd_text, hd0] at hc
    exact hx (Option.some.inj hc)
  unfold call at h
  cases hk : kindOf args with
  | toy paths notes v w =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := toy_word hc hp h hm
    exact absurd e1 (nP _ 'T' rfl (by decide))
  | whole config ivk request y proof a =>
    rw [hk] at h
    obtain ⟨pol, kl, lay, key, req, yy, prf, ent, k, e, e1, e2, e3, e4, e5, e6⟩ :=
      whole_word hc hp h hm
    cases e with
    | yes about cl =>
      exact ⟨_, _, _, _, _, _, pol, kl, lay, key, req, yy, prf, ent, k, about, cl, rfl, e1, e2, e5,
        e6⟩
    | withinLimits about cl => exact absurd e4 (nP _ 'W' rfl (by decide))
    | partPassed s cl => exact absurd e4 (nP _ 'P' rfl (by decide))
    | notVer cs o cl => cases e3
    | refusedBy s w n => cases e3
    | wrongId => cases e3
    | policy w => cases e3
    | no n => cases e3
    | notChecked n => cases e3
    | unreadable role => cases e3
    | usage w => cases e3
  | keyPart config key a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, s, _, _, e1, _, _⟩ := keyPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | leafPart config key entry a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, s, _, _, e1, _, _⟩ := leafPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | plan config bits =>
    rw [hk] at h
    exact absurd (plan_word hc hp h hm) (nP _ 'P' rfl (by decide))
  | bad words =>
    rw [hk] at h
    exact (faultWith_said h hm).elim

/-- The words `WITHIN LIMITS`. If a run of the program hands over a line that begins with W, whether
or not that succeeds, the call is a whole call, the run is its eight reads and the lines of a result
within limits, the line is the last of them, and `Checks.wholeCall` on the call's options and the
answers of the eight reads is that result. -/
theorem said_within {C : Checks} {args : List String} {evs : List Event} {r : Ending} {ok : Bool}
    {l : String} (hc : hd l = some 'W') (h : (call C args).Ends evs r)
    (hm : Event.say l ok ∈ evs) :
    ∃ (config ivk request y proof : String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (about : Covered) (cl : Closing),
      kindOf args = .whole config ivk request y proof a ∧
      C.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      C.wholeCall a.options
        { filesOf pol kl lay key req yy prf with entry := fileIn ent } = .withinLimits about cl ∧
      l = (Line.withinLimits about).text C.lists ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay,
        .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
        .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
        .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
        (saidAll C.lists (before { bits := a.options.bits, leaf := k } (.withinLimits about cl)) ++
          saidLast l ok) ∧
      r = (if ok then .ended (.withinLimits about cl) else .unwritten) := by
  have hp : Pass 'W' := Or.inr (Or.inl rfl)
  have nP : ∀ (x : Line) (d : Char), x.first = d → d ≠ 'W' → l ≠ x.text C.lists := by
    intro x d hd0 hx e
    rw [e, hd_text, hd0] at hc
    exact hx (Option.some.inj hc)
  unfold call at h
  cases hk : kindOf args with
  | toy paths notes v w =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := toy_word hc hp h hm
    exact absurd e1 (nP _ 'T' rfl (by decide))
  | whole config ivk request y proof a =>
    rw [hk] at h
    obtain ⟨pol, kl, lay, key, req, yy, prf, ent, k, e, e1, e2, e3, e4, e5, e6⟩ :=
      whole_word hc hp h hm
    cases e with
    | yes about cl => exact absurd e4 (nP _ 'Y' rfl (by decide))
    | withinLimits about cl =>
      exact ⟨_, _, _, _, _, _, pol, kl, lay, key, req, yy, prf, ent, k, about, cl, rfl, e1, e2, e4,
        e5, e6⟩
    | partPassed s cl => exact absurd e4 (nP _ 'P' rfl (by decide))
    | notVer cs o cl => cases e3
    | refusedBy s w n => cases e3
    | wrongId => cases e3
    | policy w => cases e3
    | no n => cases e3
    | notChecked n => cases e3
    | unreadable role => cases e3
    | usage w => cases e3
  | keyPart config key a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, s, _, _, e1, _, _⟩ := keyPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | leafPart config key entry a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, s, _, _, e1, _, _⟩ := leafPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | plan config bits =>
    rw [hk] at h
    exact absurd (plan_word hc hp h hm) (nP _ 'P' rfl (by decide))
  | bad words =>
    rw [hk] at h
    exact (faultWith_said h hm).elim

/-- The words `TEST FILES PASSED`. If a run of the program hands over a line that begins with T,
whether or not that succeeds, the call is a call on test files, the line is `TEST FILES PASSED`, the
run has read the call's paths in their order, the verdict on the bytes read is `accepted`, and the
line on proof of work is printed directly before the line. -/
theorem said_test {C : Checks} {args : List String} {evs : List Event} {r : Ending} {ok : Bool}
    {l : String} (hc : hd l = some 'T') (h : (call C args).Ends evs r)
    (hm : Event.say l ok ∈ evs) :
    ∃ paths notes v w bs o least, kindOf args = .toy paths notes v w ∧
      bs.length = paths.length ∧ v bs = some .accepted ∧ w bs = .ok (o, least) ∧
      l = Line.testPassed.text C.lists ∧
      evs = readEvents paths bs ++
        (saidAll C.lists (notes.map Line.note ++ [.work o least]) ++ saidLast l ok) ∧
      r = (if ok then .testPassed else .unwritten) := by
  have hp : Pass 'T' := Or.inr (Or.inr (Or.inr rfl))
  have nP : ∀ (x : Line) (d : Char), x.first = d → d ≠ 'T' → l ≠ x.text C.lists := by
    intro x d hd0 hx e
    rw [e, hd_text, hd0] at hc
    exact hx (Option.some.inj hc)
  unfold call at h
  cases hk : kindOf args with
  | toy paths notes v w =>
    rw [hk] at h
    obtain ⟨bs, o, least, e1, e2, e3, e4, e5, e6⟩ := toy_word hc hp h hm
    exact ⟨_, _, _, _, bs, o, least, rfl, e1, e2, e3, e4, e5, e6⟩
  | whole config ivk request y proof a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, e, _, _, e3, e4, _, _⟩ := whole_word hc hp h hm
    cases e with
    | yes about cl => exact absurd e4 (nP _ 'Y' rfl (by decide))
    | withinLimits about cl => exact absurd e4 (nP _ 'W' rfl (by decide))
    | partPassed s cl => exact absurd e4 (nP _ 'P' rfl (by decide))
    | notVer cs o cl => cases e3
    | refusedBy s w n => cases e3
    | wrongId => cases e3
    | policy w => cases e3
    | no n => cases e3
    | notChecked n => cases e3
    | unreadable role => cases e3
    | usage w => cases e3
  | keyPart config key a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, s, _, _, e1, _, _⟩ := keyPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | leafPart config key entry a =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, s, _, _, e1, _, _⟩ := leafPart_word hc hp h hm
    exact absurd e1 (nP _ 'P' rfl (by decide))
  | plan config bits =>
    rw [hk] at h
    exact absurd (plan_word hc hp h hm) (nP _ 'P' rfl (by decide))
  | bad words =>
    rw [hk] at h
    exact (faultWith_said h hm).elim

/-- The words `PART PASSED`. If a run of the program hands over a line that begins with P and is not
the last line of a planning call, whether or not that succeeds, then the check of the call, which is
whole or on one file alone, gave on the answers of the run's reads the result that a part passed,
and the line is that result's last line. -/
theorem said_part {C : Checks} {args : List String} {evs : List Event} {r : Ending} {ok : Bool}
    {l : String} (hc : hd l = some 'P') (hl : l ≠ Line.planOnly.text C.lists)
    (h : (call C args).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ (s : StageName) (cl : Closing), l = (Line.partPassed s).text C.lists ∧
      r = (if ok then .ended (.partPassed s cl) else .unwritten) ∧
      ((∃ (config ivk request y proof : String) (a : Asked)
          (pol kl lay key req yy prf ent : FileRead) (k : Nat),
          kindOf args = .whole config ivk request y proof a ∧
          C.wholeCall a.options
            { filesOf pol kl lay key req yy prf with entry := fileIn ent } = .partPassed s cl ∧
          evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
            .read (config ++ "/KL.bin") (fileLimit + 1) kl,
            .read (config ++ "/layout.txt") (textLimit + 1) lay,
            .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
            .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
            .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++
            (saidAll C.lists (before {} (.partPassed s cl)) ++ saidLast l ok)) ∨
      (∃ (config key : String) (a : Asked) (pol kl lay kb : FileRead),
          kindOf args = .keyPart config key a ∧
          C.keyCall a.options (keyFiles pol kl lay kb) = .partPassed s cl ∧
          evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
            .read (config ++ "/KL.bin") (fileLimit + 1) kl,
            .read (config ++ "/layout.txt") (textLimit + 1) lay,
            .read key (fileLimit + 1) kb] ++
            (saidAll C.lists (before {} (.partPassed s cl)) ++ saidLast l ok)) ∨
      (∃ (config key entry : String) (a : Asked) (pol kl lay kb ent : FileRead),
          kindOf args = .leafPart config key entry a ∧
          C.leafCall a.options (leafFiles pol kl lay kb ent) = .partPassed s cl ∧
          evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
            .read (config ++ "/KL.bin") (fileLimit + 1) kl,
            .read (config ++ "/layout.txt") (textLimit + 1) lay, .read key (fileLimit + 1) kb,
            .read entry (fileLimit + 1) ent] ++
            (saidAll C.lists (before {} (.partPassed s cl)) ++ saidLast l ok))) := by
  have hp : Pass 'P' := Or.inr (Or.inr (Or.inl rfl))
  have nP : ∀ (x : Line) (d : Char), x.first = d → d ≠ 'P' → l ≠ x.text C.lists := by
    intro x d hd0 hx e
    rw [e, hd_text, hd0] at hc
    exact hx (Option.some.inj hc)
  unfold call at h
  cases hk : kindOf args with
  | toy paths notes v w =>
    rw [hk] at h
    obtain ⟨_, _, _, _, _, _, e1, _, _⟩ := toy_word hc hp h hm
    exact absurd e1 (nP _ 'T' rfl (by decide))
  | whole config ivk request y proof a =>
    rw [hk] at h
    obtain ⟨pol, kl, lay, key, req, yy, prf, ent, k, e, _, e2, e3, e4, e5, e6⟩ :=
      whole_word hc hp h hm
    cases e with
    | yes about cl => exact absurd e4 (nP _ 'Y' rfl (by decide))
    | withinLimits about cl => exact absurd e4 (nP _ 'W' rfl (by decide))
    | partPassed s cl =>
      exact ⟨s, cl, e4, e6, Or.inl
        ⟨_, _, _, _, _, _, pol, kl, lay, key, req, yy, prf, ent, k, rfl, e2, e5⟩⟩
    | notVer cs o cl => cases e3
    | refusedBy s w n => cases e3
    | wrongId => cases e3
    | policy w => cases e3
    | no n => cases e3
    | notChecked n => cases e3
    | unreadable role => cases e3
    | usage w => cases e3
  | keyPart config key a =>
    rw [hk] at h
    obtain ⟨pol, kl, lay, kb, s, cl, e1, e2, e3, e4⟩ := keyPart_word hc hp h hm
    exact ⟨s, cl, e2, e4, Or.inr (Or.inl ⟨_, _, _, pol, kl, lay, kb, rfl, e1, e3⟩)⟩
  | leafPart config key entry a =>
    rw [hk] at h
    obtain ⟨pol, kl, lay, kb, ent, s, cl, e1, e2, e3, e4⟩ := leafPart_word hc hp h hm
    exact ⟨s, cl, e2, e4, Or.inr (Or.inr ⟨_, _, _, _, pol, kl, lay, kb, ent, rfl, e1, e3⟩)⟩
  | plan config bits =>
    rw [hk] at h
    exact absurd (plan_word hc hp h hm) hl
  | bad words =>
    rw [hk] at h
    exact (faultWith_said h hm).elim

/-! ## The line for programs -/

/-- The character of a string at a place, counted from 0. -/
def charAt (s : String) (i : Nat) : Option Char := s.toList[i]?

/-- A character of a is at the same place in a ++ b. -/
theorem charAt_append {a : String} {c : Char} {i : Nat} (b : String) (h : charAt a i = some c) :
    charAt (a ++ b) i = some c := by
  unfold charAt at *
  rw [String.toList_append, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-- The line begins with `result-v1 status=0`, as far as it takes to tell it from every other line
of the program: its first character is r, its third is s, and its eighteenth is 0. -/
def Result0 (l : String) : Prop :=
  hd l = some 'r' ∧ charAt l 2 = some 's' ∧ charAt l 17 = some '0'

/-- The line for programs with the exit code 0 satisfies `Result0`. -/
theorem result0_text (bits leaf : Nat) (a : Covered) (c : Closing) :
    Result0 ((Line.result 0 bits leaf a c).text L) := by
  refine ⟨hd_text _ _, ?_, ?_⟩
  · simp only [Line.text]
    repeat (first | decide | apply charAt_append)
  · simp only [Line.text]
    repeat (first | decide | apply charAt_append)

/-- True for a yes and for a result within limits. -/
def wholePass : CallEnd → Bool
  | .yes _ _ => true
  | .withinLimits _ _ => true
  | _ => false

/-- False only for a line for programs with the wrong exit code. The right one is 0 if `pass`, else
14. -/
def fits (pass : Bool) : Line → Bool
  | .result st _ _ _ _ => if pass then st == 0 else st == 14
  | _ => true

/-- In the lines of a result the line for programs has the exit code 0 if the result is a yes or
within limits, and 14 if not. -/
theorem lines_fit (p : Fields) (e : CallEnd) :
    ∀ x ∈ before p e ++ [verdict p e], fits (wholePass e) x = true := by
  have key : (before p e ++ [verdict p e]).all (fits (wholePass e)) = true := by
    cases e with
    | yes a c =>
      simp [before, closingWhole, verdict, fits, wholePass, List.all_append, List.all_map]
    | withinLimits a c =>
      simp [before, closingWhole, verdict, fits, wholePass, List.all_append, List.all_map]
    | partPassed s c =>
      cases hs : (s == StageName.leaf) <;>
        simp [before, closingPart, verdict, fits, hs, List.all_append, List.all_map]
    | notVer cs o c =>
      cases o <;>
        simp [before, closingWhole, closingPart, verdict, fits, wholePass, List.all_append,
          List.all_map]
    | refusedBy s w n => rfl
    | wrongId => rfl
    | policy w => rfl
    | no n => rfl
    | notChecked n => rfl
    | unreadable role => rfl
    | usage w => rfl
  exact fun x hx => List.all_eq_true.1 key x hx

/-- If a line of a result satisfies `Result0`, the result is a yes or within limits. -/
theorem result0_pass {p : Fields} {e : CallEnd} {x : Line} (hx : x ∈ before p e ++ [verdict p e])
    (h : Result0 (x.text L)) : wholePass e = true := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hd_text] at h1
  have hf := lines_fit p e x hx
  have no : ∀ c : Char, x.first = c → c ≠ 'r' → False := fun c hc hn =>
    hn (by rw [← hc]; exact Option.some.inj h1)
  cases x with
  | result st b lf a c =>
    cases hw : wholePass e with
    | true => rfl
    | false =>
      rw [hw] at hf
      have hst : st = 14 := eq_of_beq hf
      subst hst
      have h4 : charAt ((Line.result 14 b lf a c).text L) 17 = some '1' := by
        simp only [Line.text]
        repeat (first | decide | apply charAt_append)
      rw [h4] at h3
      exact absurd h3 (by decide)
  | refusedBy s o =>
    have h4 : charAt ((Line.refusedBy s o).text L) 2 = some 'f' := by
      cases o with
      | none => exact charAt_append _ (by decide)
      | some why =>
        simp only [Line.text]
        split <;> repeat (first | decide | apply charAt_append)
    rw [h4] at h2
    exact absurd h2 (by decide)
  | commitmentId o => exact (no 'c' rfl (by decide)).elim
  | idCompared b => exact (no 'i' rfl (by decide)).elim
  | hPar s => exact (no 'h' rfl (by decide)).elim
  | keyNotChecked => exact (no 'k' rfl (by decide)).elim
  | weightHiding => exact (no 'w' rfl (by decide)).elim
  | covered a => exact (no 'c' rfl (by decide)).elim
  | stageWork s w => exact (no 's' rfl (by decide)).elim
  | work o l => exact (no 'p' rfl (by decide)).elim
  | commitment n record => exact (no 'c' rfl (by decide)).elim
  | theCall => exact (no '-' rfl (by decide)).elim
  | callCause c => exact (no 't' rfl (by decide)).elim
  | otherId1 => exact (no 'i' rfl (by decide)).elim
  | otherId2 => exact (no 'i' rfl (by decide)).elim
  | policyWhy w => exact (no 'p' rfl (by decide)).elim
  | note n =>
    cases n with
    | bits k => exact (no 't' rfl (by decide)).elim
    | keyFile => exact (no 'n' rfl (by decide)).elim
    | tableFile => exact (no 'n' rfl (by decide)).elim
  | planLine c s =>
    cases c <;> first
      | exact (no 'k' rfl (by decide)).elim
      | exact (no 'e' rfl (by decide)).elim
      | exact (no 'f' rfl (by decide)).elim
      | exact (no 's' rfl (by decide)).elim
  | noPlan c =>
    cases c <;> first
      | exact (no 'k' rfl (by decide)).elim
      | exact (no 'e' rfl (by decide)).elim
      | exact (no 'f' rfl (by decide)).elim
      | exact (no 's' rfl (by decide)).elim
  | unreadable role u => exact (no 'i' rfl (by decide)).elim
  | yes => exact (no 'Y' rfl (by decide)).elim
  | withinLimits a => exact (no 'W' rfl (by decide)).elim
  | partPassed s => exact (no 'P' rfl (by decide)).elim
  | notVer => exact (no 'N' rfl (by decide)).elim
  | no n => exact (no 'N' rfl (by decide)).elim
  | notChecked n => exact (no 'N' rfl (by decide)).elim
  | testPassed => exact (no 'T' rfl (by decide)).elim
  | planOnly => exact (no 'P' rfl (by decide)).elim

/-- A line that a run of `sayAll ls next` hands over is in ls, or is handed over by `next`. -/
theorem sayAll_any {next : Ask Ending} {r : Ending} {l : String} {ok : Bool} :
    ∀ (ls : List String) {evs : List Event}, (sayAll ls next).Ends evs r →
    Event.say l ok ∈ evs → l ∈ ls ∨ ∃ t, next.Ends t r ∧ Event.say l ok ∈ t
  | [], evs, h, hm => Or.inr ⟨evs, h, hm⟩
  | x :: ls, evs, h, hm => by
    obtain ⟨ok', t, rfl, h2⟩ := ends_say h
    cases hm with
    | head => exact Or.inl List.mem_cons_self
    | tail _ hm2 =>
      cases ok' with
      | false =>
        obtain ⟨rfl, _⟩ := unwritten_ends h2
        cases hm2 with
        | tail _ h3 => cases h3
      | true =>
        rcases sayAll_any ls h2 hm2 with h3 | h3
        · exact Or.inl (List.mem_cons_of_mem _ h3)
        · exact Or.inr h3

/-- Every line that a run of `finish L p e` hands over is a line of the result e. -/
theorem finish_any {p : Fields} {e : CallEnd} {evs : List Event} {r : Ending} {l : String}
    {ok : Bool} (h : (finish L p e).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ x ∈ before p e ++ [verdict p e], l = x.text L := by
  have step : (sayAll ((before p e).map (Line.text L))
      (lastSay ((verdict p e).text L) (.ended e))).Ends evs r →
      ∃ x ∈ before p e ++ [verdict p e], l = x.text L := by
    intro hs
    rcases sayAll_any _ hs hm with h1 | ⟨t, h1, m1⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h1
      exact ⟨x, List.mem_append_left _ hx, rfl⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, (lastSay_said h1 m1).1⟩
  cases e with
  | usage w => exact (faultWith_said h hm).elim
  | yes a c => exact step h
  | withinLimits a c => exact step h
  | partPassed s c => exact step h
  | notVer cs o c => exact step h
  | refusedBy s w n => exact step h
  | wrongId => exact step h
  | policy w => exact step h
  | no n => exact step h
  | notChecked n => exact step h
  | unreadable role => exact step h

/-- If a run of `finish L p e` hands over a line that satisfies `Result0`, e is a yes or within
limits. -/
theorem finish_result0 {p : Fields} {e : CallEnd} {evs : List Event} {r : Ending} {l : String}
    {ok : Bool} (h0 : Result0 l) (h : (finish L p e).Ends evs r) (hm : Event.say l ok ∈ evs) :
    wholePass e = true := by
  obtain ⟨x, hx, rfl⟩ := finish_any h hm
  exact result0_pass hx h0

/-- As `fetch_said`, for a line that satisfies `Result0`. -/
theorem fetch_result0 {m : Nat} {p : String} {next : FileRead → Ask Ending} {evs : List Event}
    {r : Ending} {l : String} {ok : Bool} (h0 : Result0 l) (h : (fetch L m p next).Ends evs r)
    (hm : Event.say l ok ∈ evs) :
    ∃ got t, evs = .read p (m + 1) got :: t ∧ (next got).Ends t r ∧
      Event.say l ok ∈ t := by
  obtain ⟨got, t, rfl, h2⟩ := ends_read h
  have hm2 : Event.say l ok ∈ t := by
    cases hm with
    | tail _ h3 => exact h3
  refine ⟨got, t, rfl, ?_, hm2⟩
  cases got with
  | bytes b =>
    have h3 : (if b.size ≤ m then next (.bytes b)
      else finish L {} (.no "file-too-long")).Ends t r := h2
    split at h3
    · exact h3
    · have h4 := finish_result0 h0 h3 hm2
      cases h4
  | absent => exact h2
  | unreadable u => exact h2

/-- A line whose first character is r is not among lines with other first characters. -/
theorem result0_not {l : String} (h0 : Result0 l) (xs : List Line)
    (hx : ∀ x ∈ xs, x.first ≠ 'r') : l ∉ xs.map (Line.text L) := by
  intro hm
  obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hm
  have h1 := h0.1
  rw [hd_text] at h1
  exact hx x hxm (Option.some.inj h1)

/-- No note begins with r. -/
theorem note_not_r (n : Note) : (Line.note n).first ≠ 'r' := by
  have ht : ('t' : Char) ≠ 'r' := by decide
  have hn : ('n' : Char) ≠ 'r' := by decide
  cases n <;> first | exact ht | exact hn

/-- No chain's name begins with r. -/
theorem initial_not_r (c : ChainIx) : c.initial ≠ 'r' := by cases c <;> decide

/-- The line for programs. If a run of the program hands over a line that begins with
`result-v1 status=0`, whether or not that succeeds, the call is a whole call, the run begins with
its eight reads, and `Checks.wholeCall` on the call's options and the answers of these reads is a
yes or a result within limits. -/
theorem said_result {C : Checks} {args : List String} {evs : List Event} {r : Ending} {ok : Bool}
    {l : String} (h0 : Result0 l) (h : (call C args).Ends evs r) (hm : Event.say l ok ∈ evs) :
    ∃ (config ivk request y proof : String) (a : Asked)
      (pol kl lay key req yy prf ent : FileRead) (k : Nat) (t : List Event),
      kindOf args = .whole config ivk request y proof a ∧
      C.entryNumber a.options (filesOf pol kl lay key req yy prf) = .ok k ∧
      wholePass (C.wholeCall a.options
        { filesOf pol kl lay key req yy prf with entry := fileIn ent }) = true ∧
      evs = [.read (config ++ "/policy.txt") (textLimit + 1) pol,
        .read (config ++ "/KL.bin") (fileLimit + 1) kl,
        .read (config ++ "/layout.txt") (textLimit + 1) lay,
        .read (ivk ++ "/key.bin") (fileLimit + 1) key, .read request (fileLimit + 1) req,
        .read y (fileLimit + 1) yy, .read proof (fileLimit + 1) prf,
        .read (ivk ++ "/leaf/" ++ toString k ++ ".bin") (fileLimit + 1) ent] ++ t := by
  have pNotR : ('p' : Char) ≠ 'r' := by decide
  unfold call at h
  cases hk : kindOf args with
  | toy paths notes v w =>
    exfalso
    rw [hk] at h
    have go : ∀ (ps : List String) (got : List ByteArray) (ev : List Event),
        (needAll C.lists ps got fun files =>
          match v files with
          | some x => sayAll (notes.map fun n => (Line.note n).text C.lists)
              (finishTest C.lists (w files) x)
          | none => faultWith "verify-on-bytes: internal fault").Ends ev r →
        Event.say l ok ∈ ev → False := by
      intro ps
      induction ps with
      | nil =>
        intro got ev hv hmv
        have k3 : (match v got with
          | some x => sayAll (notes.map fun n => (Line.note n).text C.lists)
              (finishTest C.lists (w got) x)
          | none => faultWith "verify-on-bytes: internal fault").Ends ev r := hv
        cases hvv : v got with
        | none =>
          rw [hvv] at k3
          exact faultWith_said k3 hmv
        | some x =>
          rw [hvv] at k3
          rcases sayAll_any _ k3 hmv with k4 | ⟨t, k4, m4⟩
          · have hn := result0_not (L := C.lists) h0 (notes.map Line.note) (by
              intro y hy
              obtain ⟨n, _, rfl⟩ := List.mem_map.1 hy
              exact note_not_r n)
            rw [List.map_map] at hn
            exact hn k4
          · cases x with
            | refused q =>
              have k5 : (finish C.lists {} (.no q.check)).Ends t r := k4
              have k6 := finish_result0 h0 k5 m4
              cases k6
            | accepted =>
              have k5 : (finishWork C.lists (w got)).Ends t r := k4
              cases hw : w got with
              | error name =>
                rw [hw] at k5
                have k6 := finish_result0 h0 (e := .no name) k5 m4
                cases k6
              | ok ow =>
                rw [hw] at k5
                rcases sayAll_any _ k5 m4 with k6 | ⟨t5, k6, m6⟩
                · exact result0_not (L := C.lists) h0 [.work ow.1 ow.2] (by
                    intro y hy
                    cases hy with
                    | head => exact pNotR
                    | tail _ h6 => cases h6) k6
                · have e1 := (lastSay_said k6 m6).1
                  have h1 := h0.1
                  rw [e1, hd_text] at h1
                  exact absurd (Option.some.inj h1) (by decide)
      | cons p ps ih =>
        intro got ev hv hmv
        obtain ⟨g, t, rfl, k2, m2⟩ := fetch_result0 h0 hv hmv
        cases g with
        | bytes b => exact ih _ t k2 m2
        | absent => exact faultWith_said k2 m2
        | unreadable u => exact faultWith_said k2 m2
    exact go paths [] evs h hm
  | whole config ivk request y proof a =>
    rw [hk] at h
    obtain ⟨pol, t1, rfl, h1, m1⟩ := fetch_result0 h0 h hm
    obtain ⟨kl, t2, rfl, h2, m2⟩ := fetch_result0 h0 h1 m1
    obtain ⟨lay, t3, rfl, h3, m3⟩ := fetch_result0 h0 h2 m2
    obtain ⟨key, t4, rfl, h4, m4⟩ := fetch_result0 h0 h3 m3
    obtain ⟨req, t5, rfl, h5, m5⟩ := fetch_result0 h0 h4 m4
    obtain ⟨yy, t6, rfl, h6, m6⟩ := fetch_result0 h0 h5 m5
    obtain ⟨prf, t7, rfl, h7, m7⟩ := fetch_result0 h0 h6 m6
    dsimp only at h7
    cases hn : C.entryNumber a.options (filesOf pol kl lay key req yy prf) with
    | error e0 =>
      unfold filesOf at hn
      rw [hn] at h7
      have h8 := finish_result0 h0 h7 m7
      cases e0 <;> cases h8
    | ok k =>
      unfold filesOf at hn
      rw [hn] at h7
      obtain ⟨ent, t8, rfl, h8, m8⟩ := fetch_result0 h0 h7 m7
      exact ⟨_, _, _, _, _, _, pol, kl, lay, key, req, yy, prf, ent, k, t8, rfl, hn,
        finish_result0 h0 h8 m8, rfl⟩
  | keyPart config key a =>
    exfalso
    rw [hk] at h
    obtain ⟨_, _, rfl, h1, m1⟩ := fetch_result0 h0 h hm
    obtain ⟨_, _, rfl, h2, m2⟩ := fetch_result0 h0 h1 m1
    obtain ⟨_, _, rfl, h3, m3⟩ := fetch_result0 h0 h2 m2
    obtain ⟨_, _, rfl, h4, m4⟩ := fetch_result0 h0 h3 m3
    have h5 := finish_result0 h0 h4 m4
    generalize C.keyCall _ _ = z at h5
    cases z <;> cases h5
  | leafPart config key entry a =>
    exfalso
    rw [hk] at h
    obtain ⟨_, _, rfl, h1, m1⟩ := fetch_result0 h0 h hm
    obtain ⟨_, _, rfl, h2, m2⟩ := fetch_result0 h0 h1 m1
    obtain ⟨_, _, rfl, h3, m3⟩ := fetch_result0 h0 h2 m2
    obtain ⟨_, _, rfl, h4, m4⟩ := fetch_result0 h0 h3 m3
    obtain ⟨_, _, rfl, h5, m5⟩ := fetch_result0 h0 h4 m4
    have h6 := finish_result0 h0 h5 m5
    generalize C.leafCall _ _ = z at h6
    cases z <;> cases h6
  | plan config bits =>
    exfalso
    rw [hk] at h
    obtain ⟨pol, _, rfl, h1, m1⟩ := fetch_result0 h0 h hm
    obtain ⟨kl, _, rfl, h2, m2⟩ := fetch_result0 h0 h1 m1
    obtain ⟨lay, _, rfl, h3, m3⟩ := fetch_result0 h0 h2 m2
    cases hq : C.plan bits (fileIn pol) (fileIn kl) (layoutIn lay) with
    | error e0 =>
      rw [hq] at h3
      have h8 := finish_result0 h0 h3 m3
      cases e0 <;> cases h8
    | ok x =>
      rw [hq] at h3
      rcases sayAll_any _ h3 m3 with h4 | ⟨t, h4, m4⟩
      · exact result0_not h0 (planLines x) (by
          intro y hy
          obtain ⟨ch, _, rfl⟩ := List.mem_map.1 hy
          split <;> exact initial_not_r ch) h4
      · have e1 := (lastSay_said h4 m4).1
        have h5 := h0.1
        rw [e1, hd_text] at h5
        exact absurd (Option.some.inj h5) (by decide)
  | bad words =>
    rw [hk] at h
    exact (faultWith_said h hm).elim

end OnBytes.Shell

#print axioms OnBytes.Shell.said_result
#print axioms OnBytes.Shell.said_yes
#print axioms OnBytes.Shell.said_within
#print axioms OnBytes.Shell.said_part
#print axioms OnBytes.Shell.said_test
