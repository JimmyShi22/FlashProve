-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/Laws.lean: what an exit code of the general shell means, in Lean's model of IO. For
proofs only: no program imports this file.

Theorems, for every body B (OnBytes/ShellOf/Body.lean).
  `mainOf_iff`: `mainOf B args` returns the code c exactly if the program as a value has a run
    whose answers the three operations gave and whose end has the code c.
  `mainOf_zero`: the exit code 0. The arguments gave a call; every file was read, within its cap;
    the heads passed; the statement x was made by `state` of the arguments and the bytes read;
    `B.short x = none`; the converter handed over some v; `B.verify x v = true`; and the lines of
    the yes were written.
  `mainOf_means`: every code: which stage ended the call, what held there, and on which answers of
    the program's own reads (`Means`).
  `code_zero`, `code_inj_kind`, `code_small`, `mainOf_codes`, `mainOf_total`, `mainOf_never_fault`.

What is not claimed. Nothing on soundness: what a yes of `B.verify` is worth is the body's matter.
The theorems go one way: none says that 0 is ever returned. The bytes are the answers of the
program's reads in Lean's model of IO; Lean's logic knows nothing of files. Nothing is said about
compiled code, Lean's run-time, the C compiler or the operating system. A crash is no verdict, and
no theorem here speaks of one. What is proved is that `mainOf` returns 0 or a code from 10 to 19
(`mainOf_codes`). That no crash ends a process with one of these codes is a matter of the run-time
and the operating system: it is trusted. For the ends "unread" and "too long" `Means` names the
file and nothing more, and for the end "unwritten" it says nothing.

-/
import OnBytes.ShellOf.Body
import OnBytes.Shell.AtOps

set_option autoImplicit false

namespace OnBytes.ShellOf

open OnBytes.Shell (Ask FileRead Event opsIO Steps World NoThrow run_bind run_pure run_try
  ends_done ends_read ends_say ends_err noThrow_run noThrow_bind noThrow_try noThrow_pure
  run_of_noThrow readIO_noThrow outIO_noThrow errIO_noThrow)

/-- The lines were handed to standard output, each with success. -/
def said (ls : List String) : List Event := ls.map fun l => Event.say l true

/-- The words were handed to standard error. -/
def errd (ls : List String) : List Event := ls.map Event.err

/-- The files were read, each answered with bytes. -/
def reads : List Want → List ByteArray → List Event
  | w :: ws, b :: bs => .read w.path (w.cap + 1) (.bytes b) :: reads ws bs
  | _, _ => []

/-- As many byte strings as files, each within its file's cap. -/
def Fits : List Want → List ByteArray → Prop
  | [], [] => True
  | w :: ws, b :: bs => b.size ≤ w.cap ∧ Fits ws bs
  | _, _ => False

/-- The questions and answers of a call that reads all its files, with the bytes bs, and ends with
e behind the lines pre. -/
def trace (B : Body) (ws : List Want) (bs : List ByteArray) (pre : List String) (e : End) :
    List Event :=
  reads ws bs ++ (errd e.aside ++ said (pre ++ [e.line B.word]))

/-! ## The pure part -/

/-- The six ways in which the pure part ends. -/
theorem judged_cases (B : Body) (a : B.A) (bs : List ByteArray) :
    (∃ y, B.head a bs = some y ∧ judged B a bs = ([], .head y)) ∨
    (∃ y, B.head a bs = none ∧ B.state a bs = .error y ∧ judged B a bs = ([], .state y)) ∨
    (∃ x y, B.head a bs = none ∧ B.state a bs = .ok x ∧ B.short x = some y ∧
      judged B a bs = ([], .notVer y)) ∨
    (∃ x y, B.head a bs = none ∧ B.state a bs = .ok x ∧ B.short x = none ∧
      B.conv a x bs = .error y ∧ judged B a bs = ([], .converter y)) ∨
    (∃ x v, B.head a bs = none ∧ B.state a bs = .ok x ∧ B.short x = none ∧
      B.conv a x bs = .ok v ∧ B.verify x v = true ∧ judged B a bs = (B.gives x v, .yes)) ∨
    (∃ x v, B.head a bs = none ∧ B.state a bs = .ok x ∧ B.short x = none ∧
      B.conv a x bs = .ok v ∧ B.verify x v = false ∧
      judged B a bs = ([], .no (B.stage x v))) := by
  cases hh : B.head a bs with
  | some y => refine Or.inl ⟨y, ?_, ?_⟩ <;> first | rfl | assumption | simp [judged, *]
  | none =>
    cases hs : B.state a bs with
    | error y =>
      refine Or.inr (Or.inl ⟨y, ?_, ?_, ?_⟩) <;> first | rfl | assumption | simp [judged, *]
    | ok x =>
      cases hn : B.short x with
      | some y =>
        refine Or.inr (Or.inr (Or.inl ⟨x, y, ?_, ?_, ?_, ?_⟩)) <;>
          first | rfl | assumption | simp [judged, *]
      | none =>
        cases hc : B.conv a x bs with
        | error y =>
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩))) <;>
            first | rfl | assumption | simp [judged, *]
        | ok v =>
          cases hv : B.verify x v with
          | true =>
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, v, ?_, ?_, ?_, ?_, ?_, ?_⟩)))) <;>
              first | rfl | assumption | simp [judged, *]
          | false =>
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, v, ?_, ?_, ?_, ?_, ?_, ?_⟩)))) <;>
              first | rfl | assumption | simp [judged, *]

/-! ## The runs of the program as a value -/

theorem ends_unwritten {evs : List Event} {e : End} (h : unwritten.Ends evs e) :
    e = .unwritten := by
  obtain ⟨t, _, h1⟩ := ends_err h
  exact (ends_done h1).2.symm

theorem ends_sayThen {ls : List String} {next : Ask End} {evs : List Event} {e : End}
    (h : (sayThen ls next).Ends evs e) :
    (∃ t, evs = said ls ++ t ∧ next.Ends t e) ∨ e = .unwritten := by
  induction ls generalizing evs with
  | nil => exact Or.inl ⟨evs, rfl, h⟩
  | cons l ls ih =>
    obtain ⟨ok, t, rfl, h1⟩ := ends_say h
    cases ok with
    | true =>
      rcases ih h1 with ⟨t', rfl, h2⟩ | h2
      · exact Or.inl ⟨t', rfl, h2⟩
      · exact Or.inr h2
    | false => exact Or.inr (ends_unwritten h1)

theorem ends_errThen {ls : List String} {next : Ask End} {evs : List Event} {e : End}
    (h : (errThen ls next).Ends evs e) : ∃ t, evs = errd ls ++ t ∧ next.Ends t e := by
  induction ls generalizing evs with
  | nil => exact ⟨evs, rfl, h⟩
  | cons l ls ih =>
    obtain ⟨t, rfl, h1⟩ := ends_err h
    obtain ⟨t', rfl, h2⟩ := ih h1
    exact ⟨t', rfl, h2⟩

theorem ends_close {w : String} {pre : List String} {e0 : End} {evs : List Event} {e : End}
    (h : (close w pre e0).Ends evs e) :
    (e = e0 ∧ evs = said (pre ++ [e0.line w])) ∨ e = .unwritten := by
  rcases ends_sayThen h with ⟨t, rfl, h1⟩ | h1
  · obtain ⟨ok, t', rfl, h2⟩ := ends_say h1
    cases ok with
    | true =>
      obtain ⟨rfl, rfl⟩ := ends_done h2
      exact Or.inl ⟨rfl, by simp [said]⟩
    | false => exact Or.inr (ends_unwritten h2)
  · exact Or.inr h1

theorem ends_readAll {word : String} {ws : List Want} {k : List ByteArray → Ask End}
    {evs : List Event} {e : End} (h : (readAll word ws k).Ends evs e) :
    (∃ bs t, Fits ws bs ∧ evs = reads ws bs ++ t ∧ (k bs).Ends t e) ∨
    (∃ w ∈ ws, e = .unread w.path ∨ e = .tooLong w.path) ∨ e = .unwritten := by
  induction ws generalizing k evs with
  | nil => exact Or.inl ⟨[], evs, trivial, rfl, h⟩
  | cons w ws ih =>
    obtain ⟨got, t, rfl, h1⟩ := ends_read h
    cases got with
    | bytes b =>
      have h2 : (if b.size ≤ w.cap then readAll word ws (fun l => k (b :: l))
          else close word [] (.tooLong w.path)).Ends t e := h1
      by_cases hb : b.size ≤ w.cap
      · rw [if_pos hb] at h2
        rcases ih h2 with ⟨bs, t', hf, rfl, h3⟩ | ⟨w', hw, he⟩ | he
        · exact Or.inl ⟨b :: bs, t', (show b.size ≤ w.cap ∧ Fits ws bs from ⟨hb, hf⟩), rfl, h3⟩
        · exact Or.inr (Or.inl ⟨w', List.mem_cons_of_mem _ hw, he⟩)
        · exact Or.inr (Or.inr he)
      · rw [if_neg hb] at h2
        rcases ends_close h2 with ⟨rfl, _⟩ | he
        · exact Or.inr (Or.inl ⟨w, List.mem_cons_self, Or.inr rfl⟩)
        · exact Or.inr (Or.inr he)
    | absent =>
      have h2 : (close word [] (.unread w.path)).Ends t e := h1
      rcases ends_close h2 with ⟨rfl, _⟩ | he
      · exact Or.inr (Or.inl ⟨w, List.mem_cons_self, Or.inl rfl⟩)
      · exact Or.inr (Or.inr he)
    | unreadable u =>
      have h2 : (close word [] (.unread w.path)).Ends t e := h1
      rcases ends_close h2 with ⟨rfl, _⟩ | he
      · exact Or.inr (Or.inl ⟨w, List.mem_cons_self, Or.inl rfl⟩)
      · exact Or.inr (Or.inr he)

/-- Every run of the program as a value: it read all files and ended as the pure part says on their
bytes, with that part's lines written; or the arguments gave no call; or a file could not be read
or was too long; or a line could not be written. -/
theorem prog_ends {B : Body} {args : List String} {evs : List Event} {e : End}
    (h : (prog B args).Ends evs e) :
    (∃ a ws bs, B.ask args = some (a, ws) ∧ Fits ws bs ∧ (judged B a bs).2 = e ∧
      evs = trace B ws bs (judged B a bs).1 e) ∨
    (B.ask args = none ∧ e = .usage) ∨
    (∃ a ws, B.ask args = some (a, ws) ∧ ∃ w ∈ ws, e = .unread w.path ∨ e = .tooLong w.path) ∨
    e = .unwritten := by
  unfold prog at h
  generalize B.ask args = o at h ⊢
  cases o with
  | none =>
    obtain ⟨t, _, h1⟩ := ends_err h
    exact Or.inr (Or.inl ⟨rfl, (ends_done h1).2.symm⟩)
  | some p =>
    obtain ⟨a, ws⟩ := p
    rcases ends_readAll h with ⟨bs, t, hf, rfl, h1⟩ | ⟨w, hw, he⟩ | he
    · obtain ⟨t', rfl, h2⟩ := ends_errThen h1
      rcases ends_close h2 with ⟨rfl, rfl⟩ | he
      · exact Or.inl ⟨a, ws, bs, rfl, hf, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl ⟨a, ws, rfl, w, hw, he⟩))
    · exact Or.inr (Or.inr (Or.inr he))

/-! ## The exit codes -/

/-- The code 0 is the yes alone. -/
theorem code_zero {e : End} (h : e.code = 0) : e = .yes := by
  cases e <;> first | rfl | exact absurd h (by simp only [End.code]; decide)

/-- Two ends with one code are of one kind: the code names the stage. -/
theorem code_inj_kind {e f : End} (h : e.code = f.code) : e.ctorIdx = f.ctorIdx := by
  cases e <;> cases f <;> first | rfl | exact absurd h (by simp only [End.code]; decide)

/-- Every code is below 256, so it is what a caller's shell sees of it. -/
theorem code_small (e : End) : e.code.toNat < 256 := by
  cases e <;> simp only [End.code] <;> decide

/-! ## The program in IO -/

theorem noThrow_prog (B : Body) (args : List String) : NoThrow ((prog B args).run opsIO) :=
  noThrow_run readIO_noThrow outIO_noThrow errIO_noThrow _

/-- The program in IO returns c exactly if the program as a value has a run whose answers the three
operations gave and whose end has the code c. -/
theorem mainOf_iff (B : Body) (args : List String) (s s' : World) (c : UInt32) :
    Shell.Run (mainOf B args) s c s' ↔
      ∃ evs e, (prog B args).Ends evs e ∧ Steps opsIO evs s s' ∧ e.code = c := by
  constructor
  · intro h
    obtain ⟨r, s1, h1, h2⟩ := (run_bind
      (x := tryCatch ((prog B args).run opsIO) fun _ => pure End.fault)
      (f := fun e => pure e.code)).1 h
    obtain ⟨h3, rfl⟩ := run_pure.1 h2
    rcases run_try.1 h1 with h4 | ⟨e, s2, h4, _⟩
    · obtain ⟨evs, h5, h6⟩ := (Ask.run_iff opsIO (prog B args) s r s1).1 h4
      exact ⟨evs, r, h5, h6, h3⟩
    · exact absurd h4 (noThrow_prog B args s e s2)
  · rintro ⟨evs, r, h1, h2, rfl⟩
    exact (run_bind (x := tryCatch ((prog B args).run opsIO) fun _ => pure End.fault)
      (f := fun e => pure e.code)).2
      ⟨r, s', run_try.2 (Or.inl ((Ask.run_iff opsIO (prog B args) s r s').2 ⟨evs, h1, h2⟩)),
        run_pure.2 ⟨rfl, rfl⟩⟩

theorem mainOf_noThrow (B : Body) (args : List String) : NoThrow (mainOf B args) :=
  noThrow_bind (x := tryCatch ((prog B args).run opsIO) fun _ => pure End.fault)
    (f := fun e => pure e.code) (noThrow_try fun _ => noThrow_pure _) fun _ => noThrow_pure _

/-- In Lean's model of IO the program returns in every state. It does not say that the real program
ends. -/
theorem mainOf_total (B : Body) (args : List String) (s : World) :
    ∃ c s', Shell.Run (mainOf B args) s c s' :=
  run_of_noThrow (mainOf_noThrow B args) s

theorem mainOf_small {B : Body} {args : List String} {s s' : World} {c : UInt32}
    (h : Shell.Run (mainOf B args) s c s') : c.toNat < 256 := by
  obtain ⟨_, e, _, _, rfl⟩ := (mainOf_iff B args s s' c).1 h
  exact code_small e

/-- The exit code 0. The arguments gave a call a with the files ws. The three operations gave:
every file read and answered with bytes bs, each within its cap; then the lines that the yes gives
out and the body's word for its yes, each written. The heads passed. `state`, on the arguments and
these bytes, made the statement x, and `B.short x = none`. The converter, on the same, handed over
v. And `B.verify x v = true`. -/
theorem mainOf_zero {B : Body} {args : List String} {s s' : World}
    (h : Shell.Run (mainOf B args) s 0 s') :
    ∃ (a : B.A) (ws : List Want) (bs : List ByteArray) (x : B.X) (v : B.V),
      B.ask args = some (a, ws) ∧ Fits ws bs ∧
      Steps opsIO (reads ws bs ++ said (B.gives x v ++ [B.word])) s s' ∧
      B.head a bs = none ∧ B.state a bs = .ok x ∧ B.short x = none ∧ B.conv a x bs = .ok v ∧
      B.verify x v = true := by
  obtain ⟨evs, e, h1, h2, h3⟩ := (mainOf_iff B args s s' 0).1 h
  cases code_zero h3
  rcases prog_ends h1 with ⟨a, ws, bs, ha, hf, hj, rfl⟩ | ⟨_, he⟩ | ⟨_, _, _, _, _, he⟩ | he
  · rcases judged_cases B a bs with ⟨y, _, q⟩ | ⟨y, _, _, q⟩ | ⟨x, y, _, _, _, q⟩ |
      ⟨x, y, _, _, _, _, q⟩ | ⟨x, v, q1, q2, q3, q4, q5, q⟩ | ⟨x, v, _, _, _, _, _, q⟩
    · rw [q] at hj; cases hj
    · rw [q] at hj; cases hj
    · rw [q] at hj; cases hj
    · rw [q] at hj; cases hj
    · rw [q] at h2
      exact ⟨a, ws, bs, x, v, ha, hf, h2, q1, q2, q3, q4, q5⟩
    · rw [q] at hj; cases hj
  · cases he
  · rcases he with he | he <;> cases he
  · cases he

/-- What held in a call that ended with e, on the questions and answers evs. In the six ends
behind the reads (yes, no, head, state, notVer, converter) the bytes bs are the answers of the
call's own reads: evs begins with them. -/
def Means (B : Body) (args : List String) (evs : List Event) : End → Prop
  | .yes => ∃ a ws bs x v, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs (B.gives x v) .yes ∧ B.head a bs = none ∧
      B.state a bs = .ok x ∧ B.short x = none ∧ B.conv a x bs = .ok v ∧ B.verify x v = true
  | .no st => ∃ a ws bs x v, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs [] (.no st) ∧ B.head a bs = none ∧
      B.state a bs = .ok x ∧ B.short x = none ∧ B.conv a x bs = .ok v ∧ B.verify x v = false ∧
      st = B.stage x v
  | .usage => B.ask args = none
  | .unread p => ∃ a ws, B.ask args = some (a, ws) ∧ ∃ w ∈ ws, w.path = p
  | .tooLong p => ∃ a ws, B.ask args = some (a, ws) ∧ ∃ w ∈ ws, w.path = p
  | .head y => ∃ a ws bs, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs [] (.head y) ∧ B.head a bs = some y
  | .state y => ∃ a ws bs, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs [] (.state y) ∧ B.head a bs = none ∧ B.state a bs = .error y
  | .notVer y => ∃ a ws bs x, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs [] (.notVer y) ∧ B.head a bs = none ∧
      B.state a bs = .ok x ∧ B.short x = some y
  | .converter y => ∃ a ws bs x, B.ask args = some (a, ws) ∧ Fits ws bs ∧
      evs = trace B ws bs [] (.converter y) ∧ B.head a bs = none ∧
      B.state a bs = .ok x ∧ B.short x = none ∧ B.conv a x bs = .error y
  | .fault => False
  | .unwritten => True

theorem prog_means {B : Body} {args : List String} {evs : List Event} {e : End}
    (h : (prog B args).Ends evs e) : Means B args evs e := by
  rcases prog_ends h with ⟨a, ws, bs, ha, hf, hj, hev⟩ | ⟨ha, rfl⟩ | ⟨a, ws, ha, w, hw, he⟩ | rfl
  · rcases judged_cases B a bs with ⟨y, q1, q⟩ | ⟨y, q1, q2, q⟩ | ⟨x, y, q1, q2, q3, q⟩ |
      ⟨x, y, q1, q2, q3, q4, q⟩ | ⟨x, v, q1, q2, q3, q4, q5, q⟩ |
      ⟨x, v, q1, q2, q3, q4, q5, q⟩ <;> rw [q] at hj hev <;> cases hj
    · exact ⟨a, ws, bs, ha, hf, hev, q1⟩
    · exact ⟨a, ws, bs, ha, hf, hev, q1, q2⟩
    · exact ⟨a, ws, bs, x, ha, hf, hev, q1, q2, q3⟩
    · exact ⟨a, ws, bs, x, ha, hf, hev, q1, q2, q3, q4⟩
    · exact ⟨a, ws, bs, x, v, ha, hf, hev, q1, q2, q3, q4, q5⟩
    · exact ⟨a, ws, bs, x, v, ha, hf, hev, q1, q2, q3, q4, q5, rfl⟩
  · exact ha
  · rcases he with rfl | rfl
    · exact ⟨a, ws, ha, w, hw, rfl⟩
    · exact ⟨a, ws, ha, w, hw, rfl⟩
  · trivial

/-- Every code names its stage: whatever the program in IO returns is the code of an end e; the
three operations gave the answers evs; and what `Means` says of evs and e held. -/
theorem mainOf_means {B : Body} {args : List String} {s s' : World} {c : UInt32}
    (h : Shell.Run (mainOf B args) s c s') :
    ∃ (e : End) (evs : List Event), e.code = c ∧ Steps opsIO evs s s' ∧ Means B args evs e := by
  obtain ⟨evs, e, h1, h2, h3⟩ := (mainOf_iff B args s s' c).1 h
  exact ⟨e, evs, h3, h2, prog_means h1⟩

/-- No run returns the code of an exception in IO. -/
theorem mainOf_never_fault {B : Body} {args : List String} {s s' : World} :
    ¬ Shell.Run (mainOf B args) s 17 s' := by
  intro h
  obtain ⟨e, _, h1, _, h2⟩ := mainOf_means h
  cases e <;> first | exact h2 | exact absurd h1 (by simp only [End.code]; decide)

/-- The codes: 0, or from 10 to 19. So 1, with which Lean's run-time was seen to end a process, is
never returned. -/
theorem mainOf_codes {B : Body} {args : List String} {s s' : World} {c : UInt32}
    (h : Shell.Run (mainOf B args) s c s') : c = 0 ∨ (10 ≤ c.toNat ∧ c.toNat ≤ 19) := by
  obtain ⟨e, _, rfl, _⟩ := mainOf_means h
  cases e <;> first | exact Or.inl rfl | exact Or.inr (by simp only [End.code]; decide)

end OnBytes.ShellOf

#print axioms OnBytes.ShellOf.mainOf_codes
#print axioms OnBytes.ShellOf.mainOf_iff
#print axioms OnBytes.ShellOf.mainOf_zero
#print axioms OnBytes.ShellOf.mainOf_means
#print axioms OnBytes.ShellOf.mainOf_never_fault
#print axioms OnBytes.ShellOf.mainOf_total
#print axioms OnBytes.ShellOf.code_inj_kind
