-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtSize.lean: a run in which a read came back full passes nothing.

Every read asks for one byte more than the file's limit (`fetch`, OnBytes/Shell/Ask.lean). A read
comes back full if it is answered with at least as many bytes as it asked for. The theorems are on
the answers of reads, not on files.

Main definitions: `NoRead`, `OnlyLong`, `Sized`, properties of the program as a tree; `Rounds`.
Main theorems, for all arguments; those on `call C args` hold for all checks C.
- `call_cut`: if some read in a run of `call C args` came back full, every line that the run hands
  to standard output is `NO: file-too-long` (the text of `Line.no "file-too-long"` under `C.lists`).
  `call_cut_end`: and the run ends with that refusal or with an unwritten answer.
- `call_sizes`: in a run that hands over any other line, every read that was answered with bytes got
  fewer bytes than it asked for. `pass_sizes`: so it is in a run that hands over a line that does
  not begin with N; no passing line begins with N (OnBytes/Shell/AtWord.lean).
- `program_sizes`, `program_code_sizes`: the same for the program's entry function in IO, from a
  line and from an exit code other than 1 and 15.
- `readUpTo_short`, `readIO_short`: if `readIO p n` returned fewer than n bytes, then after the
  rounds that returned them a call of `Handle.read` on the same handle, for at least one byte,
  returned none. So the loop did not stop because its rounds ran out. `program_code_reads` gives the
  hypotheses of `readIO_short` for the reads of `program_code_sizes`.

What is not claimed. That a call of `Handle.read` which returns no byte means the end of the file,
that the bytes returned are the file's, or that the file stayed the same: Lean's logic knows nothing
of files (OnBytes/Shell/AtBottom.lean). Nothing about compiled code, Lean's run-time or the
operating system. For proofs only; the program does not import this file.
-/
import OnBytes.Shell.AtMain
import OnBytes.Shell.AtWord
import OnBytes.Shell.AtBottom

namespace OnBytes.Shell

open OnBytes.Model.Stages (CallEnd)

/-- The program q reads no file. -/
def NoRead : Ask Ending → Prop
  | .done _ => True
  | .read _ _ _ => False
  | .say _ next => ∀ ok, NoRead (next ok)
  | .err _ next => NoRead next

/-- The line that ends a call on a file above its limit. -/
def tooLong (L : Lists) : String := (Line.no "file-too-long").text L

/-- Every line that q prints on standard output is `tooLong L`, and q ends with that refusal or with
an unwritten answer. -/
def OnlyLong (L : Lists) : Ask Ending → Prop
  | .done r => r = .ended (.no "file-too-long") ∨ r = .unwritten
  | .read _ _ next => ∀ got, OnlyLong L (next got)
  | .say l next => l = tooLong L ∧ ∀ ok, OnlyLong L (next ok)
  | .err _ next => OnlyLong L next

/-- After a read that was answered with at least as many bytes as it asked for, q is `OnlyLong`; and
once q has printed a line or written to standard error, it reads no more. -/
def Sized (L : Lists) : Ask Ending → Prop
  | .done _ => True
  | .read _ n next =>
    (∀ b : ByteArray, n ≤ b.size → OnlyLong L (next (.bytes b))) ∧ ∀ got, Sized L (next got)
  | .say _ next => ∀ ok, NoRead (next ok)
  | .err _ next => NoRead next

variable {L : Lists}

/-- A run of a program that reads no file holds no read. -/
theorem noRead_ends : ∀ (q : Ask Ending), NoRead q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → ∀ p n got, Event.read p n got ∉ evs := by
  intro q
  induction q with
  | done r0 =>
    intro _ evs r hr p n got hm
    obtain ⟨rfl, _⟩ := ends_done hr
    cases hm
  | read p0 n0 next _ => exact fun h => h.elim
  | say l0 next ih =>
    intro h evs r hr p n got hm
    obtain ⟨ok0, t, rfl, h2⟩ := ends_say hr
    cases hm with
    | tail _ hm => exact ih ok0 (h ok0) t r h2 p n got hm
  | err x next ih =>
    intro h evs r hr p n got hm
    obtain ⟨t, rfl, h2⟩ := ends_err hr
    cases hm with
    | tail _ hm => exact ih h t r h2 p n got hm

/-- Every line that a run of a program with `OnlyLong` hands over is `tooLong L`, and the run ends
with that refusal or with an unwritten answer. -/
theorem onlyLong_ends : ∀ (q : Ask Ending), OnlyLong L q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → (r = .ended (.no "file-too-long") ∨ r = .unwritten) ∧
      ∀ l ok, Event.say l ok ∈ evs → l = tooLong L := by
  intro q
  induction q with
  | done r0 =>
    intro h evs r hr
    obtain ⟨rfl, rfl⟩ := ends_done hr
    exact ⟨h, fun l ok hm => by cases hm⟩
  | read p0 n0 next ih =>
    intro h evs r hr
    obtain ⟨got0, t, rfl, h2⟩ := ends_read hr
    refine ⟨(ih got0 (h got0) t r h2).1, fun l ok hm => ?_⟩
    cases hm with
    | tail _ hm => exact (ih got0 (h got0) t r h2).2 l ok hm
  | say l0 next ih =>
    intro h evs r hr
    obtain ⟨ok0, t, rfl, h2⟩ := ends_say hr
    refine ⟨(ih ok0 (h.2 ok0) t r h2).1, fun l ok hm => ?_⟩
    cases hm with
    | head => exact h.1
    | tail _ hm => exact (ih ok0 (h.2 ok0) t r h2).2 l ok hm
  | err x next ih =>
    intro h evs r hr
    obtain ⟨t, rfl, h2⟩ := ends_err hr
    refine ⟨(ih h t r h2).1, fun l ok hm => ?_⟩
    cases hm with
    | tail _ hm => exact (ih h t r h2).2 l ok hm

/-- What `Sized` says of runs: if some read was answered with at least as many bytes as it asked
for, every line that the run hands over is `tooLong L`, and the run ends with that refusal or with
an unwritten answer. -/
theorem sized_ends : ∀ (q : Ask Ending), Sized L q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → ∀ p n (b : ByteArray), Event.read p n (.bytes b) ∈ evs → n ≤ b.size →
    (r = .ended (.no "file-too-long") ∨ r = .unwritten) ∧
      ∀ l ok, Event.say l ok ∈ evs → l = tooLong L := by
  intro q
  induction q with
  | done r0 =>
    intro _ evs r hr p n b hm
    obtain ⟨rfl, _⟩ := ends_done hr
    cases hm
  | read p0 n0 next ih =>
    intro h evs r hr p n b hm hn
    obtain ⟨got0, t, rfl, h2⟩ := ends_read hr
    have key : (r = .ended (.no "file-too-long") ∨ r = .unwritten) ∧
        ∀ l ok, Event.say l ok ∈ t → l = tooLong L := by
      cases hm with
      | head => exact onlyLong_ends _ (h.1 b hn) t r h2
      | tail _ hm => exact ih got0 (h.2 got0) t r h2 p n b hm hn
    refine ⟨key.1, fun l ok hs => ?_⟩
    cases hs with
    | tail _ h3 => exact key.2 l ok h3
  | say l0 next _ =>
    intro h evs r hr p n b hm
    obtain ⟨ok0, t, rfl, h2⟩ := ends_say hr
    cases hm with
    | tail _ hm => exact (noRead_ends _ (h ok0) t r h2 p n _ hm).elim
  | err x next _ =>
    intro h evs r hr p n b hm
    obtain ⟨t, rfl, h2⟩ := ends_err hr
    cases hm with
    | tail _ hm => exact (noRead_ends _ h t r h2 p n _ hm).elim

/-- A program that reads no file is `Sized`. -/
theorem sized_of_noRead : ∀ (q : Ask Ending), NoRead q → Sized L q
  | .done _, _ => trivial
  | .read _ _ _, h => h.elim
  | .say _ _, h => h
  | .err _ _, h => h

/-- A fault reads no file. -/
theorem noRead_fault (w : String) : NoRead (faultWith w) := trivial

/-- An answer that cannot be written reads no file. -/
theorem noRead_unwritten : NoRead unwritten := trivial

/-- The last step of a call reads no file. -/
theorem noRead_lastSay (l : String) (r : Ending) : NoRead (lastSay l r) :=
  fun ok => by cases ok <;> trivial

/-- Printed lines read no file. -/
theorem noRead_sayAll {next : Ask Ending} (h : NoRead next) :
    ∀ ls : List String, NoRead (sayAll ls next)
  | [] => h
  | _ :: ls => fun ok => by
      cases ok with
      | true => exact noRead_sayAll h ls
      | false => trivial

/-- The end of a call reads no file. -/
theorem noRead_finish (p : Fields) (e : CallEnd) : NoRead (finish L p e) := by
  cases e <;> first
    | trivial
    | exact noRead_sayAll (noRead_lastSay _ _) _

/-- The end of a call on a file above its limit prints only `tooLong L`. -/
theorem onlyLong_finish : OnlyLong L (finish L {} (.no "file-too-long")) :=
  ⟨rfl, fun ok => by
    cases ok with
    | true => exact Or.inl rfl
    | false => exact Or.inr rfl⟩

/-- A read with its test of the length is `Sized`, if what follows is. -/
theorem sized_fetch {m : Nat} {p : String} {next : FileRead → Ask Ending}
    (h : ∀ r, Sized L (next r)) : Sized L (fetch L m p next) := by
  constructor
  · intro b hb
    show OnlyLong L (if b.size ≤ m then next (.bytes b) else finish L {} _)
    rw [if_neg (by omega)]
    exact onlyLong_finish
  · intro got
    cases got with
    | bytes b =>
      show Sized L (if b.size ≤ m then next (.bytes b) else finish L {} _)
      split
      · exact h _
      · exact sized_of_noRead _ (noRead_finish _ _)
    | absent => exact h _
    | unreadable u => exact h _

/-- The read of a file that is needed is `Sized`, if what follows is. -/
theorem sized_need {p : String} {next : ByteArray → Ask Ending} (h : ∀ b, Sized L (next b)) :
    Sized L (need L p next) := by
  apply sized_fetch
  intro r
  cases r with
  | bytes b => exact h b
  | absent => exact sized_of_noRead _ (noRead_fault _)
  | unreadable u => exact sized_of_noRead _ (noRead_fault _)

/-- The end of a call on the files of a test protocol reads no file. -/
theorem noRead_verdict (notes : List Note) (v : Option Verdict) (w : Work) :
    NoRead (match v with
      | some x => sayAll (notes.map fun n => (Line.note n).text L) (finishTest L w x)
      | none => faultWith "verify-on-bytes: internal fault") := by
  cases v with
  | some x =>
    refine noRead_sayAll ?_ _
    cases x with
    | accepted =>
      cases w with
      | error name => exact noRead_finish (L := L) {} (.no name)
      | ok o => exact noRead_sayAll (noRead_lastSay _ _) _
    | refused r => exact noRead_finish (L := L) {} (.no r.check)
  | none => exact noRead_fault _

/-- The reads of several files that are needed are `Sized`, if what follows is. -/
theorem sized_needAll : ∀ (ps : List String) (got : List ByteArray)
    (next : List ByteArray → Ask Ending), (∀ l, Sized L (next l)) →
    Sized L (needAll L ps got next)
  | [], got, _, h => h got
  | _ :: ps, got, next, h => sized_need fun b => sized_needAll ps (got ++ [b]) next h

/-- A call on test files is `Sized`. -/
theorem sized_judgeFiles (ps : List String) (notes : List Note)
    (v : List ByteArray → Option Verdict) (w : List ByteArray → Work) :
    Sized L (judgeFiles L ps notes v w) :=
  sized_needAll ps [] _ fun l => sized_of_noRead _ (noRead_verdict notes (v l) (w l))

/-- A whole call is `Sized`. -/
theorem sized_whole (C : Checks) (config ivk request y proof : String) (a : Asked) :
    Sized C.lists (whole C config ivk request y proof a) := by
  unfold whole
  refine sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ =>
    sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ => ?_
  dsimp only
  split
  · exact sized_of_noRead _ (noRead_finish _ _)
  · exact sized_fetch fun _ => sized_of_noRead _ (noRead_finish _ _)

/-- A call on a key file alone is `Sized`. -/
theorem sized_keyPart (C : Checks) (config key : String) (a : Asked) :
    Sized C.lists (keyPart C config key a) :=
  sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ =>
    sized_of_noRead _ (noRead_finish _ _)

/-- A call on an entry file alone is `Sized`. -/
theorem sized_leafPart (C : Checks) (config key entry : String) (a : Asked) :
    Sized C.lists (leafPart C config key entry a) :=
  sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ =>
    sized_fetch fun _ => sized_of_noRead _ (noRead_finish _ _)

/-- A planning call is `Sized`. -/
theorem sized_planCall (C : Checks) (config : String) (bits : Nat) :
    Sized C.lists (planCall C config bits) := by
  unfold planCall
  refine sized_fetch fun _ => sized_fetch fun _ => sized_fetch fun _ => ?_
  split
  · exact sized_of_noRead _ (noRead_finish _ _)
  · exact sized_of_noRead _ (noRead_sayAll (noRead_lastSay _ _) _)

/-- The program is `Sized`, for all arguments. -/
theorem sized_call (C : Checks) (args : List String) : Sized C.lists (call C args) := by
  unfold call
  cases kindOf args with
  | toy paths notes v w => exact sized_judgeFiles _ _ _ _
  | whole config ivk request y proof a => exact sized_whole C _ _ _ _ _ _
  | keyPart config key a => exact sized_keyPart C _ _ _
  | leafPart config key entry a => exact sized_leafPart C _ _ _ _
  | plan config bits => exact sized_planCall C _ _
  | bad words => exact sized_of_noRead _ (noRead_fault _)

/-- If some read in a run was answered with at least as many bytes as it asked for, every line that
the run hands to standard output is `NO: file-too-long`. -/
theorem call_cut {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {p : String} {n : Nat} {b : ByteArray}
    (hm : Event.read p n (.bytes b) ∈ evs) (hn : n ≤ b.size) {l : String} {ok : Bool}
    (hs : Event.say l ok ∈ evs) : l = (Line.no "file-too-long").text C.lists :=
  (sized_ends _ (sized_call C args) evs r h p n b hm hn).2 l ok hs

/-- If some read in a run was answered with at least as many bytes as it asked for, the run ends
with the refusal `file-too-long` or with an unwritten answer. -/
theorem call_cut_end {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {p : String} {n : Nat} {b : ByteArray}
    (hm : Event.read p n (.bytes b) ∈ evs) (hn : n ≤ b.size) :
    r = .ended (.no "file-too-long") ∨ r = .unwritten :=
  (sized_ends _ (sized_call C args) evs r h p n b hm hn).1

/-- In a run that hands over another line than `NO: file-too-long`, every read that was answered
with bytes got fewer bytes than it asked for. -/
theorem call_sizes {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {l : String} {ok : Bool} (hs : Event.say l ok ∈ evs)
    (hl : l ≠ (Line.no "file-too-long").text C.lists) {p : String} {n : Nat} {b : ByteArray}
    (hm : Event.read p n (.bytes b) ∈ evs) : b.size < n :=
  Nat.lt_of_not_le fun hn => hl (call_cut h hm hn hs)

/-- In a run that hands over a line that does not begin with N, every read that was answered with
bytes got fewer bytes than it asked for. -/
theorem pass_sizes {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {l : String} {ok : Bool} (hs : Event.say l ok ∈ evs) {c : Char}
    (hc : hd l = some c) (hN : c ≠ 'N') {p : String} {n : Nat} {b : ByteArray}
    (hm : Event.read p n (.bytes b) ∈ evs) : b.size < n := by
  refine call_sizes h hs (fun e => hN ?_) hm
  rw [e, hd_text] at hc
  exact (Option.some.inj hc).symm

/-- As `pass_sizes`, for the program itself. Whatever code the program returns, it has a run with
the answers that the three operations gave; and if that run hands over a line that does not begin
with N, every read of the run that was answered with bytes got fewer bytes than it asked for. -/
theorem program_sizes {args : List String} {s s' : World} {c : UInt32}
    (h : Run (program args) s c s') :
    ∃ evs r, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c ∧
      ∀ l ok x, Event.say l ok ∈ evs → hd l = some x → x ≠ 'N' →
        ∀ p n (b : ByteArray), Event.read p n (.bytes b) ∈ evs → b.size < n := by
  obtain ⟨evs, r, h1, h2, h3⟩ := (main_iff modelChecks args s s' c).1 h
  exact ⟨evs, r, h1, h2, h3, fun l ok x hs hc hN p n b hm => pass_sizes h1 hs hc hN hm⟩

/-- From the exit code. If the program returns another code than 1 and 15, it has a run with the
answers that the three operations gave in which every read that was answered with bytes got fewer
bytes than it asked for. -/
theorem program_code_sizes {args : List String} {s s' : World} {c : UInt32}
    (h : Run (program args) s c s') (h1 : c ≠ 1) (h15 : c ≠ 15) :
    ∃ evs r, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c ∧
      ∀ p n (b : ByteArray), Event.read p n (.bytes b) ∈ evs → b.size < n := by
  obtain ⟨evs, r, e1, e2, e3⟩ := (main_iff modelChecks args s s' c).1 h
  refine ⟨evs, r, e1, e2, e3, fun p n b hm => Nat.lt_of_not_le fun hn => ?_⟩
  rcases call_cut_end e1 hm hn with rfl | rfl
  · exact h1 e3.symm
  · exact h15 e3.symm

/-- Rounds of the loop `readUpTo h n` in which `Handle.read` returned bytes: from what has been
read, acc, in the state s, to bs in the state s'. Each round asks for the bytes that are still
wanted, at most `readChunk`, starts in the state that the round before left, and appends what it
got. -/
inductive Rounds (h : IO.FS.Handle) (n : Nat) : ByteArray → World → ByteArray → World → Prop where
  /-- no round -/
  | none (acc : ByteArray) (s : World) : Rounds h n acc s acc s
  /-- a round that returned bytes, and then further rounds -/
  | more {acc c bs : ByteArray} {s s1 s' : World} (hn : ¬ n ≤ acc.size)
      (hr : Run (h.read (min (n - acc.size) readChunk).toUSize) s c s1) (hc : c.isEmpty = false)
      (ht : Rounds h n (acc ++ c) s1 bs s') : Rounds h n acc s bs s'

/-- If the loop `readUpTo`, with at least as many rounds as bytes are still wanted, returned fewer
than n bytes, it made rounds, perhaps none, that returned bytes, and then, from the state that they
left, a call of `Handle.read` for the bytes still wanted, at least one and at most `readChunk`, that
returned no byte and left the loop's last state. -/
theorem readUpTo_short {h : IO.FS.Handle} {n : Nat} {bs : ByteArray} {s' : World} :
    ∀ (r : Nat) (acc : ByteArray) (s : World), n ≤ acc.size + r →
    Run (readUpTo h n r acc) s bs s' → bs.size < n →
    ∃ s1 c, Rounds h n acc s bs s1 ∧
      Run (h.read (min (n - bs.size) readChunk).toUSize) s1 c s' ∧ c.isEmpty = true
  | 0, acc, s, hr, hrun, hb => by
    obtain ⟨rfl, _⟩ := readUpTo_zero.1 hrun
    omega
  | r + 1, acc, s, hr, hrun, hb => by
    rcases readUpTo_succ.1 hrun with ⟨h0, rfl, _⟩ | ⟨hn, c, s1, h1, h2⟩
    · omega
    · rcases h2 with ⟨hc, rfl, rfl⟩ | ⟨hc, h3⟩
      · exact ⟨s, c, .none _ _, h1, hc⟩
      · have hc2 : c.size ≠ 0 := by
          intro h0
          simp [ByteArray.isEmpty, h0] at hc
        obtain ⟨s2, c2, e1, e2, e3⟩ := readUpTo_short r (acc ++ c) s1
          (by rw [ByteArray.size_append]; omega) h3 hb
        exact ⟨s2, c2, .more hn h1 hc e1, e2, e3⟩

/-- If `readIO p n` returned fewer than n bytes: `metadata` said that p is a regular file,
`Handle.mk p .read` returned a handle, the loop made rounds on that handle, perhaps none, that
returned the bytes, and then a call of `Handle.read` on it, for at least one byte, returned no byte
and left the last state. -/
theorem readIO_short {p : String} {n : Nat} {bs : ByteArray} {s s' : World}
    (h : Run (readIO p n) s (.bytes bs) s') (hb : bs.size < n) :
    ∃ md hd s1 s2 s3 c, Run (System.FilePath.metadata p) s md s1 ∧ (md.type != .file) = false ∧
      Run (IO.FS.Handle.mk p .read) s1 hd s2 ∧ Rounds hd n ByteArray.empty s2 bs s3 ∧
      Run (hd.read (min (n - bs.size) readChunk).toUSize) s3 c s' ∧ c.isEmpty = true := by
  obtain ⟨md, hd, s1, s2, h1, h2, h3, h4⟩ := readIO_bytes h
  obtain ⟨s3, c, h5, h6, h7⟩ := readUpTo_short n ByteArray.empty s2 (by simp) h4 hb
  exact ⟨md, hd, s1, s2, s3, c, h1, h2, h3, h5, h6, h7⟩

/-- Every read among steps whose answers the operations w gave is a run of `w.read`, between two
states. -/
theorem steps_read {ε σ : Type} (w : Ops (EST ε σ)) {p : String} {n : Nat} {got : FileRead} :
    ∀ (evs : List Event) (s s' : Void σ), Steps w evs s s' → Event.read p n got ∈ evs →
    ∃ sa sb, Run (w.read p n) sa got sb
  | .read p0 n0 g0 :: t, s, s', h, hm => by
    obtain ⟨s1, h1, h2⟩ := h
    cases hm with
    | head => exact ⟨s, s1, h1⟩
    | tail _ hm => exact steps_read w t s1 s' h2 hm
  | .say l ok :: t, s, s', h, hm => by
    obtain ⟨s1, _, h2⟩ := h
    cases hm with
    | tail _ hm => exact steps_read w t s1 s' h2 hm
  | .err x :: t, s, s', h, hm => by
    obtain ⟨s1, _, h2⟩ := h
    cases hm with
    | tail _ hm => exact steps_read w t s1 s' h2 hm

/-- The hypotheses of `readIO_short`, for the reads of `program_code_sizes`. If the program returns
another code than 1 and 15, every read of its run that was answered with bytes is a run of `readIO`,
between some two states, that returned fewer bytes than were asked for. -/
theorem program_code_reads {args : List String} {s s' : World} {c : UInt32}
    (h : Run (program args) s c s') (h1 : c ≠ 1) (h15 : c ≠ 15) :
    ∃ evs r, (call modelChecks args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c ∧
      ∀ p n (b : ByteArray), Event.read p n (.bytes b) ∈ evs →
        b.size < n ∧ ∃ sa sb, Run (readIO p n) sa (.bytes b) sb := by
  obtain ⟨evs, r, e1, e2, e3, e4⟩ := program_code_sizes h h1 h15
  exact ⟨evs, r, e1, e2, e3, fun p n b hm => ⟨e4 p n b hm, steps_read opsIO evs s s' e2 hm⟩⟩

end OnBytes.Shell

#print axioms OnBytes.Shell.program_code_reads
#print axioms OnBytes.Shell.readIO_short
#print axioms OnBytes.Shell.program_code_sizes
#print axioms OnBytes.Shell.call_cut_end
#print axioms OnBytes.Shell.program_sizes
#print axioms OnBytes.Shell.call_cut
#print axioms OnBytes.Shell.call_sizes
