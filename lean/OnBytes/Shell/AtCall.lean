-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtCall.lean: what every run of the program prints and reads.

The program is the value `call C args` (OnBytes/Shell/Call.lean), where C holds the checks on a
model's files. Each main theorem but `status_zero` is first a property of the tree (`Honest`,
`Bounded`, `Plain`), proved for all arguments and all C. The program is gone through once, in
`kept_call`: a property that the smallest parts of the program keep (`Kept`) holds of the program.

Main theorems.
- `call_last`: the last step of a run of `call C args` prints the last line of its ending, with
  success, unless the run ends in a fault or with an unwritten answer.
- `status_zero`: the exit code of an ending is 0 only if the ending is a yes or a result within
  limits.
- `call_reads`: every read in a run of `call C args` asks for one byte more than `fileLimit`,
  `textLimit` or `listLimit`.
- `call_says`: every line that a run of `call C args` prints on standard output is `Line.text` of
  some line, under the lists `C.lists`. So the only file content that reaches standard output is the
  fields of these lines, in the forms that OnBytes/Shell/Lines.lean gives them.

What is not claimed. Nothing about the checks themselves. Nothing on standard error, where the usage
text and paths from the arguments are written. Nothing about compiled code, Lean's run-time or the
operating system: the theorems are about the value `call C args`, not about what a process does
before or beside it, such as the start of Lean's run-time. How the runs of this file relate to the
program in IO is in OnBytes/Shell/AtMain.lean. For proofs only; the program does not import this
file.
-/
import OnBytes.Shell.Call
import OnBytes.Shell.Ends

namespace OnBytes.Shell

open OnBytes.Model.Stages (CallEnd)

/-! ## Going through the program once -/

/-- The property Φ holds of the smallest parts of the program and is kept by its steps. -/
structure Kept (L : Lists) (Φ : Ask Ending → Prop) : Prop where
  /-- the last line of a result -/
  last : ∀ p e, Φ (lastSay ((verdict p e).text L) (.ended e))
  /-- a fault -/
  fault : ∀ w, Φ (faultWith w)
  /-- an answer that cannot be written -/
  unwritten : Φ unwritten
  /-- a read of one byte more than one of the three limits -/
  read : ∀ p m next, m = fileLimit ∨ m = textLimit ∨ m = listLimit → (∀ r, Φ (next r)) →
    Φ (.read p (m + 1) next)
  /-- a line before the last -/
  line : ∀ (x : Line) next, Φ next →
    Φ (.say (x.text L) fun ok => if ok then next else Shell.unwritten)
  /-- the last step of a planning call -/
  planEnd : Φ (lastSay (Line.planOnly.text L) .planned)
  /-- the last step of a call on test files that found no fault -/
  testEnd : Φ (lastSay (Line.testPassed.text L) .testPassed)

variable {L : Lists} {Φ : Ask Ending → Prop}

/-- Lines before the last line keep the property. -/
theorem kept_lines (K : Kept L Φ) {next : Ask Ending} (h : Φ next) :
    ∀ xs : List Line, Φ (sayAll (xs.map (Line.text L)) next)
  | [] => h
  | x :: xs => K.line x _ (kept_lines K h xs)

/-- The end of a call keeps the property. -/
theorem Kept.finish (K : Kept L Φ) (p : Fields) (e : CallEnd) : Φ (finish L p e) := by
  cases e <;> first | exact K.fault _ | exact kept_lines K (K.last p _) _

/-- The end of a call on test files in which no check failed keeps the property. -/
theorem Kept.finishWork (K : Kept L Φ) (w : Work) : Φ (finishWork L w) := by
  cases w with
  | error name => exact K.finish {} (.no name)
  | ok o => exact kept_lines K K.testEnd [.work o.1 o.2]

/-- The end of a call on test files keeps the property. -/
theorem Kept.finishTest (K : Kept L Φ) (w : Work) (x : Verdict) :
    Φ (finishTest L w x) := by
  cases x with
  | accepted => exact K.finishWork w
  | refused r => exact K.finish {} (.no r.check)

/-- A read with its test of the length keeps the property. -/
theorem kept_fetchTo (K : Kept L Φ) {m : Nat} (hm : m = fileLimit ∨ m = textLimit ∨ m = listLimit)
    {p : String} {next : FileRead → Ask Ending} (h : ∀ r, Φ (next r)) : Φ (fetch L m p next) := by
  refine K.read p m _ hm fun r => ?_
  cases r with
  | bytes b =>
    show Φ (if b.size ≤ m then next (.bytes b) else Shell.finish L {} _)
    split
    · exact h _
    · exact K.finish _ _
  | absent => exact h _
  | unreadable u => exact h _

/-- A read under `fileLimit`, the limit of the binary files of a model, keeps the property. -/
theorem kept_fetch (K : Kept L Φ) {p : String} {next : FileRead → Ask Ending}
    (h : ∀ r, Φ (next r)) : Φ (fetch L fileLimit p next) := kept_fetchTo K (Or.inl rfl) h

/-- A read under `textLimit`, the limit of a configuration's two text files, keeps the property. -/
theorem kept_text (K : Kept L Φ) {p : String} {next : FileRead → Ask Ending}
    (h : ∀ r, Φ (next r)) : Φ (fetch L textLimit p next) := kept_fetchTo K (Or.inr (Or.inl rfl)) h

/-- A read under `listLimit`, the limit of a test protocol's files, keeps the property. -/
theorem kept_list (K : Kept L Φ) {p : String} {next : FileRead → Ask Ending}
    (h : ∀ r, Φ (next r)) : Φ (fetch L listLimit p next) := kept_fetchTo K (Or.inr (Or.inr rfl)) h

/-- The read of a file that is needed keeps the property. -/
theorem kept_need (K : Kept L Φ) {p : String} {next : ByteArray → Ask Ending}
    (h : ∀ b, Φ (next b)) : Φ (need L p next) := by
  refine kept_list K fun r => ?_
  cases r with
  | bytes b => exact h b
  | absent => exact K.fault _
  | unreadable u => exact K.fault _

/-- The reads of several files that are needed keep the property. -/
theorem kept_needAll (K : Kept L Φ) : ∀ (ps : List String) (got : List ByteArray)
    (next : List ByteArray → Ask Ending), (∀ l, Φ (next l)) → Φ (needAll L ps got next)
  | [], got, _, h => h got
  | _ :: ps, got, next, h => kept_need K fun b => kept_needAll K ps (got ++ [b]) next h

/-- A call on test files keeps the property. -/
theorem kept_judgeFiles (K : Kept L Φ) (ps : List String) (notes : List Note)
    (v : List ByteArray → Option Verdict)
    (w : List ByteArray → Work) : Φ (judgeFiles L ps notes v w) := by
  refine kept_needAll K ps [] _ fun l => ?_
  show Φ (match v l with
    | some x => sayAll (notes.map fun n => (Line.note n).text L) (Shell.finishTest L (w l) x)
    | none => faultWith "verify-on-bytes: internal fault")
  split
  · rename_i x _
    have h := kept_lines K (K.finishTest (w l) x) (notes.map Line.note)
    rw [List.map_map] at h
    exact h
  · exact K.fault _

/-- A planning call keeps the property. -/
theorem kept_planCall (C : Checks) (K : Kept C.lists Φ) (config : String) (bits : Nat) :
    Φ (planCall C config bits) := by
  refine kept_text K fun _ => kept_fetch K fun _ => kept_text K fun _ => ?_
  split
  · exact K.finish _ _
  · exact kept_lines K K.planEnd _

/-- A whole call keeps the property. -/
theorem kept_whole (C : Checks) (K : Kept C.lists Φ) (config ivk request y proof : String)
    (a : Asked) : Φ (whole C config ivk request y proof a) := by
  unfold whole
  refine kept_text K fun _ => kept_fetch K fun _ => kept_text K fun _ => kept_fetch K fun _ =>
    kept_fetch K fun _ => kept_fetch K fun _ => kept_fetch K fun _ => ?_
  dsimp only
  split
  · exact K.finish _ _
  · exact kept_fetch K fun _ => K.finish _ _

/-- A call on a key file alone keeps the property. -/
theorem kept_keyPart (C : Checks) (K : Kept C.lists Φ) (config key : String) (a : Asked) :
    Φ (keyPart C config key a) :=
  kept_text K fun _ => kept_fetch K fun _ => kept_text K fun _ => kept_fetch K fun _ =>
    K.finish _ _

/-- A call on an entry file alone keeps the property. -/
theorem kept_leafPart (C : Checks) (K : Kept C.lists Φ) (config key entry : String) (a : Asked) :
    Φ (leafPart C config key entry a) :=
  kept_text K fun _ => kept_fetch K fun _ => kept_text K fun _ => kept_fetch K fun _ =>
    kept_fetch K fun _ => K.finish _ _

/-- A property that the smallest parts keep holds of the program, for all arguments. -/
theorem kept_call (C : Checks) (K : Kept C.lists Φ) (args : List String) : Φ (call C args) := by
  unfold call
  cases kindOf args with
  | toy paths notes v w => exact kept_judgeFiles K _ _ _ _
  | whole config ivk request y proof a => exact kept_whole C K _ _ _ _ _ _
  | keyPart config key a => exact kept_keyPart C K _ _ _
  | leafPart config key entry a => exact kept_leafPart C K _ _ _ _
  | plan config bits => exact kept_planCall C K _ _
  | bad words => exact K.fault _

/-! ## The last line -/

/-- The line l is the last line of a call that ends with r, for some `Fields`: so the reason printed
for an unreadable input is left open. A fault and an answer that could not be written have none. -/
def Last (L : Lists) (l : String) : Ending → Prop
  | .ended e => ∃ p, l = (verdict p e).text L
  | .testPassed => l = Line.testPassed.text L
  | .planned => l = Line.planOnly.text L
  | .fault => False
  | .unwritten => False

/-- If q stops in anything but a fault or an unwritten answer, the step before printed the last line
of its ending. -/
def Honest (L : Lists) : Ask Ending → Prop
  | .done r => r = .fault ∨ r = .unwritten
  | .read _ _ next => ∀ got, Honest L (next got)
  | .say l next => (∀ ok, Honest L (next ok)) ∨
      ∃ r, Last L l r ∧ next true = .done r ∧ Honest L (next false)
  | .err _ next => Honest L next

/-- What `Honest` says of runs. -/
theorem honest_ends : ∀ (q : Ask Ending), Honest L q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → r ≠ .fault → r ≠ .unwritten →
    ∃ pre l, evs = pre ++ [.say l true] ∧ Last L l r := by
  intro q
  induction q with
  | done r0 =>
    intro h evs r hr n1 n2
    obtain ⟨_, rfl⟩ := ends_done hr
    rcases h with h | h
    · exact absurd h n1
    · exact absurd h n2
  | read p0 n0 next ih =>
    intro h evs r hr n1 n2
    obtain ⟨got, t, rfl, h2⟩ := ends_read hr
    obtain ⟨pre, l, rfl, hl⟩ := ih got (h got) t r h2 n1 n2
    exact ⟨_ :: pre, l, rfl, hl⟩
  | say l0 next ih =>
    intro h evs r hr n1 n2
    obtain ⟨ok, t, rfl, h2⟩ := ends_say hr
    rcases h with h | ⟨r0, hl0, h3, h4⟩
    · obtain ⟨pre, l, rfl, hl⟩ := ih ok (h ok) t r h2 n1 n2
      exact ⟨_ :: pre, l, rfl, hl⟩
    · cases ok with
      | true =>
        rw [h3] at h2
        obtain ⟨rfl, rfl⟩ := ends_done h2
        exact ⟨[], l0, rfl, hl0⟩
      | false =>
        obtain ⟨pre, l, rfl, hl⟩ := ih false h4 t r h2 n1 n2
        exact ⟨_ :: pre, l, rfl, hl⟩
  | err x next ih =>
    intro h evs r hr n1 n2
    obtain ⟨t, rfl, h2⟩ := ends_err hr
    obtain ⟨pre, l, rfl, hl⟩ := ih h t r h2 n1 n2
    exact ⟨_ :: pre, l, rfl, hl⟩

/-- An answer that cannot be written is honest. -/
theorem honest_unwritten : Honest L unwritten := Or.inr rfl

/-- Printing l and then ending with r is honest if l is the last line of r. -/
theorem honest_lastSay {l : String} {r : Ending} (h : Last L l r) : Honest L (lastSay l r) :=
  Or.inr ⟨r, h, rfl, honest_unwritten⟩

/-- The smallest parts are honest. -/
theorem kept_honest (L : Lists) : Kept L (Honest L) where
  last p _ := honest_lastSay ⟨p, rfl⟩
  fault _ := Or.inl rfl
  unwritten := honest_unwritten
  read _ _ _ _ h := h
  line _ _ h := Or.inl fun ok => by
    cases ok with
    | true => exact h
    | false => exact honest_unwritten
  planEnd := honest_lastSay rfl
  testEnd := honest_lastSay rfl

/-- The last step of a run prints the last line of its ending, with success, unless the run ends in
a fault or with an unwritten answer. -/
theorem call_last {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) (n1 : r ≠ .fault) (n2 : r ≠ .unwritten) :
    ∃ pre l, evs = pre ++ [.say l true] ∧ Last C.lists l r :=
  honest_ends _ (kept_call C (kept_honest _) args) evs r h n1 n2

/-- The exit code of an ending is 0 only if the ending is a yes or a result within limits. The
theorem is on the number that `main` returns. An operating system's shell sees that number modulo
256. Every exit code of this program is one of 0, 1, 2, 3, 4, 5, 14, 15 (`Ending.status`,
`CallEnd.status`); that all are below 256 is `status_small` (OnBytes/Shell/AtMain.lean). -/
theorem status_zero {r : Ending} (h : r.status = 0) :
    ∃ a c, r = .ended (.yes a c) ∨ r = .ended (.withinLimits a c) := by
  cases r with
  | fault => cases h
  | unwritten => cases h
  | ended e =>
    cases e with
    | yes a c => exact ⟨a, c, Or.inl rfl⟩
    | withinLimits a c => exact ⟨a, c, Or.inr rfl⟩
    | partPassed s c => cases h
    | notVer cs a c => cases h
    | refusedBy s w n => cases h
    | wrongId => cases h
    | policy w => cases h
    | no n => cases h
    | notChecked n => cases h
    | unreadable role => cases h
    | usage w => cases h
  | testPassed => cases h
  | planned => cases h

/-! ## The reads -/

/-- Every read asks for one byte more than one of the three limits. -/
def Bounded : Ask Ending → Prop
  | .done _ => True
  | .read _ n next => (n = fileLimit + 1 ∨ n = textLimit + 1 ∨ n = listLimit + 1) ∧
      ∀ got, Bounded (next got)
  | .say _ next => ∀ ok, Bounded (next ok)
  | .err _ next => Bounded next

/-- What `Bounded` says of runs. -/
theorem bounded_ends : ∀ (q : Ask Ending), Bounded q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → ∀ p n got, Event.read p n got ∈ evs →
    n = fileLimit + 1 ∨ n = textLimit + 1 ∨ n = listLimit + 1 := by
  intro q
  induction q with
  | done r0 =>
    intro _ evs r hr p n got hm
    obtain ⟨rfl, _⟩ := ends_done hr
    cases hm
  | read p0 n0 next ih =>
    intro h evs r hr p n got hm
    obtain ⟨got0, t, rfl, h2⟩ := ends_read hr
    cases hm with
    | head => exact h.1
    | tail _ hm => exact ih got0 (h.2 got0) t r h2 p n got hm
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

/-- The last step of a call reads nothing. -/
theorem bounded_lastSay (l : String) (r : Ending) : Bounded (lastSay l r) := fun ok => by
  cases ok <;> exact trivial

/-- The smallest parts are bounded. -/
theorem kept_bounded (L : Lists) : Kept L Bounded where
  last _ _ := bounded_lastSay _ _
  fault _ := trivial
  unwritten := trivial
  read _ _ _ hm h := ⟨hm.elim (fun e => Or.inl (by rw [e])) fun h2 =>
    h2.elim (fun e => Or.inr (Or.inl (by rw [e]))) fun e => Or.inr (Or.inr (by rw [e])), h⟩
  line _ _ h := fun ok => by
    cases ok with
    | true => exact h
    | false => exact trivial
  planEnd := bounded_lastSay _ _
  testEnd := bounded_lastSay _ _

/-- Every read in a run asks for one byte more than one of the three limits. -/
theorem call_reads {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {p : String} {n : Nat} {got : FileRead}
    (hm : Event.read p n got ∈ evs) :
    n = fileLimit + 1 ∨ n = textLimit + 1 ∨ n = listLimit + 1 :=
  bounded_ends _ (kept_call C (kept_bounded _) args) evs r h p n got hm

/-! ## The printed lines -/

/-- Every line that the program prints on standard output is the text of a `Line`. -/
def Plain (L : Lists) : Ask Ending → Prop
  | .done _ => True
  | .read _ _ next => ∀ got, Plain L (next got)
  | .say l next => (∃ x : Line, l = x.text L) ∧ ∀ ok, Plain L (next ok)
  | .err _ next => Plain L next

/-- What `Plain` says of runs. -/
theorem plain_ends : ∀ (q : Ask Ending), Plain L q → ∀ (evs : List Event) (r : Ending),
    q.Ends evs r → ∀ l ok, Event.say l ok ∈ evs → ∃ x : Line, l = x.text L := by
  intro q
  induction q with
  | done r0 =>
    intro _ evs r hr l ok hm
    obtain ⟨rfl, _⟩ := ends_done hr
    cases hm
  | read p0 n0 next ih =>
    intro h evs r hr l ok hm
    obtain ⟨got0, t, rfl, h2⟩ := ends_read hr
    cases hm with
    | tail _ hm => exact ih got0 (h got0) t r h2 l ok hm
  | say l0 next ih =>
    intro h evs r hr l ok hm
    obtain ⟨ok0, t, rfl, h2⟩ := ends_say hr
    cases hm with
    | head => exact h.1
    | tail _ hm => exact ih ok0 (h.2 ok0) t r h2 l ok hm
  | err x next ih =>
    intro h evs r hr l ok hm
    obtain ⟨t, rfl, h2⟩ := ends_err hr
    cases hm with
    | tail _ hm => exact ih h t r h2 l ok hm

/-- The last step of a call that prints a line's text is plain. -/
theorem plain_lastSay (x : Line) (r : Ending) : Plain L (lastSay (x.text L) r) :=
  ⟨⟨x, rfl⟩, fun ok => by cases ok <;> exact trivial⟩

/-- The smallest parts are plain. -/
theorem kept_plain (L : Lists) : Kept L (Plain L) where
  last _ _ := plain_lastSay _ _
  fault _ := trivial
  unwritten := trivial
  read _ _ _ _ h := h
  line x _ h := ⟨⟨x, rfl⟩, fun ok => by
    cases ok with
    | true => exact h
    | false => exact trivial⟩
  planEnd := plain_lastSay _ _
  testEnd := plain_lastSay _ _

/-- Every line that a run prints on standard output is the text of a `Line`. -/
theorem call_says {C : Checks} {args : List String} {evs : List Event} {r : Ending}
    (h : (call C args).Ends evs r) {l : String} {ok : Bool} (hm : Event.say l ok ∈ evs) :
    ∃ x : Line, l = x.text C.lists :=
  plain_ends _ (kept_call C (kept_plain _) args) evs r h l ok hm

end OnBytes.Shell

#print axioms OnBytes.Shell.call_last
#print axioms OnBytes.Shell.call_reads
#print axioms OnBytes.Shell.call_says
