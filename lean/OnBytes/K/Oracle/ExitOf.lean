-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/ExitOf.lean: from a pass of the program's own pure function on the bytes of a whole
call (`.passing = true`: YES or WITHIN LIMITS) to the exit code 0, in Lean's model of the program as
a tree of questions; and the exit code 0 both ways.

Why. `main_zero_served` (OnBytes/K/ExitServed.lean) and all that stands on it go from the exit code
0 to facts on the files' bytes. Nothing went back: that "a call ends with the exit code 0" can be
met was tied to nothing. `program` (OnBytes/Shell/Checks.lean) is `mainIO` (OnBytes/Shell/Ops.lean)
with `modelChecks`: it runs a plain value, `call modelChecks args : Ask Ending`
(OnBytes/Shell/Ask.lean, Call.lean), with the three operations of input and output. That value is a
tree of reads and printed lines. `q.Ends evs r` (OnBytes/Shell/Ends.lean) says: on the outside
world's answers in the list evs the program q asks exactly the list's questions and stops with r.
Here that tree is walked forwards at a whole call.

Main names.
  `answers`: what the outside world answers in a whole call that goes through: the eight reads are
    answered with the bytes of F, AND EVERY LINE IS TAKEN: each printed line is answered "written".
    A write that fails is another run, with another ending.
  `call_ends_of_wholeCall`: IN LEAN'S MODEL OF THE PROGRAM AS A TREE OF QUESTIONS: if the arguments
    are those of a whole call, the outside world answers the eight reads with these bytes, each file
    within the program's limit, and takes every line, the entry's number in F is the one that the
    proof file names, and the pure function `Model.Verify.wholeCall` passes on these bytes at the
    options typed, THE CALL ENDS WITH THE STATUS 0. A theorem on a plain value: none of the
    operations of input and output occurs in it.
  `status_of_passing`: `CallEnd.passing` is true of three results, and one of them, "a part has
    passed", has the exit code 3. A whole call never ends so (`cpStagesRun_whole`,
    OnBytes/K/ServedLaws.lean). So a whole call that passes has the status 0: that, under hk, is the
    statement. YES and WITHIN LIMITS alone have that status (`status_zero`,
    OnBytes/Shell/AtCall.lean).
  `main_zero_of_wholeCall`: the same at the entry function, under one hypothesis more: from the
    state s to the state s' the program's three operations gave these answers (`Steps opsIO`,
    OnBytes/Shell/AtOps.lean).
  `main_zero_iff`: `main` returns 0 from s to s' exactly if the call is a whole call and there are
    eight files' bytes, within the limits, with the entry's number that the proof file names, on
    which the pure function passes at the options typed, and which, with every line taken, the three
    operations gave from s to s'. The way there is `program_zero_kind`
    (OnBytes/Shell/AtWholeKind.lean) with laws of OnBytes/Model/VerifyLawsWhole.lean,
    VerifyLaws.lean and OnBytes/Shell/AtPart.lean.
  Tools: `fetch_ends`, `sayAll_ends`, `lastSay_ends`, `finish_ends`.

What is not claimed. THAT `wholeCall` PASSES ANY FILES: it is proved of none. THE HYPOTHESIS `Steps
opsIO ..` CAN NEVER BE DISCHARGED INSIDE LEAN, NOR REFUTED, WITHOUT A FURTHER ASSUMPTION: the three
operations are made of constants of Lean's core without a body that the kernel can unfold (they have
a hidden default, which the kernel never unfolds). That sentence is reasoning about Lean and no
theorem. In Lean it is a hypothesis on uninterpreted constants; that these are the real operations
of input and output is the compiler's binding: the seam to the outside. So no run of `main` is
exhibited, and `main_zero_iff` is an equivalence of two statements neither of which is shown of any
states. It is a statement on the term `main` in Lean's model of input and output, with the
operations uninterpreted: not on the compiled program, not on a disk, not on the C++ verifier. "The
exit code is 0 exactly if the pure function passes on what was read" says too little: see the three
riders in the docstring of `main_zero_iff`. `EntryArmO.zero` (OnBytes/K/Oracle/ArmO.lean) begins at
a run of `main`: that its premise holds of some states hangs on that hypothesis; what it concludes
of the files' bytes and of the checker is had from the pure function's pass without it
(OnBytes/K/Oracle/WholeCallO.lean [not in this library]; so here read: not proved in this library).
That a file on a disk holds these bytes.
That the compiled program does what the term says. What the heads of OnBytes/K/Oracle/WholeCall.lean
and of the files of OnBytes/Shell/ do not claim. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.WholeCall
import OnBytes.Shell.AtTie

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.Shell
open OnBytes.Model.Stages (CallEnd)
open OnBytes.Model.Verify (Options wholeCall entryNumber)

/-- A read that is answered with bytes within the limit goes on with these bytes. -/
theorem fetch_ends {L : Lists} {limit : Nat} {path : String} {next : FileRead → Ask Ending}
    {b : ByteArray} {evs : List Event} {r : Ending} (hb : b.size ≤ limit)
    (h : (next (.bytes b)).Ends evs r) :
    (fetch L limit path next).Ends (.read path (limit + 1) (.bytes b) :: evs) r := by
  unfold fetch
  refine .read ?_
  show (if b.size ≤ limit then next (.bytes b) else _).Ends evs r
  rw [if_pos hb]
  exact h

/-- Lines that are all printed with success, and then what follows. -/
theorem sayAll_ends {next : Ask Ending} {evs : List Event} {r : Ending} (h : next.Ends evs r) :
    ∀ ls : List String, (sayAll ls next).Ends (ls.map (fun l => Event.say l true) ++ evs) r
  | [] => h
  | _ :: ls => .say (sayAll_ends h ls)

/-- The last line, printed with success. -/
theorem lastSay_ends (l : String) (r : Ending) : (lastSay l r).Ends [.say l true] r :=
  .say (.done r)

/-- The lines of a passing result, all printed with success. -/
theorem finish_ends (L : Lists) (p : Fields) {e : CallEnd} (he : e.passing = true) :
    (finish L p e).Ends
      (saidAll L (before { bits := p.bits, leaf := p.leaf, leafCall := p.leafCall } e) ++
        [.say ((verdict {} e).text L) true]) (.ended e) := by
  have h := sayAll_ends (lastSay_ends ((verdict p e).text L) (.ended e))
    ((before p e).map (Line.text L))
  rw [List.map_map] at h
  have hv : verdict p e = verdict {} e := verdict_same (by cases e <;> first | rfl | cases he) p {}
  rw [← before_eq, ← hv]
  cases e <;> first | exact h | cases he

/-- A whole call that passes has the status 0. `CallEnd.passing` is also true of the result "a part
has passed", whose status is 3; a whole call never ends so (`cpStagesRun_whole`,
OnBytes/K/ServedLaws.lean). -/
theorem status_of_passing {o : Options} {F : Files}
    (hk : entryNumber o (callOf F) = .ok F.entry)
    (hp : (wholeCall o (callOf F)).passing = true) : (wholeCall o (callOf F)).status = 0 := by
  have hp' : (wholeCall o { callOf F with entry := some F.ent }).passing = true := hp
  cases hw : wholeCall o (callOf F) with
  | yes a c => rfl
  | withinLimits a c => rfl
  | partPassed s c =>
    exfalso
    obtain ⟨r, ent, _, _, _, _, g1, _, g3, _⟩ := Model.Verify.wholeCall_passed hk hp'
    unfold wholeCall at hw
    rw [g1] at hw
    dsimp only [callOf] at hw
    exact cpStagesRun_whole hw
  | notVer a b c => rw [hw] at hp; cases hp
  | refusedBy a b c => rw [hw] at hp; cases hp
  | wrongId => rw [hw] at hp; cases hp
  | policy a => rw [hw] at hp; cases hp
  | no a => rw [hw] at hp; cases hp
  | notChecked a => rw [hw] at hp; cases hp
  | unreadable a => rw [hw] at hp; cases hp
  | usage a => rw [hw] at hp; cases hp

/-- What the outside world answers in a whole call that goes through: the eight reads are answered
with the bytes of F, and every line of the result e is answered "written". The list is that of
`program_yes` (OnBytes/Shell/AtTie.lean), at reads that are answered with bytes. -/
def answers (config ivk request y proof : String) (bits : Nat) (F : Files) (e : CallEnd) :
    List Event :=
  wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL) (.bytes F.lay)
      (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof) (.bytes F.ent) ++
    (saidAll modelChecks.lists (before { bits := bits, leaf := F.entry } e) ++
      [.say ((verdict {} e).text modelChecks.lists) true])

/-- In Lean's model of the program as a tree of questions: if the arguments are those of a whole
call, the entry's number in F is the one that the proof file names (hk), the pure function passes on
the eight files' bytes at the options typed (YES or WITHIN LIMITS), and the files are within the
program's limits, then on the answers `answers ..` (the eight reads answered with these bytes, every
line taken) the call ends with the pure function's result, and its status is 0. A statement on a
plain value. -/
theorem call_ends_of_wholeCall {args : List String} {config ivk request y proof : String}
    {a : Asked} (hkind : kindOf args = .whole config ivk request y proof a) {F : Files}
    (hk : entryNumber a.options (callOf F) = .ok F.entry)
    (hp : (wholeCall a.options (callOf F)).passing = true) (hw : Within F) :
    (call modelChecks args).Ends
      (answers config ivk request y proof a.options.bits F (wholeCall a.options (callOf F)))
      (.ended (wholeCall a.options (callOf F))) ∧
    (Ending.ended (wholeCall a.options (callOf F))).status = 0 := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  refine ⟨?_, status_of_passing hk hp⟩
  unfold call
  rw [hkind]
  show (whole modelChecks config ivk request y proof a).Ends _ _
  unfold whole answers wholeReads
  refine fetch_ends w3 (fetch_ends w5 (fetch_ends w4 (fetch_ends w1 (fetch_ends w6
    (fetch_ends w7 (fetch_ends w8 ?_))))))
  have hk' : modelChecks.entryNumber a.options
      { policy := fileIn (.bytes F.pol), KL := fileIn (.bytes F.KL),
        layout := layoutIn (.bytes F.lay), key := fileIn (.bytes F.key),
        request := fileIn (.bytes F.request), y := fileIn (.bytes F.y),
        proof := fileIn (.bytes F.proof) } = .ok F.entry := hk
  simp only [hk']
  refine fetch_ends w2 ?_
  exact finish_ends modelChecks.lists _ hp

/-- The same at the entry function, under the same premises (hk among them: the entry's number in F
is the one that the proof file names): if moreover the program's three operations gave these answers
from the state s to the state s', `main` returns 0 from s to s'. That hypothesis can be neither
discharged nor refuted inside Lean without a further assumption: see the head. -/
theorem main_zero_of_wholeCall {args : List String} {config ivk request y proof : String}
    {a : Asked} (hkind : kindOf args = .whole config ivk request y proof a) {F : Files}
    (hk : entryNumber a.options (callOf F) = .ok F.entry)
    (hp : (wholeCall a.options (callOf F)).passing = true) (hw : Within F) {s s' : World}
    (hs : Steps opsIO
      (answers config ivk request y proof a.options.bits F (wholeCall a.options (callOf F))) s s') :
    Shell.Run (_root_.main args) s 0 s' := by
  obtain ⟨h1, h2⟩ := call_ends_of_wholeCall hkind hk hp hw
  rw [Shell.main_eq]
  exact (main_iff modelChecks args s s' 0).2 ⟨_, _, h1, hs, h2⟩

/-- The exit code 0, both ways: `main` returns 0 from s to s' exactly if there are eight files'
bytes such that all of the following hold. (i) Every line of the result was written: on the same
bytes a write that fails ends otherwise. (ii) All eight reads gave bytes within the program's
limits: above a limit the pure function is not called. (iii) The call is a whole call, the pure
function passes at the options typed, and the entry's number is the one that the proof file names. A
gloss on (iii): a pass is YES or WITHIN LIMITS. In the statement (i) and the reads of (ii) stand in
one clause: the program's three operations gave these answers from s to s' (`Steps opsIO`); the
limits are `Within F`. The statement is on the term `main` in Lean's model of input and output, with
the operations uninterpreted: not on the compiled program, not on a disk, not on the C++ verifier.
-/
theorem main_zero_iff {args : List String} {s s' : World} :
    Shell.Run (_root_.main args) s 0 s' ↔
      ∃ (config ivk request y proof : String) (a : Asked) (F : Files),
        kindOf args = .whole config ivk request y proof a ∧
        entryNumber a.options (callOf F) = .ok F.entry ∧
        (wholeCall a.options (callOf F)).passing = true ∧ Within F ∧
        Steps opsIO
          (answers config ivk request y proof a.options.bits F (wholeCall a.options (callOf F)))
          s s' := by
  constructor
  · intro h
    rw [Shell.main_eq] at h
    obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, e, l, k1, _,
      h2, hkd, k2, k3, sz⟩ := program_zero_kind h
    have hpass : e.passing = true := by
      obtain ⟨ab, cl, ⟨e1, _⟩ | ⟨e1, _⟩⟩ := hkd <;> rw [e1] <;> rfl
    have hl : l = (verdict {} e).text modelChecks.lists := by
      obtain ⟨ab, cl, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := hkd <;> rw [e1, e2] <;> rfl
    subst hl
    subst k3
    obtain ⟨r, entb, p, C, table, further, g1, g2, g3, g4, _⟩ :=
      Model.Verify.wholeCall_passed k2 hpass
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Model.Verify.readCall_ok g1
    obtain ⟨layb, hlay⟩ := Model.Verify.planned_layout g4
    rw [hlay] at f3
    cases fileIn_some f1
    cases fileIn_some f2
    cases layoutIn_some f3
    cases fileIn_some f4
    cases fileIn_some f5
    cases fileIn_some f6
    cases fileIn_some f7
    cases fileIn_some g3
    subst g2
    refine ⟨config, ivk, request, y, proof, a,
      ⟨r.pol, layb, r.KL, r.key, entb, r.request, r.y, r.proof, r.entry⟩, k1, k2, hpass, ?_, h2⟩
    exact ⟨Nat.le_of_lt_succ (sz (ivk ++ "/key.bin") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (ivk ++ "/leaf/" ++ toString r.entry ++ ".bin") _ _
        (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (config ++ "/policy.txt") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (config ++ "/layout.txt") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (config ++ "/KL.bin") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz request _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz y _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz proof _ _ (by simp [wholeReads]))⟩
  · rintro ⟨config, ivk, request, y, proof, a, F, h1, h2, h3, h4, h5⟩
    exact main_zero_of_wholeCall h1 h2 h3 h4 h5

end OnBytes.K.Oracle
