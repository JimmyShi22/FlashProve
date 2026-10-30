-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ServedAny.lean: at the exit code 0 of verify-on-bytes the test `servedAt` holds at every
description of the run, not only at some. For proofs only; the program does not import this file.

The laws on the exit code say "there are" paths, options a and files F such that the arguments are
read as a whole call with a, and the program's operations answered the call's eight reads with F's
bytes. Two such laws give two sets of values. An operation's answer is a function of the state in
which it is asked, so both sets hold the same bytes for the first seven reads.
  `steps_read`: two runs from one state that begin with the same read got the same answer and go on
    from one state.
  `reads_same`: so two descriptions of one whole call hold the same three public files, key,
    request, reply and proof.
  `served_any`: if verify-on-bytes returns 0, then for all paths, options a and files F that
    describe the run: if a names neither -policy nor -no-proof-of-work, the user's statement at F
    and a passes `servedAt` (OnBytes/K/Served.lean) at F's own three public files.
  `pay_served`, `pay_own`: so behind every statement of the form "there are … F, a … and if the
    statement at F and a is served, then Q a F" the premise is paid at that statement's own F and a,
    whatever Q says: three pins and two options are left, or the two options alone.
  `top_paid`: a use, at `top` (OnBytes/K/Top.lean), in one line.
What is not claimed: nothing on the eighth read: the entry's number is not shown to be the same in
two descriptions. All that the head of OnBytes/K/Served.lean does not claim.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.TopServed

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event FileRead wholeReads kindOf Asked Run)

/-- Two runs from one state that begin with the same read. -/
theorem steps_read {p : String} {n : Nat} {g g' : FileRead} {t t' : List Event} {s u u' : World}
    (h : Steps opsIO (.read p n g :: t) s u) (h' : Steps opsIO (.read p n g' :: t') s u') :
    g = g' ∧ ∃ s1, Steps opsIO t s1 u ∧ Steps opsIO t' s1 u' := by
  obtain ⟨s1, r1, k1⟩ := h
  obtain ⟨s2, r2, k2⟩ := h'
  have e : EST.Out.ok g s1 = EST.Out.ok g' s2 := r1.symm.trans r2
  cases e
  exact ⟨rfl, s1, k1, k2⟩

/-- Two descriptions of one whole call hold the same bytes for the first seven reads. -/
theorem reads_same {config ivk request y proof : String} {k k' : Nat}
    {pol kl lay key req yy prf ent pol' kl' lay' key' req' yy' prf' ent' : ByteArray}
    {t t' : List Event} {s u u' : World}
    (h : Steps opsIO (wholeReads config ivk request y proof k (.bytes pol) (.bytes kl) (.bytes lay)
      (.bytes key) (.bytes req) (.bytes yy) (.bytes prf) (.bytes ent) ++ t) s u)
    (h' : Steps opsIO (wholeReads config ivk request y proof k' (.bytes pol') (.bytes kl')
      (.bytes lay') (.bytes key') (.bytes req') (.bytes yy') (.bytes prf') (.bytes ent') ++ t') s
      u') :
    pol = pol' ∧ kl = kl' ∧ lay = lay' ∧ key = key' ∧ req = req' ∧ yy = yy' ∧ prf = prf' := by
  obtain ⟨e1, _, h, h'⟩ := steps_read h h'
  obtain ⟨e2, _, h, h'⟩ := steps_read h h'
  obtain ⟨e3, _, h, h'⟩ := steps_read h h'
  obtain ⟨e4, _, h, h'⟩ := steps_read h h'
  obtain ⟨e5, _, h, h'⟩ := steps_read h h'
  obtain ⟨e6, _, h, h'⟩ := steps_read h h'
  obtain ⟨e7, _, _, _⟩ := steps_read h h'
  cases e1
  cases e2
  cases e3
  cases e4
  cases e5
  cases e6
  cases e7
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the exit code 0 `servedAt` holds at every description of the run. In words: the head of this
file. -/
theorem served_any {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') (config ivk request y proof : String) (a : Asked)
    (F : Files) (t : List Event)
    (hk : kindOf args = .whole config ivk request y proof a)
    (hs : Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
      (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
      (.bytes F.ent) ++ t) s s')
    (o1 : a.options.policy = none) (o2 : a.options.noProofOfWork = false) :
    servedAt ⟨F.pol, F.lay, F.KL⟩ (stmOf F a.options) = true := by
  obtain ⟨config', ivk', request', y', proof', a', r, lay, ent, t', p, C, table, further, id, pre,
    post, _, h1, h2, _, _, _, _, _, _, _, _, _, h12, _, h14, _, _, _, _, _, hsv⟩ :=
    main_zero_served h
  rw [hk] at h1
  cases h1
  obtain ⟨e1, e2, e3, _, e5, e6, _⟩ := reads_same hs h2
  have ho : optionsServed a.options = true := by
    unfold optionsServed
    simp [h12, h14, o1, o2]
  have hv := hsv ho
  unfold stmOf
  rw [e1, e2, e3, e5, e6]
  exact hv

/-- Pays the premise "the statement is served" behind any statement on the exit code 0 that has the
form of `top` (OnBytes/K/Top.lean), whatever its conclusion Q says of the options a and the files F:
for a notion of "served" that holds wherever `servedAt Z` is true, three pins and two options are
left. -/
theorem pay_served (Z : Pub) {Served : UserStm → Prop} (hT : ∀ x, servedAt Z x = true → Served x)
    {Q : Asked → Files → Prop} {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s')
    (hq : ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event)
      (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧ (Served (stmOf F a.options) → Q a F)) :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event)
      (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
        a.options.noProofOfWork = false → Q a F) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, h5⟩ := hq
  exact ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4,
    fun z1 z2 z3 o1 o2 => h5 (hT _ ((servedAt_pins Z _).2
      ⟨z1, z2, z3, served_any h config ivk request y proof a F t h1 h2 o1 o2⟩))⟩

/-- The same for a notion of "served" that holds wherever `servedAt` is true at the statement's own
three public files: two options are left, and no pin. -/
theorem pay_own {Served : UserStm → Prop}
    (hT : ∀ x : UserStm, servedAt ⟨x.pol, x.lay, x.KL⟩ x = true → Served x)
    {Q : Asked → Files → Prop} {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s')
    (hq : ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event)
      (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧ (Served (stmOf F a.options) → Q a F)) :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event)
      (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (a.options.policy = none → a.options.noProofOfWork = false → Q a F) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, h5⟩ := hq
  exact ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4,
    fun o1 o2 => h5 (hT _ (served_any h config ivk request y proof a F t h1 h2 o1 o2))⟩

/-- A use: `top5` (OnBytes/K/TopVC.lean has the like form) and `top` are paid in one line. -/
theorem top_paid {T : Target} (Z : Pub) (hT : ∀ x, servedAt Z x = true → T.Served x)
    (R : Reading T) (H : Holes T R) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event)
      (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
        a.options.noProofOfWork = false →
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧ T.verify (stmOf F a.options) v = true) :=
  pay_served Z hT h (top R H h)

end OnBytes.K
