-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/SpineOptions.lean: two laws on the options of a whole call of
`OnBytes.Model.Verify.wholeCall`, the library's pure function of a whole call.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean). What they are for: a
verifier written over the whole call's twin (Johnson/Top/PortWritten.lean [not in this library])
runs at options of one form: the ID in lower-case digits, 128 bits, no other option. A run of the
program has its own options: its ID may be typed in capitals, and it may have asked for the next
token alone. The two laws carry a result from the one to the other (Johnson/Top/SpineWritten.lean
[not in this library]).

Main theorems.
  `idAsked_idem`: what the program reads an ID as, it reads as itself.
  `wholeCall_sameId`: THE FIRST LAW: the whole call takes the ID through `idAsked` (and through
    whether one is named at all): two spellings that the program reads as one give one result.
  `wholeCall_next`: THE SECOND LAW: a whole call that passes with -next-token has the same result
    without it: the option only adds a test. (Its premise that the first tests name a number follows
    from the pass; it is asked all the same.)

Limits: both laws are of `OnBytes.Model.Verify.wholeCall`, with the program's own hash functions
inside: nothing on the twin at a letter: at another g nothing is carried from one set of options to
another. The second law goes one way: from a pass with the option to the same result without it.
Nothing on -policy, the bits or -no-proof-of-work. That any call passes is not shown. Nothing on
soundness. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.ExitRequest

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Verify

/-! ## The ID's case -/

/-- A digit of base 16 in lower case is no capital from A to F. -/
theorem lower_keeps (c : Char) (h : (c.isDigit || ('a' ≤ c && c ≤ 'f')) = true) :
    ('A' ≤ c && c ≤ 'F') = false := by
  have e1 : ('A' : Char).val.toNat = 65 := rfl
  have e2 : ('F' : Char).val.toNat = 70 := rfl
  have e3 : ('a' : Char).val.toNat = 97 := rfl
  have e4 : ('f' : Char).val.toNat = 102 := rfl
  simp only [Char.isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
    UInt32.le_iff_toNat_le, ge_iff_le] at h
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.le_def, UInt32.le_iff_toNat_le]
  have e5 : ('0' : Char).val.toNat = 48 := rfl
  have e6 : ('9' : Char).val.toNat = 57 := rfl
  omega

/-- What the program reads an ID as, it reads as itself. -/
theorem idAsked_idem {t x : String} (h : idAsked t = some x) : idAsked x = some x := by
  unfold idAsked at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    generalize hl : (t.toList.map fun c => if ('A' ≤ c && c ≤ 'F') = true then c.toLower else c) = l
      at hc
    have hc' := hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc'
    have hm : (l.map fun c => if ('A' ≤ c && c ≤ 'F') = true then c.toLower else c) = l := by
      conv => rhs; rw [← List.map_id l]
      refine List.map_congr_left fun c hcl => ?_
      rw [lower_keeps c (hc'.2 c hcl)]
      rfl
    unfold idAsked
    dsimp only
    rw [String.toList_ofList, hm]
    rw [if_pos hc]
  · cases h

/-- The first tests of a call take the ID through `idAsked` alone. -/
theorem readFirst_sameId {o : Options} {t t' : String} (f : Files)
    (n : Bool) (ho : o.id = some t) (e : idAsked t' = idAsked t) :
    readFirst { o with id := some t' } f n = readFirst o f n := by
  unfold readFirst
  simp only [ho, e, Option.isSome_some]

/-- **The whole call takes the ID through `idAsked` alone**: two spellings that the program reads as
one give one result. -/
theorem wholeCall_sameId {o : Options} {t t' : String} (f : Files)
    (ho : o.id = some t) (e : idAsked t' = idAsked t) :
    OnBytes.Model.Verify.wholeCall { o with id := some t' } f =
      OnBytes.Model.Verify.wholeCall o f := by
  have hr : readCall { o with id := some t' } f = readCall o f := by
    unfold readCall
    rw [readFirst_sameId f true ho e]
  unfold OnBytes.Model.Verify.wholeCall
  rw [hr]
  rfl

/-! ## The option -next-token -/

/-- A bind in `Except`, what follows being compared only at a value that the first step returns. -/
theorem bind_congr_ok {ε α β : Type} {x : Except ε α} {f g : α → Except ε β}
    (h : ∀ a, x = .ok a → f a = g a) : (x >>= f) = (x >>= g) := by
  cases x with
  | error e => rfl
  | ok a => exact h a rfl

/-- The stage request up to the verdict reads -next-token in the list of missed conditions alone. -/
theorem requestRun_next (C : Common) (o : Options) (r : Read) (entry : ByteArray)
    (hf : ∀ so cov, Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so →
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov →
      servedForm (servedOf C { o with nextToken := false } r.layout.isSome so cov) =
        servedForm (servedOf C o r.layout.isSome so cov)) :
    requestRun C { o with nextToken := false } r entry = requestRun C o r entry := by
  unfold requestRun
  dsimp only
  refine bind_congr_ok fun _ _ => ?_
  refine bind_congr_ok fun so hso => ?_
  refine bind_congr_ok fun cov hcov => ?_
  rw [hf so cov hso hcov]

/-- Where no condition is missed with -next-token, none is missed without it. -/
theorem servedForm_next {C : Common} {o : Options} {l : Bool} {so : Head.StOwn}
    {cov : Head.Covered} (h : servedForm (servedOf C o l so cov) = []) :
    servedForm (servedOf C { o with nextToken := false } l so cov) = [] := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, -, a20,
    a21⟩ := (K.servedForm_nil _).1 h
  exact (K.servedForm_nil _).2 ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, rfl, a20, a21⟩

/-- **A whole call that passes with -next-token has the same result without it**: the option only
adds a test. -/
theorem wholeCall_next {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (hp : (OnBytes.Model.Verify.wholeCall o { f with entry := entry }).passing = true) :
    OnBytes.Model.Verify.wholeCall { o with nextToken := false } { f with entry := entry } =
      OnBytes.Model.Verify.wholeCall o { f with entry := entry } := by
  obtain ⟨r, ent, p, C, _, _, g1, _, g3, _, g5, _⟩ := wholeCall_passed hk hp
  obtain ⟨_, _, ⟨a3, w3, q3⟩, _⟩ := wholeCall_stages hp g1 g3 g5
  obtain ⟨so, cov, _, _, _, c1, c2, _, _, c6, _⟩ := requestStage_passed q3
  have hrun : requestRun C { o with nextToken := false } r ent = requestRun C o r ent := by
    refine requestRun_next C o r ent fun so' cov' e1 e2 => ?_
    obtain rfl : so = so' := Except.ok.inj (c1.symm.trans e1)
    obtain rfl : cov = cov' := Except.ok.inj (c2.symm.trans e2)
    rw [c6, servedForm_next c6]
  have hst : requestStage C { o with nextToken := false } r ent = requestStage C o r ent := by
    unfold requestStage
    rw [hrun]
  have hall : stagesOf { o with nextToken := false } r ent = stagesOf o r ent := by
    unfold stagesOf
    rw [g5]
    dsimp only
    rw [hst]
  subst g3
  unfold OnBytes.Model.Verify.wholeCall
  have hr : readCall { o with nextToken := false } { f with entry := some ent } =
      readCall o { f with entry := some ent } := rfl
  rw [hr, readCall_entry, g1]
  dsimp only
  rw [hall]

end OnBytes.K.Oracle
