-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FitSilent.lean: the tests on the three silent rounds' messages of a key file and
of a proof file, and that the data of OnBytes/Maker/Page/Silent.lean (`silentKey`, `silentProof`)
meet the laws of OnBytes/Maker/Page/FitAt.lean (`SilentLaws`) under them.

Definitions that compute, statements and proofs. The bytes of a chain's statement do not hold every
field of the typed first query: of the outer roots they hold the first alone; a key file's first
statement holds neither the instance nor the stored copy's number; a proof file's holds the instance
through the letter req. So the tests pin these fields, by nothing that hangs on a file:
  the outer roots are the first of them and then `tl` of it and of THE MESSAGE's answers, for a
    fixed function tl (for a key file: the code of the answers; for a proof file: the first root
    once more, and then that code);
  a key file: no instance; the copy's number is 0;
  a proof file: an instance that passes a test okX; each of its two strings has fewer than 2^64 - 8
    bytes; the copy's number is below 2^64.

Main names:
  `undoes_cancel`, `table_ok`, `table_cancel`: the item "table" at the head of a statement gives
    back root and answers, by the library's readers (Fmt/Rules1Laws.lean, Fmt/ChainStmLaws.lean).
  `cmsFit`, `tableSmall`: two tests. `cmsFit_eq`.
  `fFrontK`, `fFrontP`, `fJoin`, `fSeam`: the tests on the messages.
  The fourth item gives back its value by `Fmt.undoes_wordsItem` (Fmt/ChainStmLaws.lean).
  `silentKey_laws`, `silentProof_laws`, `silentProof_laws_words`: `SilentLaws`.
req gives two strings: `.1` the value of the item "request", `.2` the request file's bytes.
Premise of `silentProof_laws`: req is one to one on the instances that pass okX (hreq).
`silentProof_laws_words` asks that of the second string alone (hw): the stronger premise; it has no
caller. req and okX are letters: that any req and a test okX that all real requests pass meet either
premise is not shown here; where hreq fails the law says nothing. The first string as the programs
spell it holds the request as one digest of the second hash function: alone it is not one to one
under a test that all
real requests pass, by counting. A request file says neither the reply nor what else a type of
instances holds: okX has to pin these. Both premises hold by themselves where okX lets one instance
through.
No letter stands under "there is".

What is not claimed. That a verifier's first queries pass the tests: in particular that the silent
messages bear the answers of the record that the verifier is handed. Nothing on strings, on any
hash, on soundness.


-/
import OnBytes.Maker.Page.FitAt
import OnBytes.Maker.Page.Silent
import Fmt.ChainStmLaws

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run
open _root_.Iop (Dig)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.Maker (FrontMsg)
open OnBytes.Tie (u64n_inj undoes_ext3)
open OnBytes.K.Arm (bitsToBytes_inj digToBytes_inj whole_of_len)

/-! ## The item "table" -/

/-- What a reader undoes can be cut off the head of a string. -/
theorem undoes_cancel {α : Type} {r : Fmt.Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (U : Fmt.Undoes r sp ok) (x y : α) (hx : ok x) (hy : ok y) (p q : ByteArray)
    (e : sp x ++ p = sp y ++ q) : x = y ∧ p = q := by
  have a := U x hx ByteArray.empty p
  have b := U y hy ByteArray.empty q
  rw [ByteArray.empty_append] at a b
  rw [e, b] at a
  have c : y = x := congrArg Prod.fst (Option.some.inj a)
  subst c
  exact ⟨rfl, (Fmt.append_cancel _ _ _ _ rfl e).2⟩

theorem ext_pos (x : UInt64 × UInt64 × UInt64) : 1 ≤ (Fmt.ext x).size := by
  unfold Fmt.ext
  simp only [ByteArray.size_append, Fmt.size_u64]
  omega

/-- The library's reader of an item "table", with no test on the answers' form. -/
theorem undoes_table :
    Fmt.Undoes (Fmt.rdNamed "table" (Fmt.rdPair Fmt.rdText
        (Fmt.rdList (Fmt.rdPair Fmt.rdWord (Fmt.rdPair Fmt.rdWord Fmt.rdWord)))))
      (fun x : ByteArray × List (UInt64 × UInt64 × UInt64) =>
        Fmt.item "table" (Fmt.pair Fmt.text (Fmt.list Fmt.ext) x))
      fun x => (x.1.size < 2 ^ 64 ∧ x.2.length < 2 ^ 64 ∧ ∀ e ∈ x.2, True) ∧
        (Fmt.pair Fmt.text (Fmt.list Fmt.ext) x).size < 2 ^ 64 :=
  Fmt.undoes_named "table" (by decide) (by decide)
    (Fmt.undoes_pair Fmt.undoes_text (Fmt.undoes_list undoes_ext3 fun x _ => ext_pos x))

theorem table_ok (r : ByteArray) (a : List (UInt64 × UInt64 × UInt64))
    (h : (Fmt.tableItem "table" r a).size < 2 ^ 64) :
    (r.size < 2 ^ 64 ∧ a.length < 2 ^ 64 ∧ ∀ e ∈ a, True) ∧
      (Fmt.pair Fmt.text (Fmt.list Fmt.ext) (r, a)).size < 2 ^ 64 := by
  have hl := Fmt.length_le_cat (sp := Fmt.ext) a fun x _ => ext_pos x
  simp only [Fmt.tableItem, Fmt.item, Fmt.text, Fmt.list, ByteArray.size_append,
    Fmt.size_u64n] at h
  refine ⟨⟨by omega, by omega, fun _ _ => trivial⟩, ?_⟩
  simp only [Fmt.pair, Fmt.text, Fmt.list, ByteArray.size_append, Fmt.size_u64n]
  omega

/-- **The item "table" at the head of a string gives back root and answers.** -/
theorem table_cancel (r r' : ByteArray) (a a' : List (UInt64 × UInt64 × UInt64))
    (p q : ByteArray) (h : (Fmt.tableItem "table" r a).size < 2 ^ 64)
    (h' : (Fmt.tableItem "table" r' a').size < 2 ^ 64)
    (e : Fmt.tableItem "table" r a ++ p = Fmt.tableItem "table" r' a' ++ q) :
    r = r' ∧ a = a' ∧ p = q := by
  obtain ⟨x, y⟩ := undoes_cancel undoes_table (r, a) (r', a') (table_ok r a h)
    (table_ok r' a' h') p q e
  exact ⟨congrArg Prod.fst x, congrArg Prod.snd x, y⟩

theorem triple_inj : Function.Injective E.triple := fun x y h => by
  cases x
  cases y
  simp only [E.triple, Prod.mk.injEq] at h
  obtain ⟨a, b, c⟩ := h
  subst a b c
  rfl

/-! ## The tests -/

/-- The outer roots are the first of them and then tl of it and of the answers. -/
def cmsFit (tl : Dig 256 → List E → List (Dig 256)) (cms : List (Dig 256)) (ans : List E) : Bool :=
  match cms with
  | [] => false
  | c :: r => decide (r = tl c ans)

theorem cmsFit_eq {tl : Dig 256 → List E → List (Dig 256)} {cms : List (Dig 256)} {ans : List E}
    (h : cmsFit tl cms ans = true) :
    cms = (cms.headD fun _ => false) :: tl (cms.headD fun _ => false) ans := by
  cases cms with
  | nil => cases h
  | cons c r =>
    have h1 : r = tl c ans := of_decide_eq_true h
    rw [List.headD_cons, ← h1]

/-- The item "table" is shorter than 2^64 bytes. -/
def tableSmall (cms : List (Dig 256)) (ans : List E) : Bool :=
  decide ((Params.OneTime.statement (tableOf cms ans)).size < 2 ^ 64)

/-- The table comes back: the outer roots, under `cmsFit`, and the answers. -/
theorem tableOf_cancel {tl : Dig 256 → List E → List (Dig 256)} {cms cms' : List (Dig 256)}
    {ans ans' : List E} (c : cmsFit tl cms ans = true) (c' : cmsFit tl cms' ans' = true)
    (s : tableSmall cms ans = true) (s' : tableSmall cms' ans' = true) (p q : ByteArray)
    (e : Params.OneTime.statement (tableOf cms ans) ++ p =
      Params.OneTime.statement (tableOf cms' ans') ++ q) : cms = cms' ∧ ans = ans' ∧ p = q := by
  obtain ⟨e1, e2, e3⟩ := table_cancel _ _ _ _ p q (of_decide_eq_true s) (of_decide_eq_true s') e
  have a : ans = ans' := List.map_injective_iff.2 triple_inj e2
  have d : (cms.headD fun _ => false) = cms'.headD fun _ => false := digToBytes_inj e1
  refine ⟨?_, a, e3⟩
  rw [cmsFit_eq c, cmsFit_eq c', d, a]

variable {X : Type}

/-- A key file's front message. -/
def fFrontK (tl : Dig 256 → List E → List (Dig 256)) (cms : List (Dig 256)) (x : Option X)
    (p : FrontMsg (List E)) : Bool :=
  x.isNone && decide (p.copy = 0) && cmsFit tl cms p.answers && tableSmall cms p.answers

/-- A proof file's front message. `req x0`: the item's value, then the request file's bytes; each is
asked to have fewer than 2^64 - 8 bytes. -/
def fFrontP (tl : Dig 256 → List E → List (Dig 256)) (req : X → ByteArray × ByteArray) (okX : X →
    Bool)
    (cms : List (Dig 256)) (x : Option X) (p : FrontMsg (List E)) : Bool :=
  (match x with
    | some x0 => okX x0 && decide ((req x0).1.size + 8 < 2 ^ 64) &&
        decide ((req x0).2.size + 8 < 2 ^ 64)
    | none => false) &&
    decide (p.copy < 2 ^ 64) && cmsFit tl cms p.answers && tableSmall cms p.answers

/-- A joining round's message. -/
def fJoin (tl : Dig 256 → List E → List (Dig 256)) (cms : List (Dig 256))
    (p : JoinMsg (List E) ByteArray) : Bool :=
  cmsFit tl cms p.answers && tableSmall cms p.answers

/-- A seam's message: every one. -/
def fSeam (_ : ByteArray) : Bool := true

/-! ## The laws -/

theorem len_32 {l : List Bool} (h : l.length = 256) : (bitsToBytes l).size = 32 :=
  size_bitsToBytes l 32 (by omega)

/-- The second chain's statement and run's value, at both kinds of file. -/
theorem stm₂_inj (tl : Dig 256 → List E → List (Dig 256)) (cms cms' : List (Dig 256))
    (r r' : List Bool) (p p' : JoinMsg (List E) ByteArray) (f : fJoin tl cms p = true)
    (f' : fJoin tl cms' p' = true) (l : r.length = 256) (l' : r'.length = 256)
    (e : Params.Shared.statement (tableOf cms p.answers) (bitsToBytes r) =
      Params.Shared.statement (tableOf cms' p'.answers) (bitsToBytes r'))
    (er : bytesToBits p.run = bytesToBits p'.run) : cms = cms' ∧ r = r' ∧ p = p' := by
  unfold fJoin at f f'
  rw [Bool.and_eq_true] at f f'
  obtain ⟨a, b, c⟩ := tableOf_cancel f.1 f'.1 f.2 f'.2 _ _ e
  have d := Fmt.inj_of_undoes (Fmt.undoes_digestItem Fmt.bindRootName (by decide) (by decide))
    _ _ (len_32 l) (len_32 l') c
  refine ⟨a, bitsToBytes_inj (whole_of_len (n := 32) (by omega)) (whole_of_len (n := 32) (by omega))
      d, ?_⟩
  cases p
  cases p'
  simp only at b er
  rw [b, bytesToBits_inj er]

/-- The third chain's statement and run's value, at both kinds of file. -/
theorem stm₃_inj (a a' c c' : List Bool) (p p' : ByteArray) (l1 : a.length = 256)
    (l2 : a'.length = 256) (l3 : c.length = 256) (l4 : c'.length = 256)
    (e : Params.Second.statement (bitsToBytes c) (bitsToBytes a) =
      Params.Second.statement (bitsToBytes c') (bitsToBytes a'))
    (er : bytesToBits p = bytesToBits p') : a = a' ∧ c = c' ∧ p = p' := by
  obtain ⟨e1, e2⟩ := Fmt.sealItems_inj _ _ _ _ (len_32 l3) (len_32 l1) (len_32 l4) (len_32 l2) e
  exact ⟨bitsToBytes_inj (whole_of_len (n := 32) (by omega)) (whole_of_len (n := 32) (by omega)) e2,
    bitsToBytes_inj (whole_of_len (n := 32) (by omega)) (whole_of_len (n := 32) (by omega)) e1,
        bytesToBits_inj er⟩

/-- **A key file's data meet the laws.** -/
theorem silentKey_laws (h : HId) (k : Params.KeyChains) (tl : Dig 256 → List E → List (Dig 256)) :
    SilentLaws (silentKey h k X) (fFrontK tl) (fJoin tl) fSeam where
  l12 := (by decide : Params.labelOneTime ≠ Params.labelShared)
  l13 := (by decide : Params.labelOneTime ≠ Params.labelSecond)
  l23 := (by decide : Params.labelShared ≠ Params.labelSecond)
  run₂ := fun p => whole_bytesToBits p.run
  run₃ := fun p => whole_bytesToBits p
  first₁ := fun cms cms' x x' p p' f f' e => by
    unfold fFrontK at f f'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at f f'
    obtain ⟨⟨⟨x0, c0⟩, m⟩, s⟩ := f
    obtain ⟨⟨⟨x0', c0'⟩, m'⟩, s'⟩ := f'
    have e1 : Params.OneTime.statement (tableOf cms p.answers) ++ ByteArray.empty =
        Params.OneTime.statement (tableOf cms' p'.answers) ++ ByteArray.empty := by
      rw [ByteArray.append_empty, ByteArray.append_empty]
      exact e
    obtain ⟨a, b, -⟩ := tableOf_cancel m m' s s' _ _ e1
    refine ⟨a, ?_, ?_⟩
    · rw [Option.isNone_iff_eq_none.1 x0, Option.isNone_iff_eq_none.1 x0']
    · cases p
      cases p'
      simp only at b c0 c0'
      rw [b, c0, c0']
  first₂ := fun cms cms' r r' p p' f f' l l' e er => stm₂_inj tl cms cms' r r' p p' f f' l l' e er
  first₃ := fun a a' c c' p p' _ _ l1 l2 l3 l4 e er => stm₃_inj a a' c c' p p' l1 l2 l3 l4 e er

/-- **A proof file's data meet the laws**, if req, the pair of strings, is one to one on the
instances that pass okX. -/
theorem silentProof_laws (h : HId) (c : Params.ProofChains) (req : X → ByteArray × ByteArray)
    (okX : X → Bool) (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y)
    (tl : Dig 256 → List E → List (Dig 256)) :
    SilentLaws (silentProof h c req) (fFrontP tl req okX) (fJoin tl) fSeam where
  l12 := (by decide : Params.labelFirst ≠ Params.labelSharedProof)
  l13 := (by decide : Params.labelFirst ≠ Params.labelSecondProof)
  l23 := (by decide : Params.labelSharedProof ≠ Params.labelSecondProof)
  run₂ := fun p => whole_bytesToBits p.run
  run₃ := fun p => whole_bytesToBits p
  first₁ := fun cms cms' x x' p p' f f' e => by
    unfold fFrontP at f f'
    cases x with
    | none => simp at f
    | some x0 =>
      cases x' with
      | none => simp at f'
      | some x0' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at f f'
        obtain ⟨⟨⟨⟨⟨o, z⟩, w⟩, c0⟩, m⟩, s⟩ := f
        obtain ⟨⟨⟨⟨⟨o', z'⟩, w'⟩, c0'⟩, m'⟩, s'⟩ := f'
        have e1 : Params.OneTime.statement (tableOf cms p.answers) ++
              (Fmt.item "stored copy" (Fmt.u64n p.copy) ++
                (Fmt.item "request" (Fmt.text (req x0).1) ++
                  Fmt.item "the request file's words" (Fmt.text (req x0).2))) =
            Params.OneTime.statement (tableOf cms' p'.answers) ++
              (Fmt.item "stored copy" (Fmt.u64n p'.copy) ++
                (Fmt.item "request" (Fmt.text (req x0').1) ++
                  Fmt.item "the request file's words" (Fmt.text (req x0').2))) := by
          simp only [← ByteArray.append_assoc]
          exact e
        obtain ⟨a, b, e2⟩ := tableOf_cancel m m' s s' _ _ e1
        obtain ⟨e3, e4⟩ := undoes_cancel
          (Fmt.undoes_named "stored copy" (by decide) (by decide) (Fmt.undoes_bytes 8))
          (Fmt.u64n p.copy) (Fmt.u64n p'.copy) ⟨Fmt.size_u64n _, by rw [id, Fmt.size_u64n]; decide⟩
          ⟨Fmt.size_u64n _, by rw [id, Fmt.size_u64n]; decide⟩ _ _ e2
        obtain ⟨e5, e7⟩ := undoes_cancel Fmt.undoes_requestItem _ _ z z' _ _ e4
        have e8 := Fmt.inj_of_undoes Fmt.undoes_wordsItem _ _ w w' e7
        refine ⟨a, by rw [hreq x0 x0' o o' (Prod.ext e5 e8)], ?_⟩
        have e6 := u64n_inj c0 c0' e3
        cases p
        cases p'
        simp only at b e6
        rw [b, e6]
  first₂ := fun cms cms' r r' p p' f f' l l' e er => stm₂_inj tl cms cms' r r' p p' f f' l l' e er
  first₃ := fun a a' c c' p p' _ _ l1 l2 l3 l4 e er => stm₃_inj a a' c c' p p' l1 l2 l3 l4 e er

/-- **The same where the request file's bytes alone are one to one** on the instances that pass okX.
-/
theorem silentProof_laws_words (h : HId) (c : Params.ProofChains) (req : X → ByteArray × ByteArray)
    (okX : X → Bool)
    (hw : ∀ x y, okX x = true → okX y = true → (req x).2 = (req y).2 → x = y)
    (tl : Dig 256 → List E → List (Dig 256)) :
    SilentLaws (silentProof h c req) (fFrontP tl req okX) (fJoin tl) fSeam :=
  silentProof_laws h c req okX (fun x y a b e => hw x y a b (congrArg Prod.snd e)) tl

end OnBytes.Maker.Page
