-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryAccepts.lean: the entry's verifier at the small files of the setting "record with
work" (`entrySmall`, OnBytes/Flat/EntryTerm.lean) accepts one written transcript exactly if one
closed Boolean is true.

Why. `entrySmall_sound` (OnBytes/Flat/EntrySound.lean) says that outside a language the prover has
lost towards "the verifier rejects". If the verifier accepted nothing, that would hold for free (the
head of OnBytes/Slice/SmallRecYes.lean says so). Here a statement, two stored tables and a
transcript are written out, and the verifier's yes on them is led back to one evaluation.

The verifier's decision is four conjuncts (`skeletonOverBothExternalStrings`, Run/PlanQX.lean): every test bit of the proof of
work is 0; each opening's part has as many draws as it says; every symbol that is read of a stored
table carries its position; the program's link (`linkVerify`, OnBytes/Iop/Link.lean) says yes on
the view, at the keys written of the two records.

Main definitions.
 `recW`      the record: one seed, its point 2, 3, .., 20, its factor 5; every answer 0.
 `keyW`      the program's key of a table with that record, in words.
 `tabW`      two stored tables of zeros; each symbol carries its position.
 `blkW`, `trW`, `trSmall`   the transcript: the prover's side is each round's own fixed message, all
             0; the verifier's messages are hash blocks in a written pattern, neither 0 nor
             constant, with every test bit 0. The drawn values are what the format's own sampler
             makes of these blocks.
 `decSmall`  THE ONE CLOSED BOOLEAN: the decision of the program's link at `keyW 0`, `keyW 1` on the
             view of that transcript.
Main theorems.
 `srKeys_recW`   the keys that are written of the pair (recW, recW) are `keyW 0`, `keyW 1`.
 `pass_small`, `full_small`, `carries_small`   the first three conjuncts hold: evaluated by Lean's
             kernel (`decide +kernel`).
 `entrySmall_accepts_iff`
             entrySmall.out (recW, recW) (tabW ..) trSmall = some () ↔ decSmall = true.

Not claimed. THAT `decSmall = true` IS NO THEOREM HERE. OnBytes/Flat/TestEntryAccepts.lean evaluates
it by Lean's evaluator (`#guard`): true. Lean's kernel has not reduced it to a value. Two obstacles
are known. The link's block sorts lists by the core library's `List.mergeSort` (`mergeEntries`,
OnBytes/Iop/Tensor.lean; `SwitchPlaces.make`, OnBytes/Iop/Cs.lean), whose `List.merge` is defined by
well-founded recursion: the kernel does not reduce it where a merge is needed. In a trial outside
this tree, with a merge by structural recursion laid in its place, proved equal to it, the kernel's
evaluation of the decision ran out of memory at 64 GiB; it had met no other stop before that, and
whether one lies behind is not known. OnBytes/Iop/Tensor.lean also keeps a memo in a `Std.HashMap`,
at whose look-up the kernel stops too; by a reading of the definitions, no theorem, the link's block
never looks into it: none of its tensors has a written-out factor. That the statement is true by the
language's last clause and not by one of its ways out: that is OnBytes/Flat/EntryAcceptsTrue.lean's
and EntryAcceptsOwn.lean's. Nothing on an honest prover for tables that are not 0; nothing on a
file, on hashes, on trees' paths; nothing at full size. A verifier that accepted this one transcript
alone would meet the right side too. Soundness speaks of false statements: this file is no evidence
for it or for any number.


-/
import OnBytes.Flat.EntryTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood _root_.Run _root_.Run.PQ Blocks OnBytes.Slice OnBytes.Maker
open Params (smallRecordRead smallRecordRounds)

/-! ## What is written is what is read -/

/-- A triple of words below p is the triple of what it is read as. -/
theorem ofE_toE (a : Fmt.Ext3) (ha : Fmt.Fld.two.okE a = true) : ofE (toE a) = a :=
  toE_inj _ _ (by simp only [Fmt.Fld.okE, ofE, ok_ofF, Bool.and_self]) ha (toE_ofE _)

/-- So it is what is written of that. -/
theorem writeE_toE (a : Fmt.Ext3) (ha : Fmt.Fld.two.okE a = true) :
    writeE (toE a) = E.ofTriple a := by
  unfold writeE
  rw [ofE_toE a ha]

/-! ## The written values -/

/-- A small number as the three words of an element of the extension field. -/
def numW (n : ℕ) : Fmt.Ext3 := (UInt64.ofNat n, 0, 0)

theorem ok_pt (t : Fin 19) : Fmt.Fld.two.okE (numW (t.val + 2)) = true := by
  revert t
  decide

theorem ok_five : Fmt.Fld.two.okE (numW 5) = true := by decide

theorem five_ne : toE (numW 5) ≠ 0 := fun h =>
  absurd (toE_inj _ _ ok_five okE_zeroE (h.trans toE_zeroE.symm)) (by decide)

/-- The record: one seed, its point 2, 3, .., 20, its factor 5; every answer 0. -/
def recW : RecSmall :=
  (fun _ => (fun t => toE (numW (t.val + 2)), ⟨toE (numW 5), five_ne⟩), fun _ => toE Fmt.Fld.zeroE)

/-- The program's key of a table with that record, in words. -/
def keyW (item : ℕ) : TableKey where
  item := item
  record := Array.ofFn fun _ : Fin (2 ^ srS.P.v * 1) => E.ofTriple Fmt.Fld.zeroE
  seeds := List.ofFn fun _ : Fin 1 =>
    ⟨List.ofFn fun t : Fin 19 => E.ofTriple (numW (t.val + 2)), E.ofTriple (numW 5)⟩

/-- The key that is written of the record is the key in words. -/
theorem keyOf_recW : keyOf (fun β : NZ => β.val) recW = keyW 0 :=
  congr
    (congrArg (TableKey.mk 0)
      (congrArg Array.ofFn (funext fun _ => writeE_toE _ okE_zeroE)))
    (congrArg List.ofFn (funext fun _ =>
      congr (congrArg SampleSeed.mk (congrArg List.ofFn (funext fun t => writeE_toE _ (ok_pt t))))
        (writeE_toE _ ok_five)))

set_option maxRecDepth 20000 in
/-- The two keys that are written of the pair of records. -/
theorem srKeys_recW : srKeys (recW, recW) = (keyW 0, keyW 1) :=
  Prod.ext (congrArg (fun k : TableKey => { k with item := 0 }) keyOf_recW)
    (congrArg (fun k : TableKey => { k with item := 1 }) keyOf_recW)

/-! ## The written transcript and tables -/

/-- Block i of the verifier's message of round n: a written pattern, neither 0 nor constant: each
32 bits are another word. -/
def blkW (n i : ℕ) : Dig 256 := fun k =>
  Nat.testBit ((n * 4099 + i * 257 + k.val / 32 + 1) * 2654435761 % 4294967296) (k.val % 32)

/-- The transcript: the prover's side is each round's own fixed message (all 0); the verifier's
messages are the pattern, with every test bit 0. -/
def trW : (ds : List RD) → ℕ → Tr (uL (ckP .two) ds)
  | [], _ => ()
  | d :: ds, n =>
    (((fun _ _ => 0), GPlain.mk d.entry.work (PlainOf.dflt d.items) default),
      GChal.zero d.entry.work (fun i => blkW n i.val), trW ds (n + 1))

/-- Two stored tables of zeros: each symbol carries its position and 256 words 0. -/
def tabW (a : ℕ) : (twoExternalStrings (2 ^ a) SgX).Str :=
  (fun p => (p.val, List.replicate 256 0), fun p => (p.val, List.replicate 256 0))

/-- What the format's sampler draws from the pattern. -/
def drawnW (ds : List RD) : List Fmt.Drawn :=
  drawnSL (ckP .two) ds (rhoSL (ckP .two) ds (trW ds 0))

/-- The view of the written transcript. -/
def viewW (ds : List RD) (a : ℕ) (xs : List XO) : Fmt.View :=
  viewX (ckP .two) ds a xs (tabW a) (trW ds 0)

/-- The four conjuncts of the written verifier's decision (`skeletonOverBothExternalStrings`, Run/PlanQX.lean), at the written
transcript and tables. -/
def accW (ds : List RD) (a : ℕ) (xs : List XO) (dec : Fmt.View → Bool) : Bool :=
  passSL (ckP .two) ds (rhoSL (ckP .two) ds (trW ds 0)) && everyOpeningHasItsDraws xs (drawnW ds) &&
    symbolsCarryTheirPositions a ds xs (drawnW ds) (tabW a) && dec (viewW ds a xs)

/-- The transcript over the rounds of `entrySmall`. -/
def trSmall : Tr srShape := (((), ()), default, trW srRds 0)

/-- THE ONE CLOSED BOOLEAN: the decision of the program's link at the two written keys on the view
of the written transcript. -/
def decSmall : Bool :=
  (linkVerify smallRecordRead.link (keyW 0) (keyW 1)).decides (Entry.start smallRecordRead)
    (viewW srD.ds srD.a srD.xs)

/-! ## Three conjuncts, by Lean's kernel -/

theorem pass_small : passSL (ckP .two) srD.ds (rhoSL (ckP .two) srD.ds (trW srD.ds 0)) = true := by
  decide +kernel

theorem full_small : everyOpeningHasItsDraws srD.xs (drawnW srD.ds) = true := by decide +kernel

theorem carries_small : symbolsCarryTheirPositions srD.a srD.ds srD.xs (drawnW srD.ds) (tabW srD.a) = true := by
  decide +kernel

/-! ## The theorem -/

/-- The family's verifier at the written values is the four conjuncts: by unfolding. -/
theorem accSmall_eq : accSmall srD.xs (recW, recW) (tabW srS.P.T.a) trSmall =
    accW srRds srS.P.T.a srD.xs (srDec (recW, recW)) := rfl

/-- At the description's own rounds and depth three of the four hold: the fourth is left. -/
theorem accW_small (dec : Fmt.View → Bool) :
    accW srRds srS.P.T.a srD.xs dec = dec (viewW srD.ds srD.a srD.xs) := by
  have ha : srS.P.T.a = srD.a := sr_a.symm
  rw [show srRds = srD.ds from sr_ds_C.symm, ha]
  unfold accW
  rw [pass_small, full_small, carries_small]
  rfl

/-- **The entry's verifier at the small size accepts the written transcript exactly if the one
closed Boolean is true.** -/
theorem entrySmall_accepts_iff :
    entrySmall.out (recW, recW) (tabW srS.P.T.a) trSmall = some () ↔ decSmall = true := by
  rw [entrySmall_out, accSmall_eq, accW_small, srDec_eq, srKeys_recW]
  show (if decSmall = true then some () else none) = some () ↔ decSmall = true
  cases decSmall <;> simp

end OnBytes.Flat

#print axioms OnBytes.Flat.srKeys_recW
#print axioms OnBytes.Flat.pass_small
#print axioms OnBytes.Flat.full_small
#print axioms OnBytes.Flat.carries_small
#print axioms OnBytes.Flat.entrySmall_accepts_iff
