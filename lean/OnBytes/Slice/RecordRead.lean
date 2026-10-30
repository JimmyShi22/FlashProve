-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecordRead.lean: the record of a stored table, as the programs have it, in the terms
of OnBytes/Slice/DecoderRec.lean and FineAtRec.lean: the sample map of one row, the answers off a
key, the seed off a log. DEFINITIONS, WITH LAWS ON THEM: NOTHING ON SOUNDNESS IS SHOWN.

The programs' record (OnBytes/Entry/Table.lean, Key/Table.lean, Iop/Foldeq.lean). A table of 2^v
rows may come with s answers for each row, elements of the extension field; they stand in the key
file, in the commitment ID's string and in every later statement. All rows share s seeds, each a
point of lg coordinates and a factor other than 0. THE SEEDS ARE DRAWN FROM THE TABLE'S NAME: root,
digest of the public files, six words of the shape; THE ANSWERS ARE NOT IN IT. They are drawn on a
chain of their own, without salt, work or random bytes: one call number 160 under the label 2^32,
then one round of calls number 162 at strings that hold the first call's answer. A further stored
copy has its own root, so its own name, seeds and answers. No program tests the answers row by row:
each run of the fold tests their fold at its own point.

Main definitions.
 `recZ l lg s`          the sample map of one row: the library's `Sample.padPow`
                        (Cb/Gen/OodDecPadPow.lean), along `splitEntry`. `recZ_before`, `recZ_pad`:
                        its matrix, written out; it is the row of `foldeqRecordRow`, by that
                        definition's text and `readE_eq`; no theorem here names `foldeqRecordRow`.
 `recAns v s k`         the answers that stand in a key.
 `recordSeedsW`         the text of the program's `recordSeeds`, generic in the hash;
                        `recordSeedsW_H`: at the format's own hash it IS `recordSeeds`: a chain of
                        named equations (`recordSeedsW_pure`, `recordFirstW_H`, `queryW_H`,
                        `recordSeeds_value`, `recordSeeds_body`, `recordSeeds_at`,
                        `recordSeeds_scrut`), with four elaborators that only fetch the value of
                        `recordSeeds` out of the environment.
 `askLog σ`, `seedAt lg s k σ`   the hash that reads a log; the seed of a key's table as a log shows
                        it: `recordSeedsW` at that hash. `askLog_offSet`, `seedAt_offSet`: neither
                        sees the entries at strings of calls with the number 169.
 `decRec`, `logRead`   the data `DecR` and `LogRead` made of these.


What is not claimed. THE SAMPLE MAP HAS NOT THE LIBRARY'S PROPERTY `Sample.OK`: on vectors with pad
entries outside the base field it fails; on the others it holds (`recZ_okOn`,
OnBytes/Slice/RecordOK.lean). No bound here on the seeds at which a record does not single one table
out (OnBytes/Slice/RecordColl.lean). THAT THE DRAW IS NEAR UNIFORM: `seedOf` of the round's blocks
is a total function, not one to one; an element of the base field is tried at most six times, then 0
is taken; a factor twice, then 1. That a log shows a seed: a committer can form its ID without
asking for it (the table of zeros has the answers 0 at every seed); said of an ID that is the hash
function's answer at the commitment ID's string without the record's seed (`idCode`,
OnBytes/Tie/IdKey.lean). Of an ID whose string holds the seed (`Fmt.publishedBytes`,
Fmt/Rules4.lean) no statement here says that its maker has asked for it. That l, lg, s, v are those
of any setting: they are arguments; lg is meant to be the code's `logEll`, and 3 s is meant to be
below l. That a raw string is the reading of an entry's part at a setting with a record: no such
part is written. Nothing on any hash function.

-/
import OnBytes.Slice.FineAtRec
import OnBytes.Slice.ProgField
import OnBytes.Slice.SimBasic
import OnBytes.Entry.Table
import OnBytes.Key.Table
import OnBytes.Tie.DigestPoint
import Cb.Gen.OodDecPadPow

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory Cb Cb.Ood
open OnBytes.Tie (IdKey)

/-! ## The sample map of one row -/

/-- A sample map along a renaming of the coordinates. -/
@[reducible] def reindex {E J J' : Type} (Z : Sample E J') (e : J → J') : Sample E J :=
  { D := Z.D, S := Z.S, mat := fun ρ s j => Z.mat ρ s (e j), err := Z.err }

/-- The factors of a seed: the elements other than 0. -/
abbrev NZ : Type := { β : GE // β ≠ 0 }

/-- There is a factor: 1. -/
instance : Nonempty NZ := ⟨⟨1, one_ne_zero⟩⟩

/-- The entries of a row's message: first those before the pads, then, for each of the s answers,
three pad entries. Entry l - 3 s + 3 a + t is pad entry t of answer a (`IndexShape.padPlace`). In a
message too short for its pads (l < 3 s) every entry is read as a pad entry; the cut is then 0. -/
def splitEntry (l s : ℕ) (p : Fin l) : Fin l ⊕ Fin s × Fin 3 :=
  if h : l - 3 * s ≤ p.val ∧ (p.val - (l - 3 * s)) / 3 < s then
    .inr (⟨(p.val - (l - 3 * s)) / 3, h.2⟩, ⟨(p.val - (l - 3 * s)) % 3, Nat.mod_lt _ (by decide)⟩)
  else .inl p

/-- **The sample map of one row of a stored table with a record of s answers**: the library's
`Sample.padPow`. A seed is, for each answer, a point of lg coordinates and a factor other than 0. In
answer i an entry before the pads has the equality kernel at the point of seed i and the entry's
bits; the three pad entries of answer i have the factor times 1, X, X^2; the pad entries of the
other answers have 0. Coordinate t of the point goes with binary digit t of the entry's number, the
lowest first, as in the program's `Tensor.eq` (`readE_eq`, OnBytes/Slice/BlkTens.lean). -/
@[reducible] def recZ (l lg s : ℕ) : Sample GE (Fin l) :=
  reindex (Sample.padPow GE (Fin lg) (Fin l) (Fin 3) NZ (fun j t => j.val.testBit t.val)
    (fun t => readE (thetaE t.val)) (fun β => β.val) s) (splitEntry l s)

/-- Before the pads: the weight of the entry's vertex at the point of seed i. -/
theorem recZ_before (l lg s : ℕ) (ρ : (recZ l lg s).D) (i : Fin s) (p : Fin l)
    (hp : p.val < l - 3 * s) :
    (recZ l lg s).mat ρ i p = eqW lg (fun t => if h : t < lg then (ρ i).1 ⟨t, h⟩ else 0) p.val := by
  show Sum.elim _ _ (splitEntry l s p) = _
  unfold splitEntry
  rw [dif_neg (fun h => by omega)]
  show Alg.eqk (ρ i).1 _ = Alg.eqk _ _
  congr 1
  funext t
  show (ρ i).1 t = if h : t.val < lg then (ρ i).1 ⟨t.val, h⟩ else 0
  rw [dif_pos t.isLt]

/-- On the pads: the factor of seed i times 1, X, X^2 on the pads of answer i; 0 on the others'. -/
theorem recZ_pad (l lg s : ℕ) (ρ : (recZ l lg s).D) (i : Fin s) (p : Fin l) (a : Fin s) (t : Fin 3)
    (hp : p.val = l - 3 * s + 3 * a.val + t.val) :
    (recZ l lg s).mat ρ i p = if a = i then (ρ i).2.val * readE (thetaE t.val) else 0 := by
  have h1 : (p.val - (l - 3 * s)) / 3 = a.val := by omega
  have h2 : (p.val - (l - 3 * s)) % 3 = t.val := by omega
  show Sum.elim _ _ (splitEntry l s p) = _
  unfold splitEntry
  rw [dif_pos ⟨by omega, by omega⟩]
  show (if (⟨(p.val - (l - 3 * s)) / 3, _⟩ : Fin s) = i then
    (ρ i).2.val * readE (thetaE ((p.val - (l - 3 * s)) % 3)) else 0) = _
  simp only [h1, h2]

/-! ## The answers, off the key -/

/-- **The answers that stand in a key**, read in the extension field: entry r * s + i is the answer
of row r under seed i (`TableKey.record`). Nothing, unless there are exactly 2^v * s. -/
noncomputable def recAns (v s : ℕ) (k : IdKey) : Option ((Fin v → Bool) × Fin s → GE) :=
  if k.2.2.answers.length = 2 ^ v * s then
    some fun x => readE (k.2.2.answers.getD (Sz.rowNo x.1 * s + x.2.val) zeroE)
  else none

/-! ## The seed, off a log -/

/-- The answer that a log shows at a byte string, as bytes: that of the first entry at the string's
bits. Nothing at the string of a call whose number is 169 modulo 65536, and nothing where the log
has no entry. The seeds' text asks at calls 160 and 162 alone, so the first refusal changes nothing
in `seedAt`; it makes `askLog_offSet` hold at every string. -/
noncomputable def askLog (σ : Trace (rom 256)) (s : ByteArray) : Option ByteArray :=
  if (Fmt.wordAt s 65).toNat % 65536 = 169 then none
  else (σ.find? fun e => decide ((e.2.1 : List Bool) = bytesToBits s)).map fun e =>
    digToBytes (e.2.2 : Dig 256)

/-- The first member with p of a list is the first with p of the members with q, if p implies q. -/
theorem find_filter {α : Type} (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    ∀ l : List α, (l.filter q).find? p = l.find? p
  | [] => rfl
  | a :: l => by
    by_cases hq : q a = true
    · rw [List.filter_cons_of_pos hq]
      by_cases hp : p a = true
      · simp [hp]
      · simp [hp, find_filter p q h l]
    · have hp : ¬ p a = true := fun hp => hq (h a hp)
      rw [List.filter_cons_of_neg hq]
      simp [hp, find_filter p q h l]

/-- It does not see the entries at strings of calls with the number 169. -/
theorem askLog_offSet (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s) (σ : Trace (rom 256)) :
    askLog (offSet S σ) = askLog σ := by
  funext s
  unfold askLog
  by_cases h9 : (Fmt.wordAt s 65).toNat % 65536 = 169
  · rw [if_pos h9, if_pos h9]
  · rw [if_neg h9, if_neg h9]
    congr 1
    unfold offSet
    refine find_filter _ _ (fun e he => ?_) σ
    have he' : (e.2.1 : List Bool) = bytesToBits s := by simpa using he
    refine decide_eq_true fun hm => ?_
    obtain ⟨half, t, i, st, bs, -, -, hh⟩ := hS _ hm
    have e2 : s = Fmt.oStr half 169 t i st bs := bytesToBits_inj (he'.symm.trans hh)
    exact h9 (by rw [e2, Tie.oStr_number])

/-- **The text of `recordSeeds` (OnBytes/Entry/Table.lean), generic in the hash**: the first value
of the seeds' chain, a call number 160 under the label 2^32 on the table's name; then the one round
of that chain, calls number 162 at strings that hold that first value; then the draw. -/
def recordSeedsW {m : Type → Type} [Monad m]
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → m ByteArray) (f : Fmt.Fld) (name : ByteArray)
    (bits count : ℕ) : m (Option (List (List E × E))) := do
  let ρ0 ← Fmt.recordFirstW h name
  let r ← Fmt.Chain.queryW h ⟨Fmt.recordLabel, ρ0, 0⟩ ByteArray.empty .seeds 0 0
    (Fmt.blocksFor (count * (bits * 18 + 36)))
  pure (r.map fun x => (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf x.2) 0).1.map fun y =>
    (y.1.map E.ofTriple, E.ofTriple y.2))

/-- That text at a hash without effects, unfolded to its one round. The hash is a variable: nothing
is computed. -/
theorem recordSeedsW_pure (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (f : Fmt.Fld)
    (name : ByteArray) (bits count : ℕ) :
    recordSeedsW (m := Id) h f name bits count =
      (Fmt.Chain.queryW (m := Id) h ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) h name, 0⟩
        ByteArray.empty .seeds 0 0 (Fmt.blocksFor (count * (bits * 18 + 36)))).map fun x =>
          (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf x.2) 0).1.map fun y =>
            (y.1.map E.ofTriple, E.ofTriple y.2) := rfl

/-! ### At the format's own hash

The proof that the text at the format's own hash is the program's `recordSeeds` is cut into named
equations, written as terms, so that no checker need compare two copies of the program's text: a
comparison of two copies that are not one and the same term can lead a checker to unfold the match
in them and then the hash. Four small elaborators fetch the value of the definition `recordSeeds`
out of the environment, whole or in part. They write no text of their own and add no axiom; Lean's
kernel checks every statement in which what they return stands. -/

open Lean Elab Term Meta in
/-- The value of the definition `recordSeeds`, as it stands in the environment. It only fetches. -/
elab "recordSeedsValue%" : term => do
  let .defnInfo d ← getConstInfo ``OnBytes.recordSeeds | throwError "no definition"
  return d.value

open Lean Elab Term Meta in
/-- That value at four arguments, with the arguments put in. It only fetches. -/
elab "recordSeedsBody%" f:term:max n:term:max b:term:max c:term:max : term => do
  let .defnInfo d ← getConstInfo ``OnBytes.recordSeeds | throwError "no definition"
  return d.value.beta #[← elabTerm f none, ← elabTerm n none, ← elabTerm b none, ← elabTerm c none]

open Lean Elab Term Meta in
/-- What the value at four arguments matches on. It only fetches. -/
elab "recordSeedsScrut%" f:term:max n:term:max b:term:max c:term:max : term => do
  let .defnInfo d ← getConstInfo ``OnBytes.recordSeeds | throwError "no definition"
  return (d.value.beta
    #[← elabTerm f none, ← elabTerm n none, ← elabTerm b none, ← elabTerm c none]).getAppArgs[1]!

open Lean Elab Term Meta in
/-- The value at four arguments with q for what it matches on. It only fetches, and puts q in. -/
elab "recordSeedsAt%" f:term:max n:term:max b:term:max c:term:max q:term:max : term => do
  let .defnInfo d ← getConstInfo ``OnBytes.recordSeeds | throwError "no definition"
  let body := d.value.beta
    #[← elabTerm f none, ← elabTerm n none, ← elabTerm b none, ← elabTerm c none]
  let args := body.getAppArgs
  return mkAppN body.getAppFn #[args[0]!, ← elabTerm q none, args[2]!, args[3]!]

/-- The first value of the seeds' chain at the format's own hash is the format's. -/
theorem recordFirstW_H (name : ByteArray) :
    Fmt.recordFirstW (m := Id) Fmt.formatHash name = Fmt.recordFirst name := rfl

/-- A round of the kind "seeds" at the format's own hash is the format's. -/
theorem queryW_H (c : Fmt.Chain) (b : ByteArray) (K : ℕ) :
    Fmt.Chain.queryW (m := Id) Fmt.formatHash c b .seeds 0 0 K = c.query b .seeds 0 0 K := rfl

/-- `recordSeeds` is its own value. -/
theorem recordSeeds_value : @recordSeeds = recordSeedsValue% := Eq.refl _

/-- The same at four arguments. -/
theorem recordSeeds_body (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    recordSeeds f name bits count = recordSeedsBody% f name bits count :=
  congrFun (congrFun (congrFun (congrFun recordSeeds_value f) name) bits) count

/-- What the program's text makes of the round's value, for a letter q in the place of that value.
-/
theorem recordSeeds_at (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (q : Option (Fmt.Chain × Array ByteArray)) :
    Option.map (fun x : Fmt.Chain × Array ByteArray =>
        List.map (fun y => (List.map E.ofTriple y.1, E.ofTriple y.2))
          (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf x.2) 0).1) q =
      recordSeedsAt% f name bits count q := by
  cases q with
  | none => rfl
  | some p => cases p; rfl

/-- The round's value in the generic text, at the format's own hash, is what the program's text
matches on. -/
theorem recordSeeds_scrut (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    Fmt.Chain.queryW (m := Id) Fmt.formatHash ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) Fmt.formatHash name, 0⟩
        ByteArray.empty .seeds 0 0 (Fmt.blocksFor (count * (bits * 18 + 36))) =
      recordSeedsScrut% f name bits count :=
  (congrArg (fun ρ => Fmt.Chain.queryW (m := Id) Fmt.formatHash ⟨Fmt.recordLabel, ρ, 0⟩ ByteArray.empty
    .seeds 0 0 (Fmt.blocksFor (count * (bits * 18 + 36)))) (recordFirstW_H name)).trans
      (queryW_H _ _ _)

/-- **At the format's own hash it is the program's `recordSeeds`.** A chain of the named equations
above, written as a term. -/
theorem recordSeedsW_H (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    recordSeedsW (m := Id) Fmt.formatHash f name bits count = recordSeeds f name bits count :=
  (recordSeedsW_pure Fmt.formatHash f name bits count).trans
    ((congrArg (Option.map fun x : Fmt.Chain × Array ByteArray =>
        List.map (fun y => (List.map E.ofTriple y.1, E.ofTriple y.2))
          (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf x.2) 0).1)
      (recordSeeds_scrut f name bits count)).trans
      ((recordSeeds_at f name bits count (recordSeedsScrut% f name bits count)).trans
        (recordSeeds_body f name bits count).symm))

/-- A seed of the program, read in the extension field: the point's coordinates (0 beyond their
end) and the factor. The program's draw gives no factor 0; should the element read be 0, the factor
1 is taken. -/
def seedOf1 (lg : ℕ) (x : List E × E) : (Fin lg → GE) × NZ :=
  (fun c => readE (x.1.getD c.val zeroE),
    if h : readE x.2 ≠ 0 then ⟨_, h⟩ else ⟨1, one_ne_zero⟩)

/-- The program's list of seeds as a seed of `recZ`. A missing seed is read as the point 0 with the
factor 1. -/
def seedOf (lg s : ℕ) (l : List (List E × E)) : Fin s → (Fin lg → GE) × NZ :=
  fun i => seedOf1 lg (l.getD i.val ([], oneE))

/-- **The seed of the key k's table as the log σ shows it**: `recordSeedsW` at the hash that reads
the log, on the table's name (root, digest of the public files, six words of the shape: NOT the
answers). Nothing, if σ lacks one of the entries. The draw is the program's: a total function of the
round's blocks, not one to one, and it does not carry uniform blocks to uniform seeds: an element of
the base field is tried at most six times, then 0 is taken. -/
noncomputable def seedAt (lg s : ℕ) (k : IdKey) (σ : Trace (rom 256)) :
    Option (Fin s → (Fin lg → GE) × NZ) :=
  (recordSeedsW (m := Option) (Fmt.HM (askLog σ)) .two (Key.nameOf k.1 k.2.1 k.2.2) lg s).bind
    fun r => r.map (seedOf lg s)

/-- It does not see the entries at strings of calls with the number 169. -/
theorem seedAt_offSet (lg s : ℕ) (S : Finset (List Bool)) (hS : ∀ x ∈ S, IsCall169 x) (k : IdKey)
    (σ : Trace (rom 256)) : seedAt lg s k (offSet S σ) = seedAt lg s k σ := by
  unfold seedAt
  rw [askLog_offSet S hS]

/-! ## The decoder's data and the two readings -/

/-- **The data of a decoder with the program's record**: a code, the number of row variables, the
radius, `recZ` at the code's message length, lg coordinates and s answers, and the cut l - 3 s: the
entries of a row's message before its pads (`IndexShape.plain`; the entries that `splitEntry` reads
as entries proper). -/
@[reducible] noncomputable def decRec (T : Fmt.M1.Code) (v eM lg s : ℕ) : DecR :=
  { T := T, v := v, eM := eM, Z := recZ T.l lg s, cut := T.l - 3 * s }

/-- **How a log and a key are read, for tables with the program's record.** The seed: `seedAt`. The
answers: `recAns`. THE RAW STRING IS A PARAMETER WITH ITS LAW.
-/
noncomputable def logRead (T : Fmt.M1.Code) (v eM lg s : ℕ)
    (raw : ByteArray → Trace (rom 256) → Dig 256 → Raw SgX)
    (raw_off : ∀ (S : Finset (List Bool)), (∀ x ∈ S, IsCall169 x) → ∀ c σ cm,
      raw c (offSet S σ) cm = raw c σ cm) : LogRead (decRec T v eM lg s) where
  raw := raw
  seed := seedAt lg s
  ans := recAns v s
  raw_off := raw_off
  seed_off := fun S hS k σ => seedAt_offSet lg s S hS k σ

end OnBytes.Slice
