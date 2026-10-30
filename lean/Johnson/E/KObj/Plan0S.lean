-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Plan0S.lean: the table and the theorem of Johnson/E/KObj/Plan0.lean with nine places
a link.

Definitions, guards by evaluation, statements and proofs.
The table `planS` was made by a program from the table of Johnson/E/KObj/Plan0.lean.
Each link's own rounds are one place (families `chain`, `headRow`; the head's merge: `merge`). A
sending in one round and the locations behind it, whose round holds the sending's answers, are one
place (`sendLoc`: a code switch). The reply is a place of its own (`reply`). A link then has the
places: code switch, lookup of the calls, own rounds, sending, smallness test's draw, sending,
lookup of the digits, batching draw, batching and fold. The last group's proximity test, from the
round before it to its last step, is one place (`test`): its blocks stand beside what is carried.
232 places; 14 families; 36 names of seams.
Main names:
  `KObj.SFam`, `KObj.planS`, `KObj.seamNamesS`, `KObj.famS`, `KObj.sfamS`, `KObj.entS`: the table.
  `KObj.PFile.FamiliesS`: the named hypotheses by family. `KObj.proofSound_planS`: from them the
    hypothesis `proofSound` (Johnson/Top/OnFilesAt.lean), word for word, at the passed object.
Limits: those of Johnson/E/KObj/Plan0.lean, to the letter: K is a parameter,
and a family's name binds nothing until K is written there; the counts are of the table, not of W
and not of the theorem; W is a parameter.
-/
import Johnson.E.KObj.PFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb Compile Compile.Batch Compile.Batch.Cms
open scoped ENNReal

/-- the families of blocks of the first proof chain, each link's own rounds merged -/
inductive SFam
  /-- a sending of oracle messages in two rounds: the words and a joint seed; the answers -/
  | send
  /-- a sub-proof's lookup of all calls, with its shift -/
  | lookupCalls
  /-- a link's own rounds as one block: the layers', attention's -/
  | chain
  /-- the smallness test's draw -/
  | rng
  /-- the lookup of a smallness test's digits, with its shift -/
  | lookupDigits
  /-- hidden scalars (or none) and a batching draw -/
  | batSigma
  /-- the batching of a group and its fold -/
  | batFold
  /-- a code switch: a sending in one round and the locations, whose round holds the answers -/
  | sendLoc
  /-- the reply -/
  | reply
  /-- the head's own rounds as one block -/
  | headRow
  /-- the head's merge -/
  | merge
  /-- a whole proximity test beside what is carried: the round before it, the stages, the last step
  -/
  | test
  /-- hidden scalars, a batching draw, then a masked sumcheck -/
  | batPsc
  /-- the chain's seal -/
  | sealR
  deriving DecidableEq, Repr

/-- place by place: the family, the entries of the plan, the name of the seam behind the place -/
def planS : List (SFam × ℕ × ℕ) :=
  [(.send, 2, 0), (.lookupCalls, 1046, 1), (.chain, 170, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 17),
   (.sendLoc, 2, 18), (.lookupCalls, 1046, 1), (.chain, 168, 2),
   (.send, 2, 3), (.rng, 1, 4), (.send, 2, 5),
   (.lookupDigits, 746, 6), (.batSigma, 1, 7), (.batFold, 10, 8),
   (.sendLoc, 2, 9), (.lookupCalls, 984, 10), (.chain, 162, 11),
   (.send, 2, 12), (.rng, 1, 13), (.send, 2, 14),
   (.lookupDigits, 716, 15), (.batSigma, 1, 16), (.batFold, 9, 19),
   (.reply, 1, 20), (.sendLoc, 2, 21), (.lookupCalls, 1080, 22),
   (.headRow, 82, 23), (.send, 2, 24), (.rng, 1, 25),
   (.send, 2, 26), (.lookupDigits, 746, 27), (.merge, 22, 28),
   (.batSigma, 1, 29), (.batFold, 10, 30), (.sendLoc, 2, 31),
   (.test, 33, 32), (.batPsc, 20, 33), (.send, 2, 34),
   (.sealR, 1, 35)]

/-- the seams' names: the names of the two neighbours -/
def seamNamesS : List (String × String) :=
  [("G# | (its own rounds) :: SEND",
    "G# | LOOKUP calls"),
   ("G# | LOOKUP calls",
    "G# | the layers' own rounds"),
   ("G# | the layers' own rounds",
    "G# | (its own rounds) :: SEND"),
   ("G# | (its own rounds) :: SEND",
    "G# | smallness test :: RNG"),
   ("G# | smallness test :: RNG",
    "G# | (its own rounds) :: SEND"),
   ("G# | (its own rounds) :: SEND",
    "G# | LOOKUP digits"),
   ("G# | LOOKUP digits",
    "G# | claims :: BAT-sigma"),
   ("G# | claims :: BAT-sigma",
    "G# | (its own rounds) :: BAT+FOLD"),
   ("G# | (its own rounds) :: BAT+FOLD",
    "A# | the code switch: SEND, LOC"),
   ("A# | the code switch: SEND, LOC",
    "attention # | LOOKUP calls"),
   ("attention # | LOOKUP calls",
    "attention # | attention's own rounds"),
   ("attention # | attention's own rounds",
    "A# | (its own rounds) :: SEND"),
   ("A# | (its own rounds) :: SEND",
    "attention # | smallness test :: RNG"),
   ("attention # | smallness test :: RNG",
    "A# | (its own rounds) :: SEND"),
   ("A# | (its own rounds) :: SEND",
    "attention # | LOOKUP digits"),
   ("attention # | LOOKUP digits",
    "attention # | all rows :: BAT-sigma"),
   ("attention # | all rows :: BAT-sigma",
    "A# | (its own rounds) :: BAT+FOLD"),
   ("A# | (its own rounds) :: BAT+FOLD",
    "G# | the code switch: SEND, LOC"),
   ("G# | the code switch: SEND, LOC",
    "G# | LOOKUP calls"),
   ("A# | (its own rounds) :: BAT+FOLD",
    "H | REPLY"),
   ("H | REPLY",
    "H | the code switch: SEND, LOC"),
   ("H | the code switch: SEND, LOC",
    "head | LOOKUP calls"),
   ("head | LOOKUP calls",
    "head | the head's own rounds"),
   ("head | the head's own rounds",
    "H | (its own rounds) :: SEND"),
   ("H | (its own rounds) :: SEND",
    "head | smallness test :: RNG"),
   ("head | smallness test :: RNG",
    "H | (its own rounds) :: SEND"),
   ("H | (its own rounds) :: SEND",
    "head | LOOKUP digits"),
   ("head | LOOKUP digits",
    "head | the head's merge"),
   ("head | the head's merge",
    "head | all rows :: BAT-sigma"),
   ("head | all rows :: BAT-sigma",
    "H | (its own rounds) :: BAT+FOLD"),
   ("H | (its own rounds) :: BAT+FOLD",
    "last group | the code switch: SEND, LOC"),
   ("last group | the code switch: SEND, LOC",
    "last group | the proximity test: BAT, five stages, BASE"),
   ("last group | the proximity test: BAT, five stages, BASE",
    "rows on the table | (its own rounds) :: BAT-sigma+PSC"),
   ("rows on the table | (its own rounds) :: BAT-sigma+PSC",
    "table | W :: SEND"),
   ("table | W :: SEND",
    "first chain | (its own rounds) :: SEAL"),
   ("first chain | (its own rounds) :: SEAL",
    "(the tail step)")]

def famS (i : ℕ) : SFam := (planS.getD i (.sealR, 0, 0)).1
def sfamS (i : ℕ) : ℕ := (planS.getD i (.sealR, 0, 0)).2.2
def entS (i : ℕ) : ℕ := (planS.getD i (.sealR, 0, 0)).2.1
def entriesOfS (f : SFam) : ℕ := ((planS.filter fun x => x.1 = f).map fun x => x.2.1).sum
def placesOfS (f : SFam) : ℕ := (planS.filter fun x => x.1 = f).length

#guard planS.length = 232
#guard (planS.map fun x => x.2.1).sum = 48293
#guard seamNamesS.length = 36
#guard (placesOfS .send, entriesOfS .send) = (52, 104)
#guard (placesOfS .lookupCalls, entriesOfS .lookupCalls) = (25, 25440)
#guard (placesOfS .chain, entriesOfS .chain) = (24, 3962)
#guard (placesOfS .rng, entriesOfS .rng) = (25, 25)
#guard (placesOfS .lookupDigits, entriesOfS .lookupDigits) = (25, 18290)
#guard (placesOfS .batSigma, entriesOfS .batSigma) = (25, 25)
#guard (placesOfS .batFold, entriesOfS .batFold) = (25, 238)
#guard (placesOfS .sendLoc, entriesOfS .sendLoc) = (25, 50)
#guard (placesOfS .reply, entriesOfS .reply) = (1, 1)
#guard (placesOfS .headRow, entriesOfS .headRow) = (1, 82)
#guard (placesOfS .merge, entriesOfS .merge) = (1, 22)
#guard (placesOfS .test, entriesOfS .test) = (1, 33)
#guard (placesOfS .batPsc, entriesOfS .batPsc) = (1, 20)
#guard (placesOfS .sealR, entriesOfS .sealR) = (1, 1)

/-- The named hypotheses of `proofSound` by family; K f, the kind of the family f, is a parameter.
-/
structure PFile.FamiliesS (W : PFile) (K : SFam → KFam.{1}) : Prop where
  places : W.n + 1 = planS.length
  /-- data: the block at each place is a value of its family's kind -/
  isOf   : ∀ i ≤ W.n, (W.row.blk i).IsOf (K (famS i))
  /-- 52 places; 104 entries of the plan -/
  send : (K .send).Good
  /-- 25 places; 25,440 entries of the plan -/
  lookupCalls : (K .lookupCalls).Good
  /-- 24 places; 3,962 entries of the plan -/
  chain : (K .chain).Good
  /-- 25 places; 25 entries of the plan -/
  rng : (K .rng).Good
  /-- 25 places; 18,290 entries of the plan -/
  lookupDigits : (K .lookupDigits).Good
  /-- 25 places; 25 entries of the plan -/
  batSigma : (K .batSigma).Good
  /-- 25 places; 238 entries of the plan -/
  batFold : (K .batFold).Good
  /-- 25 places; 50 entries of the plan -/
  sendLoc : (K .sendLoc).Good
  /-- 1 places; 1 entries of the plan -/
  reply : (K .reply).Good
  /-- 1 places; 82 entries of the plan -/
  headRow : (K .headRow).Good
  /-- 1 places; 22 entries of the plan -/
  merge : (K .merge).Good
  /-- 1 places; 33 entries of the plan -/
  test : (K .test).Good
  /-- 1 places; 20 entries of the plan -/
  batPsc : (K .batPsc).Good
  /-- 1 places; 1 entries of the plan -/
  sealR : (K .sealR).Good
  seams  : ∀ g < seamNamesS.length, ∀ i ≤ W.n, sfamS i = g → W.row.SeamAt i
  hands  : ∀ i ≤ W.n, (W.row.seated i).Hands (W.rd i) (W.rd (i + 1))
  head   : W.head.Good
  headH  : W.head.Hands ⟨Prod.snd, id⟩ (W.rd 0)
  tail   : W.tail.Good
  tailH  : W.tail.Hands (W.rd (W.n + 1)) ⟨Prod.snd, Prod.fst⟩
  linOn  : W.linOn.Each

theorem sfamS_lt (i : ℕ) : sfamS i < seamNamesS.length := by
  unfold sfamS
  by_cases h : i < planS.length
  · rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true ((List.all_eq_true.1
      (by decide +kernel : (planS.all fun x => decide (x.2.2 < seamNamesS.length)) = true)) _
      (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    decide +kernel

theorem PFile.fields_of_familiesS (W : PFile) (K : SFam → KFam.{1}) (F : W.FamiliesS K) :
    W.Fields where
  head := F.head
  headH := F.headH
  blocks := W.blocks_by_family famS K F.isOf fun f => by
    cases f
    · exact F.send
    · exact F.lookupCalls
    · exact F.chain
    · exact F.rng
    · exact F.lookupDigits
    · exact F.batSigma
    · exact F.batFold
    · exact F.sendLoc
    · exact F.reply
    · exact F.headRow
    · exact F.merge
    · exact F.test
    · exact F.batPsc
    · exact F.sealR
  seams := fun i hi => F.seams (sfamS i) (sfamS_lt i) i hi rfl
  hands := F.hands
  tail := F.tail
  tailH := F.tailH
  linOn := F.linOn

/-- `proofSound` at the passed object of a written proof file, from its hypotheses by family. -/
theorem proofSound_planS (W : PFile) (K : SFam → KFam.{1}) (F : W.FamiliesS K)
    (H : W.objB.obj.Hon) (Nn : Type) [Inhabited Nn]
    (σT : Samplers (W.objB.obj.S H).lhr.offline.shape) (σL : Samplers (W.objB.obj.S H).lhr.link.shape)
    (σB : Samplers (W.objB.obj.S H).lhr.onlineBatch.loc.shape) (g : (W.objB.obj.S H).Bits)
    (κs Kb κ : ℝ≥0∞) (gdB : σB.Good κs Kb)
    (b1 : Err.BelowG g.req (W.req.blk W.C.cells0).err κ)
    (b2 : Err.BelowG g.linOn W.linOn.blk.b.err κ) :
    ∃ (wit : W.C.X × ((W.objB.obj.S H).lhrW Nn σT σL σB g).Rec →
        (oneExternalString ((W.objB.obj.S H).lhrW Nn σT σL σB g).wordLength
          ((W.objB.obj.S H).lhrW Nn σT σL σB g).Symbol).Str →
        Tr ((W.objB.obj.S H).lhrW Nn σT σL σB g).onlineBatch.loc.shape → W.C.Cells) (ε : _),
      Err.Below ε (κs * κ) ∧ ∀ rec, (((W.objB.obj.S H).lhrW Nn σT σL σB g).batAt rec).SndBKT
        ((W.objB.obj.S H).lhrW Nn σT σL σB g).maxBatchSize ((W.objB.obj.S H).lhrW Nn σT σL σB g).early
        ((W.objB.obj.S H).lhrW Nn σT σL σB g).late
        (((W.objB.obj.S H).lhrW Nn σT σL σB g).relB W.C.Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  W.objB.proofSound_lhrW H (W.proofBlocks (W.fields_of_familiesS K F)) Nn σT σL σB g κs Kb κ gdB
    b1 b2

#print axioms KObj.PFile.fields_of_familiesS
#print axioms KObj.proofSound_planS

end KObj
