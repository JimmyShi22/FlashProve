-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KeyAlong.lean: (KEY): THE KEY's RECORD AS THE TWO SIDES READ IT. The shared chain's block 1 reads the record off the key in its own state (recAt, Johnson/Desc/K14/Law/CellsTie.lean): each seed's factor AS IT STANDS. The top statements' side reads it off the same key by the library's recOfKey
(OnBytes/Slice/BlkKeyRec.lean; recBack, OnBytes/Slice/KeyBack.lean, is its text at three plain numbers): a factor 0 is read AS 1, because the library's type of factors has no 0. Two definitions, six theorems. General in the shape.

  NoZero s k: no factor of the key's seeds, as far as the shape has answers, is read as 0.
  recAtKey: recAt's text as a function of the key alone · recAt_key: rfl.
  key_iff: **THE TWO READINGS GIVE ONE RECORD (through trS, which forgets "not 0") IF AND ONLY IF NoZero.** So NoZero is not a convenience: at every key with a factor 0 the equation is false.
  noZero_keyOf: NoZero holds of every key that was WRITTEN of a record of the library's type (keyOf, OnBytes/Slice/KeyOfRec.lean): by that type.
  key_at_keyOf: so at such a key block 1's reader gives the written record back, through trS.
  dec_at_key: under NoZero, at every configuration over decROfS: THE GUARDED DECODER decK AT A STATE IS configurationOfStoredTable.D AT THE RECORD THAT recOfKey READS OFF THAT STATE's KEY.
  dec_at_keyOf: at a state whose key was written of rec: decK there IS configurationOfStoredTable.D at rec.
WHO CAN PROMISE NoZero. Not the description's test on the instance (okKey, Johnson/Desc/K14/Blocks.lean: words below the prime; the item's number: no test on a factor). Not the public part's type (a key there is any TableKey). The chain's own text refuses a factor 0 (Johnson/Desc/K14/Text.lean: "no seed of the record has the factor 0") two blocks behind block 1: too late for block 1's law. IT IS PROMISED WHERE THE PUBLIC
PART IS MADE OF THE TOP STATEMENTS' INSTANCE: there the key is keyOf of the instance's record.

Limits. rank is the library's. Nothing is said at a key with a factor 0 but that the equation fails. A key with fewer seeds than the shape has answers is read at the default seed there, by both sides. That a description's public part holds keyOf of the instance's record, and that its shared chain's first state holds that key, are premises of whoever calls this. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ConfAlong
import Johnson.Desc.Sound.PointAtK14Closed
import OnBytes.Slice.KeyBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open VerifiableInference.Desc.Sound (tabBack decGuard decAtRec CellsOf)

/-- No factor of the key's seeds, as far as the shape has answers, is read as 0. -/
def NoZero (s : IndexShape) (k : TableKey) : Prop :=
  ∀ a : Fin s.answers, readE (k.seeds.getD a.val default).beta ≠ 0

/-- Block 1's reader of the record, as a function of the key alone. -/
def recAtKey (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (k : TableKey) : (ixOf2 p.S.fold err eM rank).Rec :=
  (seedsFn OnBytes.Model.Reading.gl p.S.fold.index k,
    recOf p.S.fold.index fun j => OnBytes.Model.Reading.gl.val (k.record.getD j zeroE))

/-- The reader reads the state's key alone. -/
theorem recAt_key (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (s : St) : recAt p err eM rank s = recAtKey p err eM rank s.loc.key := rfl

/-- **(KEY), exactly**: the two readings of a key give one record just where no factor is read as 0. -/
theorem key_iff (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (k : TableKey) :
    recAtKey p err eM rank k =
        ((trS p.S.fold.index err (recOfKey p.S.fold.index k).1, (recOfKey p.S.fold.index k).2) :
          (ixOf2 p.S.fold err eM rank).Rec) ↔
      NoZero p.S.fold.index k := by
  constructor
  · intro h a h0
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) a)
    have h2 : readE (k.seeds.getD a.val default).beta =
        (asFactor (readE (k.seeds.getD a.val default).beta)).val := h1
    exact (asFactor (readE (k.seeds.getD a.val default).beta)).property (h2.symm.trans h0)
  · intro h
    refine Prod.ext ?_ ?_
    · funext a
      refine Prod.ext rfl ?_
      show readE (k.seeds.getD a.val default).beta =
        (asFactor (readE (k.seeds.getD a.val default).beta)).val
      exact (asFactor_val (h a)).symm
    · funext q
      show readE (k.record.getD (numOf p.S.fold.index.v q.1 * p.S.fold.index.answers + q.2.val) zeroE) =
        readE (k.record.getD (Sz.rowNo q.1 * p.S.fold.index.answers + q.2.val) zeroE)
      rw [numOf_rowNoS]
      rfl

/-- A key that was written of a record of the library's type has no factor 0: by that type. -/
theorem noZero_keyOf (s : IndexShape) (rec : RecP NZ s.v s.cubeBits s.answers) :
    NoZero s (keyOf (fun β : NZ => β.val) rec) := by
  intro a
  rw [keyOf_beta]
  exact (rec.1 a).2.property

/-- So at such a key block 1's reader gives the written record back. -/
theorem key_at_keyOf (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (rec : RecP NZ p.S.fold.index.v p.S.fold.index.cubeBits p.S.fold.index.answers) :
    recAtKey p err eM rank (keyOf (fun β : NZ => β.val) rec) =
      ((trS p.S.fold.index err rec.1, rec.2) : (ixOf2 p.S.fold err eM rank).Rec) := by
  rw [(key_iff p err eM rank _).2 (noZero_keyOf p.S.fold.index rec), ← recBack_eq_recOfKey, recBack_keyOf]

/-- **Under NoZero the guarded decoder at a state is the top statements' own decoder at the record read off that state's key.** -/
theorem dec_at_key {X : Type} (p : Par) (err eM : Nat) (A : (decROfS p.S.fold eM).Claims X)
    (R : (decROfS p.S.fold eM).RelationsAndEncoding A) (c : CellsOf) (s : St) (h : NoZero p.S.fold.index s.loc.key) :
    decK p err eM (rankLib p.S.fold) (DecR.configurationOfStoredTable A R).held c s =
      (DecR.configurationOfStoredTable A R).D (tabBack p.S.fold.index.code.logN c) (recOfKey p.S.fold.index s.loc.key) := by
  rw [dec_at_conf p err eM A R c]
  show decGuard _ _ (DecR.configurationOfStoredTable A R).held c (recAt p err eM (rankLib p.S.fold) s) = _
  rw [recAt_key, (key_iff p err eM (rankLib p.S.fold) s.loc.key).2 h]
  rfl

/-- **At a state whose key was written of a record the guarded decoder is the top statements' own at that record.** -/
theorem dec_at_keyOf {X : Type} (p : Par) (err eM : Nat) (A : (decROfS p.S.fold eM).Claims X)
    (R : (decROfS p.S.fold eM).RelationsAndEncoding A) (c : CellsOf) (s : St) (rec : (decROfS p.S.fold eM).Rec)
    (hk : s.loc.key = keyOf (fun β : NZ => β.val) rec) :
    decK p err eM (rankLib p.S.fold) (DecR.configurationOfStoredTable A R).held c s =
      (DecR.configurationOfStoredTable A R).D (tabBack p.S.fold.index.code.logN c) rec := by
  rw [dec_at_key p err eM A R c s (by rw [hk]; exact noZero_keyOf p.S.fold.index rec), hk,
    ← recBack_eq_recOfKey, recBack_keyOf]

-- A CONTROL: at a key whose first seed has the factor 0, at a shape with an answer, NoZero fails: so by key_iff (KEY) fails there
example (s : IndexShape) (h : 0 < s.answers) : ¬ NoZero s { seeds := [⟨[], zeroE⟩] } :=
  fun hn => hn ⟨0, h⟩ readE_zero

end Desc.K14.Law

#print axioms Desc.K14.Law.key_iff
#print axioms Desc.K14.Law.noZero_keyOf
#print axioms Desc.K14.Law.key_at_keyOf
#print axioms Desc.K14.Law.dec_at_key
#print axioms Desc.K14.Law.dec_at_keyOf
