-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DataAlong.lean: "ONE DECODER" WHERE TYPES HANG ON THE DATA. The top statements' configuration stands over data of a decoder D₀ at WRITTEN numbers; the shared chain's block 1's guarded decoder decK stands over the plan's shape, a letter. The claims, the rest, the records and the messages are typed over the
data: an equation of two data does not rewrite them. Here each thing that must cross is CARRIED ALONG THE EQUATION BY A DEFINITION, and each fact on it is proved with the data as a VARIABLE (the equation is then taken away by substitution). Five definitions, nine theorems.

  heldAlong e A R: the configuration's own held ("in range", then the matrix), as a function of block 1's messages · trAlong e: a record of D₀, as a record of block 1's typed data (it forgets "the factor is not 0").
  held_refl, tr_refl: at the equation rfl they are configurationOfStoredTable's held and (trS of the seed, the answers): rfl.
  dec_at_data: **AT EVERY DATA D₀ THAT ARE decROfS OF THE SHAPE, every claims and rest: configurationOfStoredTable.D, through the cells, IS decGuard collAt dcdAt (heldAlong …) at trAlong of the record.**
  Sized ix a l r v lg s cut: seven equations of numbers: the table's shape has these · decRNum: the data at seven plain numbers and a radius · decR_sized: under Sized, decROfS = decRNum.
  key_at_num: under Sized and NoZero: block 1's reader of a key gives trAlong of recBack v lg s of that key · keyOf_at_num: at a key that was written of a record: trAlong of that record (no premise on factors: by type).
  full_sized: the full size's seven numbers, from one equation on the plan's table's shape.
  heldFull: heldAlong at the release's configuration (kcReq, Johnson/Flat/TiesAtReq.lean).
  dec_full_keyOf: **AT THE RELEASE's CONFIGURATION AT THE WRITTEN SIZES: at a state whose key was written of rec: decK … heldFull c s = (kcReq N pp E).conf.D (tabBack frS.P.T.a c) rec.**
  dec_full_key: the same at any key without a factor 0, at recBack frS.P.v 29 1 of the key.
WHAT IT IS NOT: that the release's plan has that table's shape: a premise (one public equation). That a description lays keyOf of the instance's record into its public part and that part's key into the shared chain's first state: premises of whoever calls it.

Limits. The full size alone for the last four. rank is the library's. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAlong
import Johnson.Desc.Sound.FullClosed
import Johnson.Flat.TiesAtReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open VerifiableInference.Desc.Sound (tabBack decGuard decAtRec CellsOf)
open VerifiableInference.OnPublicFiles (kcReq)

section Along
variable (p : Par) (err eM : Nat)

/-- The configuration's own held, as a function of block 1's messages: carried along the equation of data. -/
noncomputable def heldAlong {D₀ : DecR} (e : decROfS p.S.fold eM = D₀) {X : Type} (A : D₀.Claims X)
    (R : D₀.RelationsAndEncoding A) :
    ((ixOf2 p.S.fold err eM (rankLib p.S.fold)).Row × Fin p.S.fold.index.code.ell → GE) → Option A.Mat := by
  subst e
  exact (DecR.configurationOfStoredTable A R).held

/-- A record of the data, as a record of block 1's typed data: carried along the equation. -/
def trAlong {D₀ : DecR} (e : decROfS p.S.fold eM = D₀) :
    D₀.Rec → (ixOf2 p.S.fold err eM (rankLib p.S.fold)).Rec := by
  subst e
  exact fun r => (trS p.S.fold.index err r.1, r.2)

/-- At the equation rfl it is the configuration's held. -/
theorem held_refl {X : Type} (A : (decROfS p.S.fold eM).Claims X) (R : (decROfS p.S.fold eM).RelationsAndEncoding A) :
    heldAlong p err eM rfl A R = (DecR.configurationOfStoredTable A R).held := rfl

/-- At the equation rfl it forgets "not 0". -/
theorem tr_refl (r : (decROfS p.S.fold eM).Rec) :
    trAlong p err eM rfl r = (trS p.S.fold.index err r.1, r.2) := rfl

/-- **The top statements' own decoder over any data that are decROfS of the shape, through the cells, is block 1's guarded decoder.** -/
theorem dec_at_data {D₀ : DecR} (e : decROfS p.S.fold eM = D₀) {X : Type} (A : D₀.Claims X) (R : D₀.RelationsAndEncoding A)
    (c : CellsOf) (r : D₀.Rec) :
    (DecR.configurationOfStoredTable A R).D (tabBack D₀.T.a c) r =
      decGuard (collAt p err eM (rankLib p.S.fold)) (dcdAt p err eM (rankLib p.S.fold))
        (heldAlong p err eM e A R) c (trAlong p err eM e r) := by
  subst e
  exact dec_at_conf p err eM A R c r

end Along

/-- The table's shape has these seven numbers. -/
structure Sized (ix : IndexShape) (a l r v lg s cut : Nat) : Prop where
  a : ix.code.logN = a
  l : ix.code.ell = l
  r : ix.code.r = r
  v : ix.v = v
  lg : ix.cubeBits = lg
  s : ix.answers = s
  cut : ix.plain = cut

/-- The library's data of a decoder with a record, at seven plain numbers and a radius. -/
@[reducible] def decRNum (a l r v lg s cut eM : Nat) : DecR :=
  { T := ⟨a, l, r⟩, v := v, eM := eM, Z := recZ l lg s, cut := cut }

/-- Under the seven equations the data off the shape are the data at the numbers. -/
theorem decR_sized (S : FoldeqShape) (eM : Nat) {a l r v lg s cut : Nat} (H : Sized S.index a l r v lg s cut) :
    decROfS S eM = decRNum a l r v lg s cut eM := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- **(KEY) at plain numbers**: block 1's reader of a key without a factor 0 gives the record that recBack reads, carried along. -/
theorem key_at_num (p : Par) (err eM : Nat) {a l r v lg s cut : Nat} (H : Sized p.S.fold.index a l r v lg s cut)
    (k : TableKey) (hz : NoZero p.S.fold.index k) :
    recAtKey p err eM (rankLib p.S.fold) k =
      trAlong p err eM (decR_sized p.S.fold eM H) (recBack v lg s k : (decRNum a l r v lg s cut eM).Rec) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  subst h1 h2 h3 h4 h5 h6 h7
  exact (key_iff p err eM (rankLib p.S.fold) k).2 hz

/-- **At a key that was written of a record**: that record, carried along. No premise on factors: by the record's type. -/
theorem keyOf_at_num (p : Par) (err eM : Nat) {a l r v lg s cut : Nat} (H : Sized p.S.fold.index a l r v lg s cut)
    (rec : RecP NZ v lg s) :
    recAtKey p err eM (rankLib p.S.fold) (keyOf (fun β : NZ => β.val) rec) =
      trAlong p err eM (decR_sized p.S.fold eM H) (rec : (decRNum a l r v lg s cut eM).Rec) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  subst h1 h2 h3 h4 h5 h6 h7
  exact key_at_keyOf p err eM (rankLib p.S.fold) rec

/-- The full size's seven numbers, from one equation on the table's shape. -/
theorem full_sized (ix : IndexShape) (sb : Nat) (h : ix = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩) :
    Sized ix 32 402653184 44040191 11 29 1 402653181 := by
  subst h
  have h29 : ceilLog2 402653184 = 29 := by decide +kernel
  exact ⟨rfl, rfl, rfl, rfl, h29, rfl, rfl⟩

section Full
variable (p : Par) (err sb : Nat) (h : p.S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩)
  (N : OnBytes.Flat.MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (frS.toDecR frZ 402653181) N pp))

/-- **The release's configuration's own held, as a function of block 1's messages.** -/
noncomputable def heldFull :
    ((ixOf2 p.S.fold err 2852142980 (rankLib p.S.fold)).Row × Fin p.S.fold.index.code.ell → GE) →
      Option (kcReq N pp E).conf.I :=
  heldAlong p err 2852142980 (full_of_index p.S.fold sb h)
    (OnBytes.Flat.claimsReqAt (frS.toDecR frZ 402653181) N pp) (OnBytes.Flat.relationsAndEncodingOfClaims _ E)

/-- **ONE DECODER AT THE RELEASE's CONFIGURATION, at a key without a factor 0.** -/
theorem dec_full_key (c : CellsOf) (s : St) (hz : NoZero p.S.fold.index s.loc.key) :
    decK p err 2852142980 (rankLib p.S.fold) (heldFull p err sb h N pp E) c s =
      (kcReq N pp E).conf.D (tabBack frS.P.T.a c) (recBack frS.P.v 29 1 s.loc.key) := by
  have e1 := dec_at_data p err 2852142980 (full_of_index p.S.fold sb h)
    (OnBytes.Flat.claimsReqAt (frS.toDecR frZ 402653181) N pp) (OnBytes.Flat.relationsAndEncodingOfClaims _ E) c
    (recBack frS.P.v 29 1 s.loc.key)
  have e2 := key_at_num p err 2852142980 (full_sized p.S.fold.index sb h) s.loc.key hz
  refine Eq.trans ?_ e1.symm
  show decGuard _ _ _ c (recAt p err 2852142980 (rankLib p.S.fold) s) = _
  rw [recAt_key, e2]
  rfl

/-- **ONE DECODER AT THE RELEASE's CONFIGURATION, at a state whose key was written of the instance's record.** -/
theorem dec_full_keyOf (c : CellsOf) (s : St) (rec : (kcReq N pp E).conf.Rec)
    (hk : s.loc.key = keyOf (fun β : NZ => β.val) rec) :
    decK p err 2852142980 (rankLib p.S.fold) (heldFull p err sb h N pp E) c s =
      (kcReq N pp E).conf.D (tabBack frS.P.T.a c) rec := by
  have e1 := dec_at_data p err 2852142980 (full_of_index p.S.fold sb h)
    (OnBytes.Flat.claimsReqAt (frS.toDecR frZ 402653181) N pp) (OnBytes.Flat.relationsAndEncodingOfClaims _ E) c rec
  have e2 := keyOf_at_num p err 2852142980 (full_sized p.S.fold.index sb h) rec
  refine Eq.trans ?_ e1.symm
  show decGuard _ _ _ c (recAt p err 2852142980 (rankLib p.S.fold) s) = _
  rw [recAt_key, hk]
  exact congrArg (fun t => decGuard _ _ (heldFull p err sb h N pp E) c t) e2

end Full

end Desc.K14.Law

#print axioms Desc.K14.Law.dec_at_data
#print axioms Desc.K14.Law.decR_sized
#print axioms Desc.K14.Law.key_at_num
#print axioms Desc.K14.Law.keyOf_at_num
#print axioms Desc.K14.Law.full_sized
#print axioms Desc.K14.Law.dec_full_key
#print axioms Desc.K14.Law.dec_full_keyOf
