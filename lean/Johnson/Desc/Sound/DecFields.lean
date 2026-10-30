-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DecFields.lean: "WHAT THE STORED TABLE DECODES TO": THE TOP STATEMENTS' DECODER AND THE TABLES' GUARDED DECODER HAVE ONE SHAPE: so that they are one is TWO TIES OF FIELDS. One theorem, one corollary. (AT THE RELEASE's CONFIGURATION THE TWO SIDES' RECORDS HAVE NOT ONE TYPE: the library's seed holds, for each answer, a point and A FACTOR OTHER THAN 0 (a subtype: recZ, OnBytes/Slice/RecordRead.lean); the typed data's
seed a point and ANY element (sampleOf, Johnson/Desc/K14/Law/TypedIx.lean): so the ties are said THROUGH A MAP tr OF RECORDS).

The top statements' decoder (ConfigurationWithOutOfDomainSample.D, Hiop/RecConf.lean) is: nothing at a collision at the record's seed; else what the configuration's dcd gives, through held. The tables' guarded decoder (decGuard, Johnson/Desc/Sound/TablePromiseAt.lean) is: nothing at coll; else what dcd gives, through held.
  dec_of_fields: at a configuration K over words of 2^a symbols: WHERE, through the string that is made of the cells (tabBack, Johnson/Desc/Sound/DecTop.lean), (c) K.coll at the record's seed says what coll says at tr of the record and (d) K.dcd gives what dcd gives there: K.conf.D through that string IS decGuard coll dcd K.held at tr of the record.
  decTop_of_fields: then the first table's decoder made of the top statements' (decTop) is decAtRec (decGuard coll dcd K.held) (tr ∘ recOf ∘ fst).
SO the condition (DEC) of Johnson/Desc/Sound/ClaimCarried.lean comes down to (c), (d) and "held is the configuration's own".

Limits. (c) and (d) are premises: at the release's configuration and the typed data of the stored table THEY ARE SHOWN BY NOBODY: each says that two readings of one string (the library's symbols; the tables' columns) give one table over the extension field, and that two records of an index (a code's matrix,
a sample, a radius, a rank) are one. The MESSAGES' type is one here by the statement's form (K.Msg): whoever lays it in must have it one by unfolding (at the release's sizes: rows Fin v → Bool, entries Fin ell: by reading). tr is a letter: the one that is meant forgets that the factor is not 0.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DecTop
import Johnson.Desc.Sound.TablePromiseAt
import OnBytes.Maker.ConfLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker
open Hiop

/-- **One shape**: the top statements' decoder, through the cells, is the guarded decoder, from two ties of fields. -/
theorem dec_of_fields {a : ℕ} {R : Type} (K : ConfLetters a) (tr : K.conf.Rec → R) (coll : CellsOf → R → Prop)
    (dcd : CellsOf → R → Option K.Msg)
    (hc : ∀ c r, K.coll (tabBack a c) r.1 ↔ coll c (tr r))
    (hd : ∀ c r, K.dcd (tabBack a c) r = dcd c (tr r)) :
    ∀ c r, K.conf.D (tabBack a c) r = decGuard coll dcd K.held c (tr r) := by
  intro c r
  unfold ConfigurationWithOutOfDomainSample.D decGuard
  by_cases h : coll c (tr r)
  · rw [if_pos h, if_pos ((hc c r).2 h)]
  · rw [if_neg h, if_neg fun h' => h ((hc c r).1 h')]
    show (K.dcd (tabBack a c) r).bind K.held = _
    rw [hd]

/-- The first table's decoder made of the top statements' is the guarded decoder at a reader of the record. -/
theorem decTop_of_fields {P S R : Type} {a : ℕ} (K : ConfLetters a) (recOf : P → K.conf.Rec)
    (tr : K.conf.Rec → R) (coll : CellsOf → R → Prop) (dcd : CellsOf → R → Option K.Msg)
    (hc : ∀ c r, K.coll (tabBack a c) r.1 ↔ coll c (tr r))
    (hd : ∀ c r, K.dcd (tabBack a c) r = dcd c (tr r)) :
    decTop (S := S) a K.conf.D recOf =
      decAtRec (decGuard coll dcd K.held) (fun x : P × S => tr (recOf x.1)) := by
  funext c x
  exact dec_of_fields K tr coll dcd hc hd c (recOf x.1)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.dec_of_fields
#print axioms VerifiableInference.Desc.Sound.decTop_of_fields
