-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LayersSayStatement.lean: what the 24 sub-proofs of the layers say, without the
head: a statement. Two definitions; no theorem.

  lastOf y Mz: the stream behind a group's last layer, as the group's list of integer matrices holds
    it.
  LayersSay: under the public premises of Johnson/Goal/Meaning/TieR.lean: if each of the 12 groups
    of layers and each of the 12 attention sub-proofs is in order at its own list (LayerOrd, AttOrd:
    every entry below 2^18, every identity 0 modulo the protocol's prime, every key an entry of its
    table), the stream that comes into a later group is the stream that went out of the group
    before, an attention sub-proof's copy of its group's queries, keys, values and outputs is the
    original, and the stream that the last group's list holds is below 2^39, then the integer
    program runs through all 48 layers on the request's tokens (SaysLayers,
    Johnson/Meaning/Halves.lean, at the program's own stream), and the stream that the last group's
    list holds is the program's.

Why the bound stands among the premises. In the library's conditions no clause of a group bounds the
stream that goes out of it: the reader's normalisation does. For the last group the reader is the
head (Cm/Rel2Layers.lean: "the bound that a head gives"); Meaning.last_bound has it from the head's
half.
-/
import Johnson.Meaning.Halves
import Johnson.Meaning.Lists
import Johnson.Meaning.PublicCore
import Ladder

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)

/-- The stream behind a group's last layer, as the group's list of integer matrices holds it: the
library's reading of the stream's limbs (FFSeg.xS at index 8) at the cells that the library's
dictionary reads in the list. -/
def lastOf (y : Lay) (Mz : Mats ℤ) : ℕ → Vec := fun pos j =>
  FFSeg.xS DF (cellsOf DF (cellsAt y Mz)) 8 j pos

/-- **What the layers' 24 sub-proofs say.** -/
def LayersSay : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (lay : Option ByteArray) (X : Model.Verify.Public),
    VerifierAndGoals.readFiles Z = .ok pp → publicOf Z.pol Z.KL lay = .ok X → Hd.PublicCore X.P →
    ∀ (i : Cm.Idx) (x : Instance ppref) (MG : ℕ → Mats ℤ) (MA : ℕ → Zs),
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x) →
      (∀ g < 12, AttOrd (Hd.shapeA X g) (MA g)) →
      (∀ g, 0 < g → g < 12 → ∀ r c, MG g (matIx X.y).iXI r c = MG (g - 1) (matIx X.y).iXO r c) →
      (∀ g < 12, ∀ r c, MA g ((Hd.shapeA X g).cf.NAs + 3) r c = MG g (matIx X.y).iQA r c) →
      (∀ pos < ppref.T, ∀ j < ppref.d, |lastOf X.y (MG 11) pos j| < 2 ^ 39) →
      SaysLayers pp i.index.val x (streamOf pp i.index.val x) ∧
        Agree ppref (lastOf X.y (MG 11)) (streamOf pp i.index.val x (2 * ppref.layers))

end Meaning
