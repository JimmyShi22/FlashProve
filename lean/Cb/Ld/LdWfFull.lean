-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfFull.lean: the two properties asked of the preamble, the reduction from the claim that the
encoded index is well-formed to the claims of the test for linear constraints (`PreListR`,
`PreKnowR`), from one record of conditions and `CharP E p`.
The lookups are the terms `K.sub`, preamble and test are over one configuration (`W.Cf`), and the
statement is at what the test takes (`W.O.left`).
A parameter list is what is asked of one sub-protocol, in two parts: a record of all items but
round-by-round knowledge soundness (`PreListR`, Hiop/RecSubs.lean), and that item, which is a
definition of its own (`PreKnowR`, Hiop/RecSubs.lean).

Definitions, statements (in `Cb.Spec`) and proofs.

What is put together. Cb/Ld/LdWf.lean: the preamble, conditional on `P.Laws` and `B.Hyp`.
Cb/Obj/LdObjectWf.lean: what it leaves is the datum of the test for linear constraints (`W.Tie`).
Cb/Ld/LdWfBlocks.lean: the lookups are the assembled lookup on the keys of the index (six fields of
`B.Hyp`; with Cb/Ld/LdWfBlocksMask.lean all eight whose names begin with lkp).
Cb/Ld/LdWfMasks.lean: the two fields on masks sent in advance, from one layout of the sender's
coins. Cb/Ld/LdWfKeys.lean: "a key map is linear", for keys affine in one column of the matrix of
the index, whatever the matrix. Cb/Obj/LdObjectConf.lean: two laws of the configuration.

The data (`LdWfF F E`):
  `W`: configuration, data of the preamble, layout, the test's further data.
  `K`: the places and numbers of the lookups.
  `D`, `L`, `t`: the honest sender, bounds for lists, long positions that the encodings bear.
  `Dm`: the parameters (letters) of each lookup's item "masked messages".
  `Rd`: the entries that the batching reads.
  `p0`, `r0`: a fixed prover encoded index, fixed randomness: values of extractors that nobody
    reads.
  `rv`, `o`, `co`: rows of keys, offsets and coefficients of the key maps.
  `G.B`: the blocks.

The conditions (`G.OK Y p Lc`), by kind:
  configuration: `conf`: `Cf.OK Lc` (code, radius, list, sample, model: Cb/Obj/LdObjectConf.lean).
  model: `describes`: a message holds an index if and only if the keys of all forests lie in their
  tables.
  places: `tie`: the matrix of the index is the index matrix in the layout of the encoded index;
  `masks`: `Y.OK`, one layout of the sender's coins and the places of all blocks' masks
  (Cb/Ld/LdWfMasks.lean); `own`: the batching's own places (Cb/Ld/LdWfOwn.lean: different; read by
  the batching; outside the public support of every claim's mask form; and the fields `mat`, `rdC`).
  keys: `lin`: the key maps are affine in one column of the matrix, with public offsets and
  coefficients.
  numbers: `lks`: `K.OK p` (numbers of keys, bit positions, table sizes against the characteristic
  p; the room for rows; what "the multiplicities" means for the bits at their places; the public
  supports: `gC l` contains the two inner masks of the last level of the forest's keys' tree,
  `gR l b` all places that the lookup on forest l names, but of the inner masks of the keys' tree
  those below its last level only (`LkAsm2.PlacesInR`, Cb/Ld/LdBldWfSupp.lean)); `deg`; `zOK`.
  codes: `laws`, `list`, `evades`: of the oracle messages that the preamble sends.
  sender: `fair`, `sender`, `sBlind`, `hides`; `multOf`: the vectors that the honest prover computes
  are the multiplicities, for every forest whose keys lie in its table.
  Still hypotheses on a block, not conditions on data:
    `item`: each lookup as a whole has the item "masked messages" with the letters `Dm l`;
    `claim`: its exact input relation gives the item's claim;
    also inside `Y.OK`: `rd`, `com` for the lookups' letters, and `blind`; of the same kind, on the
    honest sender `D` (a free value with laws): `sender`, `sBlind`, `hides` above, and inside `Y.OK`
    its fields `pad`, `own`, `off` (`MaskLay.OK`, Cb/Ld/LdWfMasks.lean).

Main names, each under `G.OK Y p Lc`, and all but `Spec.ldWfFull_laws` under `CharP E p`:
  `Spec.ldWfFull_laws`, `Spec.ldWfFull_hyp`: the conditions give `P.Laws` and `B.Hyp`.
  `Spec.ldWfFull`: the two items of the object: `PreListR` and `PreKnowR` of `G.B.wf` at `W.O.left`:
    the parameter list of the preamble of weights-formedness and its item on knowledge soundness:
    from weights-formedness, on statements without a collision of the index, with the relaxation
    "the index decoder answers", into the collision-free statements of the constraint relation of
    `W.O.left`. Nothing is extracted.
  `Spec.ldWfFull_side`: nothing hidden is withheld, nothing is tied, and the preamble bears what
    follows (at most `t a` long positions of each oracle message a; of the index a set within `q`)
    (`Side`, Ior/KnowCollPiece.lean: `noHid`, `noTie`, `bears`; `Bears`, Ior/Bears.lean; in words:
    the doc comment of `Spec.ldWf_side`, Cb/Ld/LdWf.lean). The two facts on the lookups that
    Cb/Ld/LdWf.lean's statement asks are theorems here.

Cb/Ld/LdWfEnd.lean has no hypothesis on a block left (`item`, `claim` and the three clauses inside
`Y.OK` are theorems there, under `Z.OK p Lc` and `CharP E p`) but for six on the sender.


Limits: this file does not say that a lookup has its item: `item` and `claim` are hypotheses. It
says nothing on numbers of an instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectWf
import Cb.Ld.LdWfBlocksProofs
import Cb.Ld.LdWfMasks
import Cb.Ld.LdWfKeys
import Cb.Ld.LdWfOwn
import Cb.Obj.LdObjectConfProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

/-- Weights-formedness with its lookups as values: the data. -/
structure LdWfF (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  W  : LdOWf F E
  K  : W.P.Lks
  D  : W.P.S.Sender (W.P.Body × W.P.Wp) W.P.Wp
  L  : W.P.S.O → ℕ
  t  : W.P.S.O → ℕ
  Dm : ∀ l, MaskData (K.sub l).R W.P.W
  Rd : W.P.bt.J → Prop
  p0 : W.Cf.conf.PIdx
  r0 : W.P.S.Rnd
  rv : ℕ → ℕ
  o  : ℕ → ℕ → E
  co : ℕ → ℕ → W.P.Rw → E

namespace LdWfF
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (G : LdWfF F E)

/-- The blocks. -/
@[reducible] def B : G.W.P.Blk := ⟨G.D, G.L, G.t, G.K.sub, G.Dm, G.Rd, G.p0, G.r0⟩

/-- The named conditions. -/
structure OK (Y : G.B.MaskLay) (p Lc : ℕ) : Prop where
  conf      : G.W.Cf.OK Lc
  describes : ∀ U, (G.W.Cf.conf.held U).isSome ↔ ∀ f, f ≤ G.W.P.n → G.W.P.InT f U
  tie       : G.W.Tie
  lin       : G.W.P.LinKeys G.rv G.o G.co
  lks       : G.K.OK p
  multOf    : ∀ U f, f ≤ G.W.P.n → G.W.P.InT f U → G.W.P.mult f U (G.W.P.bodyOf U)
  laws      : ∀ a, (G.W.P.S.om a).C.Laws
  list      : ∀ a, (G.W.P.S.om a).ListLE (G.L a)
  evades    : ∀ a, (G.W.P.S.om a).Evades
  fair      : G.W.P.Sd.Fair
  sender    : G.D.Laws G.W.P.back
  sBlind    : G.D.Blind G.W.P.Sd
  hides     : G.D.Nn.Hides (G.W.P.S.budT G.t)
  masks     : Y.OK
  deg       : 2 ≤ G.W.P.deg
  zOK       : G.W.P.Z.OK
  own       : G.W.P.OwnPlaces G.Rd
  /-- still hypotheses on a block -/
  item      : ∀ l, l ≤ G.W.P.n → (G.K.sub l).H.MM (G.Dm l)
  claim     : ∀ l, l ≤ G.W.P.n →
    ∀ x y w, (jt2 G.W.P.S G.W.Cf.conf.E0 G.W.P.Wp G.W.P.onW (G.W.P.honAt l)
          ((G.W.P.lk l).inP (G.W.P.multAt l)) (G.W.P.lk l).inR).rel
        x y w →
      (G.Dm l).Cl ((G.Dm l).pub x) ((G.Dm l).kc w)

end LdWfF

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldWfFull_laws : Prop := ∀ (G : LdWfF F E) (Y : G.B.MaskLay) (p Lc : ℕ), G.OK Y p Lc → G.W.P.Laws

def ldWfFull_hyp : Prop :=
  ∀ (p : ℕ) [CharP E p] (G : LdWfF F E) (Y : G.B.MaskLay) (Lc : ℕ), G.OK Y p Lc → G.B.Hyp

/-- The two items of the object, from the named conditions and `CharP E p`. -/
def ldWfFull : Prop :=
  ∀ (p : ℕ) [CharP E p] (G : LdWfF F E) (Y : G.B.MaskLay) (Lc : ℕ), G.OK Y p Lc →
    PreListR G.W.O.left G.B.wf G.B.hWf id id G.W.Cf.conf.Rwf G.B.nums ∧
    PreKnowR G.W.O.left G.B.wf G.W.Cf.conf.free G.W.Cf.conf.RwfR (fun _ _ _ => ()) G.B.nums.err

/-- Under the hypotheses below, the preamble bears what follows within `qFam q G.t` (`Side`'s field
`bears`). -/
def ldWfFull_side : Prop :=
  ∀ (p : ℕ) [CharP E p] (G : LdWfF F E) (Y : G.B.MaskLay)
      (Lc : ℕ) (q : Finset G.W.Cf.conf.E0.Pos → Prop),
    G.OK Y p Lc → Side G.B.wf G.B.hWf G.B.nums.bud q (G.W.P.S.qFam q G.t)

end
end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldWfFull_laws : Spec.ldWfFull_laws F E := fun G _ _ _ h =>
  { describes := h.describes
    held_hold := ldCf_held_hold F E G.W.Cf h.conf.held
    dcd_enc := ldCf_dcd_enc F E G.W.Cf h.conf.core.dist h.conf.rad
    multOf := h.multOf
    keyLin := ldWfK_keyLin E G.W.Cf.conf G.W.P G.rv G.o G.co h.lin }

theorem ldWfFull_hyp : Spec.ldWfFull_hyp F E := fun p _ G Y Lc h =>
  have hL := ldWfFull_laws G Y p Lc h
  have hM := ldWfM_hyp G.W.Cf.conf G.W.P G.B Y h.masks h.hides
  { laws := h.laws
    fair := h.fair
    list := h.list
    evades := h.evades
    sender := h.sender
    sBlind := h.sBlind
    hides := h.hides
    lkp := ldWfB_lkp E p G.W.Cf.conf G.W.P G.K hL h.lks
    lkpM := h.item
    lkpC := h.claim
    lkpI := fun l _ => ldWfB_idx E G.W.Cf.conf G.W.P G.K l
    lkpP := fun l _ => ldWfB_passes E G.W.Cf.conf G.W.P G.K l
    lkpH := fun l _ => ldWfB_same E G.W.Cf.conf G.W.P G.K l
    lkpN := ldWfB_len E p G.W.Cf.conf G.W.P G.K h.lks
    lkpS := ldWfB_supp E p G.W.Cf.conf G.W.P G.K h.lks
    fresh := hM.1
    freshB := hM.2
    deg := h.deg
    zOK := h.zOK
    own := ldWfOwn_ok G.W.Cf.conf G.W.P G.Rd h.own }

theorem ldWfFull : Spec.ldWfFull F E := fun p _ G Y Lc h =>
  ldOWf_items G.W G.B h.tie (ldWfFull_laws G Y p Lc h) (ldWfFull_hyp p G Y Lc h)

theorem ldWfFull_side : Spec.ldWfFull_side F E := fun p _ G Y Lc q h =>
  ldWf_side E G.W.Cf.conf G.W.P G.B q (ldWfFull_hyp p G Y Lc h)
    (fun l _ ρ =>
      lift_bud G.W.P.S
        (ldLkpAsm2N_plainI E (G.K.asm l) G.W.P.N Sum.inr G.W.Cf.conf G.W.P.S.Msg G.W.P.msg) ρ ∅)
    (fun l _ ρ U =>
      lift_need G.W.P.S
        (ldLkpAsm2N_plainI E (G.K.asm l) G.W.P.N Sum.inr G.W.Cf.conf G.W.P.S.Msg G.W.P.msg) ρ U)

end
end Cb
