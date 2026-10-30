-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfEnd.lean: the properties asked of the reduction from the claim that the encoded index is
well-formed to the claims of the test for linear constraints (the preamble's two items and its
budgets' half), from conditions on its data and on the honest sender.
Weights-formedness, the end. No hypothesis on a block is left, but for six on the sender.

The sender `Z.D` is a free value with laws. These are six clauses: `sender`, `sBlind`, `hides`;
`pad`, `sOwn`, `sOff`. They are properties of a term, not of data. For the standard sender they are
theorems (Cb/Ld/LdWfEndStd.lean: `ldWfE_std`; Cb/Obj/LdObjectDataSnd.lean: `ldWfE_okStd`), under the
hypotheses of their statements, among them `Y.OK Z.t` (`Sig.StdL.OK`, Cb/Ld/LdSendStdL.lean; it is
`ok` below), two of whose fields are `hides` and `priv`. Then
`Z.Rest2 p`, `laws`, `conf`, `list`, `evades`, places (`plL`, `plB`, `noPad`), and `isStd`, `ok`,
`body`, `bdDat` of `LdWfE.StdW.Hyp` (Cb/Obj/LdObjectDataSnd.lean), with the proof `hpl` among its
data `V` and the instance `[∀ b, Fintype (Z.K.wfI Z.Rl b → E)]`, are all that is asked for
`Z.OK p Lc`.
Definitions, statements (in `Cb.Spec`) and proofs (an assembly). The two items are `PreListR` and
`PreKnowR` (Hiop/RecSubs.lean), the budgets' half is `Side` (Ior/KnowCollPiece.lean).

Cb/Ld/LdWfFull.lean asks two things of a block (each lookup as a whole has the item "masked
messages"; its exact relation gives the item's claim), and, inside its clause on masks, three more
(the lookups' letters are functions of the wide reading (`wfWide`, Cb/Ld/LdWfMasks.lean); no earlier
lookup looks at later masks).
All five are theorems, each under the hypotheses of its statement:
  the item at the base for the assembled lookup (Cb/Ld/LdLkpMaskAsm2.lean), its conditions on places
  from four plain ones (Cb/Ld/LdLkpMaskPlaces2.lean: `PlacesOK`); carried to the lookups of the
  preamble (Cb/Ld/LdLkpMaskLift2.lean, Cb/Ld/LdWfBlocksMask.lean); the letters, that is the item's
  parameters (Cb/Ld/LdWfMasksLkp.lean); one value for all places of masks (Cb/Ld/LdWfMasksAll.lean).

The data (`LdWfE F E`). `W`: configuration, data of the preamble, layout, the test's further data.
`K`: numbers and places of the lookups. `D`, `L`, `t`: honest sender, bounds for lists, long
positions borne. `Rl f`: the entries that the item of lookup f reads; `RdB`: those that the batching
reads. `X`: where the named entries are in the messages, the wide reading, the layout of the
sender's coins, the places of all blocks' masks. `rv`, `o`, `co`: the key maps.

The conditions (`Z.OK p Lc`), by kind. Every one speaks of data, but for the six on the sender.
  configuration: `conf`: `Cf.OK Lc`; `val`: the encoded index has a value (a word exists).
  model: `describes`: a message holds an index if and only if the keys of all forests lie in their
  tables.
  keys: `lin`: the key maps are affine in one column of the matrix of the index.
  numbers: `lks`: `K.OK p` (Cb/Ld/LdWfBlocks.lean). It holds more than numbers: `v`, `adm`: numbers
  of keys, bit positions, table sizes against the characteristic p; `rows`: the room for rows;
  `mult` (model): what "the multiplicities" means for the bits at their places; `supC`, `supR`
  (places): the public support gC f contains the two inner masks of the last level of the forest's
  keys' tree, gR f b all places that the lookup names but those two inner masks (exactly: `cK l b`
  is asked for l < v' only: `LkAsm2.PlacesInR`, Cb/Ld/LdBldWfSupp.lean) (Cb/Ld/LdWfBlocks.lean,
  "Why"); `deg`; `zOK`.
  codes: `laws`, `list`, `evades`: of the oracle messages that the preamble sends.
  sender: `fair`, `sender`, `sBlind`, `hides`, `multOf`; `pad`, `sOwn`, `sOff`: the layout of its
  coins (the pads alone fix the law of the answers; the entry at a mask place is the mask value;
  other entries shown read neither these masks nor the pads).
  places: `tie`: the matrix of the index is the index matrix in the layout of the encoded index.
    `lkPl`: inside each lookup: its own masks that are played lie at pairwise different places,
      outside its data (matrix and bits); keys read the data only.
    `rdL`: the item of lookup f reads its data and own masks.
    `own`: the batching's own places: different, read by the batching, outside the public support of
      every claim's mask form; and the fields `mat`, `rdC` (`OwnPlaces`, Cb/Ld/LdWfOwn.lean).
    `ent`, `inRd`, `rdJ`, `atEq`, `ownL`: the named entries are different entries of the messages;
      mask places are shown by the wide reading; what a block reads of named entries is shown; the
      lookups' places are named entries, read by their own lookup.
    `apart`: between the blocks: a named entry that the messages of lookup j read (its bits, its own
      masks) is shown by the wide reading and is no mask place of a later block (a later lookup, or
      the batching).

Main names, each under `CharP E p` and `Z.OK p Lc`:
  `Spec.ldWfEnd`: the two items of the object: `PreListR` and `PreKnowR` of the preamble at
    `W.O.left`.
  `Spec.ldWfEnd_side`: nothing hidden is withheld, nothing is tied, the preamble bears what follows
  within `Z.W.P.S.qFam q Z.t` (the field `bears` of `Side`).
  `Spec.ldWfEnd_laws`, `Spec.ldWfEnd_hyp`: `P.Laws` and `B.Hyp` (for callers that ask these).

That the conditions can be met together is shown elsewhere, at a toy, nothing assumed beside
whatever the arguments hold as proofs, over two different fields (p = 2^64 - 2^32 + 1 and its
cubic extension), below the Johnson radius: Cb/GlVal/GlToyWfJ.lean.

Limits: "apart" speaks of earlier lookups against later blocks. That no mask place of any block is a
bit of any forest is not asked. That no mask place is a played bit place (`Z.K.bAt f u j`, f ≤
`Z.W.P.n`, u < 2 ^ `Z.W.P.d f`, j < 2 ^ `Z.K.w f`) is neither stated nor proved in this library. The
mask forms' supports gC need hold two places only. The rows' supports gR are coarse: all places of
the lookup but these two.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfFull
import Cb.Ld.LdWfBlocksMaskProofs
import Cb.Ld.LdWfMasksAll
import Cb.Ld.LdLkpMaskPlaces2Proofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

/-- Weights-formedness: all data. -/
structure LdWfE (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  W   : LdOWf F E
  K   : W.P.Lks
  D   : W.P.S.Sender (W.P.Body × W.P.Wp) W.P.Wp
  L   : W.P.S.O → ℕ
  t   : W.P.S.O → ℕ
  Rl  : ℕ → W.P.bt.J → Prop
  RdB : W.P.bt.J → Prop
  X   : K.MaskPl D Rl
  p0  : W.Cf.conf.PIdx
  r0  : W.P.S.Rnd
  rv  : ℕ → ℕ
  o   : ℕ → ℕ → E
  co  : ℕ → ℕ → W.P.Rw → E

namespace LdWfE
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdWfE F E)

/-- The data of Cb/Ld/LdWfFull.lean, with the lookups' parameters put in. -/
@[reducible] def G : LdWfF F E :=
  ⟨Z.W, Z.K, Z.D, Z.L, Z.t, Z.K.dm Z.Rl Z.K.cc, Z.RdB, Z.p0, Z.r0, Z.rv, Z.o, Z.co⟩

/-- the places of all masks, as the data of Cb/Ld/LdWfMasks.lean -/
@[reducible] def Y : Z.G.B.MaskLay := (Z.X.Q Z.L Z.t Z.K.cc Z.RdB Z.p0 Z.r0).Y

/-- what the messages of lookup j read -/
def Sr (j : ℕ) : Z.W.P.bt.J → Prop := (Z.K.asm j).srAll (Z.K.Dt j)

/-- The conditions that speak neither of a code of an oracle message, nor of a list, nor of the
sender (but for: its seeds are fair; the vectors that it computes are the multiplicities, where the
keys lie in the table). -/
structure Rest2 (p : ℕ) : Prop where
  val       : Nonempty Z.W.Cf.conf.E0.Str
  describes : ∀ U, (Z.W.Cf.conf.held U).isSome ↔ ∀ f, f ≤ Z.W.P.n → Z.W.P.InT f U
  lin       : Z.W.P.LinKeys Z.rv Z.o Z.co
  lks       : Z.K.OK p
  deg       : 2 ≤ Z.W.P.deg
  zOK       : Z.W.P.Z.OK
  fair      : Z.W.P.Sd.Fair
  multOf    : ∀ U f, f ≤ Z.W.P.n → Z.W.P.InT f U → Z.W.P.mult f U (Z.W.P.bodyOf U)
  tie       : Z.W.Tie
  lkPl      : ∀ f, f ≤ Z.W.P.n → (Z.K.asm f).PlacesOK (Z.K.Dt f)
  rdL       : ∀ f, f ≤ Z.W.P.n → ∀ j, Z.Sr f j → Z.Rl f j
  own       : Z.W.P.OwnPlaces Z.RdB
  ent       : Z.W.P.EntAt Z.X.nAt
  inRd      : ∀ b i, Z.X.RdW (Z.X.nAt (Z.X.pa b i))
  rdJ       : ∀ b n, Z.X.rd Z.RdB b (Sum.inr n) → Z.X.RdW (Z.X.nAt n)
  atEq      : ∀ (l : Fin (Z.W.P.n + 1)) i,
    (Z.K.pl Z.Rl l).pl i = (Sum.inr (Z.X.atL l i) : Z.W.P.bt.J)
  ownL      : ∀ (l : Fin (Z.W.P.n + 1)) i, Z.Rl l (Sum.inr (Z.X.atL l i))
  apart     : ∀ b j,
    j < Z.G.B.upTo b → ∀ n, Z.Sr j (Sum.inr n) → Z.X.RdW (Z.X.nAt n) ∧ ∀ i, n ≠ Z.X.pa b i

/-- With the layout of the sender's coins: the pads alone fix the law of the answers; the entry at a
mask place is the mask value; other entries shown read neither these masks nor the pads. For
standard senders: theorems, under the hypotheses of their statements (Cb/Ld/LdWfEndStd.lean). -/
structure Rest1 (p : ℕ) : Prop extends Z.Rest2 p where
  pad       : Z.X.L.PadLaw Z.W.P.Sd
  sOwn      : ∀ b w ms f η i,
    Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms f η))) (Z.X.nAt (Z.X.pa b i)) =
      Z.X.vl b (ms (Z.X.bk b)) i
  sOff      : ∀ b w ms ms' f η η' n, Z.X.L.oth (Z.X.bk b) ms = Z.X.L.oth (Z.X.bk b) ms' →
    Z.X.RdW n → (∀ i, n ≠ Z.X.nAt (Z.X.pa b i)) →
    Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms f η))) n =
      Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms' f η'))) n

/-- With the sender's three laws: it sends what "back" undoes; its answers are blind; what its
encodings hide (a clause on sender and codes together). For standard senders they are theorems,
under the hypotheses of their statements (Cb/Obj/LdObjectSenders.lean, Cb/Gl/GlSenders.lean). -/
structure Rest0 (p : ℕ) : Prop extends Z.Rest1 p where
  sender    : Z.D.Laws Z.W.P.back
  sBlind    : Z.D.Blind Z.W.P.Sd
  hides     : Z.D.Nn.Hides (Z.W.P.S.budT Z.t)

/-- The conditions that do not speak of a list: with the laws of the codes of the oracle messages
sent. -/
structure Rest (p : ℕ) : Prop extends Z.Rest0 p where
  laws      : ∀ a, (Z.W.P.S.om a).C.Laws

/-- The conditions: on data, and six on the sender (a free value with laws: `Rest0`'s `sender`,
`sBlind`, `hides`; `Rest1`'s `pad`, `sOwn`, `sOff`; theorems for the standard sender, under the
hypotheses of their statements). The three that speak of lists stand apart (Cb/Ld/LdWfEndThird.lean
derives them within a third of the distances). -/
structure OK (p Lc : ℕ) : Prop extends Z.Rest p where
  conf      : Z.W.Cf.OK Lc
  list      : ∀ a, (Z.W.P.S.om a).ListLE (Z.L a)
  evades    : ∀ a, (Z.W.P.S.om a).Evades

end LdWfE

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldWfEnd_ok : Prop := ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (Lc : ℕ), Z.OK p Lc → Z.G.OK Z.Y p Lc

def ldWfEnd_laws : Prop := ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (Lc : ℕ), Z.OK p Lc → Z.W.P.Laws

def ldWfEnd_hyp : Prop := ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (Lc : ℕ), Z.OK p Lc → Z.G.B.Hyp

/-- The two items of the object, from conditions on data and on the sender, and `CharP E p`. -/
def ldWfEnd : Prop :=
  ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (Lc : ℕ), Z.OK p Lc →
    PreListR Z.W.O.left Z.G.B.wf Z.G.B.hWf id id Z.W.Cf.conf.Rwf Z.G.B.nums ∧
    PreKnowR Z.W.O.left Z.G.B.wf Z.W.Cf.conf.free Z.W.Cf.conf.RwfR (fun _ _ _ => ()) Z.G.B.nums.err

/-- Under the hypotheses below, the preamble bears what follows within `Z.W.P.S.qFam q Z.t` (the
field `bears` of `Side`). -/
def ldWfEnd_side : Prop :=
  ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (Lc : ℕ) (q : Finset Z.W.Cf.conf.E0.Pos → Prop),
    Z.OK p Lc → Side Z.G.B.wf Z.G.B.hWf Z.G.B.nums.bud q (Z.W.P.S.qFam q Z.t)

end
end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the laws of the data -/
theorem LdWfE.laws (Z : LdWfE F E) (p Lc : ℕ) (h : Z.OK p Lc) : Z.W.P.Laws :=
  { describes := h.describes
    held_hold := ldCf_held_hold F E Z.W.Cf h.conf.held
    dcd_enc := ldCf_dcd_enc F E Z.W.Cf h.conf.core.dist h.conf.rad
    multOf := h.multOf
    keyLin := ldWfK_keyLin E Z.W.Cf.conf Z.W.P Z.rv Z.o Z.co h.lin }

/-- the conditions on places inside the lookups -/
theorem LdWfE.mok (Z : LdWfE F E) (p Lc : ℕ) (h : Z.OK p Lc) : Z.K.MOK Z.Rl :=
  ⟨fun f hf => ldLkpPlaces2_ok E (Z.K.asm f) (Z.K.Dt f) (h.lkPl f hf), h.rdL⟩

theorem ldWfEnd_ok : Spec.ldWfEnd_ok F E := by
  intro p _ Z Lc h
  haveI := h.val
  have hL := Z.laws p Lc h
  have hM := Z.mok p Lc h
  have hX : Z.X.OK Z.L Z.t Z.K.cc Z.RdB Z.p0 Z.r0 Z.Sr (fun j => (Z.K.asm j).swAll) :=
    { ent := h.ent, inRd := h.inRd, rdJ := h.rdJ, atEq := h.atEq, ownL := h.ownL
      ownB := ldWfOwn_ok Z.W.Cf.conf Z.W.P Z.RdB h.own
      apart := h.apart, pad := h.pad, own := h.sOwn, off := h.sOff
      plOK := fun l =>
        (ldLkpPl2_asm E (Z.K.asm l) _ _ _ _ _ (Z.Rl l) (Z.K.Dt l)
          (hM.mask l (Nat.le_of_lt_succ l.2))).1.1
      link := fun j hj =>
        ldLkpMaskAsm2_link E p (Z.K.asm j) (Z.K.asm j).ValidMu Z.W.Cf.conf.E0 _ Unit Unit
          Z.W.P.msg (Z.K.Dt j) (Z.Rl j) (Z.K.cc j) (h.lks.adm j hj)
          (ldLkpAsm2_muValid E (Z.K.asm j) (h.lks.adm j hj).1) (hM.mask j hj)
          (hM.rd j hj) (fun _ _ hc => hc)
          ((Z.K.asm j).stab_claim E (Z.K.asm j).ValidMu (Z.K.Dt j) (hM.mask j hj)
            (ldWfB_reads E Z.W.Cf.conf Z.W.P Z.K j))
      srRd := h.rdL
      ccRd := fun j _ k k' st hk hc =>
        ldWfB_reads E Z.W.Cf.conf Z.W.P Z.K j st k k' (fun a ha => hk a (Or.inl ha)) hc }
  exact
    { conf := h.conf, describes := h.describes, tie := h.tie, lin := h.lin, lks := h.lks,
      multOf := h.multOf, laws := h.laws, list := h.list, evades := h.evades
      fair := h.fair, sender := h.sender, sBlind := h.sBlind, hides := h.hides
      masks := ldWfMS_ok Z.W.Cf.conf Z.W.P Z.G.B (Z.X.Q Z.L Z.t Z.K.cc Z.RdB Z.p0 Z.r0)
        (ldWfMA_ok Z.W.Cf.conf Z.W.P Z.K Z.D Z.Rl Z.X Z.L Z.t Z.K.cc Z.RdB Z.p0 Z.r0 Z.Sr _ hX)
      deg := h.deg, zOK := h.zOK, own := h.own
      item := ldWfB_mm E p Z.W.Cf.conf Z.W.P Z.K Z.Rl h.lks hM
      claim := ldWfB_cl E p Z.W.Cf.conf Z.W.P Z.K Z.Rl hL h.lks hM }

theorem ldWfEnd_laws : Spec.ldWfEnd_laws F E := fun p _ Z Lc h => Z.laws p Lc h

theorem ldWfEnd_hyp : Spec.ldWfEnd_hyp F E := fun p _ Z Lc h =>
  ldWfFull_hyp p Z.G Z.Y Lc (ldWfEnd_ok p Z Lc h)

theorem ldWfEnd : Spec.ldWfEnd F E := fun p _ Z Lc h => ldWfFull p Z.G Z.Y Lc (ldWfEnd_ok p Z Lc h)

theorem ldWfEnd_side : Spec.ldWfEnd_side F E := fun p _ Z Lc q h =>
  ldWfFull_side p Z.G Z.Y Lc q (ldWfEnd_ok p Z Lc h)

end
end Cb
