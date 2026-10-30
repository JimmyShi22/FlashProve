-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/BatTok.lean: hidden products are sent, one drawn element batches them, and a token
sumcheck is run on the batch: the two blocks joined.

What the verifier's routine does (hearProducts, OnBytes/Model/HeadHeard.lean): it receives one
hidden value for each product of two maps, summed over the positions under the equality polynomial
at a public point; it draws one element; then it runs the token sumcheck whose summand adds the
products under the powers of that element.

The joints. What the caller claims of the products is a letter phi. Before: phi holds of the true
products. After: phi holds of the hidden values (what was sent, less the mask entries); the hidden
value of the sumcheck's first scalar is the sum of these hidden values under the powers; and the
sumcheck's output claims hold.

bt_knowAt: the soundness side of the joined block, with the errors of the two blocks one behind the
other. It is put together from bat_knowAt (Cb/Pv/Head/Batch.lean) and tok_knowAt
(Cb/Pv/Head/Tok.lean) by the rules of Cb/G6/Join.lean.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of this block (in a row of blocks: of the first block) is drawn.
That is the caller's to show.

What is not claimed: see the two files.


-/
import Cb.Pv.Head.TokMeans
import Cb.Pv.Head.Batch
import Cb.G6.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole Cb.Pv.Head.Bat

section
variable {E : Type} [Field E]

/-- The true product number j: the extension, at the sumcheck's point, of the product of its two
tables. -/
def trueP (k : TokKind) (W : TokWorld E k) (st : TokSt E W.Pb k) (m : W.J → E) (j : Fin k.np) :
    E :=
  Blocks.ext k.vars
    (fun i => W.tab st.pb m (k.pairs.get j).1 i * W.tab st.pb m (k.pairs.get j).2 i)
    (Blocks.nat st.pt)

/-- The extension of the summand's table is the sum of the true products under the weights. -/
theorem tokAt_ext (k : TokKind) (W : TokWorld E k) (st : TokSt E W.Pb k) (m : W.J → E) :
    Blocks.ext k.vars (tokAt k W st m) (Blocks.nat st.pt) =
      ∑ j : Fin k.np, st.om j * trueP k W st m j := by
  have e1 : tokAt k W st m = fun i => ∑ j : Fin k.np, st.om j *
      (W.tab st.pb m (k.pairs.get j).1 i * W.tab st.pb m (k.pairs.get j).2 i) := rfl
  rw [e1, Blocks.ext_sum]
  exact sum_congr rfl fun j _ => Blocks.ext_smul k.vars _ _ _

/-- The entries as the sumcheck behind a batch reads them: what was sent for the products has
become public; the tables do not read it. -/
@[reducible] def TokWorld.behind {k : TokKind} (W : TokWorld E k) : TokWorld E k where
  Pb := W.Pb × (Fin k.np → E)
  J := W.J
  finJ := W.finJ
  decJ := W.decJ
  msk := W.msk
  tab := fun pb => W.tab pb.1

/-- The slot of the first product: the products' slots end where the sumcheck's begin. -/
def TokKind.sPv (k : TokKind) : ℕ := k.sCl - k.np

/-- What stands around the joined block and rides through it. -/
structure BtFrame (E : Type) (k : TokKind) (W : TokWorld E k) where
  Kc : Type
  /-- the committed messages -/
  M : Type
  Wp : Type
  Ex : ExtSpec
  /-- what else is claimed of point, public data, oracles and witness -/
  A0 : IOR.Rels Kc ((Fin k.lt → E) × W.Pb) Ex (M × Wp)
  /-- the entries of the committed messages -/
  msg : M → W.J → E
  /-- what the caller claims of the products -/
  phi : (Fin k.lt → E) × W.Pb → (Fin k.np → E) → (W.J → E) → Prop

variable {k : TokKind} {W : TokWorld E k}

/-- The state of the sumcheck, from the point, the public data, what was sent and the weights. -/
def stAt (x : (Fin k.lt → E) × W.Pb) (sent : Fin k.np → E) (om : Fin k.np → E) :
    TokSt E W.behind.Pb k :=
  ⟨x.1, om, (x.2, sent)⟩

/-- The frame of the batch. The true values do not read what is sent or drawn. -/
def BtFrame.bat (Fr : BtFrame E k W) : BatFrame E k.np where
  X := (Fin k.lt → E) × W.Pb
  J := W.J
  Kc := Fr.Kc
  M := Fr.M
  Wp := Fr.Wp
  Ex := Fr.Ex
  A0 := Fr.A0
  msg := Fr.msg
  msk := fun j => W.msk (k.sPv + j)
  tv := fun x m j => trueP k W ⟨x.1, fun _ => 0, x.2⟩ m j
  phi := Fr.phi

/-- The frame of the sumcheck. The caller's claim on its first scalar t: phi holds of the hidden
products, and these add up, under the weights, to t less the mask entry of the first slot. -/
noncomputable def BtFrame.tok (Fr : BtFrame E k W) : TokFrame E k W.behind where
  Kc := Fr.Kc
  M := Fr.M
  Wp := Fr.Wp
  Ex := Fr.Ex
  A0 :=
    ⟨fun st y w => Fr.A0.rel (st.zt, st.pb.1) y w,
      fun a w => Fr.A0.relR ((a.1.zt, a.1.pb.1), a.2) w,
      fun a => Fr.A0.on ((a.1.zt, a.1.pb.1), a.2), Fr.A0.core⟩
  msg := Fr.msg
  psi := fun st t m =>
    Fr.phi (st.zt, st.pb.1) (Fr.bat.hid st.pb.2 m) m ∧
      ∑ j : Fin k.np, st.om j * Fr.bat.hid st.pb.2 m j = t - m (W.msk k.sCl)

/-- From what the batch hands on to the sumcheck's state: the weights are the powers. -/
def btMap (b : (((Fin k.lt → E) × W.Pb) × (Fin k.np → E)) × E) : TokSt E W.behind.Pb k :=
  stAt b.1.1 b.1.2 fun j => b.2 ^ (j : ℕ)

variable [Fintype E]

/-- The joined block. -/
noncomputable def btR (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) :
    IOR ((Fin k.lt → E) × W.Pb) Ex
      ((TokSt E W.behind.Pb k × E) × (tokT k W.behind).par.Out) Ex :=
  (batR E ((Fin k.lt → E) × W.Pb) k.np Ex).seq
    ((tokR k W.behind Ex).pre (fun b => some (btMap b)) (ExtMap.id Ex))

/-- The soundness side of the joined block. -/
theorem bt_knowAt (Fr : BtFrame E k W) :
    KnowAt (btR k W Fr.Ex) (batIn Fr.bat) (tokOut k W.behind Fr.tok) (fun _ _ _ wp => wp)
      (Err.app (batErr E ((Fin k.lt → E) × W.Pb) k.np Fr.Ex) (tokErr k W.behind Fr.Ex)) :=
  knowAt_seq (bat_knowAt Fr.bat)
    (knowAt_preMap (A' := batOut Fr.bat) btMap (fun _ _ h => h)
      (fun b y w _ h => by
        obtain ⟨h0, h1, h2⟩ := h
        have h2' : ∑ j : Fin k.np, b.2 ^ (j : ℕ) * Fr.bat.hid b.1.2 (Fr.msg w.1) j =
            Cb.Pv.Lay.tsum (tokT k W.behind).par (btMap b) (Fr.msg w.1) -
              Fr.msg w.1 (W.msk k.sCl) := h2
        rw [tok_tsum, add_sub_cancel_right, tokAt_ext] at h2'
        exact ⟨h0, h1, h2'⟩)
      (tok_knowAt k W.behind Fr.tok))

/-- The joined block's errors are the two written lists, one behind the other. -/
theorem bt_nums (Ex : ExtSpec) :
    errList (Err.app (batErr E ((Fin k.lt → E) × W.Pb) k.np Ex) (tokErr k W.behind Ex)) =
      (k.np - 1) :: k.errs := by
  rw [errList_app, tok_nums]
  rfl

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.tokAt_ext
#print axioms Cb.Pv.Head.Tok.bt_knowAt
#print axioms Cb.Pv.Head.Tok.bt_nums
