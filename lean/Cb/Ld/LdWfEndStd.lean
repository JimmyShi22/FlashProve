-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfEndStd.lean: six clauses of `Z.OK` (Cb/Ld/LdWfEnd.lean), derived for the standard sender
under further hypotheses.
Weights-formedness with the standard sender: under the hypotheses of its statement
(`Spec.ldWfE_std`), the six clauses on its sender and on the layout of the sender's coins follow
from the layout of the messages and from places.

Definitions, statement (`Cb.Spec.ldWfE_std`) and proof.
Cb/Ld/LdWfEnd.lean (`Z : LdWfE F E`: all data of the preamble of weights-formedness) asks of the
honest sender `Z.D` and of the layout of its coins `Z.X.L`: `sender`, `sBlind`, `hides` (the
sender's three laws); `pad` (the pads alone fix the law of the answers); `sOwn` (the entry at a mask
place is the mask value); `sOff` (other entries shown read neither these masks nor the pads).
This file uses Cb/Ld/LdSendStdL.lean (`Y : P.S.StdL Fp`: data, free entries, pads),
Cb/Obj/LdObjectSenders.lean (`P.stdD`: the standard sender) and Cb/Ld/LdSendStdBlocks.lean (masks of
several blocks at free entries).

Main names:
  `K.stdX ..`: the record of mask places (Cb/Ld/LdWfMasksAll.lean: `MaskPl`) for the standard
    sender: its layout of coins is `Y.layB pl ..`; block names as they are; mask values as they are.
    pl b i: the free entry at which the mask i of the block b is; different masks, of one block or
    of two, are at different free entries (`hpl`).
  `Spec.ldWfE_std`: if the pair (Z.D, Z.X) is (the standard sender, K.stdX ..) [one equation on the
    pair: the second depends on the first by type], `Y.OK Z.t`, `P.body` reads the data of the
    messages alone by a map that undoes dat, the place that the preamble names for the mask i of the
    block b is the free entry pl b i (`plL`, `plB` of `LdWfE.StdW.Hyp`,
    Cb/Obj/LdObjectDataSnd.lean), and no entry that is shown is a pad (noPad): all six clauses.

Limits: this file says nothing on the other clauses of `Z.Rest1`. It does not say that the
conditions can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfEnd
import Cb.Obj.LdObjectSenders
import Cb.Ld.LdSendStdBlocks
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp Cb.Ood

namespace LdWfP.Lks
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks)

/-- the names of the masks of a block -/
def wfI (Rl : ℕ → P.bt.J → Prop) : Option (Fin (P.n + 1)) → Type
  | some l => (K.pl Rl l).I
  | none => PIdx P.bt.fmt

variable {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (Rl : ℕ → P.bt.J → Prop)
  [∀ b, Fintype (K.wfI Rl b → E)] (Y : P.S.StdL Fp) (dat : P.Body → ∀ a, Y.Dt a → E)
  (w0 : P.Body × P.Wp) (nAt : P.N → P.S.Ent) (RdW : P.S.Ent → Prop)
  (atL : ∀ l : Fin (P.n + 1), (K.pl Rl l).I → P.N) (pl : ∀ b, K.wfI Rl b → Σ a, Y.Fr a)
  (hpl : Function.Injective fun x : Σ b, K.wfI Rl b => pl x.1 x.2)

/-- The record of mask places for the standard sender. -/
@[reducible] def stdX : K.MaskPl (P.stdD Y dat w0) Rl where
  nAt := nAt
  RdW := RdW
  L := Y.layB pl hpl (fun w : P.Body × P.Wp => dat w.1) (fun w => w.2) w0
  bk := id
  eL := fun _ => Equiv.refl _
  eB := Equiv.refl _
  atL := atL

end LdWfP.Lks

def Spec.ldWfE_std : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Z : LdWfE F E) [∀ b, Fintype (Z.K.wfI Z.Rl b → E)]
      (Y : Z.W.P.S.StdL Fp) (dat : Z.W.P.Body → ∀ a, Y.Dt a → E) (w0 : Z.W.P.Body × Z.W.P.Wp)
      (bd : (∀ a, Y.Dt a → E) → Z.W.P.Body) (nAt : Z.W.P.N → Z.W.P.S.Ent) (RdW : Z.W.P.S.Ent → Prop)
      (atL : ∀ l : Fin (Z.W.P.n + 1), (Z.K.pl Z.Rl l).I → Z.W.P.N)
      (pl : ∀ b, Z.K.wfI Z.Rl b → Σ a, Y.Fr a)
      (hpl : Function.Injective fun x : Σ b, Z.K.wfI Z.Rl b => pl x.1 x.2),
    (⟨Z.D, Z.X⟩ : Σ D, Z.K.MaskPl D Z.Rl) =
      ⟨Z.W.P.stdD Y dat w0, Z.K.stdX Z.Rl Y dat w0 nAt RdW atL pl hpl⟩ →
    Y.OK Z.t → (∀ m, Z.W.P.body m = bd (Y.dataOf m)) → (∀ b, bd (dat b) = b) →
    (∀ l i, nAt (atL l i) = Y.entF (pl (some l) i)) →
    (∀ i, nAt (Z.W.P.wAt i) = Y.entF (pl none i)) → (∀ n, RdW n → Y.NoPad n) →
    Z.D.Laws Z.W.P.back ∧
    Z.D.Blind Z.W.P.Sd ∧
    Z.D.Nn.Hides (Z.W.P.S.budT Z.t) ∧
    Z.X.L.PadLaw Z.W.P.Sd ∧
    (∀ b w ms f η i, Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms f η))) (Z.X.nAt (Z.X.pa b i)) =
      Z.X.vl b (ms (Z.X.bk b)) i) ∧
    ∀ b w ms ms' f η η' n, Z.X.L.oth (Z.X.bk b) ms = Z.X.L.oth (Z.X.bk b) ms' →
      Z.X.RdW n → (∀ i, n ≠ Z.X.nAt (Z.X.pa b i)) →
      Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms f η))) n =
        Z.W.P.S.ents (Z.D.upM (Z.D.put w (Z.X.L.mk' ms' f η'))) n

theorem ldWfE_std : Spec.ldWfE_std := by
  intro F E Fp _ _ _ _ _ _ _ _ Z _ Y dat w0 bd nAt RdW atL pl hpl hZ hY hbody hbd hL hB hRd
  have key : ∀ x : Σ D, Z.K.MaskPl D Z.Rl,
    x = ⟨Z.W.P.stdD Y dat w0, Z.K.stdX Z.Rl Y dat w0 nAt RdW atL pl hpl⟩ →
    x.1.Laws Z.W.P.back ∧
    x.1.Blind Z.W.P.Sd ∧
    x.1.Nn.Hides (Z.W.P.S.budT Z.t) ∧
    x.2.L.PadLaw Z.W.P.Sd ∧
    (∀ b w ms f η i, Z.W.P.S.ents (x.1.upM (x.1.put w (x.2.L.mk' ms f η))) (x.2.nAt (x.2.pa b i)) =
      x.2.vl b (ms (x.2.bk b)) i) ∧
    ∀ b w ms ms' f η η' n, x.2.L.oth (x.2.bk b) ms = x.2.L.oth (x.2.bk b) ms' →
      x.2.RdW n → (∀ i, n ≠ x.2.nAt (x.2.pa b i)) →
      Z.W.P.S.ents (x.1.upM (x.1.put w (x.2.L.mk' ms f η))) n =
        Z.W.P.S.ents (x.1.upM (x.1.put w (x.2.L.mk' ms' f η'))) n := by
    rintro _ rfl
    obtain ⟨s1, s2, s3⟩ := ldWf_std Fp E _ Z.W.P Y Z.t dat w0 bd hY hbody hbd
    obtain ⟨b1, b2, b3⟩ := stdL_blocks Fp E Z.W.P.S Y Z.t _ _
      (fun w : Z.W.P.Body × Z.W.P.Wp => dat w.1) (fun w => w.2) w0 _ (Z.K.wfI Z.Rl) pl hpl hY
    refine ⟨s1, s2, s3, b1 _, fun b w ms f η i => ?_,
      fun b w ms ms' f η η' n ho hn hoff => b3 b w ms ms' f η η' n ho (hRd n hn) fun i => ?_⟩
    · cases b with
      | none => exact (congrArg _ (hB i)).trans (b2 none w ms f η i)
      | some l => exact (congrArg _ (hL l i)).trans (b2 (some l) w ms f η i)
    · cases b with
      | none => exact fun h => hoff i (h.trans (hB i).symm)
      | some l => exact fun h => hoff i (h.trans (hL l i).symm)
  exact key ⟨Z.D, Z.X⟩ hZ

end Cb
