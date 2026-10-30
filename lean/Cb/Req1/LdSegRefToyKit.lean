-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefToyKit.lean: a family of oracle messages with one datum a member, and its sending:
all hypotheses of a move "send" met, from one law (`h` of `datSend_hyp`), for any finite set of
names.

Definitions, theorems. Building stone for toys; a guard against empty theorems; no parameter of a
protocol.
The member is the oracle message of Cb/Ld/LdSendToy.lean (the field with 101 elements; five points;
two rows: one datum, one pad; radius 2, beyond unique decoding; lists of at most 2; the sample
"datum + β · pad").

Main names (in `Cb.LdToy`):
  `datSig I`: the family: one member for each name in I.
  `datAt m i`: the datum of the member i.
  `datMsg v`: messages with the data v (all pads 0).
  `datMem`, `datSnd val rest w0`: the honest sender: the witness w gives the data val w; the pads
    are independent coins; rest w stays a further witness.
  `datSendD a I Wp' bk val rest w0`: the data of a move "send" after a stage a (`LdSendD`,
    Cb/Req1/LdSegKit.lean): independent seeds; lists of at most 2; each encoding bears 1 long
    position.
  `datSend_hyp`: `(datSendD ..).Hyp`, from one law: what is read off messages with the data val w,
    and rest w, give w back.

Limits: this file says nothing on real parameters: no security.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendToy
import Cb.Ld.LdSendMem
import Cb.Req1.LdSegKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop Blocks Cb.Ood

section
variable (I : Type) [Fintype I] [DecidableEq I]

/-- The family. -/
@[reducible] def datSig : Sig K := { O := I, om := fun _ => toyS }

variable {I}

/-- the datum of a member -/
def datAt (m : (datSig I).Msg) (i : I) : K := m i (nu.symm (Sum.inl ()))

/-- messages with given data -/
def datMsg (v : I → K) : (datSig I).Msg := fun i j => Sum.elim (fun _ => v i) (fun _ => 0) (nu j)

theorem datAt_msg (v : I → K) (i : I) : datAt (datMsg v) i = v i := by
  show Sum.elim (fun _ => v i) (fun _ => (0 : K)) (nu (nu.symm (Sum.inl ()))) = v i
  rw [Equiv.apply_symm_apply]
  rfl

variable {W W' : Type}

/-- the sender of one member -/
@[reducible] def datMem (val : W → K) (w0 : W) : toyS.Sender W Unit where
  N := (toyLd Bool).Nn
  upM := fun m => m
  upR := fun r => r
  Mk := K
  put := fun w k j => Sum.elim (fun _ => val w) (fun _ => k) (nu j)
  rest := fun _ => ()
  w0 := w0

/-- The sender of the family. -/
@[reducible] def datSnd (val : W → I → K) (rest : W → W') (w0 : W) :
    (datSig I).Sender W W' :=
  Sig.Sender.ofMem (N := datSig I) (fun a => datMem (fun w => val w a) w0) rest w0

theorem datMem_uniform (val : W → K) (w0 : W) : (datMem val w0).Uniform := fun ρ w =>
  toyD_uniform ρ (val w)

theorem datAt_put (val : W → I → K) (rest : W → W') (w0 : W) (w : W)
    (k : (datSnd val rest w0).Mk) (i : I) :
    datAt ((datSnd val rest w0).upM ((datSnd val rest w0).put w k)) i = val w i := by
  show Sum.elim (fun _ => val w i) (fun _ => k i) (nu (nu.symm (Sum.inl ()))) = val w i
  rw [Equiv.apply_symm_apply]
  rfl

end

section
variable {Kc : Type} (a : LdStage K Kc) (I : Type) [Fintype I] [DecidableEq I] (Wp' : Type)
  (bk : (datSig I).Msg → Wp' → a.Wp) (val : a.S.Wit × a.Wp → I → K)
  (rest : a.S.Wit × a.Wp → a.S.Wit × Wp') (w0 : a.S.Wit × a.Wp)

/-- The data of the move. -/
@[reducible] def datSendD : LdSendD a :=
  ⟨datSig I, Sig.Seeds.indep (datSig I), Wp', bk, datSnd val rest w0, fun _ => 2, fun _ => 1⟩

/-- All that a move "send" asks. -/
theorem datSend_hyp
    (h : ∀ w (m : (datSig I).Msg),
      (∀ i, datAt m i = val w i) → a.S.backN (datSig I) bk m (rest w) = w) :
    (datSendD a I Wp' bk val rest w0).Hyp := by
  have hT := ld_toy Bool
  exact
  { laws := fun _ => hT.1
    fair := (ldSendFam_fair_indep K (datSig I)).1
    list := fun _ => sig_list_of_code K toyS 2 hT.2.2.2.1
    evades := fun _ => toyS_evades
    sender := ldSendMem_laws K (datSig I) _ _ _ rest w0 _ (fun _ _ _ => rfl) fun w k =>
      h w _ fun i => datAt_put val rest w0 w k i
    blind := ldSendMem_blind K (datSig I) _ _ _ rest w0 _ fun i =>
      ldSend_blind_of_uniform K toyS _ Unit _ (datMem_uniform (fun w => val w i) w0)
    hides := ldSendMem_hides K (datSig I) _ _ _ rest w0 _ fun _ => hT.2.2.2.2.2.2.1 }

end
end LdToy
end Cb
