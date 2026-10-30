-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/House.lean: the links of the house with parts and their chain: definitions, and two
equalities by rfl. It imports no file of the program.

Why. The library's house for a witness file is a chain: sending · one link a forest · batching
(Cb/Ld/LdWf.lean). Here the same chain is laid with one link a lookup with parts, of links without
an honest side (Cb/Pv/KeyLookup/ChainK.lean), between the library's own joints `P.jIn`, `P.J l`,
`P.jLast`.
  `lLkK P K B l`   the link of lookup l, from `P.J (K.start l)` to `P.J (K.start (l + 1))`: the
                   lookup at the base (`(B l).lam1`, Cb/Pv/KeyLookup/Asm.lean) kept over the
                   signature;
                   then, in one step without rounds, its read-out is pulled onto the named entries
                   and filed (`fileOut`). What cannot be filed is rejected.
  `lSendK P L`     the sending without its honest side; `lSendK_eq`: it is the library's `B.lSend`,
                   H forgotten (by rfl).
  `lBattK P l`     the batching's link, started at the joint after l forests; `lBattK_eq`: at P.n +
                   1 it is the library's, H forgotten (by rfl).
  `chainK`, `wfK`  sending · the lookups 0 … K.nL · batching; closed as the library closes its own
                   chain (`closeF`).
Under: nothing: definitions. Does not say: that any link is knowledge sound (the lookups' links:
Cb/Pv/KeyLookup/HouseLk.lean; the sending: Cb/Pv/KeyFrame/LawsS.lean; of lBattK, chainK and wfK no
file says Know); that the blocks B exist. After: the library's lLkp, lSend, lBatt, chain, wf
(Cb/Ld/LdWf.lean).

-/
import Cb.Ld.LdWfProofsLinks     -- step0, stepToBatt, batt_st, bIn, bOut, rcIn, rcOut
import Cb.Ld.LdWfBlocksProofs    -- keyE, ldWfB_key, inTable_congr, holds_congr
import Cb.Ld.LdWfCloseProofs     -- closeF, ldClose_know
import Cb.Pv.KeyLookup.Cut
import Cb.Pv.KeyLookup.ChainK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Cb.LdWfP

variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-- The link of lookup l: the lookup at the base over the signature, then, in one step without
rounds, the pull and the filing. -/
noncomputable def lLkK (K : Cut P) (B : ∀ l, Bks (K.dat l) C.E0) (l : ℕ) :
    LinkK Unit (P.J (K.start l)) (P.J (K.start (l + 1))) where
  R := ((B l).lam1.R.keep P.S.Smp P.S.ext).post
    (fun x => fileOut P (K.start l) (K.S l).m (pullOut Sum.inr x.1, x.2)) (ExtMap.id _)
  ext := fun _ _ w => w
  e := (B l).lam1.e

/-- The sending without its honest side; and that it is the library's. -/
noncomputable def lSendK (L : P.S.O → ℕ) : LinkK Unit P.jIn (P.J 0) where
  R := (ldSendFam P.S P.Sd P.WSt C.E0).pre (fun rec => some (P.st0 rec)) (ExtMap.id _)
  ext := fun _ _ w => w.2.1
  e := (ldSendFamErr P.S P.Sd L, (0, ()))
theorem lSendK_eq (B : P.Blk) : LinkK.ofLink B.lSend = lSendK P B.L := rfl
/-- The batching's link at the chain's end. -/
noncomputable def lBattK (l : ℕ) : LinkK Unit (P.J l) P.jLast :=
  ⟨P.lBatt.R, P.lBatt.ext, P.lBatt.P.err⟩
theorem lBattK_eq : lBattK P (P.n + 1) = LinkK.ofLink P.lBatt := rfl

/-- The chain; and the chain closed. -/
noncomputable def chainK (K : Cut P) (B : ∀ l, Bks (K.dat l) C.E0) (L : P.S.O → ℕ) :
    ChainK Unit P.jIn P.jLast :=
  ((ChainK.one (lSendK P L)).append (ChainK.fam (fun l => P.J (K.start l)) (lLkK P K B) K.nL)).snoc
    (lBattK P (K.start (K.nL + 1)))
noncomputable def wfK (K : Cut P) (B : ∀ l, Bks (K.dat l) C.E0) (L : P.S.O → ℕ) (p0 : C.PIdx) :
    IOR C.Rec C.E0 (P.left.Xl × C.Rec) P.left.El := closeF ((chainK P K B L).link p0).R

end Lk6
