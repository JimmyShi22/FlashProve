-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lin.lean: the blocks of the test on a stored table, up to the rows that its closing tests,
each as a kind of block: for each block the statement that it is knowledge sound, and its proof by
one call of the library.

The test is the library's `LdLinP` (Cb/Ld/LdLin.lean). Its chain `P.core` is: a step without rounds;
the sending of W; the shared point; the sending of the folded row; the locations, at which columns
of the stored table are read; the sending of the third family; the point zeta. The library states
its own four blocks as bundles, of which knowledge soundness is one part, and proves the whole chain
under a record that also speaks of the senders. Here each block has that part alone, between the
library's joints with their conditions moved into the relaxed relations, on all statements. No term
of the library is stated anew. Definitions and proofs.
Main names:
  `know_step0`, `know_pt`, `know_loc`, `know_zeta`: the library's own four blocks: one projection
    each of `ldLin_step0`, `ldLin_pt`, `ldLin_loc`, `ldLin_zeta` (Cb/Ld/LdLinProofs.lean).
  `know_sW`, `know_sU`, `know_sO`: the three sendings: one call each of `ldSendFam_into`
    (Cb/Ld/LdSendFamProofs.lean).
  `sndOf P wa`: a value of the record that `ldLin_loc` takes for its budgets of positions. No
    verifier reads it, and no statement of this file names it.
  `Size`: the types, the record P, the condition on0 on tables and records, the number εf, and two
    fixed values (a position i₀, a witness wa of the oracles left).
  `HPt s`, `HLoc s`, `HZeta s`: the statements of the three kinds of round that are the test's own.
    `hPt` under `P.FoldErr on0 εf`; `hLoc` without a premise; `hZeta` for an injective `P.D.py`.
  `pt_rounds`, `pt_errs`, `pt_vals` and the same for `loc`, `zeta`: one round each; the library's
    three error counts; the numbers of values of the verifier's messages.
  `coreKB`: the whole chain in a batch of N slots: `ldLinCB_coreK` (Cb/Thin/K4/SndK.lean), repeated
    here under this file's name so that both forms stand in one place.
Limits: `P.FoldErr` is a condition here: the library derives it from a distance, lists and agreement
(`ldLin_foldErr`, Cb/Ld/LdLin.lean). Fair seeds, bounded lists and evading samples are conditions on
the three families. Nothing says that a chain of the programs is a value of `Size`, or that an error
is small. The statements at one instance do not give the batch's: that is `coreKB`. Nothing on the
closing. Nothing on an honest prover.
-/
import Cb.Ld.LdLinProofsChain
import Cb.Ld.LdSendFamProofs
import Cb.Thin.K4.SndK
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lin
open Iop Prob Hiop Blocks Cb.Ood IOR Cb

section Blocks
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y]

/-- A value of the record that the library's statement on the locations takes for its budgets. -/
noncomputable def sndOf (P : LdLinP E ι κ J Y) (wa : P.Wa) : P.Snd where
  dW :=
    { Nn := ⟨Unit, Unit, fun _ _ a => (P.NW.om a).sy0, fun _ => none⟩
      upM := fun _ _ _ => 0
      upR := fun _ _ _ => 0
      Mk := Unit
      put := fun _ _ => ()
      rest := fun w => w.2
      w0 := (fun _ => 0, (fun _ _ => 0, wa)) }
  dU :=
    { Nn := ⟨Unit, Unit, fun _ _ a => (P.NU.om a).sy0, fun _ => none⟩
      upM := fun _ _ _ => 0
      upR := fun _ _ _ => 0
      Mk := Unit
      put := fun _ _ => ()
      rest := fun w => w.2
      w0 := (fun _ => 0, (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, wa))) }
  dO :=
    { Nn := ⟨Unit, Unit, fun _ _ a => (P.NO.om a).sy0, fun _ => none⟩
      upM := fun _ _ _ => 0
      upR := fun _ _ _ => 0
      Mk := Unit
      put := fun _ _ => ()
      rest := fun w => w.2
      w0 := (fun _ => 0, (fun _ => (fun _ => 0, fun _ => 0),
        (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, wa)))) }
  LW := fun _ => 0
  LU := fun _ => 0
  LO := fun _ => 0
  tW := fun _ => 0
  tU := fun _ => 0
  tO := fun _ => 0

variable (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

omit [Fintype E] [Nonempty ι] in
/-- The step without rounds at the head of the chain. -/
theorem know_step0 :
    P.step0.red.Know (fun _ => True) (P.j0 on0).cf.relR (P.jA on0).cf.relR (fun _ _ w => w.2) () :=
  (ldk_pieceTr_cf (ldLin_step0 P on0 fun _ => True)).good.know

omit [Fintype E] [Nonempty ι] in
/-- The two rounds of the sending of W. -/
theorem know_sW (L : P.NW.O → ℕ) (hF : P.SdW.Fair) (hl : ∀ a, (P.NW.om a).ListLE (L a))
    (hE : ∀ a, (P.NW.om a).Evades) :
    P.sW.red.Know (fun _ => True) (P.jA on0).cf.relR (P.j1 on0).cf.relR
      (fun _ _ w => P.backW (P.NW.msgs w.1) w.2) (ldSendFamErr P.NW P.SdW L, (0, ())) :=
  (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
    (ldSendFam_into E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW L hF hl hE)

omit [Nonempty ι] in
/-- The round of the shared point. -/
theorem know_pt (εf : ℕ) (hF : P.FoldErr on0 εf) :
    P.pt.red.Know (fun _ => True) (P.j1 on0).cf.relR (P.j2 on0).cf.relR (fun _ _ w => w.2)
      ((P.errPt εf, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLin_pt P on0 εf (fun _ => True) hF)).good.know

omit [Fintype E] [Nonempty ι] in
/-- The two rounds of the sending of the folded row. -/
theorem know_sU (L : P.NU.O → ℕ) (hF : P.SdU.Fair) (hl : ∀ a, (P.NU.om a).ListLE (L a))
    (hE : ∀ a, (P.NU.om a).Evades) :
    P.sU.red.Know (fun _ => True) (P.j2 on0).cf.relR (P.j3 on0).cf.relR
      (fun _ _ w => P.backU (P.NU.msgs w.1) w.2) (ldSendFamErr P.NU P.SdU L, (0, ())) :=
  (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
    (ldSendFam_into E P.NU P.SdU Unit P.X2 P.W2 P.W1 P.E1 (P.j2 on0) P.backU L hF hl hE)

omit [Fintype E] in
/-- The round of the locations. -/
theorem know_loc (wa : P.Wa) :
    P.loc.red.Know (fun _ => True) (P.j3 on0).cf.relR P.j4.cf.relR (fun _ _ w => w.2)
      ((P.errLoc, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLin_loc P on0 (sndOf P wa) fun _ => True)).good.know

omit [Fintype E] [Fintype ι] [Nonempty ι] in
/-- The two rounds of the sending of the third family. -/
theorem know_sO (L : P.NO.O → ℕ) (hF : P.SdO.Fair) (hl : ∀ a, (P.NO.om a).ListLE (L a))
    (hE : ∀ a, (P.NO.om a).Evades) :
    P.sO.red.Know (fun _ => True) P.j4.cf.relR P.j5.cf.relR
      (fun _ _ w => P.backO (P.NO.msgs w.1) w.2) (ldSendFamErr P.NO P.SdO L, (0, ())) :=
  (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
    (ldSendFam_into E P.NO P.SdO Unit P.X4 P.W4 P.W3 P.E4 P.j4 P.backO L hF hl hE)

omit [Nonempty ι] in
/-- The round of the point zeta. -/
theorem know_zeta (hpy : Function.Injective P.D.py) :
    P.zeta.red.Know (fun _ => True) P.j5.cf.relR P.j6.cf.relR (fun _ _ w => w)
      ((P.errZeta, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLin_zeta P (fun _ => True) hpy)).good.know

/-- The whole chain in a batch of N slots. -/
theorem coreKB (N εf : ℕ) (S : P.Snd) (hF : P.FoldErr on0 εf) (hpy : Function.Injective P.D.py)
    (hS : S.OKK) : (P.chainA on0 S εf N).KB N (P.key0 on0) P.key6 :=
  ldLinCB_coreK P on0 N εf S hF hpy hS

/-! ### rounds, errors, numbers of values -/

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem pt_rounds : P.pt.shape.length = 1 := rfl
omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem pt_errs (εf : ℕ) :
    Err.toList (s := P.pt.shape) ((P.errPt εf, ()) : ℕ × Unit) = [P.errPt εf] := rfl
omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem pt_vals : P.pt.shape.chalList = [Fintype.card P.D.Pt] := rfl

omit [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
theorem loc_rounds : P.loc.shape.length = 1 := rfl
omit [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
theorem loc_errs : Err.toList (s := P.loc.shape) ((P.errLoc, ()) : ℕ × Unit) = [P.errLoc] := rfl
omit [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
theorem loc_vals : P.loc.shape.chalList = [Fintype.card (Fin P.t → ι)] := rfl

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem zeta_rounds : P.zeta.shape.length = 1 := rfl
omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem zeta_errs :
    Err.toList (s := P.zeta.shape) ((P.errZeta, ()) : ℕ × Unit) = [P.errZeta] := rfl
omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem zeta_vals : P.zeta.shape.chalList = [Fintype.card (Fin P.D.l → E)] := rfl

end Blocks

/-! ### the three kinds of round that are the test's own, at a size -/

/-- What the test is made of: data alone. -/
structure Size (E : Type) [Field E] [Fintype E] : Type 1 where
  ι : Type
  κ : Type
  J : Type
  Y : Type
  [finι : Fintype ι]
  [finκ : Fintype κ]
  [finJ : Fintype J]
  [finY : Fintype Y]
  /-- a position of the table's code -/
  i₀ : ι
  P : LdLinP E ι κ J Y
  /-- the condition on a table and its record -/
  on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop
  /-- a bound on the points that are bad for the fold -/
  εf : ℕ
  /-- a witness of the oracles left -/
  wa : P.Wa

attribute [instance] Size.finι Size.finκ Size.finJ Size.finY

variable {E : Type} [Field E] [Fintype E] (s : Size E)

instance : Nonempty s.ι := ⟨s.i₀⟩

/-- The statement that the round of the shared point is knowledge sound. -/
def HPt : Prop :=
  s.P.pt.red.Know (fun _ => True) (s.P.j1 s.on0).cf.relR (s.P.j2 s.on0).cf.relR (fun _ _ w => w.2)
    ((s.P.errPt s.εf, ()) : ℕ × Unit)

theorem hPt (h : s.P.FoldErr s.on0 s.εf) : HPt s := know_pt s.P s.on0 s.εf h

/-- The statement that the round of the locations is knowledge sound. -/
def HLoc : Prop :=
  s.P.loc.red.Know (fun _ => True) (s.P.j3 s.on0).cf.relR s.P.j4.cf.relR (fun _ _ w => w.2)
    ((s.P.errLoc, ()) : ℕ × Unit)

theorem hLoc : HLoc s := know_loc s.P s.on0 s.wa

/-- The statement that the round of the point zeta is knowledge sound. -/
def HZeta : Prop :=
  s.P.zeta.red.Know (fun _ => True) s.P.j5.cf.relR s.P.j6.cf.relR (fun _ _ w => w)
    ((s.P.errZeta, ()) : ℕ × Unit)

theorem hZeta (h : Function.Injective s.P.D.py) : HZeta s := know_zeta s.P h

/-! ### beside the statements -/

theorem pt_point (h : s.P.FoldErr s.on0 s.εf) : Nonempty s.P.pt.shape.IsPoint :=
  (ldLin_pt s.P s.on0 s.εf (fun _ => True) h).good.point
theorem pt_isLocal (h : s.P.FoldErr s.on0 s.εf) : s.P.pt.IsLocal :=
  (ldLin_pt s.P s.on0 s.εf (fun _ => True) h).good.isLocal
theorem loc_point : Nonempty s.P.loc.shape.IsPoint :=
  (ldLin_loc s.P s.on0 (sndOf s.P s.wa) fun _ => True).good.point
theorem loc_isLocal : s.P.loc.IsLocal :=
  (ldLin_loc s.P s.on0 (sndOf s.P s.wa) fun _ => True).good.isLocal
theorem zeta_point (h : Function.Injective s.P.D.py) : Nonempty s.P.zeta.shape.IsPoint :=
  (ldLin_zeta s.P (fun _ => True) h).good.point
theorem zeta_isLocal (h : Function.Injective s.P.D.py) : s.P.zeta.IsLocal :=
  (ldLin_zeta s.P (fun _ => True) h).good.isLocal

end Cb.Pv.Lin

#print axioms Cb.Pv.Lin.know_step0
#print axioms Cb.Pv.Lin.know_sW
#print axioms Cb.Pv.Lin.hPt
#print axioms Cb.Pv.Lin.hLoc
#print axioms Cb.Pv.Lin.hZeta
#print axioms Cb.Pv.Lin.coreKB
