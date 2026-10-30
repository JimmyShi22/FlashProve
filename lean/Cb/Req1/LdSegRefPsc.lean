-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPsc.lean: a block at the base as a move of a segment: what a segment requires of it,
from the block's own theorems.

Definitions, statements and proofs. By packing only; no block is proved here.

A segment of a request (Cb/Req1/LdSeg.lean) is made of lists of moves between stages (oracle
messages with samples, further oracles, a base joint on the messages). The zerocheck, the sumcheck
for a polynomial summand, the line step and the assembled lookup are blocks at the base (`Cb.BkA`,
Cb/Ld/LdLkpTreeP.lean: they send no oracle; the tuple of messages is a part of the witness). Here
such a block is entered as a move "sub", and what a segment, a request and their formats require of
a move is derived from what is proved of the block.

Main names:
  `a.after B`: the stage after the block: same oracle messages, same further oracles, same further
    witness; new explicit part and base joint B.
  `a.linkA B b`, `a.mvA B b`: the block b, lifted over the oracle messages of the stage
    (`LdStage.lift`, Cb/Req1/LdSeg.lean), as a link and as a move "sub" of one link.
  `mvA_hyp`: `b.Good a.A B` (for each fixed tuple: `GoodAt`) ⇒ the move's hypothesis (every link has
    the bundle without its clause on zero knowledge).
  `mvA_goodT`: `b.Good a.A B` and honest-verifier exact zero knowledge of b (`Honest.Exact`,
    Ior/Honest.lean) ⇒ the link has the whole bundle (a draw: `draw_exact_any`).
  `mvA_fmt`: `b.Plain` (Cb/Ld/LdLkpFormat.lean), and b hands on what rc reads ⇒ the move has the
    format (Cb/Req1/LdReqFormat.lean): the encoded index, wherever it is among the further oracles,
    is left alone; rc, px are handed on; every bound q is borne.
  `mvA_okT`, `mvA_okM`: the move's zero-knowledge clause (Cb/Req1/LdSegFresh.lean: `OkGiven base`):
    `mvA_okT`, under `b.Good a.A B` and `b.H.Exact a.A.rel b.P.bud`: from the whole bundle
    (`mvA_goodT`); `mvA_okM`: from the masked bundle (`(a.linkA B b).GoodM D`) with letters D whose
    fact is fresh at the start (`base D.fact`).
  `mvA_carry`: carrying a later block's masks: `b.Plain`, b reads the entries in Rd only
    (Cb/Ld/LdLkpFormatBlind.lean: `SameOn`), the fact f changes no entry in Rd (hk), f is fresh at
    the start ⇒ f is fresh after the move.
  `pscBk T ..`, `inBk Z ..`: the sumcheck, and the step into a sumcheck (zerocheck, line step, point
    of a forest), as blocks at the base.
  `pscBk_good` (from the true sum claim to the output rows, beside any joint; from the conditions on
    T), `pscBk_plain`, `pscBk_pass`; `inBk_good`, `inBk_exact` (nothing to simulate), `inBk_plain`,
    `inBk_pass`, `inBk_sameOn` (it reads no entry).
  For the assembled lookup: Cb/Ld/LdLkpAsm*.lean (good), Cb/Ld/LdLkpAsm2Fmt.lean (plain, pass).

Limits: this file does not say which blocks a reference segment has, in which order, with which
claims.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegProofs
import Cb.Req1.LdSegFormat
import Cb.Req1.LdSegFormatKit
import Cb.Req1.LdSegFresh
import Cb.Ld.LdLkpFormatBlind
import Cb.Ld.LdLkpAsm2Fmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The stage after a block at the base. -/
@[reducible] def LdStage.after
    (a : LdStage E Kc) {St' : Type} (B : Rels Kc St' a.E₀ (a.S.Msg × a.Wp)) : LdStage E Kc :=
  ⟨a.S, St', a.E₀, a.Wp, B⟩

/-- The block as a link, and as a move. -/
def LdStage.linkA (a : LdStage E Kc) {St' : Type} (B : Rels Kc St' a.E₀ (a.S.Msg × a.Wp))
    (b : BkA Kc a.S.Msg a.St St' a.E₀ a.Wp) : Link Kc a.J (a.after B).J :=
  a.lift B b.R b.H (fun _ _ _ wp => wp) b.P
def LdStage.mvA (a : LdStage E Kc) {St' : Type} (B : Rels Kc St' a.E₀ (a.S.Msg × a.Wp))
    (b : BkA Kc a.S.Msg a.St St' a.E₀ a.Wp) : LdMv a (a.after B) :=
  .sub _ _ (.one (a.linkA B b))

variable (a : LdStage E Kc)
  {St' : Type} (B : Rels Kc St' a.E₀ (a.S.Msg × a.Wp)) (b : BkA Kc a.S.Msg a.St St' a.E₀ a.Wp)

theorem mvA_tag : (a.mvA B b).tag = .sub := rfl

theorem linkA_goodB (h : b.Good a.A B) : (a.linkA B b).GoodB :=
  (ldSeg_lift E Kc a St' a.Wp a.E₀ B b.R b.H _ b.P h).1

theorem mvA_hyp (h : b.Good a.A B) : (a.mvA B b).Hyp := by
  unfold LdStage.mvA
  simp only [LdMv.Hyp, Chain.AllB]
  exact linkA_goodB a B b h

theorem mvA_goodT (h : b.Good a.A B) (hx : b.H.Exact a.A.rel b.P.bud) : (a.linkA B b).GoodT :=
  (ldSeg_lift E Kc a St' a.Wp a.E₀ B b.R b.H _ b.P h).2 hx

theorem mvA_fmt {E0 : ExtSpec} {Rc Pw : Type} (hp : b.Plain) (i : IxAt E0 a.E₀) {rc : a.St → Rc}
    {rc' : St' → Rc} (hr : b.R.Passes rc rc') (px : a.Wp → Pw) (q : Finset a.Ex.Pos → Prop) :
    (a.mvA B b).Fmt (a.fmt i rc px q) ((a.after B).fmt i rc' px q) :=
  (Chain.fmt_one _ _ _).2
    { idx := IdxLink.of_step (lift_idxStep a.S hp) i
      pass := (hr.keepX a.S.Smp).keepE a.S.ext
      hands := lift_hands a.S hp _ fun w => px w.2
      bears := lift_bears a.S hp q }

theorem mvA_okT (base : MaskFact a.J.W → Prop) (h : b.Good a.A B) (hx : b.H.Exact a.A.rel b.P.bud) :
    (a.mvA B b).chain.OkGiven base :=
  (Chain.okGiven_one _ _).2 (Or.inl (mvA_goodT a B b h hx))

theorem mvA_okM (base : MaskFact a.J.W → Prop) (D : MaskData (a.linkA B b).R a.J.W)
    (h : (a.linkA B b).GoodM D) (hb : base D.fact) :
    (a.mvA B b).chain.OkGiven base :=
  (Chain.okGiven_one _ _).2 (Or.inr ⟨D, h, hb⟩)

theorem mvA_carry {J : Type} (hp : b.Plain) {msg : a.S.Msg → J → E} {Rd : J → Prop}
    (hs : b.SameOn msg Rd) (base : MaskFact a.J.W → Prop) (f : MaskFact a.J.W)
    (hk : ∀ w w' m,
      f.kc w' = f.put m (f.kc w) → ∀ j, Rd j → msg (a.S.msgs w'.1) j = msg (a.S.msgs w.1) j)
    (hb : base f) :
    (a.mvA B b).chain.FreshGiven base f :=
  (Chain.freshGiven_one _ _ _).2
    (Or.inr ⟨f.Kc, f.kc, f.put, hb, blind_of_sameOn a.S hp hs f.kc f.Mk f.put hk⟩)

end

/-! ## The blocks -/

section Blocks
variable {E : Type} [Field E] [Fintype E]

/-- The sumcheck as a block at the base. -/
def pscBk (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E) :
    BkA Kc M (E × T.St) T.par.Out Ex Wp :=
  ⟨T.par.psc Ex, T.par.hon Ex fun w => msg w.1, T.par.nums Ex Kc⟩

/-- The step into a sumcheck as a block at the base. -/
def inBk (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type) :
    BkA Kc M Z.St0 (E × Z.T.St) Ex Wp :=
  ⟨IOR.draw Z.ev.D Z.nxX Ex,
    Honest.draw Z.ev.D Z.nxX Ex (M × Wp),
    Nums.draw Kc Z.ev.D Z.nxX Ex Z.ev.err⟩

theorem pscBk_good (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E)
    (A0 : Rels Kc T.St Ex (M × Wp)) (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj) :
    (pscBk T Ex M Wp Kc msg).Good
      (T.baseIn A0 fun w => msg w.1) (T.par.baseOut A0 fun w => msg w.1) := by
  have e : T.SumHolds = T.par.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m).symm
  unfold PscOur.baseIn
  rw [e]
  exact psc_goodAt E T.par Ex M Wp Kc A0 msg ((psc_our_ok E T).1 hV)
    (psc_our_deg E T hX hY) ((psc_our_ok E T).2 hI)

theorem pscBk_plain (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E) :
    (pscBk T Ex M Wp Kc msg).Plain :=
  plain_psc T.par Ex Kc M Wp fun w => msg w.1
theorem pscBk_pass (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E) :
    (pscBk T Ex M Wp Kc msg).R.Passes Prod.snd PscPar.Out.st :=
  psc_passes T.par Ex

theorem inBk_good (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type) (R0 : Rels Kc Z.St0 Ex (M × Wp))
    (msg : M → Z.T.J → E) (hL : Z.Link) (hB : Z.Back) (hO : Z.ev.OK) :
    (inBk Z Ex M Wp Kc).Good (Z.relsIn R0 msg) (Z.relsOut R0 msg) :=
  pscIn_goodAt E Z Ex M Wp Kc R0 msg hL hB hO
theorem inBk_exact (Z : PscIn E) (Ex : ExtSpec)
    (M Wp Kc : Type) (P : Z.St0 → Ex.Str → M × Wp → Prop) :
    (inBk Z Ex M Wp Kc).H.Exact P (inBk Z Ex M Wp Kc).P.bud :=
  draw_exact_any Ex (M × Wp) Z.ev.D Z.nxX P
theorem inBk_plain (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type) : (inBk Z Ex M Wp Kc).Plain :=
  plain_draw _ _ _
theorem inBk_pass (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type) (hB : Z.Back) :
    (inBk Z Ex M Wp Kc).R.Passes id fun x => Z.old x.2 :=
  Passes.draw _ _ Ex _ _ fun st β => hB st β
/-- a step into a sumcheck reads no entry -/
theorem inBk_sameOn (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc J : Type)
    (msg : M → J → E) (Rd : J → Prop) :
    (inBk Z Ex M Wp Kc).SameOn msg Rd :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

end Blocks
end Cb
