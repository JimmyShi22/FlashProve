-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqStd.lean: for toys: a preamble of a request with one segment, of standard parts,
for any configuration, an abstract field and variable codes: its hypotheses, its honest-verifier
zero knowledge (`r.Zk`) and its formats from conditions on codes and numbers; so the object's list.
(not all hypotheses are named here: see `Spec.ldOS_std`)

Definitions, one statement and proofs. A tool for guards against empty theorems; no parameter of a
protocol.
The preamble of a request is the field `req` of `SubsR` (Hiop/RecSubs.lean). The object's list of a
preamble is its parameter list there: `PreListR` (all items but knowledge soundness) with
`PreKnowR`.
Why: the theorems of Cb/Obj/LdObjectReqSeg.lean take a request `r : O.Req` (Cb/Req1/LdReq.lean: a
first sending, segments, a last part) with `r.Hyp`, `r.Zk` and `r.chain.Fmt` to the object's list of
a preamble. Here a request is built, and, under the hypotheses below, the three are proved.

The data: Cf: the configuration; `R : StdGM E P`, T, kp, Hh, V: a standard group whose messages can
be sent, its arrangement, its kept messages, the new messages of its closing
(Cb/Ld/LdGroupStdMsg.lean, Cb/Ld/LdGroupStd.lean, Cb/Ld/LdGroupNewStd.lean); numbers.

Main names: the request (`rqReq`):
  `rqFirst`: the first sending: the oracle messages of the group, each a standard oracle message:
    data 0, the pad a coin; independent seeds.
  `rqInF`, `rqInG`, `rqInM`, `rqInB`: a step without rounds: no row is claimed of the group but the
    samples' rows, which the bridge takes in by construction.
  `rqSeg`: one segment without a body and without a batching: bridge (independent coefficients),
    arrangement, fold; the one sending (the carried message, the kept messages encoded anew); the
    locations. In `rqSeg`, `rqReq`, `rqReqW` the link for the first three is a parameter `l`;
    `rqL` is the link of bridge, arrangement and fold, which `Spec.ldOS_std` and the theorems on
    formats put in for `l`.
  `rqOutF`, `rqOutM`, `rqOutB`: a step without rounds.
  `LdOLe Cf Sa`, `RqEnd Cf Dl`, `En.Laws`: what the request leaves is a parameter. Asked: a claim
    holds (tensor row and "more") of any message of the index if and only if what is claimed after
    the locations does (Cb/Req1/LdSegKit.lean: `LdLocD.After`: the folded form, the old samples'
    rows, the symbols read, all on the cut of the new messages). So the test that follows chooses
    its own parameters.
  `RqEnd.plain on₀`: the plain choice: a claim is (what the locations leave, the instance); the
    tensor row is trivial (g = 0, target 0, no rest); "more" := After; layout and families are
    on₀'s.
Proved:
  `rqFirst_hyp`, `rqIn_step`, `rqOut_step`, `rqReq_hyp` (`r.Hyp`), each under the hypotheses of its
    statement; `rqReq_zk` (`r.Zk`: nothing is asked, beside its hypotheses (`r.Hyp`): no move is a
    sub-protocol or a split, so no mask is used (but the fold's: Cb/Ld/LdGroupFold.lean) (in this
    sense: `r.Zk` holds, by `LdMv.Zk`, Cb/Req1/LdReq.lean)).
  The demands on positions, backwards: `rqQi` (at the end: at most t₂ long positions of each new
    message, nothing of older ones); `rq_loc_need` (the locations add tl positions of the open word:
    within what the one sending bears and `rqQc`); `rq_fold_need` (tl ≤ t: within what the fold's
    fresh mask bears); `rqQ1`, `rq_in_need` (t ≤ t₁: at most t long positions of each member: within
    what the first sending bears).
  Of the encoded index nothing is bounded here: the preamble does not read it and sends no encoding
    of it (the formats' first clause).
  `rqReqW`, `rqReqW_hyp`, `rqReqW_zk`, `rqReqW_fmt`, each under the hypotheses of its statement: the
    same request with any last part behind the locations (a list of moves to any stage): its three
    bundles from those of the last part.
  `rqL_fmt`, `rqReq_fmt` (`r.Fmt`), each under the hypotheses of its statement.
  `Spec.ldOS_std`: `Nonempty P`, `RqHyp`, `En.Laws` ⇒ `r.Hyp` ∧ `r.Zk` ∧ `r.chain.Fmt` ∧
    `PreListR` ∧ `PreKnowR`.

Notation: `Hh`: a choice of kept messages in a standard group (`StdHeld`, Cb/Ld/LdGroupStd.lean);
`d`: a natural number (`SumPar.Hyp`, Cb/Ld/LdTowerSumMain.lean, field `codes`, says that it is a
distance of the fold's three codes); `Lst`, `mC`, `mS`, `mW`: maps ℕ → ℕ (`SumPar.Hyp`, field
`errs`, says that, after j rounds, `Lst j` bounds the lists of the complex and `mC j`, `mS j`,
`mW j` the counts of mutual correlated agreement of the three tables); `L`: a natural number
(`RqHyp.list` asks `R.D.G.C.ListAt R.e L`).

Limits: in the plain choice of its end, and in that of Cb/Obj/LdObjectPartReq.lean, the request has
g = 0, τ = 0: no pending tensor row, no mask message for it, no final batching: it claims nothing
about the encoded index.
The model does not enter: the request's own claim (the first joint: `C.Rreq`, relaxed `C.RreqR`) is
carried beside all blocks and reads no oracle message; at the end the relaxed relation is asked to
hold of all cells (`RqHyp.rno`: a trivial model). What runs is the machinery.
This file does not say that `RqHyp` can be met (Cb/Obj/LdObjectPartReqToy.lean). No lookup, no
sumcheck (but the fold's: Cb/Ld/LdGroupFold.lean), no range check, no split, no mask that crosses a
closing: this request exercises sendings, a bridge, an arrangement with copies and zero rows, a
fold, kept messages, locations, formats and budgets. In the plain choice "more" is a predicate; as a
list of rows: Cb/Req1/LdSegAfterRows.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStd
import Cb.Obj.LdObjectReqSeg
import Cb.Req1.LdSegFormatMoves
import Cb.Req1.LdSegFormatGroup
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Obj.LdObject
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- the first joint of a request, beside messages that it does not read -/
def reqOver (C : ConfigurationWithOutOfDomainSample) (M : Type) : Rels Unit (C.X × C.Rec) C.E0 (M × (C.PIdx × C.Cells)) where
  rel  := fun x y w => C.Rreq x y w.2
  relR := fun a w => C.RreqR a w.2.2
  on   := fun a => (C.D a.2 a.1.2).isSome
  core := fun _ => ()

/-- no rows -/
abbrev noSb : Empty → Type := fun e => e.elim
def noSl (E J : Type) : ∀ b : Empty, Slf E (noSb b) J := fun b => b.elim

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P] (C : ConfigurationWithOutOfDomainSample) (R : StdGM E P)

/-- the first stage -/
@[reducible] def rqA : LdStage E Unit := LdStage.start E Unit (ldReqRels C fun _ => ())

/-- The first sending: the messages of the group; their data are 0, their pads are coins. -/
@[reducible] def rqFirst (w0 : (rqA (E := E) C).W) (L t : ℕ) :
    LdSendD (rqA (E := E) C) where
  N := R.D.S
  Sd := Sig.Seeds.indep _
  Wp' := C.PIdx × C.Cells
  bk := fun _ w => w
  D := Sig.Sender.ofMem (fun o => (R.M o).snd (fun _ _ => 0) w0) (fun w => w) w0
  L := fun _ => L
  t := fun _ => t

theorem rqFirst_hyp (w0 : (rqA (E := E) C).W) {L t : ℕ} (h : ∀ a, (R.M a).OK L t) :
    (rqFirst C R w0 L t).Hyp where
  laws := fun i => (h i).laws
  fair := (ldSendFam_fair_indep E _).1
  list := fun i => stdM_list (R.M i) (h i)
  evades := fun i => stdM_evades (R.M i) (h i)
  sender := ldSendMem_laws E R.D.S _ _ (fun o => (R.M o).snd (fun _ _ => 0) w0) (fun w => w) w0 _
    (fun a m r => stdM_enc (R.M a) _ _ m r) (fun _ _ => rfl)
  blind := ldSendMem_blind E R.D.S _ _ (fun o => (R.M o).snd (fun _ _ => 0) w0) (fun w => w)
    w0 _ fun a => stdM_blind (R.M a) (h a) _ _
  hides := ldSendMem_hides E R.D.S _ _ (fun o => (R.M o).snd (fun _ _ => 0) w0) (fun w => w) w0
    (fun _ => t) fun a => stdM_hides (R.M a) (h a) _ _

variable [Nonempty P] (T : StdArr R.D) (kp : R.A → Prop) [DecidablePred kp] (Hh : StdHeld T kp)

instance : Nonempty R.D.G.P := inferInstanceAs (Nonempty P)

/-- the bridge's evader: independent coefficients on the sample rows -/
@[reducible] def rqZ : Evader E (R.D.G.Row Empty) :=
  @Evader.indep E (R.D.G.Row Empty) _ _ _ (Classical.decEq _)

/-- Bridge-to-fold: no rows are claimed of the group but the samples'; beside it, the request's own
claim, which reads no message -/
@[reducible] def rqFold : LdFoldD E Unit :=
  Hh.hd.foldD noSb (noSl E _) (rqZ R) (reqOver C ((R.D.S.sub kp).Msg))

/-- the step into the segment: the empty family is dropped; "no rows" is written -/
def rqInF (x : ((C.X × C.Rec) × ((Sig.nil E).sum R.D.S).Smp)) : Option (rqFold C R T kp Hh).src.X :=
  some (((fun e => e.elim, fun e => e.elim), x.1), fun o => x.2 (.inr o))
def rqInG : ExtMap (C.E0.prod ((Sig.nil E).sum R.D.S).ext) (rqFold C R T kp Hh).src.Ex where
  map y := (y.1, fun o => y.2 (.inr o))
  src q := match q with
    | .inl p => {.inl p}
    | .inr ⟨o, x⟩ => {.inr ⟨.inr o, x⟩}
def rqInM (p : ((C.X × C.Rec) × ((Sig.nil E).sum R.D.S).Smp) ×
      (((Sig.nil E).sum R.D.S).Wit × (C.PIdx × C.Cells))) :
    (rqFold C R T kp Hh).src.X × (rqFold C R T kp Hh).src.W :=
  ((((fun e => e.elim, fun e => e.elim), p.1.1), fun o => p.1.2 (.inr o)),
    (fun o => p.2.1 (.inr o), p.2.2))
def rqInB (_ : ((C.X × C.Rec) × ((Sig.nil E).sum R.D.S).Smp) ×
      (C.E0.prod ((Sig.nil E).sum R.D.S).ext).Str)
    (w : (rqFold C R T kp Hh).src.W) :
    ((Sig.nil E).sum R.D.S).Wit × (C.PIdx × C.Cells) :=
  ((Sig.nil E).join R.D.S (T := OMsg.Wit) (Sig.nilFam E) w.1, w.2)

theorem rqIn_step (w0 : (rqA (E := E) C).W) (L t : ℕ) :
    StepT (rqInF C R T kp Hh) (rqInG C R T kp Hh) (rqInM C R T kp Hh) (rqInB C R T kp Hh)
      (rqFirst C R w0 L t).tgt.J.rels (rqFold C R T kp Hh).src.J.rels where
  isLocal := by
    intro y y' q h
    rcases q with p | ⟨o, x⟩
    · exact congrArg Sum.inl (Sum.inl.inj (h (.inl p) (Finset.mem_singleton_self _)))
    · have h1 := eq_of_heq
        (Sigma.mk.inj (Sum.inr.inj (h (.inr ⟨.inr o, x⟩) (Finset.mem_singleton_self _)))).2
      exact congrArg (fun v => Sum.inr (⟨o, v⟩ : R.D.S.ext.Sym)) h1
  acc := fun x y w hw =>
    ⟨rfl, fun o => hw.1 (.inr o), fun o => hw.2.1 (.inr o), fun b => b.elim, hw.2.2⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' _ hf hw
    obtain rfl : _ = x' := Option.some.inj hf
    rcases hw with hw | hw
    · refine Or.inl ⟨fun i => ?_, hw.2.2⟩
      rcases i with e | o
      · exact e.elim
      · exact hw.1 o
    · exact Or.inr fun hon => hw ⟨fun o => hon.1 (.inr o), hon.2⟩

end

/-- What a preamble leaves and the data of the test after it, over a fixed configuration and fixed
oracle messages: the fields of `LdOLd` (Cb/Obj/LdObject.lean) but S. -/
structure LdOLe {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) (Sa : Sig E) where
  Cl : Type
  Y   : Type
  [finY : Fintype Y]
  klo : ℕ
  l   : ℕ
  lay : Y × (Fin klo → Bool) → Cf.J₀
  py  : Y → Fin l → Bool
  g     : Cl → Y → E
  ψ     : Cl → (Fin Cf.X.v → E) × (Fin klo → E)
  τ     : Cl → E
  restM : Cl → Sa.Msg → E
  more  : Cl → Sa.Msg → Prop
  e' : ℕ
  t  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Y → (NO.om iO).C.J

/-- the LdOLd -/
@[reducible] def LdOLe.on {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E}
    {Sa : Sig E} (D : LdOLe Cf Sa) : LdOLd Cf :=
  { S := Sa, Cl := D.Cl, Y := D.Y, finY := D.finY, klo := D.klo, l := D.l, lay := D.lay, py := D.py,
    g := D.g, ψ := D.ψ, τ := D.τ, restM := D.restM, more := D.more, e' := D.e', t := D.t,
    NW := D.NW, SdW := D.SdW, iW := D.iW, lW := D.lW, NU := D.NU, SdU := D.SdU, iU := D.iU,
    lU := D.lU, NO := D.NO, SdO := D.SdO, iO := D.iO, lO := D.lO }

/-- The end of a request after locations: the data. -/
structure RqEnd {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Cf : LdCf F E) (Dl : LdLocD E Unit) where
  e  : LdOLe Cf Dl.S
  /-- how a claim is made of what the locations leave and the instance -/
  cl : ((Dl.Xc × Dl.hd.Smp) × Dl.Lc) × Cf.conf.X → e.Cl

/-- a claim holds if and only if what is claimed after the locations does -/
structure RqEnd.Laws {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} {Dl : LdLocD E Unit} (En : RqEnd Cf Dl) : Prop where
  fwd : ∀ x xm rec U m, Dl.After x m → En.e.on.ol.holds (En.cl (x, xm)) rec U m
  bwd : ∀ x xm rec U m, En.e.on.ol.holds (En.cl (x, xm)) rec U m → Dl.After x m

/-- The plain choice. -/
@[reducible] def RqEnd.plain {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} (Dl : LdLocD E Unit) (on₀ : LdOLd Cf) : RqEnd Cf Dl where
  e := { Cl := ((Dl.Xc × Dl.hd.Smp) × Dl.Lc) × Cf.conf.X, Y := on₀.Y, finY := on₀.finY,
         klo := on₀.klo, l := on₀.l, lay := on₀.lay, py := on₀.py, g := fun _ _ => 0,
         ψ := fun _ => (fun _ => 0, fun _ => 0), τ := fun _ => 0, restM := fun _ _ => 0,
         more := fun cl m => Dl.After cl.1 m, e' := on₀.e', t := on₀.t, NW := on₀.NW,
         SdW := on₀.SdW, iW := on₀.iW, lW := on₀.lW, NU := on₀.NU, SdU := on₀.SdU, iU := on₀.iU,
         lU := on₀.lU, NO := on₀.NO, SdO := on₀.SdO, iO := on₀.iO, lO := on₀.lO }
  cl := id

theorem rqEnd_plain {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} (Dl : LdLocD E Unit) (on₀ : LdOLd Cf) : (RqEnd.plain Dl on₀).Laws where
  fwd := fun _ _ _ _ _ h => ⟨by
    show ∑ y, ∑ c, (0 : E) * _ * _ + 0 = 0
    rw [add_zero]
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by rw [zero_mul, zero_mul], h⟩
  bwd := fun _ _ _ _ _ h => h.2

section
variable {F E P Pn : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype P]
  [Nonempty P] [Fintype Pn] (Cf : LdCf F E) (R : StdGM E P) (T : StdArr R.D) (kp : R.A → Prop)
  [DecidablePred kp] (Hh : StdHeld T kp) (V : StdNew Hh.hd Pn)
  (w1 : (rqFold Cf.conf R T kp Hh).tgt.S.Wit × (rqFold Cf.conf R T kp Hh).tgt.Wp) (L₂ t₂ tl : ℕ)

/-- The second half of the closing. -/
@[reducible] def rqClose : LdCloseD (rqFold Cf.conf R T kp Hh) :=
  V.close noSb (noSl E _) (rqZ R) (reqOver Cf.conf ((R.D.S.sub kp).Msg)) w1 L₂ t₂ tl

variable (En : RqEnd Cf (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc)

/-- What the request leaves. -/
@[reducible] def rqO : LdOL F E := En.e.on.ol

/-- the last stage -/
@[reducible] def rqZ' : LdStage E Unit :=
  (rqO Cf R T kp Hh V w1 L₂ t₂ tl En).zReq fun _ => ()

/-- the last step: the explicit part is re-bracketed; the cells leave the witness -/
def rqOutF (x : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.X) :
    Option (rqZ' Cf R T kp Hh V w1 L₂ t₂ tl En).X :=
  some ((En.cl (x.1.1, x.1.2.1), x.1.2.2), x.2)
def rqOutM (p : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.X ×
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.W) :
    (rqZ' Cf R T kp Hh V w1 L₂ t₂ tl En).X × (rqZ' Cf R T kp Hh V w1 L₂ t₂ tl En).W :=
  (((En.cl (p.1.1.1, p.1.1.2.1), p.1.1.2.2), p.1.2), (p.2.1, p.2.2.1))
def rqOutB (c0 : Cf.conf.Cells)
    (_ : (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.X ×
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.Ex.Str)
    (w : (rqZ' Cf R T kp Hh V w1 L₂ t₂ tl En).W) :
    (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.W := (w.1, (w.2, c0))

theorem rqOut_step (c0 : Cf.conf.Cells) (hE : En.Laws) (hno : ∀ i x c, Cf.conf.Rno i x c) :
    StepT (rqOutF Cf R T kp Hh V w1 L₂ t₂ tl En) (ExtMap.id _)
      (rqOutM Cf R T kp Hh V w1 L₂ t₂ tl En) (rqOutB Cf R T kp Hh V w1 L₂ t₂ tl En c0)
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.J.rels
      (rqZ' Cf R T kp Hh V w1 L₂ t₂ tl En).J.rels where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  acc := fun x y w hw => ⟨rfl, hw.1, hw.2.1, hw.2.2.2.1, hE.fwd _ _ _ _ _ hw.2.2.1⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' _ hf hw
    obtain rfl : _ = x' := Option.some.inj hf
    by_cases hon : ((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.S.over
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.A).on (x, y)
    · have hD : (Cf.conf.D y.1 x.1.2.2).isSome := hon.2
      rcases hw with hw | hw
      · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hD
        obtain ⟨U, -, hm⟩ := hw.2
        exact Or.inl ⟨hw.1, hE.bwd _ _ _ U _ hm, i, hi, hno i _ c0⟩
      · refine absurd ⟨hon.1, fun hc => ?_⟩ hw
        have hc' : Cf.conf.coll y.1 x.1.2.2.1 := hc
        unfold ConfigurationWithOutOfDomainSample.D at hD
        rw [if_pos hc'] at hD
        cases hD
    · exact Or.inr hon

variable (w0 : (rqA (E := E) Cf.conf).W) (L₁ t₁ : ℕ)
  (l : Link Unit (rqFold Cf.conf R T kp Hh).src.J (rqFold Cf.conf R T kp Hh).mid)
  (c0 : Cf.conf.Cells)

/-- the one segment -/
@[reducible] def rqSeg :
    LdSeg (rqFold Cf.conf R T kp Hh).src (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt :=
  V.seg noSb (noSl E _) (rqZ R) (reqOver Cf.conf ((R.D.S.sub kp).Msg)) l w1 L₂ t₂ tl

/-- The request with any last part: the first sending; the step into the segment; one segment; then
a list of moves "last" from the stage after the locations to any stage z. -/
def rqReqW {z : LdStage E Unit}
    (last : LdProg (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt z)
    (lastT : last.All fun t => t = .sub ∨ t = .step) :
    LdReq (rqA (E := E) Cf.conf) z where
  first := rqFirst Cf.conf R w0 L₁ t₁
  a₁ := (rqFold Cf.conf R T kp Hh).src
  more := .snoc (.nil _)
    (.step _ _ (rqInF Cf.conf R T kp Hh) (rqInG Cf.conf R T kp Hh)
      (rqInM Cf.conf R T kp Hh) (rqInB Cf.conf R T kp Hh))
  b := (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt
  segs := .snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l)
  last := last
  moreT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inr rfl⟩
  lastT := lastT

theorem rqReqW_hyp {z : LdStage E Unit}
    (last : LdProg (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt z)
    (lastT : last.All fun t => t = .sub ∨ t = .step) (h₁ : ∀ a, (R.M a).OK L₁ t₁)
    (hl : (rqFold Cf.conf R T kp Hh).Hyp l) (h₂ : V.OK L₂ t₂) (hlast : last.Hyp) :
    (rqReqW Cf R T kp Hh V w1 L₂ t₂ tl w0 L₁ t₁ l last lastT).Hyp where
  first := rqFirst_hyp Cf.conf R w0 h₁
  more := (LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nil _, rqIn_step Cf.conf R T kp Hh w0 L₁ t₁⟩
  segs := by
    show LdSegs.Hyp (.snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l))
    rw [LdSegs.Hyp, LdSegs.Hyp]
    exact ⟨trivial, stdNew_seg V _ _ _ _ l w1 tl hl h₂⟩
  last := hlast

/-- zero knowledge: the parts before "last" ask nothing, beside their hypotheses; "last" is asked at
what is fresh after the segment -/
theorem rqReqW_zk {z : LdStage E Unit}
    (last : LdProg (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt z)
    (lastT : last.All fun t => t = .sub ∨ t = .step)
    (hlast : last.Zk
      ((rqReqW Cf R T kp Hh V w1 L₂ t₂ tl w0 L₁ t₁ l last lastT).segs.After
        (rqReqW Cf R T kp Hh V w1 L₂ t₂ tl w0 L₁ t₁ l last lastT).base₀)) :
    (rqReqW Cf R T kp Hh V w1 L₂ t₂ tl w0 L₁ t₁ l last lastT).Zk where
  segs := by
    show LdSegs.Zk (.snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l)) _
    rw [LdSegs.Zk, LdSegs.Zk]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · exact ldReq_zk_free E Unit _ _ _ _ (LdProg.all_nil _ _)
    · exact ldReq_zk_free E Unit _ _ _ _ (LdProg.all_nil _ _)
    · exact ldReq_zk_free E Unit _ _ _ _
        ((LdProg.all_snoc' _ _ _).2
          ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)
    · exact ldReq_zk_free E Unit _ _ _ _
        ((LdProg.all_snoc' _ _ _).2
          ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)
  last := hlast

/-- The request: the first sending; the step into the segment; one segment; the last step. -/
def rqReq : (rqO Cf R T kp Hh V w1 L₂ t₂ tl En).Req (fun _ => ()) (fun _ => ()) where
  first := rqFirst Cf.conf R w0 L₁ t₁
  a₁ := (rqFold Cf.conf R T kp Hh).src
  more := .snoc (.nil _)
    (.step _ _ (rqInF Cf.conf R T kp Hh) (rqInG Cf.conf R T kp Hh)
      (rqInM Cf.conf R T kp Hh) (rqInB Cf.conf R T kp Hh))
  b := (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt
  segs := .snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l)
  last := .snoc (.nil _)
    (.step _ _ (rqOutF Cf R T kp Hh V w1 L₂ t₂ tl En) (ExtMap.id _)
      (rqOutM Cf R T kp Hh V w1 L₂ t₂ tl En) (rqOutB Cf R T kp Hh V w1 L₂ t₂ tl En c0))
  moreT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inr rfl⟩
  lastT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inr rfl⟩

/-- The hypotheses of all its moves. -/
theorem rqReq_hyp (h₁ : ∀ a, (R.M a).OK L₁ t₁) (hl : (rqFold Cf.conf R T kp Hh).Hyp l)
    (h₂ : V.OK L₂ t₂) (hE : En.Laws) (hno : ∀ i x c, Cf.conf.Rno i x c) :
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ l c0).Hyp where
  first := rqFirst_hyp Cf.conf R w0 h₁
  more := (LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nil _, rqIn_step Cf.conf R T kp Hh w0 L₁ t₁⟩
  segs := by
    show LdSegs.Hyp (.snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l))
    rw [LdSegs.Hyp, LdSegs.Hyp]
    exact ⟨trivial, stdNew_seg V _ _ _ _ l w1 tl hl h₂⟩
  last :=
    (LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nil _, rqOut_step Cf R T kp Hh V w1 L₂ t₂ tl En c0 hE hno⟩

/-- Zero knowledge asks nothing more: no move is a sub-protocol with masks or a split. (in this
sense: `(rqReq ..).Zk` holds, by `LdMv.Zk`, Cb/Req1/LdReq.lean) -/
theorem rqReq_zk : (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ l c0).Zk where
  segs := by
    show LdSegs.Zk (.snoc (.nil _) (rqSeg Cf R T kp Hh V w1 L₂ t₂ tl l)) _
    rw [LdSegs.Zk, LdSegs.Zk]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · exact ldReq_zk_free E Unit _ _ _ _ (LdProg.all_nil _ _)
    · exact ldReq_zk_free E Unit _ _ _ _ (LdProg.all_nil _ _)
    · exact ldReq_zk_free E Unit _ _ _ _
        ((LdProg.all_snoc' _ _ _).2
          ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)
    · exact ldReq_zk_free E Unit _ _ _ _
        ((LdProg.all_snoc' _ _ _).2
          ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)
  last := ldReq_zk_free E Unit _ _ _ _
    ((LdProg.all_snoc' _ _ _).2
      ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)

end

/-! ## The formats -/

/-- the encoded index is all of the further oracles -/
def ixId (E0 : ExtSpec) : IxAt E0 E0 := ⟨id, id⟩

section
variable {F E P Pn : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype P]
  [Nonempty P] [Fintype Pn] (Cf : LdCf F E) (R : StdGM E P) (T : StdArr R.D) (kp : R.A → Prop)
  [DecidablePred kp] (Hh : StdHeld T kp) (V : StdNew Hh.hd Pn)
  (w1 : (rqFold Cf.conf R T kp Hh).tgt.S.Wit × (rqFold Cf.conf R T kp Hh).tgt.Wp) (L₂ t₂ tl : ℕ)
  (En : RqEnd Cf (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc)

/-- of the carried oracles: nothing of the kept oracle messages -/
def rqQF : Finset (LdCarE (S := R.D.S) kp Cf.conf.E0).Pos → Prop := fun W => W.toRight = ∅

/-- with the test open: at most tl positions of the open word, nothing of the oracle messages that
are not held -/
def rqQc : Finset (rqFold Cf.conf R T kp Hh).tgt.Ex.Pos → Prop := fun U =>
  U.toLeft.toLeft.card ≤ tl ∧ U.toRight = ∅

/-- at the end: at most t₂ long positions of each new oracle message; nothing of older ones; of the
encoded index whatever -/
def rqQi : Finset (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.Ex.Pos → Prop :=
  (rqFold Cf.conf R T kp Hh).S₂.qSum V.N.N₀ (E₀ := Cf.conf.E0) (fun W => W.toRight = ∅) fun _ => t₂

open Classical in
/-- Under the hypotheses below, what the locations need is within what the one sending bears -/
theorem rq_loc_need (ρ : Rho (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.link.R.shape)
    (U : Finset (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.Ex.Pos)
    (hU : rqQi Cf R T kp Hh V w1 L₂ t₂ tl U) :
    (rqFold Cf.conf R T kp Hh).S₂.qSum V.N.N₀ (E₀ := (rqFold Cf.conf R T kp Hh).tgt.E₀)
      (rqQc Cf R T kp Hh tl) (fun _ => t₂)
      ((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.link.R.need ρ U) := by
  have hn := ldFmt_loc_need E Unit (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc ρ U
  refine ⟨fun W hW => ⟨?_, ?_⟩, fun a => ?_⟩
  · refine le_trans (Finset.card_le_card (t := Finset.univ.image ρ.1) fun x hx => ?_)
      (le_trans Finset.card_image_le (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin])))
    obtain ⟨u, hu, hs⟩ := (hW _).1 (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hx))
    rcases u with q | ⟨a | a, z⟩
    · obtain rfl : Sum.inl x = q := Sum.inl.inj (Sum.inl.inj (Finset.mem_singleton.1 hs))
      rcases (hn _).1 hu with ⟨k, hk⟩ | ⟨u', _, hu'⟩
      · exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, (Sum.inl.inj (Sum.inl.inj hk)).symm⟩
      · rcases u' with p | s
        · cases Sum.inl.inj hu'
        · cases hu'
    · cases Sum.inl.inj (Finset.mem_singleton.1 hs)
    · cases Finset.mem_singleton.1 hs
  · refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
    obtain ⟨u, hu, hs'⟩ := (hW _).1 (Finset.mem_toRight.1 hs)
    rcases u with q | ⟨a | a, z⟩
    · cases Sum.inl.inj (Finset.mem_singleton.1 hs')
    · obtain rfl : s = ⟨a, z⟩ := Sum.inr.inj (Sum.inl.inj (Finset.mem_singleton.1 hs'))
      rcases (hn _).1 hu with ⟨k, hk⟩ | ⟨u', hu1, hu'⟩
      · cases hk
      · rcases u' with p | s'
        · cases hu'
        · obtain rfl : (⟨Sum.inl a, z⟩ : ((rqFold Cf.conf R T kp Hh).S₂.sum V.N.N₀).ext.Pos) = s' :=
            Sum.inr.inj hu'
          have h0 := hU.1 ((U.biUnion ((rqFold Cf.conf R T kp Hh).S₂.mergeE V.N.N₀ Cf.conf.E0).src).toLeft) fun p => by
            rw [Finset.mem_toLeft, Finset.mem_biUnion]
          have h1 : (⟨a, z⟩ : (rqFold Cf.conf R T kp Hh).S₂.ext.Pos) ∈
              ((U.biUnion
                ((rqFold Cf.conf R T kp Hh).S₂.mergeE V.N.N₀ Cf.conf.E0).src).toLeft).toRight :=
            Finset.mem_toRight.2 (Finset.mem_toLeft.2
              (Finset.mem_biUnion.2 ⟨_, hu1, Finset.mem_singleton_self _⟩))
          rw [h0] at h1
          exact absurd h1 (Finset.notMem_empty _)
    · cases Finset.mem_singleton.1 hs'
  · refine le_trans (cnt_mono fun x hx => ?_) (hU.2 a)
    rcases (hn _).1 hx with ⟨k, hk⟩ | ⟨u', hu1, hu'⟩
    · cases hk
    · rcases u' with p | s'
      · cases hu'
      · obtain rfl := Sum.inr.inj hu'
        exact hu1

variable (t : ℕ)

/-- Under the hypotheses below, what is needed with the test open is, before the step that lets the
kept messages be read in the folded word, within what the fold bears -/
theorem rq_fold_need (ht : tl ≤ t) (U : Finset (rqFold Cf.conf R T kp Hh).tgt.Ex.Pos)
    (W : Finset (rqFold Cf.conf R T kp Hh).mid.E.Pos)
    (hW : ∀ x, x ∈ W ↔ ∃ u ∈ U, x ∈ (rqFold Cf.conf R T kp Hh).pE.src u)
    (hU : rqQc Cf R T kp Hh tl U) :
    besideQ (fun S : Finset (rqFold Cf.conf R T kp Hh).Cf.ext.Pos => S.card ≤ t) (rqQF Cf R kp)
      W := by
  have hr : ∀ s, (Sum.inr s : (rqFold Cf.conf R T kp Hh).tgt.Ex.Pos) ∉ U := fun s hs => by
    have h1 := Finset.mem_toRight.2 hs
    rw [hU.2] at h1
    exact absurd h1 (Finset.notMem_empty _)
  refine ⟨le_trans (Finset.card_le_card fun x hx => ?_) (le_trans hU.1 ht),
    Finset.eq_empty_of_forall_notMem fun s hs => ?_⟩
  · obtain ⟨u, hu, hs⟩ := (hW _).1 (Finset.mem_toLeft.1 hx)
    rcases u with (x' | p) | s
    · obtain rfl : x = x' := Sum.inl.inj (Finset.mem_singleton.1 hs)
      exact Finset.mem_toLeft.2 (Finset.mem_toLeft.2 hu)
    · obtain ⟨q, -, hq⟩ := (mem_biUnion_at _).1 hs
      cases Finset.mem_singleton.1 hq
    · exact absurd hu (hr s)
  · obtain ⟨u, hu, hs'⟩ := (hW _).1 (Finset.mem_toRight.1 (Finset.mem_toRight.1 hs))
    rcases u with (x' | p) | s'
    · cases Finset.mem_singleton.1 hs'
    · obtain ⟨q, hq0, hq⟩ := (mem_biUnion_at _).1 hs'
      obtain rfl := Finset.mem_singleton.1 hq0
      cases Sum.inr.inj (Finset.mem_singleton.1 hq)
    · exact absurd hu (hr s')

open Classical in
/-- before the bridge: the sources of at most t common long positions of the group, and of the
encoded index whatever -/
def rqQ1 : Finset (rqFold Cf.conf R T kp Hh).src.Ex.Pos → Prop := fun W =>
  ∃ U,
    besideQ (fun S : Finset R.D.G.C.ext.Pos => S.card ≤ t) (rqQF Cf R kp) U ∧
    W = U.biUnion (ldBrG R.D.G kp Cf.conf.E0).src

open Classical in
/-- Under the hypotheses below, `rqQ1` is within what the first sending bears -/
theorem rq_in_need (t₁ : ℕ) (ht : t ≤ t₁) (U : Finset (rqFold Cf.conf R T kp Hh).src.Ex.Pos)
    (W : Finset (Cf.conf.E0.prod ((Sig.nil E).sum R.D.S).ext).Pos)
    (hW : ∀ x, x ∈ W ↔ ∃ u ∈ U, x ∈ (rqInG Cf.conf R T kp Hh).src u) (hU : rqQ1 Cf R T kp Hh t U) :
    (Sig.nil E).qSum R.D.S (E₀ := Cf.conf.E0) (fun _ => True) (fun _ => t₁) W := by
  obtain ⟨U', ⟨h1, h2⟩, rfl⟩ := hU
  refine ⟨fun _ _ => trivial, fun a => ?_⟩
  rw [cnt_eq_card_filter]
  refine le_trans (le_trans (Finset.card_le_card (t := U'.toLeft) fun x hx => ?_) h1) ht
  obtain ⟨u, hu, hs⟩ := (hW _).1 (Finset.mem_filter.1 hx).2
  rcases u with p | ⟨o, z⟩
  · cases Finset.mem_singleton.1 hs
  · obtain ⟨ha, hz⟩ := Sigma.mk.inj (Sum.inr.inj (Finset.mem_singleton.1 hs))
    obtain rfl : a = o := Sum.inr.inj ha
    obtain rfl : x = z := eq_of_heq hz
    rcases ldBrG_mem_inr R.D.G kp Cf.conf.E0 _ U' a x hu with ⟨_, z', hz', he⟩ | ⟨hk, hm⟩
    · obtain rfl : z' = x := he
      exact hz'
    · have h3 := Finset.mem_toRight.2 hm
      rw [show U'.toRight.toRight = ∅ from h2] at h3
      exact absurd h3 (Finset.notMem_empty _)

variable (dw : R.D.S.Wit × (Cf.conf.PIdx × Cf.conf.Cells)) (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ)

/-- bridge, arrangement, fold -/
@[reducible] def rqL :
    Link Unit (rqFold Cf.conf R T kp Hh).src.J (rqFold Cf.conf R T kp Hh).mid :=
  Hh.hd.link noSb (noSl E _) (rqZ R) (reqOver Cf.conf ((R.D.S.sub kp).Msg))
    (fun _ => Or.inl trivial) dw d t Lst mC mS mW L

omit [Nonempty P] in
theorem rqZ_ok : (rqZ R).OK := by
  letI : DecidableEq (R.D.G.Row Empty) := Classical.decEq _
  exact ok_indep E (R.D.G.Row Empty)

open Classical in
/-- Under the hypotheses below, bridge, arrangement, fold has the format -/
theorem rqL_fmt (hS : T.sh.OK) (hY : T.sh.par.Hyp d R.e t Lst mC mS mW)
    (hLi : R.D.G.C.ListAt R.e L) :
    (rqL Cf R T kp Hh t dw d Lst mC mS mW L).Fmt
      ((rqFold Cf.conf R T kp Hh).src.fmt (ixId Cf.conf.E0)
        (fun st => (Prod.snd st.2 : Cf.conf.Rec))
        (Prod.fst : _ → Cf.conf.PIdx) (rqQ1 Cf R T kp Hh t))
      ((rqFold Cf.conf R T kp Hh).fmtMid
        (ixId Cf.conf.E0) Prod.snd Prod.fst (besideQ (fun S => S.card ≤ t) (rqQF Cf R kp))) where
  idx := ldFmt_run_idx E Empty _ R.D.S R.D.G kp noSb (noSl E _) (rqZ R) _ _ _ _ (ixId Cf.conf.E0)
  pass := ldFmt_run_pass E Empty _ _ R.D.S R.D.G kp noSb (noSl E _) (rqZ R) _ _ _ Prod.snd
  hands := ldFmt_run_hands E Empty _ _ _ R.D.S R.D.G kp noSb (noSl E _) (rqZ R) _ _ _ Prod.fst _
  bears := (ldGroup_fold E Empty Unit _ _ R.D.S R.D.G T.sh kp noSb (noSl E _) (rqZ R) L _
    (reqOver Cf.conf ((R.D.S.sub kp).Msg)) (fun _ => Or.inl trivial) dw d t Lst mC mS mW
    (rqQ1 Cf R T kp Hh t) (rqQF Cf R kp) hS hY (rqZ_ok R) hLi (ldStd_fits E P R.D) fun U hU =>
      ⟨U, hU, Finset.ext fun _ => (mem_biUnion_at _).trans (mem_biUnion_at _).symm⟩).1.bears

variable (w0 : (rqA (E := E) Cf.conf).W) (L₁ t₁ : ℕ) (c0 : Cf.conf.Cells)

/-- the step into the segment moves the encoded index from its place to its place -/
theorem rqInG_moves :
    (rqInG Cf.conf R T kp Hh).Moves
      ((ixId Cf.conf.E0).inl ((Sig.nil E).sum R.D.S).ext) ((ixId Cf.conf.E0).inl R.D.S.ext) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun q hq p hp => ?_⟩
  rcases q with p' | ⟨o, x⟩
  · exact hq p (congrArg Sum.inl (Sum.inl.inj (Finset.mem_singleton.1 hp)).symm)
  · cases Finset.mem_singleton.1 hp

open Classical in
/-- The request with any last part has the format, if the last part has it from the format behind
the locations (the encoded index is all of the further oracles; the demand `rqQi`), under the
further hypotheses below. -/
theorem rqReqW_fmt {z : LdStage E Unit}
    (last : LdProg (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt z)
    (lastT : last.All fun t => t = .sub ∨ t = .step)
    (ψ : JFmt Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx z.J)
    (hlast : last.Fmt
      ((rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.fmt
        (ixId Cf.conf.E0) (fun st => Prod.snd st.2) Prod.fst (rqQi Cf R T kp Hh V w1 L₂ t₂ tl)) ψ)
    (h₁ : ∀ a, (R.M a).OK L₁ t₁) (h₂ : V.OK L₂ t₂) (hS : T.sh.OK)
    (hY : T.sh.par.Hyp d R.e t Lst mC mS mW) (hLi : R.D.G.C.ListAt R.e L)
    (ht : tl ≤ t) (ht₁ : t ≤ t₁) :
    (rqReqW Cf R T kp Hh V w1 L₂ t₂ tl w0 L₁ t₁
        (rqL Cf R T kp Hh t dw d Lst mC mS mW L) last lastT).Fmt
      ((rqA (E := E) Cf.conf).fmt (ixId Cf.conf.E0) Prod.snd Prod.fst fun _ => True) ψ := by
  refine ⟨(rqFirst Cf.conf R w0 L₁ t₁).tgt.fmt
      (ixId Cf.conf.E0) Prod.snd Prod.fst ((Sig.nil E).qSum R.D.S (fun _ => True) fun _ => t₁),
    (rqFold Cf.conf R T kp Hh).src.fmt
      (ixId Cf.conf.E0) (fun st => Prod.snd st.2) Prod.fst (rqQ1 Cf R T kp Hh t),
    (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.fmt
      (ixId Cf.conf.E0) (fun st => Prod.snd st.2) Prod.fst (rqQi Cf R T kp Hh V w1 L₂ t₂ tl),
    ?_, ?_, ?_, hlast⟩
  · exact ldFmt_send E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx (rqA Cf.conf)
      (rqFirst Cf.conf R w0 L₁ t₁) (ixId _) Prod.snd Prod.fst Prod.fst (fun _ => True)
      (rqFirst_hyp Cf.conf R w0 h₁) fun _ => rfl
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩
    exact ldFmt_step E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx _ _ _ _ _ _ _ _
      (rqInG_moves Cf R T kp Hh) (fun x x' hx => by obtain rfl : _ = x' := Option.some.inj hx; rfl)
      (fun _ => rfl) (fun U W hW hU => rq_in_need Cf R T kp Hh t t₁ ht₁ U W hW hU)
  · refine (LdSegs.fmt_snoc _ _ _ _).2 ⟨_, (LdSegs.fmt_nil _ _ _).2 rfl, ?_⟩
    refine ⟨_, _,
      (rqFold Cf.conf R T kp Hh).tgt.fmt ((ixId Cf.conf.E0).inr _) (fun st => Prod.snd st.2)
        (fun w => Prod.fst w.2) (rqQc Cf R T kp Hh tl),
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).snd.tgt.fmt ((ixId Cf.conf.E0).inr _)
        (fun st => Prod.snd st.2) Prod.fst
        ((rqFold Cf.conf R T kp Hh).S₂.qSum V.N.N₀ (rqQc Cf R T kp Hh tl) fun _ => t₂),
      (LdProg.fmt_nil _ _ _).2 rfl,
      (LdProg.fmt_nil _ _ _).2 rfl,
      ?_, ?_, ?_⟩
    · refine (LdProg.fmt_snoc _ _ _ _).2
        ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
      exact ldFmt_fold E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx (rqFold Cf.conf R T kp Hh) _
        (ixId _) Prod.snd Prod.fst _ _ _ (rqL_fmt Cf R T kp Hh t dw d Lst mC mS mW L hS hY hLi)
        (fun U W hW hU => rq_fold_need Cf R T kp Hh tl t ht U W hW hU)
    · exact ldFmt_send E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx
        (rqFold Cf.conf R T kp Hh).tgt (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).snd
        ((ixId _).inr _) (fun st => Prod.snd st.2) (fun w => Prod.fst w.2) Prod.fst
        (rqQc Cf R T kp Hh tl) (stdNew_snd V _ _ _ _ w1 tl h₂) fun _ => rfl
    · refine (LdProg.fmt_snoc _ _ _ _).2
        ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
      exact ldFmt_loc E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx
        (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc (ixId _) Prod.snd Prod.fst _ _
        (fun ρ U hU => rq_loc_need Cf R T kp Hh V w1 L₂ t₂ tl ρ U hU)

open Classical in
/-- Under the hypotheses below, the request has the format. -/
theorem rqReq_fmt (qz : Finset (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.Ex.Pos → Prop)
    (hq : ∀ U, qz U → rqQi Cf R T kp Hh V w1 L₂ t₂ tl U) (h₁ : ∀ a, (R.M a).OK L₁ t₁)
    (h₂ : V.OK L₂ t₂) (hS : T.sh.OK) (hY : T.sh.par.Hyp d R.e t Lst mC mS mW)
    (hLi : R.D.G.C.ListAt R.e L) (ht : tl ≤ t) (ht₁ : t ≤ t₁) :
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0).Fmt
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).fmtA (fun _ => ()) fun _ => True)
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).fmtZ (fun _ => ()) qz) := by
  refine ⟨(rqFirst Cf.conf R w0 L₁ t₁).tgt.fmt
      (ixId Cf.conf.E0) Prod.snd Prod.fst ((Sig.nil E).qSum R.D.S (fun _ => True) fun _ => t₁),
    (rqFold Cf.conf R T kp Hh).src.fmt
      (ixId Cf.conf.E0) (fun st => Prod.snd st.2) Prod.fst (rqQ1 Cf R T kp Hh t),
    (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc.tgt.fmt
      (ixId Cf.conf.E0) (fun st => Prod.snd st.2) Prod.fst (rqQi Cf R T kp Hh V w1 L₂ t₂ tl),
    ?_, ?_, ?_, ?_⟩
  · exact ldFmt_send E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx (rqA Cf.conf)
      (rqFirst Cf.conf R w0 L₁ t₁) (ixId _) Prod.snd Prod.fst Prod.fst (fun _ => True)
      (rqFirst_hyp Cf.conf R w0 h₁) fun _ => rfl
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩
    exact ldFmt_step E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx _ _ _ _ _ _ _ _
      (rqInG_moves Cf R T kp Hh) (fun x x' hx => by obtain rfl : _ = x' := Option.some.inj hx; rfl)
      (fun _ => rfl) (fun U W hW hU => rq_in_need Cf R T kp Hh t t₁ ht₁ U W hW hU)
  · refine (LdSegs.fmt_snoc _ _ _ _).2 ⟨_, (LdSegs.fmt_nil _ _ _).2 rfl, ?_⟩
    refine ⟨_, _,
      (rqFold Cf.conf R T kp Hh).tgt.fmt ((ixId Cf.conf.E0).inr _) (fun st => Prod.snd st.2)
        (fun w => Prod.fst w.2) (rqQc Cf R T kp Hh tl),
      (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).snd.tgt.fmt ((ixId Cf.conf.E0).inr _)
        (fun st => Prod.snd st.2) Prod.fst
        ((rqFold Cf.conf R T kp Hh).S₂.qSum V.N.N₀ (rqQc Cf R T kp Hh tl) fun _ => t₂),
      (LdProg.fmt_nil _ _ _).2 rfl,
      (LdProg.fmt_nil _ _ _).2 rfl,
      ?_, ?_, ?_⟩
    · refine (LdProg.fmt_snoc _ _ _ _).2
        ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
      exact ldFmt_fold E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx (rqFold Cf.conf R T kp Hh) _
        (ixId _) Prod.snd Prod.fst _ _ _ (rqL_fmt Cf R T kp Hh t dw d Lst mC mS mW L hS hY hLi)
        (fun U W hW hU => rq_fold_need Cf R T kp Hh tl t ht U W hW hU)
    · exact ldFmt_send E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx
        (rqFold Cf.conf R T kp Hh).tgt (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).snd
        ((ixId _).inr _) (fun st => Prod.snd st.2) (fun w => Prod.fst w.2) Prod.fst
        (rqQc Cf R T kp Hh tl) (stdNew_snd V _ _ _ _ w1 tl h₂) fun _ => rfl
    · refine (LdProg.fmt_snoc _ _ _ _).2
        ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
      exact ldFmt_loc E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx
        (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc (ixId _) Prod.snd Prod.fst _ _
        (fun ρ U hU => rq_loc_need Cf R T kp Hh V w1 L₂ t₂ tl ρ U hU)
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩
    refine ldFmt_step E Unit Cf.conf.E0 Cf.conf.Rec Cf.conf.PIdx _ _ _ _ _ _ _ _
      (ExtMap.Moves.id _) (fun x x' hx => by obtain rfl : _ = x' := Option.some.inj hx; rfl)
      (fun _ => rfl) (fun U W hW hU => ?_)
    have e : W = U :=
      Finset.ext fun x =>
        (hW x).trans ⟨fun ⟨u, hu, hx⟩ => (Finset.mem_singleton.1 hx) ▸ hu,
          fun hx => ⟨x, hx, Finset.mem_singleton_self _⟩⟩
    rw [e]
    exact hq U hU

/-- What is asked: conditions on codes, on the arrangement, on numbers; the model's relaxed relation
is trivial. -/
structure RqHyp : Prop where
  first : ∀ a, (R.M a).OK L₁ t₁
  new   : V.OK L₂ t₂
  shape : T.sh.OK
  held  : Hh.hd.Laws
  fold  : T.sh.par.Hyp d R.e t Lst mC mS mW
  list  : R.D.G.C.ListAt R.e L
  loc   : tl ≤ t
  pos   : t ≤ t₁
  rno   : ∀ i x c, Cf.conf.Rno i x c

variable {Cf R T kp Hh V w1 L₂ t₂ tl t d Lst mC mS mW L L₁ t₁}

open Classical in
theorem rqL_hyp (h : RqHyp Cf R T kp Hh V L₂ t₂ tl t d Lst mC mS mW L L₁ t₁) :
    (rqFold Cf.conf R T kp Hh).Hyp (rqL Cf R T kp Hh t dw d Lst mC mS mW L) :=
  ldGroup_seg E Empty Unit _ _ R.D.S R.D.G T.sh kp Hh.hd noSb (noSl E _) (rqZ R) _
    (reqOver Cf.conf ((R.D.S.sub kp).Msg)) (fun _ => Or.inl trivial) dw d t Lst mC mS mW L h.shape
    h.held h.fold (rqZ_ok R) h.list (ldStd_fits E P R.D)

end

/-- States: under `Nonempty P`, `RqHyp` and `En.Laws`, the request with standard parts meets the
object's list. -/
def Spec.ldOS_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (P Pn : Type) [Fintype P] [Nonempty P] [Fintype Pn] (Cf : LdCf F E) (R : StdGM E P)
      (T : StdArr R.D) (kp : R.A → Prop) [DecidablePred kp] (Hh : StdHeld T kp)
      (V : StdNew Hh.hd Pn)
      (w1 : (rqFold Cf.conf R T kp Hh).tgt.S.Wit × (rqFold Cf.conf R T kp Hh).tgt.Wp) (L₂ t₂ tl : ℕ)
      (En : RqEnd Cf (rqClose Cf R T kp Hh V w1 L₂ t₂ tl).loc) (t : ℕ)
      (dw : R.D.S.Wit × (Cf.conf.PIdx × Cf.conf.Cells)) (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ)
      (w0 : (rqA (E := E) Cf.conf).W) (L₁ t₁ : ℕ) (c0 : Cf.conf.Cells)
      (w₀ : Cf.conf.PIdx × Cf.conf.Cells) (z0 : Cf.conf.PIdx)
      (r0 : (rqO Cf R T kp Hh V w1 L₂ t₂ tl En).S.Rnd),
    RqHyp Cf R T kp Hh V L₂ t₂ tl t d Lst mC mS mW L L₁ t₁ → En.Laws →
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0).Hyp ∧
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0).Zk ∧
    (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁
        (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0).chain.Fmt
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).fmtA (fun _ => ()) fun _ => True)
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).fmtZ (fun _ => ()) (rqQi Cf R T kp Hh V w1 L₂ t₂ tl)) ∧
    PreListR (rqO Cf R T kp Hh V w1 L₂ t₂ tl En).left
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
        (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
        w₀).req
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
        (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
        w₀).hReq
      Prod.snd Prod.fst Cf.conf.Rreq
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
        (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
        w₀).nums ∧
    PreKnowR (rqO Cf R T kp Hh V w1 L₂ t₂ tl En).left
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
        (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
        w₀).req
      (fun a => (Cf.conf.D a.2 a.1.2).isSome) Cf.conf.RreqR
      (((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
          (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
          w₀).cellsOf
        z0 r0)
      ((rqO Cf R T kp Hh V w1 L₂ t₂ tl En).termOf
        (rqReq Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0)
        w₀).nums.err

theorem ldOS_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOS_std F E := by
  intro P Pn _ _ _ Cf R T kp _ Hh V w1 L₂ t₂ tl En t dw d Lst mC mS mW L w0 L₁ t₁ c0 w₀ z0 r0 h hE
  have hH := rqReq_hyp Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁
    (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0 h.first (rqL_hyp dw h) h.new hE h.rno
  have hZ :=
    rqReq_zk Cf R T kp Hh V w1 L₂ t₂ tl En w0 L₁ t₁ (rqL Cf R T kp Hh t dw d Lst mC mS mW L) c0
  have hF := ldFmt_req E Unit _ _ _ _ _ _ _ _
    (rqReq_fmt Cf R T kp Hh V w1 L₂ t₂ tl En t dw d Lst mC mS mW L w0 L₁ t₁ c0 _ (fun _ hU => hU)
      h.first h.new h.shape h.fold h.list h.loc h.pos)
  obtain ⟨a1, a2⟩ :=
    ldOS_object F E (rqO Cf R T kp Hh V w1 L₂ t₂ tl En) Unit _ _ _ w₀ _ _ z0 r0 hH hZ hF
  exact ⟨hH, hZ, hF, a1, a2⟩

end Cb
