-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailSeams.lean: the draw of the matrix of a smallness test between two sendings: the
kind at joints whose condition may fail, and the two seams beside it.

In a proof file's first chain the draw stands between two sendings of oracle messages. A sending
(`kSend`, Johnson/Top/H/Send.lean) ends at `Cb.Pv.Send.outJ`, a joint of the form `.cf`
(Ior/KnowCollGood.lean): its condition is met by all statements, and its relaxed relation is
enlarged by the statements outside the old condition. A joint `jOver Sg A` has the condition that no
oracle message has a collision at its sample's seed. That is a fact on the words, which the first
map of a step without rounds does not see; so the clause `onOut` of `KObj.StepD.OK`
(Johnson/E/KObj/RowS.lean) is not to be had, in general, from a sending's last joint to a joint
`jOver Sg A` (by reading; no theorem here says so). It is had to `(jOver Sg A).cf`, as in the
library's own renaming step (`sigSum_step`, Cb/Ld/LdSigSumProofs.lean). A block has its
property between two joints if and only if it has it between their `.cf` (`KObj.BK.good_cf`,
Johnson/E/KObj/Cf.lean). Definitions, statements and proofs.

Main names:
  `KTailRngCf`, `KTailRngCf_good`: the kind of Johnson/Top/H/TailRng.lean, the same reduction,
    extractor and errors, between `(jOver Sg A).cf` and `(jOver Sg B).cf`.
  `seamSent S s A₀ bk C`: from the last joint of the sending of the family s.N to a statement over
    S, at the joint A₀ before it, to `(jOver (S.sum s.N) C).cf`: the library's renaming
    (`Sig.mergeX`, `mergeE`, `splitW`, Cb/Ld/LdSigSum.lean): samples, words and witnesses of S and
    of the family are laid side by side.
  `seamSent_ok`: if A₀'s condition gives C's (`hon`) and, under A₀'s condition, C's relaxed relation
    gives A₀'s, a part of whose witness is read off the new messages (`hrel`): `StepD.OK`.
  `SentCaller`, `SentCaller.caller`, `SentCaller.before`: who calls the draw behind a sending; the
    callers of the draw and of that sending.
  `seamToRng`, `seamToRng_ok`: that seam, from `kSend`'s last joint at `before` to `KTailRngCf`'s
    first at `caller`; `hon` is met by definition, `hrel` stays a premise.
  `seamSame J on relR`, `seamSame_ok`: on the same types nothing is mapped; from two premises.
  `sendBehind`, `seamFromRng`, `seamFromRng_ok`: the caller of the sending behind the draw,
    which starts at the joint at which the draw ends; the seam between them: no premise.
  `seamSentP`, `seamToRngP`, `sendBehindP`, `seamFromRngP`, with `…_ok`: the same between joints
    with their conditions: for a sending whose last joint is `jOver N (N.pull A back)`, and not
    its `.cf`; no such kind of sending is named here.
  `jOver_eq`: a joint `jOver S A` does not read A's cores: two base joints with the same condition
    and relaxed relation give one joint. So a kind whose base joints have the core Unit has the
    blocks of every file whose base joints differ from them in the cores alone.

Limits: `hrel` is a hypothesis: it is shown of no sub-proof here. Nothing says which family is sent
at which place. A seam adds no round and no error. Nothing on an honest prover.
-/
import Johnson.Top.H.TailRng
import Johnson.Top.H.Send
import Johnson.E.KObj.Cf
import Johnson.E.KObj.RowS
import Cb.Ld.LdSigSumProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR VerifiableInference.OnPublicFiles

/-- The draw of the matrix, between joints whose condition may fail. -/
noncomputable def KTailRngCf : KFam.{1} where
  ι := TailCaller
  mem := fun c => c.s.OK
  src := fun c => (KTailRng.src c).cf
  dst := fun c => (KTailRng.dst c).cf
  blk := fun c => (KTailRng.blk c).cf

theorem KTailRngCf_good : KTailRngCf.Good := fun c hc =>
  (BK.good_cf (KTailRng.blk c)).1 (KTailRng_good c hc)

section
variable {E : Type} [Field E] (S : Sig E) {Kc Kc' St Wp Wp' : Type} {E₀ : ExtSpec}

/-- A joint over a signature does not read the base joint's cores. -/
theorem jOver_eq (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc' St E₀ (S.Msg × Wp))
    (h1 : A.on = A'.on) (h2 : A.relR = A'.relR) : jOver S A = jOver S A' := by
  have e1 : (S.over A).on = (S.over A').on := by
    funext a
    show (_ ∧ A.on _) = (_ ∧ A'.on _)
    rw [h1]
  have e2 : (S.over A).relR = (S.over A').relR := by
    funext a w
    show (_ ∧ A.relR _ _) = (_ ∧ A'.relR _ _)
    rw [h2]
  show (⟨St × S.Smp, E₀.prod S.ext, S.Wit × Wp, (S.over A).on, (S.over A).relR⟩ : JK) =
    ⟨St × S.Smp, E₀.prod S.ext, S.Wit × Wp, (S.over A').on, (S.over A').relR⟩
  rw [e1, e2]

/-- From a sending's last joint to a joint over the old and the new oracle messages. -/
@[reducible] def seamSent (s : Cb.Pv.Send.Size E) (A₀ : Rels Kc St E₀ (S.Msg × Wp))
    (bk : s.N.Msg → Wp' → Wp) (C : Rels Kc' St E₀ ((S.sum s.N).Msg × Wp')) :
    StepD (jOf (Cb.Pv.Send.outJ s (S.over A₀) (S.backN s.N bk))) (jOver (S.sum s.N) C).cf :=
  ⟨S.mergeX s.N St, S.mergeE s.N E₀, fun _ w => S.splitW s.N Wp' w⟩

/-- What that seam owes, from two premises on the base joints. -/
theorem seamSent_ok (s : Cb.Pv.Send.Size E) (A₀ : Rels Kc St E₀ (S.Msg × Wp))
    (bk : s.N.Msg → Wp' → Wp) (C : Rels Kc' St E₀ ((S.sum s.N).Msg × Wp'))
    (hon : ∀ a, A₀.on a → C.on a)
    (hrel : ∀ a w, A₀.on a → C.relR a w → (S.grow s.N A₀ bk).relR a w) :
    (seamSent S s A₀ bk C).OK where
  isLocal := (sigSum_step E S s.N Kc St Wp Wp' E₀ A₀ bk).isLocal
  onOut := fun _ _ _ _ => trivial
  know := fun b x' w hb hx hw => by
    refine (sigSum_step E S s.N Kc St Wp Wp' E₀ A₀ bk).know b.1 b.2 x' w trivial hx ?_
    by_cases ho : A₀.on (x'.1, ((S.mergeE s.N E₀).map b.2).1)
    · rcases hw with hw | hn
      · exact Or.inl ⟨hw.1, hrel _ _ ho hw.2⟩
      · exact Or.inr fun h => hn ⟨h.1, hon _ ho⟩
    · exact Or.inr fun h => ho h.2

/-- The same renaming between joints with their conditions: from the joint over the family that was
sent, at the joint over S before the sending, to a joint over both. -/
@[reducible] def seamSentP (N : Sig E) (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
    (C : Rels Kc' St E₀ ((S.sum N).Msg × Wp')) :
    StepD (jOver N (N.pull (S.over A₀) (S.backN N bk))) (jOver (S.sum N) C) :=
  ⟨S.mergeX N St, S.mergeE N E₀, fun _ w => S.splitW N Wp' w⟩

/-- What it owes, from the same two premises. -/
theorem seamSentP_ok (N : Sig E) (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
    (C : Rels Kc' St E₀ ((S.sum N).Msg × Wp')) (hon : ∀ a, A₀.on a → C.on a)
    (hrel : ∀ a w, A₀.on a → C.relR a w → (S.grow N A₀ bk).relR a w) :
    (seamSentP S N A₀ bk C).OK where
  isLocal := (sigSum_step E S N Kc St Wp Wp' E₀ A₀ bk).isLocal
  onOut := fun b x' hb hx => by
    obtain rfl : (b.1.1.1, S.join N (T := OMsg.Smp) b.1.1.2 b.1.2) = x' := Option.some.inj hx
    refine ⟨fun a => ?_, hon _ hb.2.2⟩
    rcases a with a | a
    · exact hb.2.1 a
    · exact hb.1 a
  know := fun b x' w hb hx hw => by
    obtain rfl : (b.1.1.1, S.join N (T := OMsg.Smp) b.1.1.2 b.1.2) = x' := Option.some.inj hx
    exact ⟨fun a => hw.1 (.inr a), fun a => hw.1 (.inl a), hrel _ _ hb.2.2 hw.2⟩

/-- On the same types nothing is mapped. -/
@[reducible] def seamSame (J : JK) (on : J.X × J.E.Str → Prop)
    (relR : J.X × J.E.Str → J.W → Prop) : StepD J ⟨J.X, J.E, J.W, on, relR⟩ :=
  ⟨some, ExtMap.id _, fun _ w => w⟩

theorem seamSame_ok (J : JK) (on : J.X × J.E.Str → Prop) (relR : J.X × J.E.Str → J.W → Prop)
    (hon : ∀ b, J.on b → on b) (hrel : ∀ b w, J.on b → relR b w → J.relR b w) :
    (seamSame J on relR).OK where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  onOut := fun b x' hb hx => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hon _ hb
  know := fun b x' w hb hx hw => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hrel _ _ hb hw

end

/-- Who calls the draw behind a sending: the old oracle messages S, the sending, and the data of a
`TailCaller` whose signature is S with the family that was sent. Data alone. -/
structure SentCaller : Type 1 where
  /-- the oracle messages before the sending; the sending -/
  S   : Sig Cb.Gl.E
  snd : Cb.Pv.Send.Size Cb.Gl.E
  s   : Cb.Pv.Tail.Size
  X   : Type
  Ex  : ExtSpec
  Wp  : Type
  w   : X → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E
  sym : (S.sum snd.N).Msg → ∀ μ : Fin s.NM, Fin (Alg.symRows (s.m μ)) → Fin (s.k μ) → Cb.Gl.E
  tab : (S.sum snd.N).Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E
  dig : Wp → Cb.Pv.Tail.Dig Cb.Gl.E s
  ride : X × Ex.Str → (S.sum snd.N).Msg → Wp → Prop

/-- The caller of the draw. -/
@[reducible] def SentCaller.caller (d : SentCaller) : TailCaller :=
  ⟨d.s, d.S.sum d.snd.N, d.X, d.Ex, d.Wp, d.w, d.sym, d.tab, d.dig, d.ride⟩

/-- The caller of the sending before the draw: A₀ is the base joint before that sending; bk makes a
part of its witness from the sent messages. -/
@[reducible] def SentCaller.before (d : SentCaller) {Kc W₀ : Type}
    (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀)) (bk : d.snd.N.Msg → d.Wp → W₀) :
    SendCaller Cb.Gl.E :=
  ⟨d.snd, Kc, d.X × d.S.Smp, d.S.Wit × W₀, d.S.Wit × d.Wp, d.Ex.prod d.S.ext, d.S.over A₀,
    d.S.backN d.snd.N bk⟩

/-- The seam from a sending into the draw. -/
@[reducible] def seamToRng (d : SentCaller) {Kc W₀ : Type} (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀))
    (bk : d.snd.N.Msg → d.Wp → W₀) :
    StepD ((kSend [d.before A₀ bk]).dst (d.before A₀ bk)) (KTailRngCf.src d.caller) :=
  seamSent d.S d.snd A₀ bk (Cb.Pv.Tail.A d.caller.letters)

/-- What it owes, from one premise: under A₀'s condition the joint before the draw gives A₀'s
relaxed relation, a part of whose witness is read off the sent messages. -/
theorem seamToRng_ok (d : SentCaller) {Kc W₀ : Type} (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀))
    (bk : d.snd.N.Msg → d.Wp → W₀)
    (hrel : ∀ a w, A₀.on a → (Cb.Pv.Tail.A d.caller.letters).relR a w →
      (d.S.grow d.snd.N A₀ bk).relR a w) : (seamToRng d A₀ bk).OK :=
  seamSent_ok d.S d.snd A₀ bk _ (fun _ _ => trivial) hrel

/-- The seam into the draw between joints with their conditions, for a sending that ends at the
joint over its family. -/
@[reducible] noncomputable def seamToRngP (d : SentCaller) {Kc W₀ : Type}
    (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀)) (bk : d.snd.N.Msg → d.Wp → W₀) :
    StepD (jOver d.snd.N (d.snd.N.pull (d.S.over A₀) (d.S.backN d.snd.N bk)))
      (KTailRng.src d.caller) :=
  seamSentP d.S d.snd.N A₀ bk (Cb.Pv.Tail.A d.caller.letters)

theorem seamToRngP_ok (d : SentCaller) {Kc W₀ : Type} (A₀ : Rels Kc d.X d.Ex (d.S.Msg × W₀))
    (bk : d.snd.N.Msg → d.Wp → W₀)
    (hrel : ∀ a w, A₀.on a → (Cb.Pv.Tail.A d.caller.letters).relR a w →
      (d.S.grow d.snd.N A₀ bk).relR a w) : (seamToRngP d A₀ bk).OK :=
  seamSentP_ok d.S d.snd.N A₀ bk _ (fun _ _ => trivial) hrel

/-- The caller of the sending behind the draw, at the joint with its condition. -/
@[reducible] def sendBehindP (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) : SendCaller Cb.Gl.E :=
  ⟨snd, Unit, (c.X × Cb.Pv.Tail.Dr c.s) × c.Sg.Smp, c.Sg.Wit × c.Wp, W', c.Ex.prod c.Sg.ext,
    c.Sg.over (Cb.Pv.Tail.B c.letters), back⟩

/-- The seam from the draw to that sending: nothing is mapped. -/
@[reducible] noncomputable def seamFromRngP (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E)
    (W' : Type) (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) :
    StepD (KTailRng.dst c) ((kSend [sendBehindP c snd W' back]).src (sendBehindP c snd W' back)) :=
  ⟨some, ExtMap.id _, fun _ w => w⟩

theorem seamFromRngP_ok (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) : (seamFromRngP c snd W' back).OK where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  onOut := fun b x' hb hx => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hb
  know := fun b x' w _ hx hw => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hw

/-- The caller of the sending behind the draw: it starts at the joint at which the draw ends; back
makes the draw's further witness, the digits among it, from the sent messages. -/
@[reducible] def sendBehind (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) : SendCaller Cb.Gl.E :=
  ⟨snd, Unit, (c.X × Cb.Pv.Tail.Dr c.s) × c.Sg.Smp, c.Sg.Wit × c.Wp, W', c.Ex.prod c.Sg.ext,
    (c.Sg.over (Cb.Pv.Tail.B c.letters)).cf, back⟩

/-- The seam from the draw to the sending behind it: nothing is mapped. -/
@[reducible] noncomputable def seamFromRng (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E)
    (W' : Type) (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) :
    StepD (KTailRngCf.dst c) ((kSend [sendBehind c snd W' back]).src (sendBehind c snd W' back)) :=
  ⟨some, ExtMap.id _, fun _ w => w⟩

/-- It owes nothing further: the two joints are one. -/
theorem seamFromRng_ok (c : TailCaller) (snd : Cb.Pv.Send.Size Cb.Gl.E) (W' : Type)
    (back : snd.N.Msg → W' → c.Sg.Wit × c.Wp) : (seamFromRng c snd W' back).OK where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  onOut := fun _ _ _ _ => trivial
  know := fun b x' w _ hx hw => by
    obtain rfl : b.1 = x' := Option.some.inj hx
    exact hw

end KObj

#print axioms KObj.KTailRngCf_good
#print axioms KObj.jOver_eq
#print axioms KObj.seamSent_ok
#print axioms KObj.seamSame_ok
#print axioms KObj.seamToRng_ok
#print axioms KObj.seamFromRng_ok
#print axioms KObj.seamSentP_ok
#print axioms KObj.seamToRngP_ok
#print axioms KObj.seamFromRngP_ok
