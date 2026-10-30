-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailFive.lean: the smallness test's five places of a link of a written proof file as
one flat record: five callers, the four steps between them, five fixed witnesses.

A link of the first proof chain has nine blocks. The fourth to the eighth belong to the smallness
test: the sending of the reads; the draw of the matrix; the sending of the digits; the lookup on the
digits; the draw that batches the sub-proof's rows. A caller of a link is made of a caller of each
block, a step without rounds at each seam, and fixed witnesses (`KObj.SeqI`,
Johnson/E/KObj/KFamSeq.lean [not imported here]). This file has the five callers and four steps in
a form that is general in the kind of link, and says from which named premises every caller counts
and every step holds. The kinds at the seventh and the eighth place are letters κ7, κ8, with their
callers and the two steps beside them: they are other files' matter. Definitions, statements and
proofs.

Main names:
  `Five κ7 κ8`: the record. Data alone: who calls the draw behind a sending (`SentCaller`,
    Johnson/Top/H/TailSeams.lean); the condition `on` that is carried past the draw; the base joint
    A₀ before the first sending; the second sending; the callers c7, c8; the steps s6, s7; the
    fixed witnesses d4 .. d8.
  `Five.c4`, `c5`, `c6`: the callers of `kSendInto`, `KTailRngOn`, `kSendInto` that are made of it.
  `Five.s4`, `s5`: the steps into the draw and out of it (Johnson/Top/H/TailRngOnSeams.lean).
  `Five.src4`: the first joint is `jOver S A₀`.
  `Five.OK`: the named premises: the two sendings' conditions (`send₁`, `send₂`); the sizes'
    (`size`); the callers c7, c8 count (`look`, `led`); A₀'s condition gives `on` (`hon`); the joint
    before the draw gives A₀'s relaxed relation (`hrel`); the two steps that are letters hold
    (`o6`, `o7`).
  `Five.OK.m4` .. `m8`, `o4`, `o5`: from them every caller counts and every step holds.
  `fiveHost`, `fiveHost_ok`: the record at the letters of a sub-proof's frame
    (Johnson/Top/H/TailHostBase.lean), with A₀ := `Cb.Sub.virtJ B' a msg₁ n` and `on` := its
    condition: `hon` and `hrel` are paid there.

Limits: the steps s6 (from the second sending into the lookup on the digits) and s7 (from that
lookup to the batching draw) are letters, and so are the two kinds: that the condition `on` passes
them is what `o6`, `o7` and the caller c7 must say. No proof file is written here.
-/
import Johnson.Top.H.TailRngOnSeams

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.TailRow
open KObj Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles Cb.Sub Cb.Pv.Tail

/-- The caller of the second sending: it starts at the joint at which the draw ends, with the
condition; bk₂ makes the draw's further witness from the sent messages. -/
@[reducible] def sixth (d : SentCaller) (on : d.X × d.Ex.Str → Prop)
    (snd₂ : Cb.Pv.Send.Size Cb.Gl.E) {Wp₂ : Type} (bk₂ : snd₂.N.Msg → Wp₂ → d.Wp) :
    SendCaller Cb.Gl.E :=
  tailSendOver (d.S.sum d.snd.N) snd₂ (TailCallerOn.B ⟨d.caller, on⟩) bk₂

/-- The smallness test's five places of a link. Data alone. -/
structure Five (κ7 κ8 : KFam.{1}) : Type 1 where
  /-- who calls the draw behind the first sending; the condition that is carried -/
  d    : SentCaller
  on   : d.X × d.Ex.Str → Prop
  /-- the base joint before the first sending; how a part of its witness is read off what is sent -/
  Kc   : Type
  W₀   : Type
  A₀   : Rels Kc d.X d.Ex (d.S.Msg × W₀)
  bk   : d.snd.N.Msg → d.Wp → W₀
  /-- the second sending -/
  snd₂ : Cb.Pv.Send.Size Cb.Gl.E
  Wp₂  : Type
  bk₂  : snd₂.N.Msg → Wp₂ → d.Wp
  /-- the callers at the seventh and the eighth place, and the steps beside them -/
  c7   : κ7.ι
  c8   : κ8.ι
  s6   : StepD ((kSendInto [sixth d on snd₂ bk₂]).dst (sixth d on snd₂ bk₂)) (κ7.src c7)
  s7   : StepD (κ7.dst c7) (κ8.src c8)
  /-- the fixed witnesses -/
  d4   : d.S.Wit × W₀
  d5   : (d.S.sum d.snd.N).Wit × d.Wp
  d6   : (d.S.sum d.snd.N).Wit × d.Wp
  d7   : (κ7.src c7).W
  d8   : (κ8.src c8).W

namespace Five
variable {κ7 κ8 : KFam.{1}} (n : Five κ7 κ8)

/-- The caller of the first sending. -/
@[reducible] def c4 : SendCaller Cb.Gl.E := n.d.before n.A₀ n.bk

/-- The caller of the draw. -/
@[reducible] def c5 : TailCallerOn := ⟨n.d.caller, n.on⟩

/-- The caller of the second sending. -/
@[reducible] def c6 : SendCaller Cb.Gl.E := sixth n.d n.on n.snd₂ n.bk₂

/-- The step from the first sending into the draw. -/
@[reducible] noncomputable def s4 : StepD ((kSendInto [n.c4]).dst n.c4) (KTailRngOn.src n.c5) :=
  tailIntoRngOn n.d n.on n.A₀ n.bk

/-- The step from the draw to the second sending. -/
@[reducible] noncomputable def s5 : StepD (KTailRngOn.dst n.c5) ((kSendInto [n.c6]).src n.c6) :=
  tailFromRngOn n.c5 n.snd₂ ((n.d.S.sum n.d.snd.N).Wit × n.Wp₂)
    ((n.d.S.sum n.d.snd.N).backN n.snd₂.N n.bk₂)

/-- The first joint of the five places. -/
theorem src4 : (kSendInto [n.c4]).src n.c4 = jOver n.d.S n.A₀ := rfl

/-- The named premises. -/
structure OK : Prop where
  send₁ : n.d.snd.OK
  size  : n.d.s.OK
  send₂ : n.snd₂.OK
  look  : κ7.mem n.c7
  led   : κ8.mem n.c8
  hon   : ∀ a, n.A₀.on a → n.on a
  hrel  : ∀ a w, n.A₀.on a → (Cb.Pv.Tail.A n.d.caller.letters).relR a w →
    (n.d.S.grow n.d.snd.N n.A₀ n.bk).relR a w
  o6    : n.s6.OK
  o7    : n.s7.OK

variable {n}

theorem OK.m4 (h : n.OK) : SendOK [n.c4] := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact h.send₁

theorem OK.m5 (h : n.OK) : KTailRngOn.mem n.c5 := h.size

theorem OK.m6 (h : n.OK) : SendOK [n.c6] := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact h.send₂

theorem OK.m7 (h : n.OK) : κ7.mem n.c7 := h.look

theorem OK.m8 (h : n.OK) : κ8.mem n.c8 := h.led

theorem OK.o4 (h : n.OK) : n.s4.OK := tailIntoRngOn_ok n.d n.on n.A₀ n.bk h.hon h.hrel

theorem OK.o5 (_ : n.OK) : n.s5.OK := tailFromRngOn_ok _ _ _ _

end Five

section
variable {κ7 κ8 : KFam.{1}} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {s : Size}
  {K Xe Wp Wp₁ : Type} {Ex : ExtSpec}
  (S₁ : Sig Cb.Gl.E) (snd : Cb.Pv.Send.Size Cb.Gl.E) (bk₁ : snd.N.Msg → Wp₁ → Wp)
  (Br B' : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → Cb.Gl.E)
  (ent : snd.N.Msg → J₂ → Cb.Gl.E)
  (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E)
  (sym : S₁.Msg → Syms Cb.Gl.E s)
  (tab : snd.N.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E)
  (dig : Wp₁ → Dig Cb.Gl.E s) (a : Xe → J₂ → Aff Cb.Gl.E J₁) (n : ℕ)

/-- The record at the letters of a sub-proof's frame: Br rides; in front of the first sending stands
B' with the ledger pulled back; its condition is carried. -/
@[reducible] def fiveHost (snd₂ : Cb.Pv.Send.Size Cb.Gl.E) {Wp₂ : Type}
    (bk₂ : snd₂.N.Msg → Wp₂ → Wp₁) (c7 : κ7.ι) (c8 : κ8.ι)
    (s6 : StepD ((kSendInto [sixth (tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig)
        (virtJ B' a msg₁ n).on snd₂ bk₂]).dst
      (sixth (tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig) (virtJ B' a msg₁ n).on snd₂ bk₂))
      (κ7.src c7))
    (s7 : StepD (κ7.dst c7) (κ8.src c8)) (d4 : S₁.Wit × Wp) (d5 d6 : (S₁.sum snd.N).Wit × Wp₁)
    (d7 : (κ7.src c7).W) (d8 : (κ8.src c8).W) : Five κ7 κ8 :=
  ⟨tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig, (virtJ B' a msg₁ n).on, K, Wp,
    virtJ B' a msg₁ n, bk₁, snd₂, Wp₂, bk₂, c7, c8, s6, s7, d4, d5, d6, d7, d8⟩

/-- Its premises: `hon` by definition, `hrel` from the frame's laws. -/
theorem fiveHost_ok (snd₂ : Cb.Pv.Send.Size Cb.Gl.E) {Wp₂ : Type} (bk₂ : snd₂.N.Msg → Wp₂ → Wp₁)
    (c7 : κ7.ι) (c8 : κ8.ι)
    (s6 : StepD ((kSendInto [sixth (tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig)
        (virtJ B' a msg₁ n).on snd₂ bk₂]).dst
      (sixth (tailSentOf S₁ snd bk₁ Br msg₁ ent w sym tab dig) (virtJ B' a msg₁ n).on snd₂ bk₂))
      (κ7.src c7))
    (s7 : StepD (κ7.dst c7) (κ8.src c8)) (d4 : S₁.Wit × Wp) (d5 d6 : (S₁.sum snd.N).Wit × Wp₁)
    (d7 : (κ7.src c7).W) (d8 : (κ8.src c8).W)
    (h1 : snd.OK) (hs : s.OK) (h2 : snd₂.OK) (h7 : κ7.mem c7) (h8 : κ8.mem c8)
    (hB : ∀ b v, Base (sym v.1) → Br.relR b v → B'.relR b v) (p : ℕ) [CharP Cb.Gl.E p]
    (hu : s.Uniq p) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hc : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (ha : ∀ (x : (tailHost S₁ snd bk₁ Br msg₁ ent w sym tab dig).let.X) j v,
      (a x.1 j).val v =
        (affRead (tailHost S₁ snd bk₁ Br msg₁ ent w sym tab dig).let x (it j)).val
          fun i => v (ic i))
    (ht : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2) (o6 : s6.OK) (o7 : s7.OK) :
    (fiveHost S₁ snd bk₁ Br B' msg₁ ent w sym tab dig a n snd₂ bk₂ c7 c8 s6 s7 d4 d5 d6 d7
      d8).OK :=
  ⟨h1, hs, h2, h7, h8, fun _ h => h,
    tailHost_hrel_base S₁ snd bk₁ Br B' msg₁ ent w sym tab dig hB p hu a ic it hc ha ht n, o6, o7⟩

end

end KObj.TailRow

#print axioms KObj.TailRow.Five.src4
#print axioms KObj.TailRow.Five.OK.m4
#print axioms KObj.TailRow.Five.OK.m6
#print axioms KObj.TailRow.Five.OK.o4
#print axioms KObj.TailRow.Five.OK.o5
#print axioms KObj.TailRow.fiveHost_ok
