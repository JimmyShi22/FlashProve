-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestWhole.lean: from "the decision of the kind K5 says yes on a view" and
"what K5 claims holds" back to "the lookup's in-joint, and the identities at1, at2 and at3 at every
valid index": the kind's own text, the chain of the own rounds and the lookup, end to end at one
value of the chain's letters.

Statements and proofs. Two laws are laid end to end. `K05_cap` and `K05_row`
(Johnson/Desc/First/Att/K05Cap.lean, Johnson/Desc/First/Att/K05Row.lean): a yes of `decide` gives,
at the closed parameters made of the plan, typed data made of what was heard; the chain's verifier
on the joined transcript puts out the chain's run; the chain's `Last` on that run holds exactly if
the kind's bill is paid. `guest_link` (Johnson/Desc/First/Att/K05GuestLink.lean): `KnowAt` over (the
lookup, then the chain) from (`forIn` and `Three`) to (`forOut` and `Last`). The base joint that
rides through the chain is a letter A0, a joint on the lookup's output statements.
Main names:
  `Good c P A0 Dn m a τ`: what the clause know of such a `KnowAt` says of one full transcript τ:
    every output of a on τ at which A0 (at the first statement) and `Last Dn` hold for (m, wp) has
    `forIn` at a and `Three P m`.
  `good_doomed`: (I) the count: for every m and every statement a with the lookup's condition,
    `Doomed` at the shape of (the lookup, then the chain), at the lookup's errors followed by the
    chain's, with `Good` at the end: from any `KnowAt` over the two whose base joint is A0.
  `whole_doomed`, `closed_doomed`: the same at A0 := `forOut`, from `guest_link`.
  `seq_out_app`, `whole_core`, `whole_step`: on a transcript of the lookup with output (x0, y),
    followed by a joined transcript of the chain: `Good`, A0 at (x0, y) and `Last` on the run give
    `forIn` at a and `Three`.
  `WholeCapSays`, `whole_of_cap`: (II) for any letters P over the lookup's types of which `CapSays`
    holds: `Good`, A0 and the kind's bill (Dn, `UnitsBill`, `TailBill` in the ledger's world) give
    `forIn` and `Three`.
  `WholeRowSays`, `whole_of_row`: the same from `RowSays`: in the bill's place stand i.g = geoOf S,
    `PointsAre`, `SayAt` (every form that the runs "first" and "second" gather is worth 0 in the
    world of the message's own mask: so by `say_at`, under its own premises), Dn, the letters'
    linear claims (`UnitsLin`, `TailLin`), `UnitsMeans` and five `EndsMean`. The second clause of
    `RowSays`, on the letter owF, is carried as it stands.
  `LinReads`, `zcRead_closed`, `linReads_met`: at the closed parameters `ZCRead` is a property of
    the letter Λ.LE; the reading itself, as Λ.LE, has it and accepts some scalars at every message.
  `whole_cap`, `whole_row`: (I) and (II) from a yes of `decide`, at A0 := `forOut` and closedOf P0 Λ
    F.ns (numsPlan p.own F.next), at every later ledger.
The bodies of `WholeCapSays` and `WholeRowSays` are the texts of `CapSays` and `RowSays` with the
last clause replaced: where these have "`Last` on the run holds exactly if RHS", those have "for
every statement and transcript of the lookup with output (x0, y): `Good`, A0 and RHS give `forIn`
and `Three`".
Premises: `FoNums.ok c.h`; `AttFits c.h P0.D P0.C`; P0.zOf is the lookup's pt; `LinReads`, at a slot
that lies in the ledger; P0.D.lT ≤ 16; those of `K05_cap` and `K05_row`.
Used beside the two laws: `IOR.red_seq_out`, `Tr.fst_app`, `Tr.snd_app`,
`Ch.out_back`, `Cb.Rider.red_out`, `Doomed`, `msg_slot`; no routine in a context.
Limits: (I) and (II) say nothing apart: the left side of (II) can hold with `Three` false at
transcripts that are not `Good`, and (I) counts these. (II) speaks of every transcript of the typed
lookup with output (x0, y): for the own rounds `K05_cap` makes the typed data of what a view holds;
for the lookup it is not shown in this file or in what it imports that the rounds of a view are such
a transcript, so (I) counts challenges of a typed protocol whose first half is tied to no view. c,
P0 and Λ are free letters; no value is given. In `whole_cap` and `whole_row` the lookup's out-joint
`forOut` at (x0, y) stands on the left side as a premise. The parameters hang on F.ns and F.next,
two numbers of the ledger in front of the kind's hearing, while (I) wants them fixed before the
lookup's first round: that no challenge turns these two numbers is not shown in this file or in what
it imports. All of m is fixed before the lookup's first round. R0 and Dn have to be without at3
(Johnson/Desc/First/Att/K05GuestLink.lean). That some view has a yes of `decide` with the left side
of (II) true is not shown. The three laws of the part "the masked sumcheck" on which `K05_cap` rests
are those of Johnson/Desc/Part/MaskedSumTie.lean. Nothing ties these statements to a verifier on
bytes. Nothing on an honest prover, completeness or hiding.

-/
import Cb.Pv.Att.ChainBack
import Johnson.Desc.First.Att.K05Row
import Johnson.Desc.First.Att.K05GuestLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf ownTrs)
open VerifiableInference.OnPublicFiles (LookupCCaller)
open VerifiableInference.Desc.Part
open K5Law (SayAt PointsAre unitReader endsE endsV endsK endsH oldOf sum3Back)

/-- The composed verifier's output on two transcripts in a row. -/
theorem seq_out_app {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (a : X₁ × E₁.Str) (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) (b : X₂ × E₂.Str) (e : X₃ × E₃.Str)
    (h1 : R₁.red.out a τ₁ = some b) (h2 : R₂.red.out b τ₂ = some e) :
    (R₁.seq R₂).red.out a (Tr.app τ₁ τ₂) = some e := by
  rw [IOR.red_seq_out]
  show (R₁.red.out a (Tr.fst (Tr.app τ₁ τ₂))).bind
    (fun b => R₂.red.out b (Tr.snd (s := R₁.shape) (Tr.app τ₁ τ₂))) = some e
  rw [Tr.fst_app, Tr.snd_app, h1]
  exact h2

/-- The step of (II), at letters: a block R₁, then any chain. -/
theorem whole_core {E M X X₁ Wp : Type} [Field E] [Fintype E] {Ex : ExtSpec} (R₁ : IOR X₁ Ex X Ex) (ch : Ch E M X)
    (relOut : X × Ex.Str → M × Wp → Prop) (relIn : X₁ × Ex.Str → M × Wp → Prop) (Dn : X → M → Prop) (m : M)
    (a : X₁ × Ex.Str) (τ₁ : Tr R₁.shape) (ts : ch.Trs) (x0 : X) (y : Ex.Str) (wp : Wp)
    (h1 : R₁.red.out a τ₁ = some (x0, y))
    (h2 : (ch.R Ex).red.out (x0, y) (ch.join Ex ts) = some (ch.run x0 ts, y)) :
    (R₁.seq (ch.R Ex)).red.out a (Tr.app τ₁ (ch.join Ex ts)) = some (ch.run x0 ts, y) ∧
    ((∀ (b : ch.End × Ex.Str) (wp : Wp), (R₁.seq (ch.R Ex)).red.out a (Tr.app τ₁ (ch.join Ex ts)) = some b →
        (relOut (ch.back b.1, b.2) (m, wp) ∧ ch.Last Dn b.1 m) → relIn a (m, wp)) →
      relOut (x0, y) (m, wp) → ch.Last Dn (ch.run x0 ts) m → relIn a (m, wp)) := by
  have ho := seq_out_app R₁ (ch.R Ex) a τ₁ (ch.join Ex ts) (x0, y) _ h1 h2
  refine ⟨ho, fun hG hF hL => hG _ wp ho ⟨?_, hL⟩⟩
  have hb : ch.back (ch.run x0 ts) = x0 := Ch.out_back Ex ch x0 y _ _ (red_out h2)
  show relOut (ch.back (ch.run x0 ts), y) (m, wp)
  rw [hb]
  exact hF

section Whole
variable (c : LookupCCaller)
  (P : OwnPar Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)))
  (A0 : Rels c.Kc (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) c.Ex (c.Sg.Msg × c.Wp))

/-- The letters of the own rounds at P. -/
noncomputable abbrev ownA : Cb.Pv.Att.AttOwn Cb.Gl.E c.Sg.Msg (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :=
  P.own (theMeans Cb.Gl.E P.D P.C P.kap)

/-- The host, then the own rounds. -/
noncomputable abbrev hostThen : IOR c.St₀ c.Ex (ownA c P).ch.End c.Ex :=
  (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.seq ((ownA c P).ch.R c.Ex)

/-- What knowledge soundness says of one full transcript. -/
def Good (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
    (a : c.St₀ × c.Ex.Str) (τ : Tr (hostThen c P).shape) : Prop :=
  ∀ (b : (ownA c P).ch.End × c.Ex.Str) (wp : c.Wp), (hostThen c P).red.out a τ = some b →
    (A0.relR ((ownA c P).ch.back b.1, b.2) (m, wp) ∧
      (ownA c P).ch.Last Dn b.1 m) →
    (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a (m, wp) ∧ Three P m

/-- **(I) The count**, from any statement of knowledge soundness over (host, then chain) whose base
joint is A0. -/
theorem good_doomed (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop)
    (hl : KnowAt (hostThen c P) (withRider (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) fun m _ => Three P m)
      (jt A0 (fun e => id ((ownA c P).ch.back e)) ((ownA c P).ch.Last Dn)) (fun _ _ _ wp => wp)
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e ((ownA c P).ch.eps c.Ex)))
    (m : c.Sg.Msg) (a : c.St₀ × c.Ex.Str) (ha : (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a) :
    Doomed (hostThen c P).shape
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e ((ownA c P).ch.eps c.Ex))
      (Good c P A0 Dn m a) :=
  hl.know m a ha

/-- **(I) The count**, at the host's own out-joint. -/
theorem whole_doomed (ok : FoNums.ok c.h = true) (F : AttFits c.h P.D P.C) (hz : ∀ b, P.zOf b = b.2.1.pt)
    (hZ : ZCRead P) (hk : P.D.lT ≤ 2 ^ P.kap)
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
    (a : c.St₀ × c.Ex.Str) (ha : (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a) :
    Doomed (hostThen c P).shape
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e ((ownA c P).ch.eps c.Ex))
      (Good c P (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Dn m a) :=
  good_doomed c P _ Dn (guest_link c P ok F hz hZ hk Dn) m a ha

/-- **The step of (II)**: on the host's transcript followed by any joined transcript of the chain.
-/
theorem whole_step (ts : (ownA c P).ch.Trs) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (a : c.St₀ × c.Ex.Str) (τ₁ : Tr (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.shape) (y : c.Ex.Str)
    (h1 : (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out a τ₁ = some (x0, y))
    (h2 : ((ownA c P).ch.R c.Ex).red.out (x0, y) ((ownA c P).ch.join c.Ex ts) =
      some ((ownA c P).ch.run x0 ts, y))
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg) (wp : c.Wp)
    (hG : Good c P A0 Dn m a (Tr.app τ₁ ((ownA c P).ch.join c.Ex ts)))
    (hF : A0.relR (x0, y) (m, wp))
    (hL : (ownA c P).ch.Last Dn ((ownA c P).ch.run x0 ts) m) :
    (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a (m, wp) ∧ Three P m :=
  (whole_core (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R (ownA c P).ch
    A0.relR
    (fun a w => (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a w ∧ Three P w.1) Dn m a τ₁ ts x0 y wp h1 h2).2
    hG hF hL

/-- What (II) says, with the kind's bill on the left. The text is that of `CapSays`
(Johnson/Desc/First/Att/K05Cap.lean) with its last clause replaced: where that has "the chain's Last
on the run holds exactly if RHS", this has "for every statement and transcript of the host with
output (x0, y): Good, forOut and RHS give forIn and Three". -/
def WholeCapSays (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (IsLeft : Left → Prop) (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop) : Prop :=
  ∃ L : Lists, RoundsAre L.rounds rs ∧ Said x h G L ∧ Sized G ∧ Stays F G ∧
    ∀ (ρ : Reading Cb.Gl.E) (nz : BetasNz ρ L) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)), Pts ρ x0 →
      ∃ (du : UnitsH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units)
        (dt : TailH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail),
        (UnitsOfP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
          TailOfP dt x h L ∧
          UnitsVals (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du
            (unitsAdd (ρ := ρ) (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
              (x0, [])) ∧
          TailVals dt (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
          dt = tailData (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
        (UnitsAreP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du h.scores.toList ∧ TailIsP dt x h L) ∧
        (UnitsClaims (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) ∧
          dt.Claims (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
        (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.R Ex).red.out (x0, y)
          ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt)) =
          some ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt), y)) ∧
        ∀ (l : Left), IsLeft l → ∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop)
          (m : c.Sg.Msg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E),
          (∀ (a : c.St₀ × c.Ex.Str) (τ₁ : Tr (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.shape) (y : c.Ex.Str)
            (wp : c.Wp), (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out a τ₁ = some (x0, y) →
          Good c P A0 Dn m a (Tr.app τ₁ ((ownA c P).ch.join c.Ex (ownTrs (ownA c P) du dt))) →
          A0.relR (x0, y) (m, wp) →
          (Dn x0 m ∧
              UnitsBill (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) l.scores.toList
                (G.worldOf ρ (maskOf m) entry) m ∧
              TailBill dt (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, [])) l
                (G.worldOf ρ (maskOf m) entry) m) →
          (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a (m, wp) ∧ Three P m)

/-- **(II) with the bill**, for any letters of which `CapSays` holds. -/
theorem whole_of_cap (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (IsLeft : Left → Prop)
    (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop)
    (H : CapSays P maskOf x F G rs h IsLeft Pts) : WholeCapSays c P A0 maskOf x F G rs h IsLeft Pts := by
  obtain ⟨L, a1, a2, a3, a4, a5⟩ := H
  refine ⟨L, a1, a2, a3, a4, fun ρ nz x0 hp => ?_⟩
  obtain ⟨du, dt, b1, b2, b3, b4, b5⟩ := a5 ρ nz x0 hp
  exact ⟨du, dt, b1, b2, b3, b4, fun l hl Dn m entry a τ₁ y wp h1 hG hF hB =>
    whole_step c P A0 _ x0 a τ₁ y h1 (b4 c.Ex y) Dn m wp hG hF ((b5 l hl Dn m entry).2 hB)⟩

/-- What (II) says, with what the batching later tests on the left. The text is that of `RowSays`
(Johnson/Desc/First/Att/K05Row.lean) with its last clause replaced in the same way. -/
def WholeRowSays (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (S : Attention.Shape) (zk : Array (Array E))
    (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop) : Prop :=
  ∃ L : Lists, RoundsAre L.rounds rs ∧ Said x h G L ∧ Sized G ∧ Stays F G ∧
    ∀ (ρ : Reading Cb.Gl.E) (nz : BetasNz ρ L) (x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)), Pts ρ x0 →
      ∃ (du : UnitsH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units)
        (dt : TailH ρ (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail),
        (UnitsOfP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
          TailOfP dt x h L ∧
          UnitsVals (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du
            (unitsAdd (ρ := ρ) (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
              (x0, [])) ∧
          TailVals dt (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
          UnitsAreP (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du h.scores.toList ∧ TailIsP dt x h L) ∧
        (UnitsClaims (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) ∧
          dt.Claims (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))) ∧
        (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.R Ex).red.out (x0, y)
          ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt)) =
          some ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans Cb.Gl.E P.D P.C P.kap)) du dt), y)) ∧
        ∀ (l : Left), leftP (geoOf S) zk h G = some l →
        ∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop)
          (m : c.Sg.Msg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ),
          i.g = geoOf S → PointsAre i.g zk h l i.p → SayAt ρ (G.worldOf ρ (maskOf m) entry) S gL i Kc →
          (∀ (a : c.St₀ × c.Ex.Str) (τ₁ : Tr (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.shape) (y : c.Ex.Str)
            (wp : c.Wp), (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out a τ₁ = some (x0, y) →
          Good c P A0 Dn m a (Tr.app τ₁ ((ownA c P).ch.join c.Ex (ownTrs (ownA c P) du dt))) →
          A0.relR (x0, y) (m, wp) →
          (Dn x0 m ∧
              (UnitsLin (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []) m ∧
                UnitsMeans (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du
                  (unitsAdd (ρ := ρ) (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten
                    L.units (x0, [])) 0 (unitReader S gL i Kc) (G.worldOf ρ (maskOf m) entry) m) ∧
              (TailLin dt (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, [])) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sE dt.dE
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aE
                  (endsE (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sVM dt.dVM
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aM
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sVD dt.dVD
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aVD
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sD dt.dD
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aD
                  (endsK (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail.sH dt.dH
                  (tailAdd (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, []))).aH
                  (endsH (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m)) →
          (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a (m, wp) ∧ Three P m) ∧
          ((P.tail (theMeans Cb.Gl.E P.D P.C P.kap)).toTail.owF
              (dt.dF.nx (dt.x6 (seenAfter (P.own (theMeans Cb.Gl.E P.D P.C P.kap)).units du (x0, [])))) m ↔
            ∀ b : Fin P.D.nb, P.sF.T.map dt.dF.st (P.msg m) (b, false)
              (ldPartIni P.sF.T.nv P.sF.T.deg (pDummy Cb.Gl.E P.sF.T.DY) dt.dF.out.pt) =
                (_root_.Fo.readHeadT (oldOf S gL i) Kc i.t.qF S.atQ ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S)
                  (b.1 / S.HA) (b.1 % S.HA)).value ρ (G.worldOf ρ (maskOf m) entry))

/-- **(II) with the join behind it**, for any letters of which `RowSays` holds. -/
theorem whole_of_row (maskOf : c.Sg.Msg → ℕ → Cb.Gl.E) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (S : Attention.Shape) (zk : Array (Array E))
    (Pts : Reading Cb.Gl.E → TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Prop)
    (H : RowSays P maskOf x F G rs h S zk Pts) : WholeRowSays c P A0 maskOf x F G rs h S zk Pts := by
  obtain ⟨L, a1, a2, a3, a4, a5⟩ := H
  refine ⟨L, a1, a2, a3, a4, fun ρ nz x0 hp => ?_⟩
  obtain ⟨du, dt, b1, b3, b4, b5⟩ := a5 ρ nz x0 hp
  exact ⟨du, dt, b1, b3, b4, fun l hl Dn m entry gL i Kc hg hP hS =>
    ⟨fun a τ₁ y wp h1 hG hF hB =>
      whole_step c P A0 _ x0 a τ₁ y h1 (b4 c.Ex y) Dn m wp hG hF ((b5 l hl Dn m entry gL i Kc hg hP hS).1.2 hB),
      (b5 l hl Dn m entry gL i Kc hg hP hS).2⟩⟩

end Whole

section Closed
variable {K M0 X Mg : Type} [Field K] [Fintype K]

/-- **The letter Λ.LE holds ZC's reading**, at the slot five + 2 of the numbers N. -/
def LinReads (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (N : Nums) : Prop :=
  ∀ (s : Seen K X) (r : Fin (5 + P0.D.lT + 2) → K) (m : Mg), Λ.LE s r m →
    r P0.iZC - Λ.maskOf m (N.five + 2) =
      AttSeg.rv P0.D P0.C (pubOfZ K (P0.zOf s.1)) (P0.tOf (Λ.restOf m)) .zc

theorem zcRead_closed (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (hs : N.five + 2 ≤ ns)
    (h : LinReads P0 Λ N) : ZCRead (closedOf P0 Λ ns N) := by
  intro s r m hLE
  have e : (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kE (closedOf P0 Λ ns N).iZC) =
      Λ.maskOf m (N.five + 2) := msg_slot P0 Λ ns N m hs
  rw [e]
  exact h s r m hLE

/-- Not hollow: the reading itself, as Λ.LE, meets LinReads and accepts some scalars at every
message. -/
theorem linReads_met (P0 : OwnPar K M0 X) (maskOf : Mg → ℕ → K) (restOf : Mg → M0)
    (LM : Seen K X → (Fin (3 * P0.npl + 7) → K) → Mg → Prop) (LD : Seen K X → (Fin 7 → K) → Mg → Prop)
    (N : Nums) :
    LinReads P0 (⟨maskOf, restOf, LM, LD, fun s r m => r P0.iZC - maskOf m (N.five + 2) =
      AttSeg.rv P0.D P0.C (pubOfZ K (P0.zOf s.1)) (P0.tOf (restOf m)) .zc⟩ : Lin P0 Mg) N ∧
    ∀ (s : Seen K X) (m : Mg), ∃ r : Fin (5 + P0.D.lT + 2) → K, r P0.iZC - maskOf m (N.five + 2) =
      AttSeg.rv P0.D P0.C (pubOfZ K (P0.zOf s.1)) (P0.tOf (restOf m)) .zc :=
  ⟨fun _ _ _ h => h, fun s m => ⟨fun _ => AttSeg.rv P0.D P0.C (pubOfZ K (P0.zOf s.1)) (P0.tOf (restOf m)) .zc +
    maskOf m (N.five + 2), add_sub_cancel_right _ _⟩⟩

end Closed

section Cap
variable (c : LookupCCaller) {M0 : Type}
  (P0 : OwnPar Cb.Gl.E M0 (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (Λ : Lin P0 c.Sg.Msg)

/-- (I) at the closed parameters. -/
theorem closed_doomed (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) (hk4 : P0.kap = 4) (ns : ℕ) (N : Nums) (hΛ : LinReads P0 Λ N) (hs : N.five + 2 ≤ ns)
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
    (a : c.St₀ × c.Ex.Str) (ha : (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a) :
    Doomed (hostThen c (closedOf P0 Λ ns N)).shape
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e ((ownA c (closedOf P0 Λ ns N)).ch.eps c.Ex))
      (Good c (closedOf P0 Λ ns N) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Dn m a) :=
  whole_doomed c (closedOf P0 Λ ns N) ok F0 hz (zcRead_closed P0 Λ ns N hs hΛ) (by
    show P0.D.lT ≤ 2 ^ P0.kap
    rw [hk4]
    omega) Dn m a ha

/-- **Both halves, from a yes of `decide`: the kind's bill on the left.** -/
theorem whole_cap (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) {St : Type} (seat : Seat St) (p : Par) (s s' : St) (rs : List Fmt.RoundView)
    (hd : decide seat p s rs = .ok s') (hzS : ∀ F, seat.ledger s = some F → Sized F)
    (hΛ : ∀ F, seat.ledger s = some F →
      LinReads P0 Λ (numsPlan p.own F.next) ∧ (numsPlan p.own F.next).five + 2 ≤ F.ns)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2])
    (hb1 : u1.below = true) (hb2 : u2.below = false) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      (∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
        (a : c.St₀ × c.Ex.Str), (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a →
        Doomed (hostThen c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).shape
          (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
            ((ownA c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).ch.eps c.Ex))
          (Good c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Dn m a)) ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        WholeCapSays c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Λ.maskOf
          p.own F G' rs h
          (fun l => leftP (geoOf S) zk h G' = some l) (LookAll P0 S zk u1 u2) := by
  obtain ⟨F, G, h, a1, a2, ah, a3⟩ :=
    K05_cap P0 Λ seat p s s' rs hd hzS hk4 rows hrec S hDS Z hlt hNP hgs hb1 hb2 zk
  exact ⟨F, G, h, a1, a2,
    fun Dn m a ha => closed_doomed c P0 Λ ok F0 hz hT hk4 _ _ (hΛ F a1).1 (hΛ F a1).2 Dn m a ha, ah,
    fun G' q1 q2 q3 => whole_of_cap c _ _ _ _ F G' rs h _ _ (a3 G' q1 q2 q3)⟩

/-- **Both halves, from a yes of `decide`: what the batching later tests on the left** (SayAt: by
say_at, under its own premises: every form that "first" and "second" gather is worth 0 in the world
of the message's own mask ∧ the letters' linear claims ∧ what the end values' readers mean). -/
theorem whole_row (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) {St : Type} (seat : Seat St) (p : Par) (s s' : St) (rs : List Fmt.RoundView)
    (hd : decide seat p s rs = .ok s') (hzS : ∀ F, seat.ledger s = some F → Sized F)
    (hΛ : ∀ F, seat.ledger s = some F →
      LinReads P0 Λ (numsPlan p.own F.next) ∧ (numsPlan p.own F.next).five + 2 ≤ F.ns)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) (hNP2 : S.NP = P0.D.nb) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      (∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
        (a : c.St₀ × c.Ex.Str), (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a →
        Doomed (hostThen c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).shape
          (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
            ((ownA c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).ch.eps c.Ex))
          (Good c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Dn m a)) ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        WholeRowSays c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) Λ.maskOf
          p.own F G' rs h S zk
          (LookAll P0 S zk u1 u2) := by
  obtain ⟨F, G, h, a1, a2, ah, a3⟩ :=
    K05_row P0 Λ seat p s s' rs hd hzS hk4 rows hrec S hDS Z hlt hNP hNP2 hgs hb1 hb2 zk
  exact ⟨F, G, h, a1, a2,
    fun Dn m a ha => closed_doomed c P0 Λ ok F0 hz hT hk4 _ _ (hΛ F a1).1 (hΛ F a1).2 Dn m a ha, ah,
    fun G' q1 q2 q3 => whole_of_row c _ _ _ _ F G' rs h S zk _ (a3 G' q1 q2 q3)⟩

end Cap

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seq_out_app
#print axioms VerifiableInference.Desc.First.Att.P.good_doomed
#print axioms VerifiableInference.Desc.First.Att.P.whole_doomed
#print axioms VerifiableInference.Desc.First.Att.P.whole_of_cap
#print axioms VerifiableInference.Desc.First.Att.P.zcRead_closed
#print axioms VerifiableInference.Desc.First.Att.P.linReads_met
#print axioms VerifiableInference.Desc.First.Att.P.whole_cap
#print axioms VerifiableInference.Desc.First.Att.P.whole_of_row
#print axioms VerifiableInference.Desc.First.Att.P.whole_row
#print axioms VerifiableInference.Desc.First.Att.P.whole_step
