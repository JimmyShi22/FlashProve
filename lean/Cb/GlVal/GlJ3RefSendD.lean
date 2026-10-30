-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3RefSendD.lean: a small test instance of one step of a
request's part of the protocol:
after any earlier steps the prover sends several Reed-Solomon codewords as oracles at once, the
verifier draws their seeds, and the prover answers with linear samples of the encoded messages. What
a list of protocol steps asks of such a step is proved for it, under the hypotheses named below.

Definitions, theorems. Building stone for toys; a guard against empty theorems; no parameter of a
protocol.
Cb/GlVal/GlJ3RefLay.lean has the data `Y : LayD I W` and the sender `Y.snd` of the family `datSig I`
(Cb/GlVal/GlJ3RefKit.lean). Here the family is sent after any stage a: it is added to the oracle
messages that are open.
A stage (`LdStage`, Cb/Req1/LdSegKit.lean) is the data of a point between two steps of the protocol.
A move (`LdMv`, Cb/Req1/LdSeg.lean) is one step from stage to stage. `LdSendD`
(Cb/Req1/LdSegKit.lean) is a sending's data and `LdSendD.Hyp` what is asked of it. `LdMv.After` is
defined in Cb/Req1/LdReq.lean.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `datSig` and `datAt`, Cb/GlVal/GlJ3RefKit.lean, with the data, the
layout (`lay`), the datum's entry (`dEnt`), sender and facts of `LayD`, Cb/GlVal/GlJ3RefLay.lean,
its member `toyS` with its facts, Cb/GlVal/GlJ3Send.lean, `nu`, Cb/GlVal/GlToySend.lean, and `LJ3`,
Cb/GlVal/GlJ3Base.lean; the stage a is a parameter): the fields are F, the integers modulo
p = 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is that of
Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).
The names of codes, messages and their facts: Cb/GlVal/GlJ3Send.lean, Cb/GlVal/GlJ3StdNames.lean,
Cb/GlVal/GlJ3PackNames.lean.

Main names (namespace `Cb.GlJ3.LayD`):
  `sendD`: the data of the move: the sending of a family with one datum a member, the masks of
    several coming blocks being coins, as a move of a preamble; its hypotheses, and the facts that
    are fresh after it: the three rows below.
  `sendD_hyp`: for a block `b`, under `h`: see its statement (`LdSendD.Hyp`).
  `sendD_after_ent`: under `hi`, `hr`, `hown`, `hoff`: see its statement.
  `sendD_after_wide`: under `ho`, `hv`: see its statement (`LdStage.wideFact`,
    Cb/Req1/LdSegCarry.lean).

Limits: a fact of the form in `sendD_after_wide` cannot cross a closing whose group holds new
members (their pads and randomness are forgotten). This file says nothing on real parameters. The
bounds that the toys write (one hidden position) are kept, though this code hides 3 (said of
`sendD`).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlJ3RefLay
import Cb.Req1.LdSegSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LayD
variable {Kc : Type} (a : LdStage E Kc) {I : Type} [Fintype I] [DecidableEq I]
  (Y : LayD I (a.S.Wit × a.Wp)) (Wp' : Type) (bk : (datSig I).Msg → Wp' → a.Wp)
  (rest : a.S.Wit × a.Wp → a.S.Wit × Wp') (w0 : a.S.Wit × a.Wp)

/-- The data of the move. -/
@[reducible] def sendD : LdSendD a :=
  ⟨datSig I, Sig.Seeds.indep (datSig I), Wp', bk, Y.snd rest w0, fun _ => LJ3, fun _ => 1⟩

/-- All that a move "send" asks (`LdSendD.Hyp`), given a block `b` and, by `h`, that
`a.S.backN (datSig I) bk` gives w back from `rest w` and any messages of the family whose data are
`Y.datum w ms`. -/
theorem sendD_hyp (b : Y.Bk)
    (h : ∀ w ms (m : (datSig I).Msg),
      (∀ i, datAt m i = Y.datum w ms i) → a.S.backN (datSig I) bk m (rest w) = w) :
    (Y.sendD a Wp' bk rest w0).Hyp := by
  have hT := ld_toy Bool
  exact
  { laws := fun _ => hT.1
    fair := (ldSendFam_fair_indep E (datSig I)).1
    list := fun _ => sig_list_of_code E toyS LJ3 hT.2.2.2.1
    evades := fun _ => toyS_evades
    sender := Y.lay_laws rest w0 _ h
    blind := Y.lay_blind rest w0 _ b
    hides := Y.lay_hides rest w0 }

/-- Fresh after the move: a block that reads entries. -/
theorem sendD_after_ent (base : MaskFact a.J.W → Prop) (b : Y.Bk) {J : Type}
    (g : (datSig I).Msg → a.S.Wit × Wp' → J → E) (Rd : J → Prop) (at' : Y.Ib b → J)
    (hi : Function.Injective at') (hr : ∀ x, Rd (at' x))
    (hown : ∀ m w' x, g m w' (at' x) = datAt m (Y.pl b x))
    (hoff : ∀ m m' w' j, (∀ i, (∀ x, Y.pl b x ≠ i) → datAt m i = datAt m' i) → Rd j →
      (∀ x, j ≠ at' x) → g m w' j = g m' w' j) :
    (LdMv.send a (Y.sendD a Wp' bk rest w0)).After base
      ⟨J → E, fun v =>
          cutTo Rd (g ((datSig I).msgs (a.S.right (datSig I) (T := OMsg.Wit) v.1))
              (a.S.left (datSig I) (T := OMsg.Wit) v.1, v.2)),
        Y.Mk b,
        fun M k => Function.extend at' (Y.ve b M) k⟩ := by
  have h2 := ldSendSig_fresh_wide E a.S (datSig I) (Sig.Seeds.indep (datSig I)) a.St a.Wp Wp' a.E₀
    (Y.snd rest w0) (fun _ => 1) a.J.rels.rel (Y.Mk b) ((Y.lay rest w0).own b) _ _ _
    (Y.lay_laws_ent rest w0 _ b g Rd at' hi hr hown hoff) (Y.lay_hides rest w0)
  refine segCarry_send_new a (Y.sendD a Wp' bk rest w0) base _ ?_
  exact h2

open Classical in
/-- Fresh after the move: the wide fact. -/
theorem sendD_after_wide (base : MaskFact a.J.W → Prop) (b : Y.Bk) (RdOld : a.S.Ent → Prop)
    (RrOld : a.S.O → Prop) (own : (datSig I).Ent → Prop) (val : Y.Mk b → (datSig I).Ent → E)
    (ho : ∀ n, own n ↔ ∃ x, n = dEnt (Y.pl b x))
    (hv : ∀ M x, val M (dEnt (Y.pl b x)) = Y.ve b M x) :
    (LdMv.send a (Y.sendD a Wp' bk rest w0)).After base
      ((Y.sendD a Wp' bk rest w0).tgt.wideFact
        (a.S.sumP (datSig I) RdOld fun n => n.2 = nu.symm (Sum.inl ()))
        (a.S.sumO (datSig I) RrOld fun _ => False) (a.S.sumP (datSig I) (fun _ => False) own)
        (Y.Mk b) fun M => a.S.sumV (datSig I) (fun _ => 0) (val M)) := by
  have hinj : Function.Injective fun x => dEnt (Y.pl b x) := fun x x' e =>
    Y.inj b (congrArg Sigma.fst e)
  have h1 := own_laws_keep E (datSig I) _ _ (Y.snd rest w0) (Y.Mk b) ((Y.lay rest w0).own b)
    (Sig.Seeds.indep (datSig I)) _ _ _
    (Y.lay_laws_ent rest w0 _ b (fun m _ => (datSig I).ents m) (fun n => n.2 = nu.symm (Sum.inl ()))
      (fun x => dEnt (Y.pl b x)) hinj (fun _ => rfl) (fun _ _ _ => rfl)
      fun m m' _ j h hj hne => by
        obtain ⟨i, j2⟩ := j
        have hj' : j2 = nu.symm (Sum.inl ()) := hj
        subst hj'
        exact h i fun x e => hne x (by rw [← e]; rfl))
  have h2 := ldSendSig_fresh_wide E a.S (datSig I) (Sig.Seeds.indep (datSig I))
    a.St a.Wp Wp' a.E₀ (Y.snd rest w0) (fun _ => 1) a.J.rels.rel (Y.Mk b)
    ((Y.lay rest w0).own b) _ _ _ h1 (Y.lay_hides rest w0)
  refine segCarry_send_new a (Y.sendD a Wp' bk rest w0) base _ ?_
  have h3 := fresh_conseq _ _ _ _ _ _ _
    (ldSendSigHon (Sig.Seeds.indep (datSig I)) a.St a.E₀ (Y.snd rest w0))
    a.J.rels.rel a.J.rels.rel _ _ _ _ _
    (fun k : ((datSig I).Ent → E) × (a.S.Wit × Wp') =>
      ((a.S.join (datSig I) (T := OMsg.Msg) (a.S.cut RdOld (a.S.msgs k.2.1))
        (fun i j => k.1 ⟨i, j⟩) : (a.S.sum (datSig I)).Msg),
        ((a.S.join (datSig I) (T := fun o => Option o.Rnd)
            (fun o => if RrOld o then some (k.2.1 o).2 else none) (fun _ => none) :
            ∀ o, Option ((a.S.sum (datSig I)).om o).Rnd),
          k.2.2)))
    (Y.Mk b) _
    (fun M k =>
      ((a.S.sum (datSig I)).ow (a.S.sumP (datSig I) (fun _ => False) own)
          (a.S.sumV (datSig I) (fun _ => 0) (val M)) k.1,
        k.2))
    (fun _ _ _ h => h) (fun _ _ h => h) (fun M k => by
      refine Prod.ext (funext fun o => ?_) rfl
      rcases o with o | i
      · funext j
        exact (if_neg fun h : False => h).symm
      · funext j
        show Function.extend (fun x => dEnt (Y.pl b x)) (Y.ve b M) k.1 ⟨i, j⟩ =
          if own ⟨i, j⟩ then val M ⟨i, j⟩ else k.1 ⟨i, j⟩
        by_cases hw : own ⟨i, j⟩
        · obtain ⟨x, e⟩ := (ho _).1 hw
          rw [if_pos hw, e, hinj.extend_apply, hv]
        · rw [if_neg hw, Function.extend_apply' _ _ _ fun ⟨x, e⟩ => hw ((ho _).2 ⟨x, e.symm⟩)]) h2
  refine Eq.mp
    (congrArg (fun kc =>
        (ldSendSigHon (Sig.Seeds.indep (datSig I)) a.St a.E₀ (Y.snd rest w0)).Fresh
          a.J.rels.rel _ kc (Y.Mk b) _)
      (funext fun v => ?_)) h3
  refine Prod.ext (funext fun o => ?_) (Prod.ext (funext fun o => ?_) rfl)
  · rcases o with o | i <;> rfl
  · rcases o with o | i
    · rfl
    · exact (if_neg fun h : False => h).symm

end LayD
end Cb.GlJ3
