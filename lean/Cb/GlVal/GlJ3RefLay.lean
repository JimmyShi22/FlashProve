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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3RefLay.lean: a small test instance of a sending of several
oracles at once: the family of Cb/GlVal/GlJ3RefKit.lean (one word of two Reed-Solomon rows for each
name: a datum and a pad) with a second honest sender, and the facts on that sender that other test
files cite.

A family with one datum a member, some of whose data are coins: the masks of several coming blocks;
under the hypotheses of the statements below, its sending is fresh for every block.
Definitions, theorems. Building stone for toys; a guard against empty theorems; no parameter of a
protocol.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `datSig`, `datAt`, `datMem` with `datMem_uniform`, and `datSnd`,
Cb/GlVal/GlJ3RefKit.lean, `toyS` and `ld_toy`, Cb/GlVal/GlJ3Send.lean, and `nu`,
Cb/GlVal/GlToySend.lean; the set I of names, the witnesses W and the seeds Sd are parameters): the
fields are F, the integers modulo p = 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Main names (namespace `Cb.GlJ3.LayD`):
  `lay_laws`, `lay_hides`, `lay_blind`, `lay_pad`, `lay_unif`: see their statements
    (`Sig.Sender.Laws`, `Sig.Sender.Blind`, `Sig.budT`, Cb/Ld/LdSendFam.lean; `Enc.Hides`,
    Cb/Gen/Code.lean; `PadLaw`, Cb/Ld/LdSendFreshMany.lean). In `lay_hides`, `Hides` is the
    conclusion; in `lay_blind`, `Blind` is. `N.Hides bud` (`Enc.Hides`) asks that, for every set S
    of positions with `bud S` and all messages m and m', the distribution of `N.shows S m r` over
    uniform r in `N.Rnd` equal that of `N.shows S m' r`; `N.shows S m r` gives the symbols of
    `N.enc m r` at the positions of S. `D.Blind Sd` (`Sig.Sender.Blind`) asks that, for every joint
    seed s and all witnesses w and w', the distribution of `D.ans Sd s w k` over uniform k in `D.Mk`
    equal that of `D.ans Sd s w' k`; `D.ans Sd s w k` gives the family, over the members a, of the
    answers `(N.om a).Z.val (Sd.sd a s)` of `D.upM (D.put w k) a`, and the distribution is of that
    whole family. For one oracle message o, `D.Blind` (`OMsg.Sender.Blind`) asks the same with a
    seed ρ of `o.Z` in place of s: that, for every ρ and all w and w', the distribution of
    `D.ans ρ w k` over uniform k in `D.Mk` equal that of `D.ans ρ w' k`, where `D.ans ρ w k` is
    `o.Z.val ρ (D.upM (D.put w k))`. (`OMsg.Sender.Blind`: Cb/Ld/LdSend.lean)
  `lay_fresh_ent`: under `hi`, `hr`, `hown`, `hoff`: see its statement. `lay_fresh_wide`: under
    `ho`, `hv`: see its statement. Both also under the laws in `Y : LayD I W` (`inj`: each `pl b` is
    injective; `apart`: different blocks apart; `neMk`: each `Mk b` is not empty) and `ne` in
    `Sd : (datSig I).Seeds` (the type D of joint seeds is not empty). In both, `Fresh` of the
    sending's honest side (`ldSendFamHon`, Cb/Ld/LdSendFam.lean) is the conclusion.
    `H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and
    every T with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its
    third part is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`,
    `Honest.seen`, Ior/KnowCollRulesMask.lean)

Limits: the bound that the toys write (one hidden position) is kept, though this code hides 3:
`lay_hides`, `lay_fresh_ent` and `lay_fresh_wide` stand at `budT fun _ => 1`. This file says nothing
on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlJ3RefKit
import Cb.Ld.LdSendFreshManyProofs
import Cb.Req1.LdSegCarry
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data. -/
structure LayD (I W : Type) [Fintype I] [DecidableEq I] : Type 1 where
  Bk : Type
  [finBk : Fintype Bk]
  [decBk : DecidableEq Bk]
  Mk : Bk → Type
  [finMk : ∀ b, Fintype (Mk b)]
  [neMk : ∀ b, Nonempty (Mk b)]
  Ib : Bk → Type
  pl : ∀ b, Ib b → I
  ve : ∀ b, Mk b ≃ (Ib b → E)
  val : W → I → E
  inj : ∀ b, Function.Injective (pl b)
  apart : ∀ b b' x x', pl b x = pl b' x' → b = b'

attribute [instance] LayD.finBk LayD.decBk LayD.finMk LayD.neMk

namespace LayD
variable {I W W' : Type} [Fintype I] [DecidableEq I] (Y : LayD I W)

open Classical in
/-- The data of all members. -/
def datum (w : W) (ms : ∀ b, Y.Mk b) (i : I) : E :=
  if h : ∃ b x, Y.pl b x = i then Y.ve h.choose (ms h.choose) h.choose_spec.choose else Y.val w i

theorem datum_own (w : W) (ms : ∀ b, Y.Mk b) (b : Y.Bk) (x : Y.Ib b) :
    Y.datum w ms (Y.pl b x) = Y.ve b (ms b) x := by
  have h : ∃ b' x', Y.pl b' x' = Y.pl b x := ⟨b, x, rfl⟩
  unfold datum
  rw [dif_pos h]
  have hb : h.choose = b := Y.apart _ _ _ _ h.choose_spec.choose_spec
  have key : ∀ (b' : Y.Bk) (x' : Y.Ib b'),
      b' = b → Y.pl b' x' = Y.pl b x → Y.ve b' (ms b') x' = Y.ve b (ms b) x := by
    rintro b' x' rfl e
    rw [Y.inj _ e]
  exact key _ _ hb h.choose_spec.choose_spec

theorem datum_off (w : W) (ms : ∀ b, Y.Mk b) (i : I) (h : ∀ b x, Y.pl b x ≠ i) :
    Y.datum w ms i = Y.val w i := by
  unfold datum
  rw [dif_neg fun ⟨b, x, e⟩ => h b x e]

/-- A datum off the places of b does not read the masks of b (`ho`, `h`). -/
theorem datum_oth (w : W) (ms ms' : ∀ b, Y.Mk b) (b : Y.Bk) (ho : ∀ j, j ≠ b → ms j = ms' j)
    (i : I) (h : ∀ x, Y.pl b x ≠ i) :
    Y.datum w ms i = Y.datum w ms' i := by
  by_cases hh : ∃ b' x', Y.pl b' x' = i
  · obtain ⟨b', x', rfl⟩ := hh
    rw [datum_own, datum_own, ho b' fun e => by subst e; exact h x' rfl]
  · rw [datum_off _ _ _ _ fun b' x' e => hh ⟨b', x', e⟩,
      datum_off _ _ _ _ fun b' x' e => hh ⟨b', x', e⟩]

/-- The sender. -/
@[reducible] def snd (rest : W → W') (w0 : W) : (datSig I).Sender W W' where
  Nn := (datSnd (I := I) (W' := W') Y.val rest w0).Nn
  upM := fun m => m
  upR := fun r => r
  Mk := ((∀ b, Y.Mk b) × Unit) × (I → E)
  put := fun w k a j => Sum.elim (fun _ => Y.datum w k.1.1 a) (fun _ => k.2 a) (nu j)
  rest := rest
  w0 := w0

/-- The layout: the identity. -/
@[reducible] def lay (rest : W → W') (w0 : W) : (Y.snd rest w0).Layout where
  Bk := Y.Bk
  Mk := Y.Mk
  F0 := Unit
  Pd := I → E
  κ := Equiv.refl _

variable (rest : W → W') (w0 : W)

theorem datAt_snd (w : W) (k : (Y.snd rest w0).Mk) (i : I) :
    datAt ((Y.snd rest w0).upM ((Y.snd rest w0).put w k)) i = Y.datum w k.1.1 i := by
  show Sum.elim (fun _ => Y.datum w k.1.1 i) (fun _ => k.2 i) (nu (nu.symm (Sum.inl ()))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The answers, written out. -/
theorem lay_ans (Sd : (datSig I).Seeds) (s : Sd.D) (w : W) (ms : ∀ b, Y.Mk b) (η : I → E) :
    (Y.snd rest w0).ans Sd s w ((Y.lay rest w0).mk' ms () η) =
      fun a =>
        toyS.Z.val (Sd.sd a s) fun j => Sum.elim (fun _ => Y.datum w ms a) (fun _ => η a) (nu j) :=
  rfl

/-- All answers together are uniform over the pads alone. -/
theorem lay_unif (Sd : (datSig I).Seeds) (s : Sd.D) (w : W) (ms : ∀ b, Y.Mk b) :
    (unif (I → E)).map (fun η => (Y.snd rest w0).ans Sd s w ((Y.lay rest w0).mk' ms () η)) =
      unif (datSig I).Answ := by
  have h := ldSendMem_uniform E (datSig I) Unit Unit (fun a => datMem (fun _ => Y.datum w ms a) ())
    (fun _ => ()) () Sd (fun a => datMem_uniform _ _) s ()
  simp only [lay_ans]
  convert h

theorem lay_pad (Sd : (datSig I).Seeds) : (Y.lay rest w0).PadLaw Sd := fun s w w' ms ms' _ _ =>
  (Y.lay_unif rest w0 Sd s w ms).trans (Y.lay_unif rest w0 Sd s w' ms').symm

theorem lay_hides : (Y.snd rest w0).Nn.Hides ((datSig I).budT fun _ => 1) :=
  ldSendMem_hides E (datSig I) _ _ _ rest w0 _ fun _ => (ld_toy Bool).2.2.2.2.2.2.1

theorem lay_laws (back : (datSig I).Msg → W' → W)
    (h : ∀ w ms (m : (datSig I).Msg), (∀ i, datAt m i = Y.datum w ms i) → back m (rest w) = w) :
    (Y.snd rest w0).Laws back :=
  ⟨fun _ _ _ => rfl, fun w k => h w k.1.1 _ fun i => Y.datAt_snd rest w0 w k i⟩

variable (Sd : (datSig I).Seeds) (X : Type) (E₀ : ExtSpec) (Ri : X → E₀.Str → W → Prop)

/-- The conditions of Cb/Ld/LdSendFresh.lean for a block that reads entries. (not all hypotheses are
named here: see the statement below) -/
theorem lay_laws_ent (b : Y.Bk) {J : Type} (g : (datSig I).Msg → W' → J → E) (Rd : J → Prop)
    (at' : Y.Ib b → J) (hi : Function.Injective at') (hr : ∀ x, Rd (at' x))
    (hown : ∀ m w' x, g m w' (at' x) = datAt m (Y.pl b x))
    (hoff : ∀ m m' w' j, (∀ i, (∀ x, Y.pl b x ≠ i) → datAt m i = datAt m' i) → Rd j →
      (∀ x, j ≠ at' x) → g m w' j = g m' w' j) :
    ((Y.lay rest w0).own b).Laws Sd (fun m w' => cutTo Rd (g m w')) fun M k =>
      Function.extend at' (Y.ve b M) k :=
  layout_laws_entries E (datSig I) W W' (Y.snd rest w0) (Y.lay rest w0) Sd b J (Y.Ib b) g Rd at'
    (fun M => Y.ve b M) (Y.lay_pad rest w0 Sd) hi hr
    (fun w ms f η x =>
      (hown _ _ x).trans
        ((Y.datAt_snd rest w0 w ((Y.lay rest w0).mk' ms f η) _).trans (Y.datum_own w ms b x)))
    fun w ms ms' f η η' j ho hj hne =>
      hoff _ _ _ j
        (fun i hi' =>
          (Y.datAt_snd rest w0 w ((Y.lay rest w0).mk' ms f η) i).trans
            ((Y.datum_oth w ms ms' b (fun j' hj' => congrFun ho ⟨j', hj'⟩) i hi').trans
              (Y.datAt_snd rest w0 w ((Y.lay rest w0).mk' ms' f η') i).symm))
        hj hne

/-- Fresh, for a block that reads entries. (not all hypotheses are named here: see the statement
below) -/
theorem lay_fresh_ent (b : Y.Bk) {J : Type} (g : (datSig I).Msg → W' → J → E) (Rd : J → Prop)
    (at' : Y.Ib b → J) (hi : Function.Injective at') (hr : ∀ x, Rd (at' x))
    (hown : ∀ m w' x, g m w' (at' x) = datAt m (Y.pl b x))
    (hoff : ∀ m m' w' j, (∀ i, (∀ x, Y.pl b x ≠ i) → datAt m i = datAt m' i) → Rd j →
      (∀ x, j ≠ at' x) → g m w' j = g m' w' j) :
    (ldSendFamHon Sd X E₀ (Y.snd rest w0)).Fresh Ri
      (fun _ T => (datSig I).budT (fun _ => 1) (ldSendFamSet (datSig I) Sd T))
      (fun v => cutTo Rd (g ((datSig I).msgs v.1) v.2)) (Y.Mk b)
      fun M k => Function.extend at' (Y.ve b M) k :=
  layout_fresh E (datSig I) Sd X W W' E₀ (Y.snd rest w0) (fun _ => 1) Ri (Y.lay rest w0)
    (Y.lay_hides rest w0) b _ _ _ (Y.lay_laws_ent rest w0 Sd b g Rd at' hi hr hown hoff)

/-- The law of the answers does not depend on the witness (b: any block). -/
theorem lay_blind (b : Y.Bk) : (Y.snd rest w0).Blind Sd :=
  own_blind E (datSig I) W W' (Y.snd rest w0) (Y.Mk b) ((Y.lay rest w0).own b) Sd _ _ _
    (Y.lay_laws_ent rest w0 Sd b (fun m _ i => datAt m i) (fun _ => True) (Y.pl b) (Y.inj b)
      (fun _ => trivial) (fun _ _ _ => rfl) fun _ _ _ j h _ hne => h j fun x e => hne x e.symm)

/-- The datum's entry of a member. -/
def dEnt (i : I) : (datSig I).Ent := ⟨i, nu.symm (Sum.inl ())⟩

open Classical in
/-- Fresh, for the wide fact (Cb/Req1/LdSegCarry.lean): of every member its datum is read, never its
pad, never its encoding randomness; the whole further witness. (not all hypotheses are named here:
see the statement below) -/
theorem lay_fresh_wide (b : Y.Bk) (own : (datSig I).Ent → Prop) (val : Y.Mk b → (datSig I).Ent → E)
    (ho : ∀ n, own n ↔ ∃ x, n = dEnt (Y.pl b x))
    (hv : ∀ M x, val M (dEnt (Y.pl b x)) = Y.ve b M x) :
    (ldSendFamHon Sd X E₀ (Y.snd rest w0)).Fresh Ri
      (fun _ T => (datSig I).budT (fun _ => 1) (ldSendFamSet (datSig I) Sd T))
      ((datSig I).wide W' (fun n => n.2 = nu.symm (Sum.inl ())) fun _ => False) (Y.Mk b)
      fun M k => ((datSig I).ow own (val M) k.1, k.2) := by
  have hinj : Function.Injective fun x => dEnt (Y.pl b x) := fun x x' e =>
    Y.inj b (congrArg Sigma.fst e)
  have h1 := own_laws_keep E (datSig I) W W' (Y.snd rest w0) (Y.Mk b)
    ((Y.lay rest w0).own b) Sd _ _ _
    (Y.lay_laws_ent rest w0 Sd b (fun m _ => (datSig I).ents m)
      (fun n => n.2 = nu.symm (Sum.inl ())) (fun x => dEnt (Y.pl b x)) hinj
      (fun _ => rfl) (fun _ _ _ => rfl)
      fun m m' _ j h hj hne => by
        obtain ⟨i, j2⟩ := j
        have hj' : j2 = nu.symm (Sum.inl ()) := hj
        subst hj'
        exact h i fun x e => hne x (by rw [← e]; rfl))
  have h2 := layout_fresh E (datSig I) Sd X W W' E₀ (Y.snd rest w0) (fun _ => 1) Ri (Y.lay rest w0)
    (Y.lay_hides rest w0) b _ _ _ h1
  have h3 := fresh_conseq _ _ _ _ _ _ _ (ldSendFamHon Sd X E₀ (Y.snd rest w0)) Ri Ri _ _ _ _ _
    (fun k : ((datSig I).Ent → E) × W' =>
      ((fun a j => k.1 ⟨a, j⟩ : (datSig I).Msg),
        ((fun _ => none : ∀ o, Option ((datSig I).om o).Rnd), k.2)))
    (Y.Mk b) _
    (fun M k => ((datSig I).ow own (val M) k.1, k.2))
    (fun _ _ _ h => h) (fun _ _ h => h) (fun M k => by
      refine Prod.ext (funext fun a => funext fun j => ?_) rfl
      show Function.extend (fun x => dEnt (Y.pl b x)) (Y.ve b M) k.1 ⟨a, j⟩ =
        if own ⟨a, j⟩ then val M ⟨a, j⟩ else k.1 ⟨a, j⟩
      by_cases hw : own ⟨a, j⟩
      · obtain ⟨x, e⟩ := (ho _).1 hw
        rw [if_pos hw, e, hinj.extend_apply, hv]
      · rw [if_neg hw, Function.extend_apply' _ _ _ fun ⟨x, e⟩ => hw ((ho _).2 ⟨x, e.symm⟩)]) h2
  refine Eq.mp
    (congrArg (fun kc => (ldSendFamHon Sd X E₀ (Y.snd rest w0)).Fresh Ri _ kc (Y.Mk b) _)
      (funext fun v => ?_)) h3
  refine Prod.ext rfl (Prod.ext (funext fun o => ?_) rfl)
  exact (if_neg fun h : False => h).symm

end LayD
end Cb.GlJ3
