-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/KeyAlone.lean: WHEN A SHARED BLOCK's ERROR IS PAID ONCE FOR ALL SLOTS. A plain
  law for ONE statement (`Leads`) of a block that reads the statement through its ACTING PART alone
  IS A LAW WITH A KEY (`LeadsK`: one game for all the statements with one acting part: in
  `LeadsBN`'s letters εO = 0).

Why. By an exact test over a full-size plan's written prices (a run, interpreted, kept off this
  library; no theorem; its print says "38 of 68") more than half of the rounds
  of a proof file's shared chain would not bear their whole price once for each of 64 slots: a rule
  that paid them once for each slot would find no room there. Their errors must be paid once for all
  slots.
THIS FILE SAYS THAT "εO = 0" IS OWED BY NOBODY BESIDE A BLOCK's LAW FOR ONE STATEMENT: it follows,
  in general, from how a description lays a shared block.
WHAT IT GIVES ARE THE FIRST AND THE THIRD OF THE THREE CLAUSES THAT `EachLeadsBN` (BothAtDesc.lean)
  ASKS OF A BLOCK: `LeadsBN`, and `KeyLaw` at the acting parts (`keyLaw_of_lift`, from the same
  `liftHands`; an outside reader's sketch). NOT the second: the condition is handed on.

  `leadsK_of_hands` (any reduction): if whether K says yes, and the key behind, are a function G of
    the key in front and the transcript, then a `Leads` whose relation reads the two statements
    through their keys is a `LeadsK` at the same errors. The condition in front is free: each slot
    may have its own: OF ONE BLOCK: along a chain the next block's condition comes from the second
    clause (see `step_of_lift`).
  `keyLaw_of_hands`: under the same G the key behind is a function of the key in front and the
    transcript (`KeyLaw`, Moves.lean). d: any map of keys, read where K says no.
  `leadsK_of_handsAct`, `keyLaw_of_handsAct`: at a piece, from `Piece.HandsAct`.
  `leadsK_of_lift`: BY MAKE: a block typed at the chain's own part of the record and lifted
    (`Block.lift`: so a description lays every block of its shared chain: `OfDesc.b₂`), whose rounds
    open no tree with a number below lo (the chain's first own tree): at the acting part that is
    meant (`actAt`: the chain's own part of the record; the stored table; the chain's own trees so
    far). By the proved `liftHands`. `keyLaw_of_lift`: the law of keys at these acting parts.
  `LeadsK.beside_sure`, `LeadsBN.beside_sure`: what each slot has of its own rides beside, for
    certain, and is in no key.
  `leadsBN_of_lift`: the same as the first clause that `EachLeadsBN` asks, at every N.
  `LeadsBN.mono_err`: at every greater list of errors. `LeadsBN.conseq`, `LeadsBN.beside_map`: items
    that ride beside a law for a batch, where the world in front is e a b w.
  `step_of_lift`: the form of the law of one block of the shared chain, for every block but the one
    at which the shared point is drawn (there εO is not 0): the shared items by the acting parts
    (one statement's plain law), the slots' own items riding for certain ⟹ `LeadsBN` of both
    together, εO = 0. OF b OUTRIGHT ITS RELATION SAYS on'₀ OF b's ACTING PART AND Q' a b: a letter:
    what holds of the two statements for certain at every yes (hs): so along a chain the next
    block's condition can hold something of a slot's own part.
WHAT IS STILL OWED for such a block: ITS PLAIN LAW FOR ONE STATEMENT, WITH A RELATION THAT SPEAKS OF
  THE ACTING PARTS ALONE (Q₀); and the second clause.
Controls (`KeyAloneToy`; both reductions say yes to all): `reads_a_slot`: a reduction whose OUTPUT
  hangs on the slot's own part: it has `Leads` at the error 1 of 3 and NOT `LeadsK` at the trivial
  key at that error: so the half of the premise on G that speaks of the key behind cannot be
  dropped; the half "whether K says yes" has no control. `no_law_at_yes`: at a reduction that always
  puts out the bad thing, the law (and so the lemma's premise) fails.
NEAREST KIN. The knowledge form's twin: `LostOfGoodIn` (`GoodIn` for one statement + `ReadsBy` ⟹
  `LostBy`), `LiftHands`, `LostBeside` (Johnson/Desc/Sound/SharedRule.lean; proved in
  SharedRuleProofs.lean, SharedOwnProofs.lean). Here: its plain form: no witness; e₀ in `step_of_lift`
  is a named map of worlds, not an extractor that is run. `keyLaw_lift` (LiftBelow.lean) carries a
  law of keys from a block's own part to the lifted piece: it asks one; `keyLaw_of_lift` makes one.
Limits: those of Leads.lean and Keyed.lean. That a real kind's relation reads the acting parts alone
  is shown of no kind here. The one member (KeyAloneMember.lean [not in this library; so here read: not proved in this library]) has lo = 0, no tree, no table, and
  trivial worlds: it exercises neither `actAt`'s third part nor ho.

-/
import Johnson.Desc.Plain.Both
import Johnson.Desc.Sound.SharedOwnProofs
import Ior.Draw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
namespace Reduction
variable {A B κ κ' : Type}

/-- **A reduction that reads the statement through its key alone: one statement's law is the law
with a key.** -/
theorem leadsK_of_hands (K : Reduction A B) (key : A → κ) (key' : B → κ')
    (G : κ → Tr K.shape → Option κ') (hG : ∀ a τ, (K.out a τ).map key' = G (key a) τ)
    (on : A → Prop) (Q₀ : κ → κ' → Prop) (ε : Err K.shape)
    (h : K.Leads on (fun a b => Q₀ (key a) (key' b)) ε) :
    K.LeadsK key on (fun a b => Q₀ (key a) (key' b)) ε := by
  intro k
  by_cases hx : ∃ a₀, key a₀ = k ∧ on a₀
  · obtain ⟨a₀, rfl, h₀⟩ := hx
    refine Doomed.mono _ _ ?_ (h a₀ h₀)
    intro τ hτ a hk _ b hb
    have e : (K.out a₀ τ).map key' = some (key' b) := by
      rw [hG a₀ τ, ← hk, ← hG a τ, hb]
      rfl
    obtain ⟨b₀, hb₀, e₀⟩ := Option.map_eq_some_iff.1 e
    rw [hk, ← e₀]
    exact hτ b₀ hb₀
  · exact Doomed.of_forall _ _ fun _ a hk ha => absurd ⟨a, hk, ha⟩ hx

/-- **Under the same G the law of keys holds.** d is read where K says no. -/
theorem keyLaw_of_hands (K : Reduction A B) (key : A → κ) (key' : B → κ')
    (G : κ → Tr K.shape → Option κ') (hG : ∀ a τ, (K.out a τ).map key' = G (key a) τ)
    (d : κ → κ') : K.KeyLaw key key' :=
  ⟨fun k τ => (G k τ).getD (d k), fun a τ b hb => by
    show key' b = (G (key a) τ).getD (d (key a))
    rw [← hG a τ, hb]
    rfl⟩

/-- What each slot has of its own rides beside, for certain. -/
theorem LeadsK.beside_sure {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop}
    {ε : Err K.shape} (h : K.LeadsK key on Q ε) (Q' : A → B → Prop)
    (hs : ∀ a τ b, on a → K.out a τ = some b → Q' a b) :
    K.LeadsK key on (fun a b => Q a b ∧ Q' a b) ε :=
  h.conseq (fun _ h => h) fun a τ b ha hb hq => ⟨hq, hs a τ b ha hb⟩

/-- A law for a batch in two parts: a stronger condition in front, a weaker relation. -/
theorem LeadsBN.conseq {K : Reduction A B} {key : A → κ} {on on' : A → Prop} {Q Q' : A → B → Prop}
    {N : ℕ} {ε : Err K.shape} (h : K.LeadsBN key on Q N ε) (ho : ∀ a, on' a → on a)
    (hQ : ∀ a τ b, on' a → K.out a τ = some b → Q a b → Q' a b) : K.LeadsBN key on' Q' N ε := by
  obtain ⟨εK, εO, hle, lK, lO, dK, dO, q⟩ := h
  exact ⟨εK, εO, hle, lK, lO, dK, fun a ha => dO a (ho a ha), fun a τ b ha hk hO hb =>
    hQ a τ b ha hb (q a τ b (ho a ha) hk hO hb)⟩

/-- What each slot has of its own rides beside a law for a batch, for certain. -/
theorem LeadsBN.beside_sure {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop}
    {N : ℕ} {ε : Err K.shape} (h : K.LeadsBN key on Q N ε) (Q' : A → B → Prop)
    (hs : ∀ a τ b, on a → K.out a τ = some b → Q' a b) :
    K.LeadsBN key on (fun a b => Q a b ∧ Q' a b) N ε :=
  h.conseq (fun _ h => h) fun a τ b ha hb hq => ⟨hq, hs a τ b ha hb⟩

/-- A law for a batch in two parts holds at every greater list of errors. -/
theorem LeadsBN.mono_err {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop}
    {N : ℕ} {ε ε' : Err K.shape} (h : K.LeadsBN key on Q N ε) (hε : Err.le ε ε') :
    K.LeadsBN key on Q N ε' := by
  obtain ⟨εK, εO, hle, rest⟩ := h
  exact ⟨εK, εO, Err.le_trans hle hε, rest⟩

/-- **Items that only ride beside a law for a batch**, where the world in front is e a b w (the
named extractor may read both statements): at the block's own errors and split.
Rc | Rc': what rides: it may read what each slot has of its own, and is in no key; hc is handed the
law's own items behind, as in
`KeepsW.beside`. -/
theorem LeadsBN.beside_map {W : Type} {K : Reduction A B} {key : A → κ} {on : A → Prop}
    {on' : B → Prop} {R : A → W → Prop} {R' : B → W → Prop} {e : A → B → W → W} {N : ℕ}
    {ε : Err K.shape}
    (h : K.LeadsBN key on (fun a b => on' b ∧ ∀ w, R' b w → R a (e a b w)) N ε)
    (Rc : A → W → Prop) (Rc' : B → W → Prop)
    (hc : ∀ a τ b w, on a → K.out a τ = some b → on' b → R' b w → Rc' b w → Rc a (e a b w)) :
    K.LeadsBN key on
      (fun a b => on' b ∧ ∀ w, R' b w ∧ Rc' b w → R a (e a b w) ∧ Rc a (e a b w)) N ε :=
  h.conseq (fun _ h => h) fun a τ b ha hb hq =>
    ⟨hq.1, fun w hw => ⟨hq.2 w hw.1, hc a τ b w ha hb hq.1 hw.1 hw.2⟩⟩

end Reduction
end Iop

noncomputable section

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S S₀ Cl W : Type} {C : CK} {F : Frame}

theorem leadsK_of_handsAct (p : Piece C F S Cl W) (act act' : BKey F S) (hh : p.HandsAct act act')
    (on : S × F.E.Str → Prop) (Q₀ : act.1 → act'.1 → Prop)
    (h : p.ior.red.Leads on (fun a b => Q₀ (act.2 a) (act'.2 b)) p.err) :
    p.ior.red.LeadsK act.2 on (fun a b => Q₀ (act.2 a) (act'.2 b)) p.err := by
  obtain ⟨G, hG⟩ := hh
  exact Reduction.leadsK_of_hands p.ior.red act.2 act'.2 G hG on Q₀ p.err h

theorem keyLaw_of_handsAct (p : Piece C F S Cl W) (act act' : BKey F S) (hh : p.HandsAct act act')
    (d : act.1 → act'.1) : p.ior.red.KeyLaw act.2 act'.2 := by
  obtain ⟨G, hG⟩ := hh
  exact Reduction.keyLaw_of_hands p.ior.red act.2 act'.2 G hG d

/-- **By make: a lifted block that opens no tree of an earlier chain is key-alone.** -/
theorem leadsK_of_lift (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl) (p : Piece C F S Cl W)
    (lo : ℕ) (hb : p.b = b₀.lift get set) (h1 : ∀ t s, get (set t s) = s)
    (h2 : ∀ t s s', set (set t s) s' = set t s') (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j)
    (on : S × F.E.Str → Prop)
    (Q₀ : (actAt F get lo p.base).1 → (actAt F get lo (p.base + p.trees)).1 → Prop)
    (h : p.ior.red.Leads on
      (fun a b => Q₀ ((actAt F get lo p.base).2 a)
        ((actAt F get lo (p.base + p.trees)).2 b)) p.err) :
    p.ior.red.LeadsK (actAt F get lo p.base).2 on
      (fun a b => Q₀ ((actAt F get lo p.base).2 a)
        ((actAt F get lo (p.base + p.trees)).2 b)) p.err :=
  leadsK_of_handsAct p _ _ (liftHands S S₀ Cl W C F get set b₀ p lo hb h1 h2 ho) on Q₀ h

/-- **By make: the third of the three clauses that `EachLeadsBN` asks**: the acting part behind such
a block is a function of the acting part in front and the transcript. -/
theorem keyLaw_of_lift (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl) (p : Piece C F S Cl W)
    (lo : ℕ) (hb : p.b = b₀.lift get set) (h1 : ∀ t s, get (set t s) = s)
    (h2 : ∀ t s s', set (set t s) s' = set t s') (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.KeyLaw (actAt F get lo p.base).2 (actAt F get lo (p.base + p.trees)).2 :=
  keyLaw_of_handsAct p _ _ (liftHands S S₀ Cl W C F get set b₀ p lo hb h1 h2 ho) id

/-- The same as the first of the three clauses that `EachLeadsBN` asks, at every number of slots:
εO = 0. -/
theorem leadsBN_of_lift (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl) (p : Piece C F S Cl W)
    (lo N : ℕ) (hb : p.b = b₀.lift get set) (h1 : ∀ t s, get (set t s) = s)
    (h2 : ∀ t s s', set (set t s) s' = set t s') (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j)
    (on : S × F.E.Str → Prop)
    (Q₀ : (actAt F get lo p.base).1 → (actAt F get lo (p.base + p.trees)).1 → Prop)
    (h : p.ior.red.Leads on
      (fun a b => Q₀ ((actAt F get lo p.base).2 a)
        ((actAt F get lo (p.base + p.trees)).2 b)) p.err) :
    p.ior.red.LeadsBN (actAt F get lo p.base).2 on
      (fun a b => Q₀ ((actAt F get lo p.base).2 a) ((actAt F get lo (p.base + p.trees)).2 b)) N
          p.err :=
  (leadsK_of_lift get set b₀ p lo hb h1 h2 ho on Q₀ h).bothN N

/-- **The form of the law of one block of the shared chain, but for the block at which the shared
point is drawn.** A, A': the acting parts in front and behind.
OWED IS h: the block's plain law FOR ONE STATEMENT, of the shared items alone, said at the acting
parts: the promise behind; and for every world w: the shared items behind at w give the shared items
in front at e₀ (A a) (A' b) w (e₀: a named map of worlds; the identity where the block lays no part
of the world). AND hc, FOR CERTAIN: what rides (the slots' own items) is carried; hc IS HANDED THE
SHARED ITEMS BEHIND TOO: so an own item may change its form at the block by leaning on a shared
item. AND hs, FOR CERTAIN: Q' a b at every yes. THEN the block has the first of the three clauses
that `EachLeadsBN` asks, at every N, at its own errors, εO = 0, of the shared items and what rides
TOGETHER, with Q' a b beside, outright: there a next condition that reads a slot's own part finds
what it needs. -/
theorem step_of_lift (get : S → S₀) (set : S → S₀ → S) (b₀ : Block S₀ Cl) (p : Piece C F S Cl W)
    (lo N : ℕ) (hb : p.b = b₀.lift get set) (h1 : ∀ t s, get (set t s) = s)
    (h2 : ∀ t s s', set (set t s) s' = set t s') (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j)
    {Wt : Type} (on : S × F.E.Str → Prop)
    (on'₀ : (actAt F get lo (p.base + p.trees)).1 → Prop)
    (R₀ : (actAt F get lo p.base).1 → Wt → Prop)
    (R'₀ : (actAt F get lo (p.base + p.trees)).1 → Wt → Prop)
    (e₀ : (actAt F get lo p.base).1 → (actAt F get lo (p.base + p.trees)).1 → Wt → Wt)
    (h : p.ior.red.Leads on (fun a b => on'₀ ((actAt F get lo (p.base + p.trees)).2 b) ∧
      ∀ w, R'₀ ((actAt F get lo (p.base + p.trees)).2 b) w →
        R₀ ((actAt F get lo p.base).2 a) (e₀ ((actAt F get lo p.base).2 a) ((actAt F get lo (p.base
            + p.trees)).2 b) w)) p.err)
    (Rc Rc' : S × F.E.Str → Wt → Prop)
    (hc : ∀ a τ b w, on a → p.ior.red.out a τ = some b →
      on'₀ ((actAt F get lo (p.base + p.trees)).2 b) →
      R'₀ ((actAt F get lo (p.base + p.trees)).2 b) w → Rc' b w →
      Rc a (e₀ ((actAt F get lo p.base).2 a) ((actAt F get lo (p.base + p.trees)).2 b) w))
    (Q' : S × F.E.Str → S × F.E.Str → Prop)
    (hs : ∀ a τ b, on a → p.ior.red.out a τ = some b → Q' a b) :
    p.ior.red.LeadsBN (actAt F get lo p.base).2 on
      (fun a b => (on'₀ ((actAt F get lo (p.base + p.trees)).2 b) ∧
        ∀ w, R'₀ ((actAt F get lo (p.base + p.trees)).2 b) w ∧ Rc' b w →
          R₀ ((actAt F get lo p.base).2 a) (e₀ ((actAt F get lo p.base).2 a) ((actAt F get lo
              (p.base + p.trees)).2 b) w) ∧
            Rc a (e₀ ((actAt F get lo p.base).2 a) ((actAt F get lo (p.base + p.trees)).2 b) w)) ∧
        Q' a b) N p.err :=
  Reduction.LeadsBN.beside_sure (Reduction.LeadsBN.beside_map
    (on' := fun b => on'₀ ((actAt F get lo (p.base + p.trees)).2 b))
    (R := fun a w => R₀ ((actAt F get lo p.base).2 a) w)
    (R' := fun b w => R'₀ ((actAt F get lo (p.base + p.trees)).2 b) w)
    (e := fun a b w => e₀ ((actAt F get lo p.base).2 a) ((actAt F get lo (p.base + p.trees)).2 b) w)
    (leadsBN_of_lift get set b₀ p lo N hb h1 h2 ho on
      (fun k k' => on'₀ k' ∧ ∀ w, R'₀ k' w → R₀ k (e₀ k k' w)) h) Rc Rc' hc) Q' hs

end VerifiableInference.Desc.Plain

namespace Iop.KeyAloneToy
open Prob IOR

variable (E : ExtSpec)

/-- A reduction whose output hangs on the slot's own part: it tells whether the drawn value is the
slot's. -/
abbrev Rd : IOR (Fin 3) E Bool E := IOR.draw (Fin 3) (fun x c => decide (c = x)) E

abbrev QT : Fin 3 × E.Str → Bool × E.Str → Prop := fun _ b => b.1 = false

theorem one_statement : (Rd E).red.Leads (fun _ => True) (QT E) ((1, ()) : ℕ × Unit) := by
  intro a _ m
  refine le_trans (cnt_mono ?_) (le_of_eq (cnt_eq_const a.1))
  intro c hc
  by_contra hne
  refine hc ?_
  show ∀ b, (Rd E).red.out a (m, c, ()) = some b → b.1 = false
  intro b hb
  obtain rfl : (decide (c = a.1), a.2) = b := Option.some.inj hb
  exact decide_eq_false hne

/-- **The premise cannot be dropped**: one statement's law holds at the error 1 of 3; the law at the
trivial key does not. -/
theorem reads_a_slot (y : E.Str) :
    ¬ (Rd E).red.LeadsK (fun _ => ()) (fun _ => True) (QT E) ((1, ()) : ℕ × Unit) := by
  intro h
  have h1 : cnt (fun c : Fin 3 => ¬ Doomed [] () fun τ : Unit =>
      ∀ a : Fin 3 × E.Str, () = () → True → ∀ b, (Rd E).red.out a (((), ()), c, τ) = some b →
        b.1 = false) ≤ 1 := h () ((), ())
  have h3 : cnt (fun _ : Fin 3 => True) ≤ 1 := by
    refine le_trans (cnt_mono fun c _ hd => ?_) h1
    have := hd (c, y) rfl trivial (decide (c = c), y) rfl
    simp at this
  rw [cnt_true] at h3
  simp at h3

/-- At a reduction that says "the bad thing" always, one statement's law fails at every error below
all. -/
theorem no_law_at_yes (y : E.Str) :
    ¬ (IOR.draw (Fin 3) (fun (_ : Fin 3) _ => true) E).red.Leads (fun _ => True) (QT E)
      ((2, ()) : ℕ × Unit) := by
  intro h
  have h1 : cnt (fun c : Fin 3 => ¬ Doomed [] () fun τ : Unit =>
      ∀ b, (IOR.draw (Fin 3) (fun (_ : Fin 3) _ => true) E).red.out (0, y) (((), ()), c, τ) =
          some b →
        b.1 = false) ≤ 2 := h (0, y) trivial ((), ())
  have h3 : cnt (fun _ : Fin 3 => True) ≤ 2 := by
    refine le_trans (cnt_mono fun c _ hd => ?_) h1
    have := hd (true, y) rfl
    simp at this
  rw [cnt_true] at h3
  simp at h3

end Iop.KeyAloneToy

#print axioms Iop.Reduction.leadsK_of_hands
#print axioms Iop.Reduction.keyLaw_of_hands
#print axioms Iop.Reduction.LeadsK.beside_sure
#print axioms Iop.Reduction.LeadsBN.beside_sure
#print axioms VerifiableInference.Desc.Plain.keyLaw_of_handsAct
#print axioms VerifiableInference.Desc.Plain.keyLaw_of_lift
#print axioms VerifiableInference.Desc.Plain.leadsK_of_handsAct
#print axioms VerifiableInference.Desc.Plain.leadsK_of_lift
#print axioms VerifiableInference.Desc.Plain.leadsBN_of_lift
#print axioms Iop.Reduction.LeadsBN.conseq
#print axioms Iop.Reduction.LeadsBN.mono_err
#print axioms Iop.Reduction.LeadsBN.beside_map
#print axioms VerifiableInference.Desc.Plain.step_of_lift
#print axioms Iop.KeyAloneToy.one_statement
#print axioms Iop.KeyAloneToy.reads_a_slot
#print axioms Iop.KeyAloneToy.no_law_at_yes
