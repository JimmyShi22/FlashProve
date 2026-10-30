-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4AtMg.lean: WHAT OF K4's ROW's RECORDS OF LINES ON THE TABLE OF JOINTS' MEANING
(`K4Front`: four lines; `K4Keeps`: thirteen) FALLS AT EVERY MEANING WITH `K4Fields` (seven of its
fields and items are the layers' own terms): look · held · shown OUTRIGHT; OTHERS UNDER NAMED
PREMISES; THE REST ASKED AS IT WAS. NO MEMBER IS SHOWN. Why: a line on the meaning that the meant
filling cannot meet makes every law above it hold for nothing: each line is held here against the
layers' own terms. WHY BY FIELDS: the one filling is composed of layers in an order that is not ours
to fix: a statement at "Mg.shown = shownJT cs G ms" fits every order in which no layer above lays
the same field or item. Definitions, statements and proofs: calls.

  `K4Fields`: SEVEN EQUATIONS: held · shown · noColl are the table's own filling's of the oracles'
    letters (Johnson/Desc/Sound/BordersFill.lean: `meaningSig`) · the items ledger · freeAbove ·
    unheard are the table's own layer's tests (Johnson/Desc/First/FillKeeper.lean) · look at a
    layers' segment is K4's layer's (FillK4.lean).
  `lookLayB_kept`: look's test rides past a yes of K4's block (`KeptAtS`).
  **`k4Front_at`**: UNDER H, the four facts on X and i, eL, eO AND fit: `K4Front` at the plan's
  letters (X.y.fo · X.y.h.lmb · 0 · `LeftQ hp.ns`): look: a term · left, leftOn: terms under eL, eO
  (the meaning's two sentences are the lookup's own items: rfl once that kind's layer lies) and h,
  hn, h0, hg · fit: a Bool on the table's rows, asked.
  `keepQ_at`: the sentence keepQ (every open public item that K4's row does not drop rides past a
  `Yes`): terms at ledger · freeAbove · unheard (every segment's) and at look (every layers'
  segment's: at the real plan K4's own alone is open, and the row drops it); callerIn at a layers'
  segment: none is open but K4's own, which the row drops (only: a line on the plan); ALL OTHER
  ITEMS: restQ: a line on the meaning.
  `makeP_at`: the sentence makeP, UNDER `K4Front` AND restP: a term at leftOn m
  (`k4_leftOn_behind`).
  **`k4Keeps_at`**: UNDER `K4Front` AND THE PREMISES NAMED BELOW: there is a place pl' with
  `K4Keeps`: next · link' · piece' out of the test `k4NextFit`; trees · msgs out of `bookFit` and
  `k4ToldFit`; below out of `fenceFit` and hbase; held · shown: terms; noColl under hsmp; pub · pubP
  out of the above with keepT · make · keepP; dec · inOrder: asked.
  `mgK4`, `fields_mgK4`: `meaningSig cs G arr smp ms decT (fillK4 links nextOf (fillKeeper nsOf
  Mg0))` has the seven, over every Mg0.

Limits. WHAT IS STILL ASKED, BY NAME: FIVE ON THE PLACE AND THE PUBLIC RECORD (H: block k is piece 3
of the layers' segment m · h: X is what publicOf returns · hn, h0, hg: i is a layers' link of X with
plan hp; m and i are tied by eL and eO alone) · FIVE Bools with code (fit · k4NextFit · k4ToldFit ·
bookFit · fenceFit) · TWO LINES ON THE PLAN AND THE PIECE (hbase · only) · ONE ON THE SAMPLE's
READER (hsmp) · TWO IFFS (eL · eO) · SEVEN LINES ON WHAT THE SEVEN EQUATIONS DO NOT FIX (dec ·
inOrder · restQ · keepT · make · keepP · restP): their owners' layers do not lie here. THE LETTERS
ARE NOT FREE: nsOf m is meant as the plan's hp.ns at the link i that eL names (and nextOf m as
FillK4.lean's Limits say): at another number, or none, no unmarked statement stands in the promise
in front of K4, and the lines that are asked inside that promise hold for nothing. THAT THE PROMISE
IN FRONT IS MET AT AN HONEST RECORD AT SUCH A MEANING IS SHOWN BY NOTHING HERE. `mgK4` IS NOT the
table's one composed filling: it lacks the model's relation's and the runs' forms' layers. K04_law,
the law of K4's block itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4PubBehind
import Johnson.Road.K4.SameReadSig
import Johnson.Road.K4.K4FrontLeft
import Johnson.Road.K4.K4KeepKeeper
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.First.BookFit
import Johnson.Desc.First.FenceFit
import Johnson.Desc.First.FillK4
import Johnson.Desc.First.K4PlanFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Place FileDescription Wit smpHeld)
open VerifiableInference.Desc.First (S LayOwn ModelPart Pub Meaning Numbers start openSets pubSets pubRowM
  pubOfItems pubFit bookFit bookFit_at told_succ_nil fenceFit fenceFit_at fillKeeper keeperItem
  ledgerB freeAboveB unheardB)
open VerifiableInference.Desc.First.FillK4 (fillK4 isLay k4Item lookLayB filledB look_agrees
  look_filled fillK4_look k4NextFit k4ToldFit k4NextFit_at k4ToldFit_at)
open VerifiableInference.Desc.Sound (Frame Piece onQ strsOf Sending Mem MsgT meaningSig shownJT
  noCollJT)
open VerifiableInference.OnPublicFiles (LeftQ k3LeftItemAt k3LeftOnItemAt)

/-- look's test rides past a yes of K4's block. -/
theorem lookLayB_kept {p : Par} {s s' : S} (K : KeptAtS p s s') (h : lookLayB s = true) :
    lookLayB s' = true := by
  obtain ⟨a, _, _, G, ha, _, h3, hL, _, _, _, _, hR, _⟩ := K
  obtain ⟨a', ha', _, e2, _, e4⟩ := hR.here a ha
  have eF : a'.F = G := by
    have : s'.fork? = some a'.F := by simp [S.fork?, ha']
    exact Option.some.inj (this.symm.trans h3)
  obtain ⟨g, hg, hall⟩ := look_filled h ha
  have hag := look_agrees h ha
  unfold lookLayB
  rw [ha']
  simp only [Bool.and_eq_true, decide_eq_true_eq, e2, e4, hg]
  refine ⟨?_, hg.symm.trans hag⟩
  unfold filledB
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro x hx
  obtain ⟨h1, h2⟩ := hall x hx
  rw [eF]
  exact ⟨by rw [hL.ns]; exact h1, (hL.keep x.1 h2).1⟩

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
variable {P W Cl Xi : Type} {Fr : Frame} (N : Numbers) (Z : P) (Mg : Meaning P W)
  (cs : OnBytes.Codes) (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (nsOf : ℕ → Option ℕ)
  {q : Piece (ckP .two) Fr S Cl W} {par : Par}

/-- **The meaning's fields and items that are the layers' own terms.** -/
structure K4Fields (links : List ModelPart) : Prop where
  held : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t
  shown : Mg.shown = shownJT cs G ms
  noColl : Mg.noColl = noCollJT cs G smp ms
  ledger : ∀ m' a, Mg.pub (.ledger m') a = ledgerB a.2
  freeAbove : ∀ m' a, Mg.pub (.freeAbove m') a = (nsOf m').any fun n => freeAboveB n a.2
  unheard : ∀ a, Mg.pub .unheard a = unheardB a.2
  look : ∀ m' a, isLay links m' = true → Mg.pub (.look m') a = lookLayB a.2

variable {Mg cs G smp ms nsOf}
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ}
  {hp : Layer.HPlan2}

/-- **UNDER H, the four facts on X and i, eL, eO AND fit: `K4Front` at a meaning with `K4Fields`.**
-/
theorem k4Front_at (E : K4Fields Mg cs G smp ms nsOf links) (H : AtK4 links ps k m pl)
    (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp)
    (eL : ∀ s, Mg.pubP (.left m) (Z, s) ↔ k3LeftItemAt X i s)
    (eO : ∀ s, Mg.pubP (.leftOn m) (Z, s) ↔ k3LeftOnItemAt X i s)
    (fit : pubFit Mg.more links ps = true) :
    K4Front Mg Z links ps m X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) :=
  k4Front_of_items Mg Z h hn h0 hg eL eO fit fun s a hl ha => by
    have hlay : isLay links m = true := by
      unfold isLay
      rw [H.sub]
      rfl
    rw [E.look m (Z, s) hlay] at hl
    exact look_agrees hl ha

/-- The sentence keepQ at such a meaning. -/
theorem keepQ_at (E : K4Fields Mg cs G smp ms nsOf links) (H : AtK4 links ps k m pl)
    (fit : pubFit Mg.more links ps = true)
    (only : ∀ m', isLay links m' = true →
      Pub.callerIn m' ∈ (pubSets Mg.more links ps)[k]?.getD [] → m' = m)
    (restQ : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], x ∉ (pubRowM Mg.more links pl).drops →
      k4Item links x = false → keeperItem x = false → Mg.pub x (Z, a.1) = true →
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true) :
    ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], x ∉ (pubRowM Mg.more links pl).drops →
      Mg.pub x (Z, a.1) = true → Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y x hx hd hp'
  have K := kept_of_yes y
  have hled : ledgerB a.1 = true := by
    have := k4_pub_front N Mg Z H fit ha hu (.ledger m) (by simp)
    rwa [E.ledger m (Z, a.1)] at this
  cases x with
  | look m' =>
    by_cases hl : isLay links m' = true
    · rw [E.look m' _ hl] at hp' ⊢
      exact lookLayB_kept K hp'
    · exact restQ a τ fo o G' ha hu y _ hx hd (by simpa [k4Item] using hl) rfl hp'
  | callerIn m' =>
    by_cases hl : isLay links m' = true
    · exfalso
      have em := only m' hl hx
      subst em
      apply hd
      rw [k4_drops H]
      simp
    · exact restQ a τ fo o G' ha hu y _ hx hd (by simpa [k4Item] using hl) rfl hp'
  | ledger m' =>
    rw [E.ledger m' _]
    exact ledgerB_kept K hled
  | freeAbove m' =>
    rw [E.freeAbove m' _] at hp' ⊢
    cases hn : nsOf m' with
    | none => simp [hn] at hp'
    | some n =>
      have h2 : freeAboveB n a.1 = true := by simpa [hn] using hp'
      simpa using freeAboveB_kept K hled h2
  | unheard =>
    rw [E.unheard _] at hp' ⊢
    show unheardB (behindOf seatS q a τ o G').1 = true
    rw [unheardB_kept K]
    exact hp'
  | _ => exact restQ a τ fo o G' ha hu y _ hx hd rfl rfl hp'

/-- The sentence makeP, at every meaning, UNDER `K4Front` AND restP. -/
theorem makeP_at (H : AtK4 links ps k m pl) {h3 : Forest.Shape} {lm first : ℕ}
    {Q3 : Fork → Prop} (Kf : K4Front Mg Z links ps m h3 lm first Q3)
    (restP : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes, x ≠ .leftOn m →
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1)) :
    ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes,
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1) := by
  intro a τ fo o G' ha hu y x hx
  by_cases e : x = .leftOn m
  · subst e
    exact k4_leftOn_behind N Mg Z H Kf ha hu y
  · exact restP a τ fo o G' ha hu y x hx e

/-- **UNDER `K4Front` AND THE PREMISES THAT THE HEAD NAMES: `K4Keeps` at a meaning with
`K4Fields`**, at
the place that the plan's test gives. -/
theorem k4Keeps_at (E : K4Fields Mg cs G smp ms nsOf links) (H : AtK4 links ps k m pl)
    {h3 : Forest.Shape} {lm first : ℕ} {Q3 : Fork → Prop}
    (Kf : K4Front Mg Z links ps m h3 lm first Q3)
    (hnext : k4NextFit links ps = true) (told : List (List VerifiableInference.Desc.Oracle))
    (htold : k4ToldFit links ps told = true) (hbf : bookFit N ps told = true)
    (hff : fenceFit N links ps = true) (hbase : N.treesAt (some pl) = q.base)
    (only : ∀ m', isLay links m' = true →
      Pub.callerIn m' ∈ (pubSets Mg.more links ps)[k]?.getD [] → m' = m)
    (hsmp : ∀ x y : S × Fr.E.Str, SameIn N Mg Z links ps k q.base x y →
      ∀ s i, smp (Z, y.1) s i = smp (Z, x.1) s i)
    (dec : ∀ a τ fo o G, Yes seatS par q a τ fo o G → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
      Mg.decodes (Z, (behindOf seatS q a τ o G).1) (strsOf Fr (behindOf seatS q a τ o G).2))
    (inOrder : ∀ x y : S × Fr.E.Str, SameIn N Mg Z links ps k q.base x y →
      Mg.inOrder (Z, x.1) = true → Mg.inOrder (Z, y.1) = true)
    (restQ : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], x ∉ (pubRowM Mg.more links pl).drops →
      k4Item links x = false → keeperItem x = false → Mg.pub x (Z, a.1) = true →
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true)
    (keepT : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      ∀ x ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []),
      Mg.pub x (Z, a.1) = true → Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true)
    (make : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes ++
        [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m],
      Mg.pub x (Z, (behindOf seatS q a τ o G').1) = true)
    (keepP : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [],
      x ∉ (pubRowM Mg.more links pl).drops → Mg.pubP x (Z, a.1) →
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1))
    (restP : ∀ a τ fo o G', onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ x ∈ (pubRowM Mg.more links pl).makes, x ≠ .leftOn m →
      Mg.pubP x (Z, (behindOf seatS q a τ o G').1)) :
    ∃ pl', K4Keeps N Mg Z links ps k m pl pl' q par := by
  obtain ⟨pl', next, link', piece'⟩ := k4NextFit_at hnext H.here H.link H.sub H.piece
  have hn := k4ToldFit_at htold H.here H.link H.sub H.piece
  have hk1 : k + 1 < ps.length := (List.getElem?_eq_some_iff.mp next).1
  have a0 := bookFit_at N ps told hbf k (by omega)
  have a1 := bookFit_at N ps told hbf (k + 1) (by omega)
  have c := told_succ_nil told k hn
  rw [H.here] at a0
  rw [next] at a1
  refine ⟨pl', k4Keeps_of_items Mg N Z H next link' piece' (by rw [a1.1, a0.1, c.1])
    (by rw [a1.2, a0.2, c.2]) dec inOrder ?_ ?_ ?_ ?_ (keepQ_at N Z E H Kf.fit only restQ) keepT
    make keepP (makeP_at N Z H Kf restP)⟩
  · intro x y t j h hx
    rw [E.held] at hx ⊢
    show smpHeld y.1.st y.1.book t j = true
    rw [held_same h.2.2]
    exact hx
  · intro z hz
    have := fenceFit_at N links ps hff k (by omega) z hz
    rw [H.here, hbase] at this
    exact this
  · intro x y t j ht h hx
    rw [E.shown] at hx ⊢
    exact shown_same G cs ms h.2.2 ht j hx
  · intro x y t j ht h hx
    rw [E.noColl] at hx ⊢
    exact noColl_same G cs smp ms Z h.2.2 (hsmp x y h) ht j hx

/-- **A named meaning, made of three layers.** NOT the table's one composed filling: it lacks the
model's relation's and the runs' forms' layers, and its decodes is the oracles' layer's. -/
abbrev mgK4 {P Xi Cells Tok : Type} (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (nsOf nextOf : ℕ → Option ℕ) (Mg0 : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) :
    Meaning P (Wit Cells Tok MsgT) :=
  meaningSig cs G arr smp ms decT (fillK4 links nextOf (fillKeeper nsOf Mg0))

/-- **It has the seven, over every Mg0.** -/
theorem fields_mgK4 {P Xi Cells Tok : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (nsOf nextOf : ℕ → Option ℕ) (Mg0 : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) :
    K4Fields (mgK4 cs G arr smp ms decT nsOf nextOf Mg0 links) cs G smp ms nsOf links :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ a hl => fillK4_look links nextOf (fillKeeper nsOf Mg0) hl a⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.lookLayB_kept
#print axioms OnBytes.Road.K4.k4Front_at
#print axioms OnBytes.Road.K4.keepQ_at
#print axioms OnBytes.Road.K4.makeP_at
#print axioms OnBytes.Road.K4.k4Keeps_at
#print axioms OnBytes.Road.K4.fields_mgK4
