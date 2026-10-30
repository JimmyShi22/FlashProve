-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunFrame.lean: THE FORM OF Honest/K9/RunSchema.lean WRITTEN OUT ON THE STATE's FIELDS: one
relation for "what a run of claims does to the verifier's state", one for "what has happened to the state since the
batching began", the record `RunRecord` that a kind fills for one entry of the order, and the theorems that pass from the
filled records to `RunPays` and to `AcceptedS` at the batching.

WHAT THE RUNS WRITE. Of the thirteen sorts of run no theorem says "and no more".
  1  under slots of the open ledger: a shown value, its factor and the mark "filled" (`Fork.hide`); a second value under
     one slot is refused, so a run that fills slots needs THEM still free when it is called
  2  in the ledger's list of owed claims: the mark "added" at a number (`Fork.paid`); a run that first tests that its debt
     is unpaid needs it still unpaid when it is called
  3  the smallness test's record: the run "K8.equations" alone, and of it no field outside the fourteen that
     `TailClaims.Law.blank` overwrites
  4  the count of rows owed, from "0 rows" to "none" (the feed-forward kind's two runs)
WHICH slots and WHICH debts a run touches it reads off the state (what its kind's rounds have heard), so the record's
letters are functions of the state s in front of the batching. Everything else rests: every reading g of the state with
`FieldRests g` (Johnson/Desc/First/Link/Law/KeepsAny.lean) has the same value behind every run.

  `SideKept Ws Ds F G`     of two ledgers: G is later than F (`PscRun.Later`: the number of slots is kept; what is filled
                           stays filled, with its value and factor); the slots in Ws are filled in G just if they were
                           in F; the list of owed claims has the same length, and the same entry at each number in Ds
  `StateKept Ws Ds whole u v`   of two states: where u has an open ledger, v has one, in `SideKept`; where u holds the
                           smallness test's record, v holds one that differs at most in the fourteen fields, and
                           not at all if `whole`
  `Since p s tr Ws Ds whole u`   u against the state s in front of the batching: `StateKept`; and against the state t₁
                           behind the draw (which is s with the batching's part laid anew: `draw_is`): every reading
                           that rests under the four writings has the same value (`Since.reads`), and the ledger's
                           core is the same (`Kept`), so what a run finds of it is `LedgerAtRun` (`Since.finds`).
                           That the draw has said yes at s and tr is a field of `Since` (`drawn`)
  `Tied`                   the tie between a kind's own run f and the run that stands in the description's list, which
                           is f behind a guard: so that a kind speaks of its own run alone (Honest/K9/RunTied.lean)
  **`RunRecord`**             THE RECORD THAT A KIND FILLS FOR ONE ENTRY. Its letters: f: my own run; own s, owe s: the slots
                           that it may fill and the debts that it may pay; tails: it may write the smallness test's
                           record; Ws s, Ds s, whole: the slots, debts and record that it needs untouched since s;
                           n s: a bound on the number of its claims. Its fields: `does` (from a yes, at the states
                           that `SinceAny` allows), `returns` (from `Since`), `count` and `fits` (from `Since` and a
                           yes). A worked instance: Honest/K9/RunIdle.lean
  `Fitted`                 the arithmetic that joins the records at a stand: nobody in front of entry j fills a slot, pays
                           a debt or writes a record that entry j needs untouched
  `called_frame`, **`runPays_of_records`**, **`accepted_of_records`**

Limits. No term of `RunRecord` is made here. `accepted_of_records` keeps, beside the premises of `accepted_of_runs`, five that are no
kind's own: `rests` (every reading that rests is kept by every run of the order), `cores` (so is the ledger's core),
`sized` (the ledger's arrays at a stand), `tied` and `fit`. The field `span` is spent by no theorem here: it is asked for `fit`. What a run needs of the PAST (what its kind's rounds heard, that the ledger's arrays are sized) is
not in `Since`: it is to be had from St, the stand.
This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RunSchema
import Johnson.Desc.ProofFile.Honest.K9.MarksKept
import Johnson.Desc.ProofFile.Honest.K9.KeepsPaid
import Johnson.Desc.First.Link.Law.KeepsAny
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.Desc.First.TailClaims.EquationsBlank
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (FieldRests)

/-! ## The relations -/

/-- Of two ledgers. Ws: slots whose marks are kept. Ds: numbers at which the list of owed claims is kept. -/
structure SideKept (Ws Ds : ℕ → Prop) (F G : Fork) : Prop where
  later : PscRun.Later F G
  marks : PscRun.Sized F → ∀ i, Ws i → (PscRun.Filled G i ↔ PscRun.Filled F i)
  size : G.owed.size = F.owed.size
  debts : ∀ i, Ds i → G.owed[i]? = F.owed[i]?

theorem SideKept.refl (Ws Ds : ℕ → Prop) (F : Fork) : SideKept Ws Ds F F :=
  ⟨PscRun.Later.refl F, fun _ _ _ => Iff.rfl, rfl, fun _ _ => rfl⟩

theorem SideKept.trans {Ws Ds : ℕ → Prop} {F G H : Fork} (a : SideKept Ws Ds F G) (b : SideKept Ws Ds G H) :
    SideKept Ws Ds F H :=
  ⟨a.later.trans b.later, fun hs i hi => (b.marks (a.later.sized hs) i hi).trans (a.marks hs i hi),
    b.size.trans a.size, fun i hi => (b.debts i hi).trans (a.debts i hi)⟩

theorem SideKept.mono {Ws Ds Ws' Ds' : ℕ → Prop} {F G : Fork} (a : SideKept Ws Ds F G)
    (hW : ∀ i, Ws' i → Ws i) (hD : ∀ i, Ds' i → Ds i) : SideKept Ws' Ds' F G :=
  ⟨a.later, fun hs i hi => a.marks hs i (hW i hi), a.size, fun i hi => a.debts i (hD i hi)⟩

/-- Of two states. whole: the smallness test's record is kept whole. -/
structure StateKept (Ws Ds : ℕ → Prop) (whole : Prop) (u v : S) : Prop where
  side : ∀ F, u.fork? = some F → ∃ G, v.fork? = some G ∧ SideKept Ws Ds F G
  tail : ∀ t, u.tl? = some t → ∃ t', v.tl? = some t' ∧ (whole → t' = t) ∧ ∀ x, TailClaims.Law.blank x t' = TailClaims.Law.blank x t
  mark : v.failed = u.failed
  out : v.out = u.out

theorem StateKept.refl (Ws Ds : ℕ → Prop) (whole : Prop) (u : S) : StateKept Ws Ds whole u u :=
  ⟨fun F hF => ⟨F, hF, SideKept.refl _ _ F⟩, fun t ht => ⟨t, ht, fun _ => rfl, fun _ => rfl⟩, rfl, rfl⟩

theorem StateKept.trans {Ws Ds : ℕ → Prop} {whole : Prop} {u v w : S} (a : StateKept Ws Ds whole u v)
    (b : StateKept Ws Ds whole v w) : StateKept Ws Ds whole u w := by
  refine ⟨fun F hF => ?_, fun t ht => ?_, b.mark.trans a.mark, b.out.trans a.out⟩
  · obtain ⟨G, hG, k1⟩ := a.side F hF
    obtain ⟨H, hH, k2⟩ := b.side G hG
    exact ⟨H, hH, k1.trans k2⟩
  · obtain ⟨t1, h1, w1, b1⟩ := a.tail t ht
    obtain ⟨t2, h2, w2, b2⟩ := b.tail t1 h1
    exact ⟨t2, h2, fun hw => (w2 hw).trans (w1 hw), fun x => (b2 x).trans (b1 x)⟩

theorem StateKept.mono {Ws Ds Ws' Ds' : ℕ → Prop} {whole whole' : Prop} {u v : S}
    (a : StateKept Ws Ds whole u v) (hW : ∀ i, Ws' i → Ws i) (hD : ∀ i, Ds' i → Ds i)
    (hw : whole' → whole) : StateKept Ws' Ds' whole' u v := by
  refine ⟨fun F hF => ?_, fun t ht => ?_, a.mark, a.out⟩
  · obtain ⟨G, hG, k1⟩ := a.side F hF
    exact ⟨G, hG, k1.mono hW hD⟩
  · obtain ⟨t1, h1, w1, b1⟩ := a.tail t ht
    exact ⟨t1, h1, fun h => w1 (hw h), b1⟩

/-- **What has happened to the state since the batching began.** s: the state in front of the batching. tr: the drawn
words. -/
structure Since (p : Desc.K9.Where) (s : S) (tr : UInt64 × UInt64 × UInt64) (Ws Ds : ℕ → Prop) (whole : Prop)
    (u : S) : Prop where
  kept : StateKept Ws Ds whole s u
  sized : ∀ F, s.fork? = some F → PscRun.Sized F
  drawn : ∃ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁
  rest : ∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
    .ok t₁ → ∀ {γ : Type} (f : S → γ), FieldRests f → f u = f t₁
  core : ∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
    .ok t₁ → Kept t₁ u

/-- What a run finds of the ledger's core. -/
theorem Since.finds {p : Desc.K9.Where} {s u : S} {tr : UInt64 × UInt64 × UInt64} {Ws Ds : ℕ → Prop}
    {whole : Prop} (h : Since p s tr Ws Ds whole u) :
    ∃ a', Desc.K9.atS.get? u = some a' ∧ LedgerAtRun (E.ofTriple tr) a' := by
  obtain ⟨t₁, hd⟩ := h.drawn
  obtain ⟨a, ha⟩ := draw_open p s t₁ _ hd
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ _ a ha hd
  exact kept_finds a a₁ _ hl t₁ u h1 (h.core t₁ hd)

/-- The state behind the draw, written out, with what `Since` says against it: every reading that rests has at u its
value at s with the batching's part laid anew. -/
theorem Since.reads {p : Desc.K9.Where} {s u : S} {tr : UInt64 × UInt64 × UInt64} {Ws Ds : ℕ → Prop}
    {whole : Prop} (h : Since p s tr Ws Ds whole u) (a : Desc.K9.Part) (ha : Desc.K9.atS.get? s = some a)
    {γ : Type} (g : S → γ) (R : FieldRests g) :
    g u = g (Desc.K9.atS.set s (drawnPart p a (E.ofTriple tr))) := by
  obtain ⟨t₁, hd⟩ := h.drawn
  rw [h.rest t₁ hd g R, draw_is p s t₁ _ a ha hd]

/-- So a reading that rests under the four writings and under the batching's own has at u its value at s. -/
theorem Since.same {p : Desc.K9.Where} {s u : S} {tr : UInt64 × UInt64 × UInt64} {Ws Ds : ℕ → Prop}
    {whole : Prop} (h : Since p s tr Ws Ds whole u) {γ : Type} (g : S → γ) (R : FieldRests g)
    (hset : ∀ e q, g (Desc.K9.atS.set e q) = g e) : g u = g s := by
  obtain ⟨t₁, hd⟩ := h.drawn
  obtain ⟨a, ha⟩ := draw_open p s t₁ _ hd
  rw [h.reads a ha g R, hset]

/-- The smallness test's window of slots is at u what it was at s. -/
theorem Since.window {p : Desc.K9.Where} {s u : S} {tr : UInt64 × UInt64 × UInt64} {Ws Ds : ℕ → Prop}
    {whole : Prop} (h : Since p s tr Ws Ds whole u) (t : HTailF2) (ht : s.tl? = some t) :
    ∃ t', u.tl? = some t' ∧ t'.slotA = t.slotA ∧ t'.slotB = t.slotB := by
  obtain ⟨t', h1, _, hb⟩ := h.kept.tail t ht
  exact ⟨t', h1, congrArg (·.slotA) (hb t), congrArg (·.slotB) (hb t)⟩

/-- **The batching's test behind a run that is no owner of the smallness test's window**: it accepts a list whose claims
name only slots below `top` or from `bot` on, where `top` is at most the window's first slot and `bot` at least its end. -/
theorem each_of_named (k : Desc.K9.SegSort) (o : ℕ × String) (cls : List Claim) (u : S) (tl : HTailF2)
    (htl : u.tl? = some tl) (hn : o ∉ Desc.K9.cutAt k 1) (top bot : ℕ)
    (hnamed : ∀ cl ∈ cls, ∀ x ∈ cl.form.slots, x.1 < top ∨ bot ≤ x.1) (hbelow : top ≤ tl.slotA)
    (habove : tl.slotB ≤ bot) : Desc.K9.eachAtS k o cls u = .ok () :=
  (each_other k o cls u tl htl hn).2 fun cl hcl x hx hw => by
    have := hnamed cl hcl x hx
    omega

/-! ## The record that a kind fills -/

/-- **The tie between a kind's own run f and the run that stands in the description's list at entry j**, which the
description's makers have wrapped in a guard on the reply: there is a run at the entry; each yes of it is a yes of f with
the same return; and it returns wherever f returns and leaves the reply. It names no state of a run of the protocol. -/
structure Tied (Lk : Link S Claim) (j : ℕ) (f : ClaimsRun) : Prop where
  there : ∀ o, Lk.order[j]? = some o → ∃ r, claimsRunOf Lk.hear o = some r
  under : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunUnder r f
  lifts : ∀ o r, Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → ∀ m t z, f m t = .ok z →
    z.2.out.reply = t.out.reply → r m t = .ok z

/-- `Since` with nothing asked of any slot, debt or of the fourteen fields: what holds at every state at which any run
of the order is called. -/
abbrev SinceAny (p : Desc.K9.Where) (s : S) (tr : UInt64 × UInt64 × UInt64) (u : S) : Prop :=
  Since p s tr (fun _ => False) (fun _ => False) False u

/-- **THE RECORD, FOR ONE ENTRY j OF THE ORDER.** f: the kind's own run, in the kind's own terms. The letters n, own, owe,
Ws, Ds are read off the state s in front of the batching: a run finds its slots and its debts in what the state holds. -/
structure RunRecord (St : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop) (Lk : Link S Claim)
    (p : Desc.K9.Where) (j : ℕ) (n : S → ℕ) (f : ClaimsRun) (own owe : S → ℕ → Prop) (tails : Prop)
    (Ws Ds : S → ℕ → Prop) (whole : Prop) (lo hi : S → ℕ) : Prop where
  /-- from a yes, at every number of claims and every state that `SinceAny` allows: my run fills slots of own s alone,
  pays debts of owe s alone, writes the smallness test's record only if tails, and leaves the mark of failure and what
  the state holds for the output -/
  does : ∀ s tr a m u z, St s tr a → SinceAny p s tr u → f m u = .ok z →
    StateKept (fun i => ¬ own s i) (fun i => ¬ owe s i) (¬ tails) u z.2
  /-- my run returns, and the batching's test behind it accepts, at every number of claims -/
  returns : ∀ o, Lk.order[j]? = some o → ∀ s tr a m u, St s tr a → Since p s tr (Ws s) (Ds s) whole u →
    ∃ z, f m u = .ok z ∧ Lk.each o z.1 z.2 = .ok ()
  count : ∀ s tr a m u z, St s tr a → Since p s tr (Ws s) (Ds s) whole u → f m u = .ok z → z.1.length ≤ n s
  fits : ∀ s tr a t₁ a₁ m u z, St s tr a →
    (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
    Desc.K9.atS.get? t₁ = some a₁ → Since p s tr (Ws s) (Ds s) whole u → f m u = .ok z →
    z.1.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true
  /-- the slots that my run fills or needs lie in one stretch -/
  span : ∀ s tr a i, St s tr a → (own s i ∨ Ws s i) → lo s ≤ i ∧ i < hi s

/-- **A record filled at a wider stand serves at a narrower one.** So a kind may fill its record at a plain stand of its
own, which names no thread, and owe apart that the gathering theorem's stand gives that one. -/
theorem RunRecord.mono {St St' : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop} {Lk : Link S Claim}
    {p : Desc.K9.Where} {j : ℕ} {n : S → ℕ} {f : ClaimsRun} {own owe : S → ℕ → Prop} {tails : Prop}
    {Ws Ds : S → ℕ → Prop} {whole : Prop} {lo hi : S → ℕ}
    (R : RunRecord St' Lk p j n f own owe tails Ws Ds whole lo hi) (hS : ∀ s tr a, St s tr a → St' s tr a) :
    RunRecord St Lk p j n f own owe tails Ws Ds whole lo hi where
  does s tr a m u z h := R.does s tr a m u z (hS s tr a h)
  returns o ho s tr a m u h := R.returns o ho s tr a m u (hS s tr a h)
  count s tr a m u z h := R.count s tr a m u z (hS s tr a h)
  fits s tr a t₁ a₁ m u z h := R.fits s tr a t₁ a₁ m u z (hS s tr a h)
  span s tr a i h := R.span s tr a i (hS s tr a h)

/-- Two stretches that lie apart: what the one needs the other does not fill. -/
theorem apart_of_spans {own Ws : ℕ → Prop} {lo hi lo' hi' : ℕ} (h1 : ∀ i, own i → lo ≤ i ∧ i < hi)
    (h2 : ∀ i, Ws i → lo' ≤ i ∧ i < hi') (h : hi ≤ lo' ∨ hi' ≤ lo) : ∀ x, Ws x → ¬ own x := by
  intro x hx ho
  have a := h1 x ho
  have b := h2 x hx
  omega

/-- **The arithmetic that joins the records**, at a stand: nobody in front of entry j fills a slot, pays a debt or writes
a record that entry j needs untouched. -/
structure Fitted (len : ℕ) (own owe : ℕ → ℕ → Prop) (tails : ℕ → Prop) (Ws Ds : ℕ → ℕ → Prop)
    (whole : ℕ → Prop) : Prop where
  slots : ∀ j, j < len → ∀ x, Ws j x → ∀ i, i < j → ¬ own i x
  debts : ∀ j, j < len → ∀ x, Ds j x → ∀ i, i < j → ¬ owe i x
  tail : ∀ j, j < len → whole j → ∀ i, i < j → ¬ tails i

/-! ## From the records to the form -/

/-- The batching's own writing leaves the smallness test's record. -/
theorem set_tl (u : S) (q : Desc.K9.Part) : (Desc.K9.atS.set u q).tl? = u.tl? := by
  have e : (Desc.K9.atS.set u q).tl? = ((u.putLink q.L).putFork q.F).tl? := rfl
  rw [e, Desc.K9.tl_putFork, Desc.K9.tl_putLink]

/-- The draw fills no slot, pays no debt and leaves the smallness test's record. -/
theorem draw_stateKept (p : Desc.K9.Where) (s t : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    StateKept (fun _ => True) (fun _ => True) True s t := by
  obtain ⟨a, ha⟩ := draw_open p s t x h
  have e := draw_is p s t x a ha h
  refine ⟨fun F hF => ?_, fun tl ht => ?_, by rw [e, set_failed], by rw [e, set_out]⟩
  · obtain rfl : a.F = F := Option.some.inj ((Desc.K9.get_fork s a ha).symm.trans hF)
    refine ⟨(drawnPart p a x).F, ?_, ?_⟩
    · rw [e]
      exact set_fork s a _ ha
    · exact ⟨⟨Nat.le_refl _, rfl, id, fun _ hj => ⟨hj, rfl, rfl⟩⟩, fun _ _ _ => Iff.rfl, rfl, fun _ _ => rfl⟩
  · exact ⟨tl, by rw [e, set_tl]; exact ht, fun _ => rfl, fun _ => rfl⟩

theorem Since.mono {p : Desc.K9.Where} {s u : S} {tr : UInt64 × UInt64 × UInt64} {Ws Ds Ws' Ds' : ℕ → Prop}
    {whole whole' : Prop} (h : Since p s tr Ws Ds whole u) (hW : ∀ i, Ws' i → Ws i) (hD : ∀ i, Ds' i → Ds i)
    (hw : whole' → whole) : Since p s tr Ws' Ds' whole' u :=
  ⟨h.kept.mono hW hD hw, h.sized, h.drawn, h.rest, h.core⟩

section
variable {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **At every state at which entry j is called**: `Since`, at the slots and debts that no run in front touches. own, owe:
by entry, at the one state s in front. -/
theorem called_frame {own owe : ℕ → ℕ → Prop} {tails : ℕ → Prop}
    (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
      claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
    (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
    {s : S} {tr : UInt64 × UInt64 × UInt64} (hsz : ∀ F, s.fork? = some F → PscRun.Sized F) :
    ∀ {j : ℕ} {cs : List Claim} {u : S}, Called Lk p s tr j cs u →
      (∀ i, i < j → ∀ o r, Lk.order[i]? = some o → claimsRunOf Lk.hear o = some r → ∀ m u z,
        SinceAny p s tr u → r m u = .ok z →
        StateKept (fun x => ¬ own i x) (fun x => ¬ owe i x) (¬ tails i) u z.2) →
      Since p s tr (upTo own j) (upTo owe j) (∀ i, i < j → ¬ tails i) u := by
  intro j cs u h
  induction h with
  | @draw t₁ hd =>
    intro _
    refine ⟨(draw_stateKept p s t₁ _ hd).mono (fun _ _ => trivial) (fun _ _ => trivial) (fun _ => trivial),
      hsz, ⟨t₁, hd⟩, ?_, ?_⟩
    · intro t₁' hd' γ g _
      obtain rfl : t₁ = t₁' := Except.ok.inj (hd.symm.trans hd')
      rfl
    · intro t₁' hd'
      obtain rfl : t₁ = t₁' := Except.ok.inj (hd.symm.trans hd')
      exact Kept.refl _
  | @run j o cs u r z _ ho hr hz _ ih =>
    intro hl
    have I := ih fun i hi => hl i (by omega)
    have d := hl j (by omega) o r ho hr _ _ _ (I.mono (fun _ h => h.elim) (fun _ h => h.elim) (fun h => h.elim)) hz
    refine ⟨?_, hsz, I.drawn, ?_, ?_⟩
    · exact (I.kept.mono (fun _ hx i hi => hx i (by omega)) (fun _ hx i hi => hx i (by omega))
        (fun hw i hi => hw i (by omega))).trans
        (d.mono (fun _ hx => hx j (by omega)) (fun _ hx => hx j (by omega)) (fun hw => hw j (by omega)))
    · intro t₁ hd γ g hR
      rw [rests g hR j o r ho hr _ _ _ hz]
      exact I.rest t₁ hd g hR
    · intro t₁ hd
      exact (I.core t₁ hd).trans (cores j o r ho hr _ _ _ hz)

variable {St : S → UInt64 × UInt64 × UInt64 → Desc.K9.Part → Prop} {n : ℕ → S → ℕ} {f : ℕ → ClaimsRun}
  {own owe : ℕ → S → ℕ → Prop} {tails : ℕ → Prop} {Ws Ds : ℕ → S → ℕ → Prop} {whole : ℕ → Prop}
  {lo hi : ℕ → S → ℕ}

/-- **From the records at the entries up to j to the form at j.** -/
theorem runPays_of_records
    (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
      claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
    (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
    (sized : ∀ s tr a, St s tr a → ∀ F, s.fork? = some F → PscRun.Sized F)
    (tied : ∀ j, j < Lk.order.length → Tied Lk j (f j))
    (fit : ∀ s tr a, St s tr a → Fitted Lk.order.length (fun j => own j s) (fun j => owe j s) tails
      (fun j => Ws j s) (fun j => Ds j s) whole)
    (laws : ∀ j, j < Lk.order.length →
      RunRecord St Lk p j (n j) (f j) (own j) (owe j) (tails j) (Ws j) (Ds j) (whole j) (lo j) (hi j))
    (j : ℕ) (hj : j < Lk.order.length) : RunPays St Lk p j (n j) := by
  have since : ∀ {s tr a cs u}, St s tr a → Called Lk p s tr j cs u →
      Since p s tr (Ws j s) (Ds j s) (whole j) u := by
    intro s tr a cs u hS hC
    have I := called_frame (own := fun j => own j s) (owe := fun j => owe j s) (tails := tails) rests cores
      (sized s tr a hS) hC
      fun i hi o r ho hr m u z hu hz =>
        (laws i (by omega)).does s tr a m u z hS hu ((tied i (by omega)).under o r ho hr m u z hz)
    have F := fit s tr a hS
    exact I.mono (fun x hx i hi => F.slots j hj x hx i hi) (fun x hx i hi => F.debts j hj x hx i hi)
      (fun hw i hi => F.tail j hj hw i hi)
  have any : ∀ {s tr a cs u}, St s tr a → Called Lk p s tr j cs u → SinceAny p s tr u :=
    fun hS hC => (since hS hC).mono (fun _ h => h.elim) (fun _ h => h.elim) (fun h => h.elim)
  have L := laws j hj
  have Tj := tied j hj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o ho s tr a cs u hS hC
    obtain ⟨z, hz, he⟩ := L.returns o ho s tr a cs.length u hS (since hS hC)
    obtain ⟨r, hr⟩ := Tj.there o ho
    exact ⟨r, z, hr,
      Tj.lifts o r ho hr _ _ _ hz (congrArg (·.reply) (L.does s tr a _ _ _ hS (any hS hC) hz).out), he⟩
  · exact fun o r ho hr s tr a cs u z hS hC hz =>
      L.count s tr a cs.length u z hS (since hS hC) (Tj.under o r ho hr _ _ _ hz)
  · exact fun o r ho hr s tr a t₁ a₁ cs u z hS hd h1 hC hz =>
      L.fits s tr a t₁ a₁ cs.length u z hS hd h1 (since hS hC) (Tj.under o r ho hr _ _ _ hz)
  · exact fun o r ho hr s tr a cs u z hS hC hz =>
      (L.does s tr a _ _ _ hS (any hS hC) (Tj.under o r ho hr _ _ _ hz)).mark
  · exact fun o r ho hr s tr a cs u z hS hC hz =>
      congrArg (·.reply) (L.does s tr a _ _ _ hS (any hS hC) (Tj.under o r ho hr _ _ _ hz)).out

end

/-- **`AcceptedS` at the batching, from the record filled at every entry of the order.** hn: the search of the thread's list
of prover's sides at the batching's place finds none. -/
theorem accepted_of_records_find {V W X Pb : Type} {Bk : ProverCoinCounts} {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ}
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (T : Thread Bk S Claim V W X Pb) {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hn : (T.hs.find? fun h => h.place == (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place) = none)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (clean : ∀ κ s m En, ThrS T Said b κ s m En → s.failed = none)
    (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
      claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
    (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
    (sized : ∀ s tr a, StandAt T Said b front s tr a → ∀ F, s.fork? = some F → PscRun.Sized F)
    (n : ℕ → S → ℕ) (f : ℕ → ClaimsRun) (tied : ∀ j, j < Lk.order.length → Tied Lk j (f j))
    (own owe : ℕ → S → ℕ → Prop) (tails : ℕ → Prop) (Ws Ds : ℕ → S → ℕ → Prop) (whole : ℕ → Prop)
    (lo hi : ℕ → S → ℕ)
    (plan : ∀ s tr a, StandAt T Said b front s tr a → sumTo (fun j => n j s) Lk.order.length ≤ a.F.planClaimsF)
    (fit : ∀ s tr a, StandAt T Said b front s tr a → Fitted Lk.order.length (fun j => own j s)
      (fun j => owe j s) tails (fun j => Ws j s) (fun j => Ds j s) whole)
    (laws : ∀ j, j < Lk.order.length → RunRecord (StandAt T Said b front) Lk p j (n j) (f j) (own j) (owe j) (tails j)
      (Ws j) (Ds j) (whole j) (lo j) (hi j)) :
    AcceptedS T Said fall b :=
  accepted_of_runs_find T Sd hblk hn fall front hfall ready clean n plan
    (runPays_of_records rests cores sized tied fit laws)

/-- The same from "no side of this kind stands in the thread's list". -/
theorem accepted_of_records {V W X Pb : Type} {Bk : ProverCoinCounts} {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ}
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (T : Thread Bk S Claim V W X Pb) {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (clean : ∀ κ s m En, ThrS T Said b κ s m En → s.failed = none)
    (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
      claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
    (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
    (sized : ∀ s tr a, StandAt T Said b front s tr a → ∀ F, s.fork? = some F → PscRun.Sized F)
    (n : ℕ → S → ℕ) (f : ℕ → ClaimsRun) (tied : ∀ j, j < Lk.order.length → Tied Lk j (f j))
    (own owe : ℕ → S → ℕ → Prop) (tails : ℕ → Prop) (Ws Ds : ℕ → S → ℕ → Prop) (whole : ℕ → Prop)
    (lo hi : ℕ → S → ℕ)
    (plan : ∀ s tr a, StandAt T Said b front s tr a → sumTo (fun j => n j s) Lk.order.length ≤ a.F.planClaimsF)
    (fit : ∀ s tr a, StandAt T Said b front s tr a → Fitted Lk.order.length (fun j => own j s)
      (fun j => owe j s) tails (fun j => Ws j s) (fun j => Ds j s) whole)
    (laws : ∀ j, j < Lk.order.length → RunRecord (StandAt T Said b front) Lk p j (n j) (f j) (own j) (owe j) (tails j)
      (Ws j) (Ds j) (whole j) (lo j) (hi j)) :
    AcceptedS T Said fall b :=
  accepted_of_records_find T Sd hblk (none_at_batching Sd T.hs hno) fall front hfall ready clean rests cores sized n f
    tied own owe tails Ws Ds whole lo hi plan fit laws

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.SideKept.trans
#print axioms ProofFile.Honest.K9.StateKept.trans
#print axioms ProofFile.Honest.K9.StateKept.mono
#print axioms ProofFile.Honest.K9.Since.finds
#print axioms ProofFile.Honest.K9.Since.reads
#print axioms ProofFile.Honest.K9.Since.same
#print axioms ProofFile.Honest.K9.Since.window
#print axioms ProofFile.Honest.K9.each_of_named
#print axioms ProofFile.Honest.K9.RunRecord.mono
#print axioms ProofFile.Honest.K9.apart_of_spans
#print axioms ProofFile.Honest.K9.set_tl
#print axioms ProofFile.Honest.K9.draw_stateKept
#print axioms ProofFile.Honest.K9.called_frame
#print axioms ProofFile.Honest.K9.runPays_of_records
#print axioms ProofFile.Honest.K9.accepted_of_records_find
#print axioms ProofFile.Honest.K9.accepted_of_records
