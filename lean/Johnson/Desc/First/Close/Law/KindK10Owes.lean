-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10Owes.lean (kind K10): K10's ONE NAMED CONDITION, SECOND FORM:
THE FIFTH TIE IS NO FIELD ANY MORE. Definitions, a statement and its proof. A file BESIDE the table
of joints: it turns nothing of it.

Why. `K10CondAt` (KindK10.lean, beside this file) has the fifth tie of `TiedAtR` as a field, word
for word (back): a part of the join's own conclusion. `k10_back_of_sides` (KindK10Riders.lean) gets
it from two sentences that are no kind's and one that is this kind's own. Here these three stand in
its place; the extractor is the table's own (`extQAt`, Johnson/Desc/Sound/BordersFill.lean), no
letter.
  `K10OwesAt .. k q₀ o Fn base`: at one place: `K10CondAt`'s fields law, front, fence, asks, dec,
    kept, trees, msgs, step, at the piece q₀ with the table's extractor at number k; and ride:
    inside the fence (the promise and "reached" in front, no mark, the piece's out, the promise
    behind): every item that is open at border k and that the sub-protocol neither closes nor reads
    holds in front if it holds behind, OF ONE WITNESS.
  `K10Owes .. l`: (1) at every place of the kind K10: a rider reads of the witness only what the
    table says (`ReadsOkAtQR`); (2) what riders read is clear of what rows lay (`RidersClearQ`); (3)
    at every place of the kind K10 there are o, Fn, base with `K10OwesAt`.
  `k10_cond_of_owes`: `K10Owes` gives `K10Cond` at E := the table's extractor. `k10_kind_of_owes`:
    so `KindTiedR .. .K10`.
Limits. A BUNDLING: `K10Owes` IS SHOWN OF NOTHING. ONE FIELD STILL NAMES A PART OF THE CONCLUSION:
law (`GoodIn`): `k10_law_withMap` (KindK10Law.lean) brings it down to one sentence hQ and the proved
sub-protocol's premises on the typed stage: not laid in here. (1) and (2) are no kind's: whoever
joins the kinds may ask them once. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.KindK10Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj Johnson.Pack
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart start openSets pubSets closersFit
  closersNext)

section
variable (cs : OnBytes.Codes) {Xi Pz Cells Tok Cl : Type} {F : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pz × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : Pz × VerifiableInference.Desc.First.S → Tok)
  (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)

/-- **THE CONDITION AT ONE PLACE, SECOND FORM.** -/
structure K10OwesAt (k : ℕ)
    (q₀ : Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl (Wit Cells Tok MsgT))
    (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
    (Fn : VerifiableInference.Desc.First.S → Prop) (base : ℕ) : Prop where
  /-- the piece's law, at the pick, with the table's extractor -/
  law : (q₀.withMap (extQAt cs G arr smp ms decT c₀ tokOf Nu links ps (fun a => a) k)).GoodIn o
    (fun _ => True) (relAt (meansQ Nu Mg fun a => a) (insQ links ps k))
    (relAt (meansQ Nu Mg fun a => a) (outsQ links ps k))
  /-- the first tie -/
  front : ∀ a, onQ Nu Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none → o a
  /-- "reached" gives the fence -/
  fence : ∀ a, Rch k a → Fn a.1.2
  /-- what the second tie asks of the meaning, at the fenced states -/
  asks : K10AsksR Fn Nu Mg ((openSets links ps (start links))[k]?.getD [])
    ((openSets links ps (start links))[k + 1]?.getD []) ((pubSets Mg.more links ps)[k]?.getD [])
    ((pubSets Mg.more links ps)[k + 1]?.getD []) (Behind F base)
  /-- "decodes" rides along K10's step, at every state -/
  dec : ∀ z s s' y y', K10Step s s' → Behind F base y y' → Mg.decodes (z, s) y →
    Mg.decodes (z, s') y'
  /-- what is kept lies in its group -/
  kept : ∀ p, ps[k]? = some p → ∀ t ∈ Nu.keptOf (p.link.getD 0), t ∈ Nu.group (p.link.getD 0)
  /-- the sub-protocol sends no tree -/
  trees : Nu.treesAt ps[k + 1]? = Nu.treesAt ps[k]?
  /-- and no message -/
  msgs : Nu.msgsAt ps[k + 1]? = Nu.msgsAt ps[k]?
  /-- what rides past holds in front if it holds behind, of one witness -/
  ride : ∀ a τ b w i, onQ Nu Mg links ps (fun a => a) k a → Rch k a → a.1.2.failed = none →
    q₀.ior.red.out a τ = some b → onQ Nu Mg links ps (fun a => a) (k + 1) b →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ Nu Mg (fun a => a) i b w → meansQ Nu Mg (fun a => a) i a w
  /-- what the piece's out holds -/
  step : ∀ a τ b, q₀.ior.red.out a τ = some b →
    b.1.1 = a.1.1 ∧ K10Step a.1.2 b.1.2 ∧ Behind F base (strsOf F a.2) (strsOf F b.2)

variable (l : List (Piece (ckP .two) F (Pz × VerifiableInference.Desc.First.S) Cl
  (Wit Cells Tok MsgT)))

/-- **THE ONE CONDITION FOR THIS KIND OF STEP, SECOND FORM.** -/
structure K10Owes : Prop where
  /-- a rider reads of the witness only what the table says: no kind's -/
  reads : ∀ i a, ps[i]? = some a → a.kind = KindName.K10 →
    ReadsOkAtQR arr Nu Mg links ps (fun a => a) Rch i
  /-- what riders read is clear of what rows lay: the table's -/
  clear : RidersClearQ arr Nu links ps
  /-- the kind's own, place by place -/
  own : ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = KindName.K10 →
    ∃ (o : (Pz × VerifiableInference.Desc.First.S) × F.E.Str → Prop)
      (Fn : VerifiableInference.Desc.First.S → Prop) (base : ℕ),
      K10OwesAt cs G arr smp ms decT c₀ tokOf Nu Mg links ps Rch i q o Fn base

/-- **The second form gives the first**, at the table's extractor. -/
theorem k10_cond_of_owes (W : K10Owes cs G arr smp ms decT c₀ tokOf Nu Mg links ps Rch l) :
    K10Cond Nu Mg links ps Rch (extQAt cs G arr smp ms decT c₀ tokOf Nu links ps fun a => a) l := by
  intro i q a hq ha hk
  obtain ⟨o, Fn, base, h⟩ := W.own i q a hq ha hk
  exact ⟨o, Fn, base, h.law, h.front, h.fence, h.asks, h.dec, h.kept, h.trees, h.msgs,
    k10_back_of_sides cs G arr smp ms decT c₀ tokOf Nu Mg links ps Rch i q (W.reads i a ha hk)
      W.clear h.ride, h.step⟩

/-- **K10's SHARE OF THE CHAIN OF PROMISES, SECOND FORM, FROM THE CONDITION's SECOND FORM.** -/
theorem k10_kind_of_owes (hF : closersFit links ps (start links) = true)
    (hX : closersNext links ps = true)
    (W : K10Owes cs G arr smp ms decT c₀ tokOf Nu Mg links ps Rch l) :
    KindTiedR Nu Mg links ps Rch (extQAt cs G arr smp ms decT c₀ tokOf Nu links ps fun a => a) l
      .K10 :=
  k10_kind Nu Mg links ps Rch _ l hF hX
    (k10_cond_of_owes cs G arr smp ms decT c₀ tokOf Nu Mg links ps Rch l W)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_cond_of_owes
#print axioms VerifiableInference.Desc.First.Close.k10_kind_of_owes
