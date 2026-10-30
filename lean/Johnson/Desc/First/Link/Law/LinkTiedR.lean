-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTiedR.lean: THE LINK's THREE PIECES (the batching; the frame's
sub-protocol behind it; the one equation) TIED TO THE TABLE IN THE SECOND FORM OF THE CHAIN OF
PROMISES (`TiedAtR`, Johnson/Desc/Sound/ChainOfPromisesR.lean): WITH A CONDITION Rch THAT EVERY
ACCEPTING STEP HANDS ON, BESIDE THE TABLE's PROMISE. So every premise of the link's law that is
asked «at every statement that meets the promise» is asked only where Rch holds too: a fact that is
shown along the verifier's run may be spent in it. Definitions and theorems; LinkTied.lean's and
LinkTiedAt.lean's, in the second form.

What is said.
  `TieOwesR`: the seven clauses of `TiedAtR` behind the law, to the letter. `tiedAtR_of`: a piece's
    law and these give `TiedAtR`. `onTR … k`: the table's promise at border k, no mark, and Rch k.
    `TieRestR`: the five clauses that are left where the two conditions are `onTR`.
    `tieOwesR_of_rest`. `link_tied_atR`: **`EachTiedR … k [pb, pq, pe]` from the link's lists of
    debts (`LinkOwes`, `TableOwes`) AT THE CONDITIONS `onTR`, the hand-on of Rch at the three
    pieces, and `TieRestR` at each.**

Limits. Rch is a letter. THE LISTS OF DEBTS STAND AS THEY WERE, at weaker premises: nothing is paid
here. Whoever calls the rule for a file owes Rch at the state at the start. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedAt
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- **SEVEN DEBTS A PIECE, SECOND FORM**: the clauses of TiedAtR behind the law, to the letter. -/
structure TieOwesR {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
    (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop) : Prop where
  t1 : ∀ a, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → o a
  t2 : ∀ a τ b, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b
  t3 : ∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w → R' b w
  t4 : ∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
    R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)
  t5 : ∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
    relQ N Mg links ps get (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg get i a (q.ext a τ w)
  mark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
    (get b.1).2.failed ≠ none
  dec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
    Mg.decodes (get b.1) (strsOf Fr b.2)

/-- A piece's law and the seven give the tie of the second form. -/
theorem tiedAtR_of {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S}
    {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {q : Piece C Fr A Cl W}
    {o o' : A × Fr.E.Str → Prop} {R R' : A × Fr.E.Str → W → Prop} (g : q.GoodIn o o' R R')
    (T : TieOwesR N Mg links ps get Rch k q o o' R R') : TiedAtR N Mg links ps get Rch k q :=
  ⟨o, o', R, R', g, T.t1, T.t2, T.t3, T.t4, T.t5, T.mark, T.dec⟩

/-- **The table's promise at border k, no mark, and Rch k.** -/
def onTR {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) :
    A × Fr.E.Str → Prop :=
  fun a => onT N Mg links ps get k a ∧ Rch k a

/-- **FIVE DEBTS A PIECE, SECOND FORM**: what is left where the two conditions are onTR. -/
structure TieRestR {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
    (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (R R' : A × Fr.E.Str → W → Prop) : Prop where
  t3 : ∀ a τ b w, onTR N Mg links ps get Rch k a → q.ior.red.out a τ = some b →
    onTR N Mg links ps get Rch (k + 1) b →
    relAt (meansQ N Mg get) (outsQ links ps k) b w → R' b w
  t4 : ∀ a τ b w, onTR N Mg links ps get Rch k a → q.ior.red.out a τ = some b →
    onTR N Mg links ps get Rch (k + 1) b →
    relAt (meansQ N Mg get) (outsQ links ps k) b w →
    R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)
  t5 : ∀ a τ b w i, onTR N Mg links ps get Rch k a → q.ior.red.out a τ = some b →
    onQ N Mg links ps get (k + 1) b → relQ N Mg links ps get (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg get i a (q.ext a τ w)
  mark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
    (get b.1).2.failed ≠ none
  dec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
    Mg.decodes (get b.1) (strsOf Fr b.2)

theorem tieOwesR_of_rest {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S}
    {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {q : Piece C Fr A Cl W}
    {R R' : A × Fr.E.Str → W → Prop} (T : TieRestR N Mg links ps get Rch k q R R') :
    TieOwesR N Mg links ps get Rch k q (onTR N Mg links ps get Rch k)
      (onTR N Mg links ps get Rch (k + 1)) R R' where
  t1 _ ha hr hm := ⟨⟨ha, hm⟩, hr⟩
  t2 _ _ _ _ _ _ _ hb := hb.1.1
  t3 a τ b w ha hr hm := T.t3 a τ b w ⟨⟨ha, hm⟩, hr⟩
  t4 a τ b w ha hr hm := T.t4 a τ b w ⟨⟨ha, hm⟩, hr⟩
  t5 a τ b w i ha hr hm := T.t5 a τ b w i ⟨⟨ha, hm⟩, hr⟩
  mark := T.mark
  dec := T.dec

variable {α W : Type} {F : Frame}

/-- **THE LINK's THREE PIECES, TIED IN THE SECOND FORM, AT THE TABLE's OWN CONDITIONS WITH Rch.** -/
theorem link_tied_atR {P : Type} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (get : S → P × First.S) (Rch : ℕ → S × F.E.Str → Prop) (k : ℕ)
    (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (onTR Nm Mg links pl get Rch k a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1))
      (onTR Nm Mg links pl get Rch (k + 1)) (onTR Nm Mg links pl get Rch (k + 1 + 1))
      (onTR Nm Mg links pl get Rch (k + 1 + 1 + 1)) (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes (F := F) L φ tmOf lenOf (onTR Nm Mg links pl get Rch k)
      (onTR Nm Mg links pl get Rch (k + 1)) (onTR Nm Mg links pl get Rch (k + 1 + 1)) Rd own rdW
      items)
    (h01 : ∀ a τ b', onTR Nm Mg links pl get Rch k a → pb.ior.red.out a τ = some b' →
      onTR Nm Mg links pl get Rch (k + 1) b')
    (hR1 : ∀ a τ b', onTR Nm Mg links pl get Rch k a → pb.ior.red.out a τ = some b' → Rw b' →
      C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', onTR Nm Mg links pl get Rch (k + 1) a → pq.ior.red.out a τ = some b' →
      Rw b' → Rw a)
    (hR3 : ∀ a τ b', onTR Nm Mg links pl get Rch (k + 1 + 1) a → pe.ior.red.out a τ = some b' →
      Rw a)
    (Hb : HandsOn Rch k pb) (Hq : HandsOn Rch (k + 1) pq) (He : HandsOn Rch (k + 1 + 1) pe)
    (Tb : TieRestR Nm Mg links pl get Rch k pb (relForms Rd own rdW items)
      (relTotB α L own rdW Rw ctx))
    (Tq : TieRestR Nm Mg links pl get Rch (k + 1) pq (relTotB' α L own rdW Rw)
      (relTot own rdW Rw))
    (Te : TieRestR Nm Mg links pl get Rch (k + 1 + 1) pe (relTot own rdW Rw)
      (relRow own N rdW)) :
    EachTiedR Nm Mg links pl get Rch k [pb, pq, pe] := by
  obtain ⟨g1, g2, g3⟩ := link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃ pb pq pe _ _ _ _
    ctx Rd own rdW items A T h01 hR1 hR2 hR3
  exact ⟨tiedAtR_of g1 (tieOwesR_of_rest Tb), Hb, tiedAtR_of g2 (tieOwesR_of_rest Tq), Hq,
    tiedAtR_of g3 (tieOwesR_of_rest Te), He, trivial⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tiedAtR_of
#print axioms VerifiableInference.Desc.LinkJoin.tieOwesR_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.link_tied_atR
