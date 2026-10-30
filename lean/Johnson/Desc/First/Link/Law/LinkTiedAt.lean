-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTiedAt.lean: THE LINK's THREE PIECES TIED TO THE TABLE, WITH THE
FOUR CONDITIONS CLOSED: at each of the four boundaries the kind's own condition := THE TABLE's OWN
PROMISE THERE, AT AN UNMARKED STATEMENT (`onT`). Then the first two of a piece's seven ties
(LinkTied.lean: `TieOwes.t1`, `t2`) hold outright. A definition, a list of five debts a piece, and
three theorems.

Why. The first tie wants a kind's condition weak (the table's promise must give it); the kind's law
wants it strong (it is all that the law may lean on). The strongest condition that the first tie
bears is the promise itself, with «no mark». With it no letter is left for the four conditions: what
the law takes of them (`OwesConds`, `TableOwes`, the three premises on the public sentence) becomes
sentences on the table's promise: some say what the promise gives at a boundary; three say that the
promise, and «no mark», ride over a block's yes.

What is said.
  `onT … k`: the table's promise at boundary k, and no mark. `TieRest`: the five ties that are left
    of a piece's seven: t3, t4, t5, mark, dec, to the letter, at the condition behind := `onT … (k +
    1)`. `tieOwes_of_rest`: they give `TieOwes` at `onT`. `link_tied_at`: **`link_tied` at on0 … on3
    := `onT … k` … `onT … (k + 3)`: from `LinkOwes` and `TableOwes` there, and `TieRest` at each of
    the three pieces: `EachTied … k [pb, pq, pe]`.**

Limits. AN IMPLICATION: shown of no record of the protocol. Six of the 21 ties are paid BY A CHOICE,
not by a proof on the protocol: their weight lies now in `OwesConds.h01`, `h12`, `hon3` at `onT`:
that the table's promise and «no mark» ride over a yes of each of the three blocks. k is free, as in
LinkTied.lean. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTied

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

/-- **The table's promise at boundary k, and no mark.** -/
def onT {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) : A × Fr.E.Str → Prop :=
  fun a => onQ N Mg links ps get k a ∧ ¬ (get a.1).2.failed ≠ none

/-- **FIVE DEBTS A PIECE**: what is left of TieOwes where the two conditions are the table's own. -/
structure TieRest {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (R R' : A × Fr.E.Str → W → Prop) : Prop where
  /-- OWES the filling of the table's letters: what the block's row opens, with what it reads and
  «no mark», gives the kind's own relation behind -/
  t3 : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → onT N Mg links ps get (k + 1) b →
    relAt (meansQ N Mg get) (outsQ links ps k) b w → R' b w
  /-- OWES the filling of the table's letters: the kind's own relation in front gives what the
  block's row closes, with what it reads and «no mark» -/
  t4 : ∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → onT N Mg links ps get (k + 1) b →
    relAt (meansQ N Mg get) (outsQ links ps k) b w →
    R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)
  /-- OWES what rides over the block: an item that is open behind the block and that its row does
  not close holds in front -/
  t5 : ∀ a τ b w i, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
    relQ N Mg links ps get (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg get i a (q.ext a τ w)
  /-- OWES the block's own text: a mark stays -/
  mark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
    (get b.1).2.failed ≠ none
  /-- OWES the block's own text: «the stored table decodes with the record» rides -/
  dec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
    Mg.decodes (get b.1) (strsOf Fr b.2)

/-- The five give the seven, at the table's own conditions. -/
theorem tieOwes_of_rest {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S} {k : ℕ} {q : Piece C Fr A Cl W}
    {R R' : A × Fr.E.Str → W → Prop} (T : TieRest N Mg links ps get k q R R') :
    TieOwes N Mg links ps get k q (onT N Mg links ps get k) (onT N Mg links ps get (k + 1)) R R' :=
  ⟨fun _ h hu => ⟨h, hu⟩, fun _ _ _ _ _ _ h => h.1, T.t3, T.t4, T.t5, T.mark, T.dec⟩

variable {α W : Type} {F : Frame}

/-- **THE LINK's THREE PIECES, TIED TO THE TABLE, AT THE TABLE's OWN CONDITIONS.** -/
theorem link_tied_at {P : Type} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (get : S → P × First.S) (k : ℕ)
    (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (onT Nm Mg links pl get k a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1))
      (onT Nm Mg links pl get (k + 1)) (onT Nm Mg links pl get (k + 1 + 1))
      (onT Nm Mg links pl get (k + 1 + 1 + 1)) (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes (F := F) L φ tmOf lenOf (onT Nm Mg links pl get k)
      (onT Nm Mg links pl get (k + 1)) (onT Nm Mg links pl get (k + 1 + 1)) Rd own rdW items)
    (h01 : ∀ a τ b', onT Nm Mg links pl get k a → pb.ior.red.out a τ = some b' →
      onT Nm Mg links pl get (k + 1) b')
    (hR1 : ∀ a τ b', onT Nm Mg links pl get k a → pb.ior.red.out a τ = some b' → Rw b' →
      C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', onT Nm Mg links pl get (k + 1) a → pq.ior.red.out a τ = some b' → Rw b' →
      Rw a)
    (hR3 : ∀ a τ b', onT Nm Mg links pl get (k + 1 + 1) a → pe.ior.red.out a τ = some b' → Rw a)
    (Tb : TieRest Nm Mg links pl get k pb (relForms Rd own rdW items)
      (relTotB α L own rdW Rw ctx))
    (Tq : TieRest Nm Mg links pl get (k + 1) pq (relTotB' α L own rdW Rw) (relTot own rdW Rw))
    (Te : TieRest Nm Mg links pl get (k + 1 + 1) pe (relTot own rdW Rw) (relRow own N rdW)) :
    EachTied Nm Mg links pl get k [pb, pq, pe] :=
  link_tied Nm Mg links pl get k C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃ pb pq pe _ _ _ _ ctx
    Rd own rdW items A T h01 hR1 hR2 hR3 (tieOwes_of_rest Tb) (tieOwes_of_rest Tq)
    (tieOwes_of_rest Te)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tieOwes_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.link_tied_at
