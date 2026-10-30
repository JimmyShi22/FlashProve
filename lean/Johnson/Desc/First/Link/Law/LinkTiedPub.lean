-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTiedPub.lean: THE LINK's THREE PIECES, AND THE SHUTTING, TIED TO THE
TABLE AT A DESCRIPTION's OWN PIECES: over the pair of the public part and the record, the table read
at the identity, the table's extractor laid in (`q.withMap E`): the form in which the chain of
promises is paid place by place (Johnson/Desc/Sound/TiedPlaces.lean: `KindTied`). A list and five
theorems: a carriage of LinkTiedAt.lean and ShutTied.lean by Johnson/Desc/Sound/TiedLift.lean's
`tiedBy_of_part`.

What is said.
  `atRec q b₀`: the piece over the record that holds the block b₀, with q's own stretch, rounds put
    back and errors, and the identity for its extractor. `tiedBy_of`: the law and `TieOwes` give
    `TiedBy`. `TiedAsks … z`: all that `link_tied_at` takes, at the public part z, at the three
    pieces `atRec`. `link_tied_pub`: **if three pieces of a description hold the link's three blocks
    lifted over the public part, the table's extractor lays nothing at their rows, and `TiedAsks`
    holds at every z: each of the three, with that extractor, is tied at its number: k, k + 1, k +
    2.** `behind_tied_pub`: the second alone: the frame's block behind the batching. `shut_tiedBy`:
    the shutting's tie (ShutTied.lean) with its four words named. `shut_tied_pub`: the like for the
    shutting, from `ShutOwes` at every z.

Limits. A CARRIAGE: AN IMPLICATION: shown of no record of the protocol. «At every z»: also at public
parts that no run reaches. The law of the frame's block behind the batching cannot be had apart from
its two neighbours': one argument goes over the three: so `behind_tied_pub` takes the whole list.
The challenge set is the two-element field's extension's (`ckP .two`), as in the batching kind's
law. k is free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ShutTied
import Johnson.Desc.Sound.TiedLift

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

/-- The piece over the record that holds b₀, with q's own stretch, rounds put back and errors. -/
def atRec {P Cl W : Type} {C : CK} {F : Frame} (q : Piece C F (P × S) Cl W) (b₀ : Block S Cl) :
    Piece C F S Cl W := ⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩

/-- The law and the seven ties, with the kind's own four words named. -/
theorem tiedBy_of {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S} {k : ℕ} {q : Piece C Fr A Cl W}
    {o o' : A × Fr.E.Str → Prop} {R R' : A × Fr.E.Str → W → Prop} (hl : q.GoodIn o o' R R')
    (T : TieOwes N Mg links ps get k q o o' R R') : TiedBy N Mg links ps get k q o o' R R' :=
  ⟨hl, T.t1, T.t2, T.t3, T.t4, T.t5, T.mark, T.dec⟩

variable {α P W : Type} {F : Frame}

/-- **ALL THAT link_tied_at TAKES, AT THE PUBLIC PART z.** -/
structure TiedAsks (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (k : ℕ)
    (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (sub : First.ModelPart) (L : Link S Claim)
    (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String)) (z : P) : Prop where
  A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
    (fun a => (onT Nm Mg links pl (fun s : S => (z, s)) k a ∧ k9OnA a.1 = true) ∧
      C (fixed9 φ a.1))
    (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1))
    (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1 + 1))
    (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1 + 1 + 1))
    (fun a w => tabAt own (rdW w) a.1) ctx
  T : TableOwes (F := F) L φ tmOf lenOf (onT Nm Mg links pl (fun s : S => (z, s)) k)
    (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1))
    (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1 + 1)) Rd own rdW items
  h01 : ∀ a τ b', onT Nm Mg links pl (fun s : S => (z, s)) k a → pb.ior.red.out a τ = some b' →
    onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b'
  hR1 : ∀ a τ b', onT Nm Mg links pl (fun s : S => (z, s)) k a → pb.ior.red.out a τ = some b' →
    Rw b' → C (fixed9 φ a.1)
  hR2 : ∀ a τ b', onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) a →
    pq.ior.red.out a τ = some b' → Rw b' → Rw a
  hR3 : ∀ a τ b', onT Nm Mg links pl (fun s : S => (z, s)) (k + 1 + 1) a →
    pe.ior.red.out a τ = some b' → Rw a
  Tb : TieRest Nm Mg links pl (fun s : S => (z, s)) k pb (relForms Rd own rdW items)
    (relTotB α L own rdW Rw ctx)
  Tq : TieRest Nm Mg links pl (fun s : S => (z, s)) (k + 1) pq (relTotB' α L own rdW Rw)
    (relTot own rdW Rw)
  Te : TieRest Nm Mg links pl (fun s : S => (z, s)) (k + 1 + 1) pe (relTot own rdW Rw)
    (relRow own N rdW)

/-- **THE LINK's THREE PIECES, TIED AT A DESCRIPTION's OWN PIECES.** -/
theorem link_tied_pub (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (k : ℕ) (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (l : ℕ) (sub : First.ModelPart)
    (L : Link S Claim) (h : SegAt l sub L) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (hqb : qb.b = (below b₁).lift Prod.snd fun t s => (t.1, s))
    (hqq : qq.b = (below b₂).lift Prod.snd fun t s => (t.1, s))
    (hqe : qe.b = (below b₃).lift Prod.snd fun t s => (t.1, s))
    (Eb Eq Ee : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEb : ∀ a b w, Eb a b w = w)
    (hEq : ∀ a b w, Eq a b w = w) (hEe : ∀ a b w, Ee a b w = w)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : ∀ z, TiedAsks Nm Mg links pl k C Rw sub L φ Ok Fu p pw tmOf lenOf d N b₃
      (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) ctx Rd own rdW items z) :
    TiedAt Nm Mg links pl (fun a => a) k (qb.withMap Eb) ∧
      TiedAt Nm Mg links pl (fun a => a) (k + 1) (qq.withMap Eq) ∧
      TiedAt Nm Mg links pl (fun a => a) (k + 1 + 1) (qe.withMap Ee) := by
  have g := fun z => link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃
    (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) _ _ _ _ ctx Rd own rdW items
    (H z).A (H z).T (H z).h01 (H z).hR1 (H z).hR2 (H z).hR3
  exact ⟨(tiedBy_of_part Nm Mg links pl k qb (below b₁) hqb Eb hEb _ _ _ _ fun z =>
      tiedBy_of (g z).1 (tieOwes_of_rest (H z).Tb)).tiedAt,
    (tiedBy_of_part Nm Mg links pl (k + 1) qq (below b₂) hqq Eq hEq _ _ _ _ fun z =>
      tiedBy_of (g z).2.1 (tieOwes_of_rest (H z).Tq)).tiedAt,
    (tiedBy_of_part Nm Mg links pl (k + 1 + 1) qe (below b₃) hqe Ee hEe _ _ _ _ fun z =>
      tiedBy_of (g z).2.2 (tieOwes_of_rest (H z).Te)).tiedAt⟩

/-- **THE FRAME's BLOCK BEHIND THE BATCHING, TIED AT A DESCRIPTION's OWN PIECE.** -/
theorem behind_tied_pub (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (k : ℕ) (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (l : ℕ) (sub : First.ModelPart)
    (L : Link S Claim) (h : SegAt l sub L) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (hqq : qq.b = (below b₂).lift Prod.snd fun t s => (t.1, s))
    (Eq : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEq : ∀ a b w, Eq a b w = w)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : ∀ z, TiedAsks Nm Mg links pl k C Rw sub L φ Ok Fu p pw tmOf lenOf d N b₃
      (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) ctx Rd own rdW items z) :
    TiedAt Nm Mg links pl (fun a => a) (k + 1) (qq.withMap Eq) :=
  (tiedBy_of_part Nm Mg links pl (k + 1) qq (below b₂) hqq Eq hEq _ _ _ _ fun z =>
    tiedBy_of (link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃ (atRec qb (below b₁))
      (atRec qq (below b₂)) (atRec qe (below b₃)) _ _ _ _ ctx Rd own rdW items (H z).A (H z).T
      (H z).h01 (H z).hR1 (H z).hR2 (H z).hR3).2.1 (tieOwes_of_rest (H z).Tq)).tiedAt

/-- The shutting's tie, with the four words named. -/
theorem shut_tiedBy {C : CK} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (z : P) (k : ℕ) (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (ps : Piece C F S Claim W) (A : ShutOwes Nm Mg links pl z k pw piece b₅ ps) :
    TiedBy Nm Mg links pl (fun s : S => (z, s)) k ps (onT Nm Mg links pl (fun s : S => (z, s)) k)
      (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1)) (fun _ _ => True) fun _ _ => True := by
  have hl : ps.GoodIn (onT Nm Mg links pl (fun s : S => (z, s)) k)
      (onT Nm Mg links pl (fun s : S => (z, s)) (k + 1)) (fun _ _ => True) (fun _ _ => True) :=
    shut_goodIn_yes pw piece b₅ A.hb₅ ps A.hps A.hext _ _ _ _ A.hands
      fun _ _ _ _ _ _ _ _ _ _ => trivial
  refine tiedBy_of hl (tieOwes_of_rest
    ⟨fun _ _ _ _ _ _ _ _ _ => trivial, fun a τ b w _ hu _ _ _ _ => ?_, A.t5, ?_, A.dec⟩)
  · refine relAt_ins Nm Mg links pl _ k a _ hu (fun i hi => ?_) fun i hi => ?_
    · rw [A.hins] at hi
      exact nomatch hi
    · rw [A.hctx] at hi
      exact nomatch hi
  · exact fun a τ b hout hm => shut_mark_yes pw piece b₅ A.hb₅ ps A.hps a b τ hout hm

/-- **THE SHUTTING, TIED AT A DESCRIPTION's OWN PIECE.** -/
theorem shut_tied_pub {C : CK} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (k : ℕ) (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (qs : Piece C F (P × S) Claim W)
    (hqs : qs.b = (below b₅).lift Prod.snd fun t s => (t.1, s))
    (Es : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEs : ∀ a b w, Es a b w = w)
    (H : ∀ z, ShutOwes Nm Mg links pl z k pw piece b₅ (atRec qs (below b₅))) :
    TiedAt Nm Mg links pl (fun a => a) k (qs.withMap Es) :=
  (tiedBy_of_part Nm Mg links pl k qs (below b₅) hqs Es hEs _ _ _ _ fun z =>
    shut_tiedBy Nm Mg links pl z k pw piece b₅ _ (H z)).tiedAt

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tiedBy_of
#print axioms VerifiableInference.Desc.LinkJoin.link_tied_pub
#print axioms VerifiableInference.Desc.LinkJoin.behind_tied_pub
#print axioms VerifiableInference.Desc.LinkJoin.shut_tied_pub
