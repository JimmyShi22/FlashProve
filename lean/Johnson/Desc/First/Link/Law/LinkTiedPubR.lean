-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTiedPubR.lean: THE LINK's THREE PIECES AND THE SHUTTING, TIED IN THE
SECOND FORM OF THE CHAIN OF PROMISES (`TiedAtR`) AT THE OWN PIECES OF THE IOP AS WRITTEN IN LEAN:
pieces over the public part and the verifier's state, with an extractor laid in that changes no
witness. LinkTiedPub.lean's four theorems, in the second form: with a condition Rch that every
accepting step hands on, beside the table's promise. Over the second form of the lift over the
public part (Johnson/Desc/Sound/TiedSeatR.lean: `tiedByR_of_part`). Definitions and theorems.

What is said.
  `RchAt Rch z`: the condition at the public part z. `tiedByR_of`: a piece's law and the seven
    clauses, with the kind's own four words named. `TiedAsksR`: all that `link_tied_atR` takes but
    the hand-ons, at the public part z. THE LAW's CONTEXT MAY HANG ON z (ctx : P → …): the context
    that the letters' debts are paid at (`ctxPins`, PinsBack.lean) does. `link_tied_pubR`:
    **`TiedAtR … (fun a => a) Rch k | k + 1 | k + 2` at the three pieces.** `behind_tied_pubR`: the
    second alone. `ShutOwesR`: what is left of the shutting's tie, each clause with Rch in hand.
    `shut_tiedByR`, `shut_tied_pubR`: **the shutting's tie.**

Limits. Rch is a letter. THE LISTS OF DEBTS STAND AS IN THE FIRST FORM, at weaker premises: nothing
is paid here. The hand-on of Rch at the pieces is other files' to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedPub
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- The condition at the public part z. -/
def RchAt {P : Type} {F : Frame} (Rch : ℕ → (P × S) × F.E.Str → Prop) (z : P) :
    ℕ → S × F.E.Str → Prop := fun k a => Rch k ((z, a.1), a.2)

/-- The law and the seven ties of the second form, with the kind's own four words named. -/
theorem tiedByR_of {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × First.S}
    {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {q : Piece C Fr A Cl W}
    {o o' : A × Fr.E.Str → Prop} {R R' : A × Fr.E.Str → W → Prop} (hl : q.GoodIn o o' R R')
    (T : TieOwesR N Mg links ps get Rch k q o o' R R') :
    TiedByR N Mg links ps get Rch k q o o' R R' :=
  ⟨hl, T.t1, T.t2, T.t3, T.t4, T.t5, T.mark, T.dec⟩

variable {α P W : Type} {F : Frame}

/-- **ALL THAT link_tied_atR TAKES BUT THE HAND-ONS, AT THE PUBLIC PART z.** -/
structure TiedAsksR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ)
    (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (sub : First.ModelPart) (L : Link S Claim)
    (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String)) (z : P) : Prop where
  A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
    (fun a => (onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a ∧ k9OnA a.1 = true) ∧
      C (fixed9 φ a.1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1 + 1))
    (fun a w => tabAt own (rdW w) a.1) ctx
  T : TableOwes (F := F) L φ tmOf lenOf (onTR Nm Mg links pl (fun s : S => (z, s)) Rz k)
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1))
    (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1)) Rd own rdW items
  h01 : ∀ a τ b', onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a →
    pb.ior.red.out a τ = some b' → onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) b'
  hR1 : ∀ a τ b', onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a →
    pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1)
  hR2 : ∀ a τ b', onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) a →
    pq.ior.red.out a τ = some b' → Rw b' → Rw a
  hR3 : ∀ a τ b', onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1) a →
    pe.ior.red.out a τ = some b' → Rw a
  Tb : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz k pb (relForms Rd own rdW items)
    (relTotB α L own rdW Rw ctx)
  Tq : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) pq (relTotB' α L own rdW Rw)
    (relTot own rdW Rw)
  Te : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1) pe (relTot own rdW Rw)
    (relRow own N rdW)

/-- **THE LINK's THREE PIECES, TIED IN THE SECOND FORM AT THE OWN PIECES OF THE IOP.** -/
theorem link_tied_pubR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
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
    (ctx : P → S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : ∀ z, TiedAsksR Nm Mg links pl (RchAt Rch z) k C Rw sub L φ Ok Fu p pw tmOf lenOf d N b₃
      (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) (ctx z) Rd own rdW items
      z) :
    TiedAtR Nm Mg links pl (fun a => a) Rch k (qb.withMap Eb) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1) (qq.withMap Eq) ∧
      TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1 + 1) (qe.withMap Ee) := by
  have g := fun z => link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃
    (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) _ _ _ _ (ctx z) Rd own rdW
    items (H z).A (H z).T (H z).h01 (H z).hR1 (H z).hR2 (H z).hR3
  exact ⟨(tiedByR_of_part Nm Mg links pl Rch k qb (below b₁) hqb Eb hEb _ _ _ _ fun z =>
      tiedByR_of (g z).1 (tieOwesR_of_rest (H z).Tb)).tiedAtR,
    (tiedByR_of_part Nm Mg links pl Rch (k + 1) qq (below b₂) hqq Eq hEq _ _ _ _ fun z =>
      tiedByR_of (g z).2.1 (tieOwesR_of_rest (H z).Tq)).tiedAtR,
    (tiedByR_of_part Nm Mg links pl Rch (k + 1 + 1) qe (below b₃) hqe Ee hEe _ _ _ _ fun z =>
      tiedByR_of (g z).2.2 (tieOwesR_of_rest (H z).Te)).tiedAtR⟩

/-- **THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING, ALONE.** -/
theorem behind_tied_pubR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (k : ℕ) (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (l : ℕ) (sub : First.ModelPart)
    (L : Link S Claim) (h : SegAt l sub L) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (hqq : qq.b = (below b₂).lift Prod.snd fun t s => (t.1, s))
    (Eq : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEq : ∀ a b w, Eq a b w = w)
    (ctx : P → S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (H : ∀ z, TiedAsksR Nm Mg links pl (RchAt Rch z) k C Rw sub L φ Ok Fu p pw tmOf lenOf d N b₃
      (atRec qb (below b₁)) (atRec qq (below b₂)) (atRec qe (below b₃)) (ctx z) Rd own rdW items
      z) :
    TiedAtR Nm Mg links pl (fun a => a) Rch (k + 1) (qq.withMap Eq) :=
  (tiedByR_of_part Nm Mg links pl Rch (k + 1) qq (below b₂) hqq Eq hEq _ _ _ _ fun z =>
    tiedByR_of (link_table C Rw l sub L h φ Ok Fu p pw tmOf lenOf d N b₃ (atRec qb (below b₁))
      (atRec qq (below b₂)) (atRec qe (below b₃)) _ _ _ _ (ctx z) Rd own rdW items (H z).A (H z).T
      (H z).h01 (H z).hR1 (H z).hR2 (H z).hR3).2.1 (tieOwesR_of_rest (H z).Tq)).tiedAtR

/-- **WHAT IS LEFT OF THE SHUTTING's TIE, SECOND FORM.** -/
structure ShutOwesR {C : CK} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (Rz : ℕ → S × F.E.Str → Prop) (z : P) (k : ℕ) (pw : Where) (piece : ℕ)
    (b₅ : Block S Claim) (ps : Piece C F S Claim W) : Prop where
  hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
    (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x
  hps : ps.b = below b₅
  hext : ∀ a τ w, ps.ext a τ w = w
  hins : (rowQ links pl k).ins = []
  hctx : (rowQ links pl k).ctx = []
  hands : ∀ a τ b, onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a →
    ps.ior.red.out a τ = some b → onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) b
  t5 : ∀ a τ b w i, onTR Nm Mg links pl (fun s : S => (z, s)) Rz k a →
    ps.ior.red.out a τ = some b → onQ Nm Mg links pl (fun s : S => (z, s)) (k + 1) b →
    relQ Nm Mg links pl (fun s : S => (z, s)) (k + 1) b w →
    openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
    meansQ Nm Mg (fun s : S => (z, s)) i a (ps.ext a τ w)
  dec : ∀ a τ b, ps.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf F a.2) →
    Mg.decodes (z, b.1) (strsOf F b.2)

/-- The shutting's tie of the second form, with the four words named. -/
theorem shut_tiedByR {C : CK} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (Rz : ℕ → S × F.E.Str → Prop) (z : P) (k : ℕ) (pw : Where) (piece : ℕ)
    (b₅ : Block S Claim) (ps : Piece C F S Claim W)
    (A : ShutOwesR Nm Mg links pl Rz z k pw piece b₅ ps) :
    TiedByR Nm Mg links pl (fun s : S => (z, s)) Rz k ps
      (onTR Nm Mg links pl (fun s : S => (z, s)) Rz k)
      (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1)) (fun _ _ => True)
      fun _ _ => True := by
  have hl : ps.GoodIn (onTR Nm Mg links pl (fun s : S => (z, s)) Rz k)
      (onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1)) (fun _ _ => True)
      (fun _ _ => True) :=
    shut_goodIn_yes pw piece b₅ A.hb₅ ps A.hps A.hext _ _ _ _ A.hands
      fun _ _ _ _ _ _ _ _ _ _ => trivial
  refine tiedByR_of hl (tieOwesR_of_rest
    ⟨fun _ _ _ _ _ _ _ _ => trivial, fun a τ b w ha _ _ _ _ => ?_, A.t5, ?_, A.dec⟩)
  · refine relAt_ins Nm Mg links pl _ k a _ ha.1.2 (fun i hi => ?_) fun i hi => ?_
    · rw [A.hins] at hi
      exact nomatch hi
    · rw [A.hctx] at hi
      exact nomatch hi
  · exact fun a τ b hout hm => shut_mark_yes pw piece b₅ A.hb₅ ps A.hps a b τ hout hm

/-- **THE SHUTTING, TIED IN THE SECOND FORM AT AN OWN PIECE OF THE IOP.** -/
theorem shut_tied_pubR {C : CK} (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (pl : List Place) (Rch : ℕ → (P × S) × F.E.Str → Prop) (k : ℕ) (pw : Where) (piece : ℕ)
    (b₅ : Block S Claim) (qs : Piece C F (P × S) Claim W)
    (hqs : qs.b = (below b₅).lift Prod.snd fun t s => (t.1, s))
    (Es : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) (hEs : ∀ a b w, Es a b w = w)
    (H : ∀ z, ShutOwesR Nm Mg links pl (RchAt Rch z) z k pw piece b₅ (atRec qs (below b₅))) :
    TiedAtR Nm Mg links pl (fun a => a) Rch k (qs.withMap Es) :=
  (tiedByR_of_part Nm Mg links pl Rch k qs (below b₅) hqs Es hEs _ _ _ _ fun z =>
    shut_tiedByR Nm Mg links pl (RchAt Rch z) z k pw piece b₅ _ (H z)).tiedAtR

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tiedByR_of
#print axioms VerifiableInference.Desc.LinkJoin.link_tied_pubR
#print axioms VerifiableInference.Desc.LinkJoin.behind_tied_pubR
#print axioms VerifiableInference.Desc.LinkJoin.shut_tied_pubR
