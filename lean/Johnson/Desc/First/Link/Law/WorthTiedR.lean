-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/WorthTiedR.lean: `ThreeAsksR` (ThreeTiedR.lean: the three laws of a
link's pieces and five debts a piece, at the public part z) FROM THE LAW OF A LINK THAT HAS THE TWO
SENTENCES ON WORTHS IN ITS FRONT RELATION (`link_table_worth`, WorthAtFront.lean),
laid at the four conditions «the table's promise, no mark, reached» (`onTR`). A call; no more.

What is said.
  `relFW`: the law's own relation in front of the batching: the listed runs' forms are worth 0, and
    the two sentences. (Its four other relations have names already: `relTotB`, `relTotB'`,
    `relTot`, `relRow`, LinkTied.lean.) `threeAsksR_of_worth`: **`ThreeAsksR Nm Mg links pl Rz k pb
    pq pe relFW relTotB relTotB' relTot relRow z` from that law's own list of premises at these
    conditions and `TieRestR` at the three pieces at these relations.**

Limits. BOOK-KEEPING. EVERY PREMISE OF THAT LAW STANDS AS A PREMISE HERE, to the letter (cut by
program out of its statement, the four conditions laid in); so do the fifteen ties. Nothing is paid.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WorthAtFront
import Johnson.Desc.First.Link.Law.ThreeTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open _root_.Run (ckP)

variable {α Cells Tok : Type} {F : Sound.Frame}

/-- In front of the batching: the listed runs' forms are worth 0, and the two sentences. -/
def relFW (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String)) (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) :
    S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop :=
  fun a w => (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
    WorthTwo fork heard x tlD D rad seatT arr a.1 w

variable {P : Type} (Nm : Numbers) (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (links : List ModelPart)
  (pl : List Place) (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (z : P)

local notation "o0" => onTR Nm Mg links pl (fun s : S => (z, s)) Rz k
local notation "o1" => onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1)
local notation "o2" => onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1)
local notation "o3" => onTR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1 + 1)

/-- **THE THREE LAWS AND FIVE DEBTS A PIECE, FROM THE LAW WITH THE TWO SENTENCES.** -/
theorem threeAsksR_of_worth (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Desc.Wit Cells Tok MsgT))
    (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) (FullAt nU) p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (o0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) o1 o2 o3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes L φ tmOf lenOf o0 o1 o2 Rd own rdW items)
    (h01 : ∀ a τ b', o0 a → pb.ior.red.out a τ = some b' → o1 b')
    (hR1 : ∀ a τ b', o0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', o1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', o2 a → pe.ior.red.out a τ = some b' → Rw a)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, (Ok q ∧ C q) → q.2 = some v → (π q.1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ (fun q => Ok q ∧ C q) q t → FullAt nU t →
      atS.get? t = some b → (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard) (x : First.Look.Place)
    (tlD : HTailF2) (D : First.Look.Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {set : Params.Setting}
    {pp : ℕ} (HD : DigOK set x tlD D rad pp) (hfk : ∀ s, fork s = s.fork?)
    (hhd : ∀ s, heard s = s.tl?.bind (·.heard))
    (hRest : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' →
      boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a (pb.ext a τ w₀) y →
      ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ)
        (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t = some b →
      k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
      b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
      blank u tl = blank u tlX → tl.heard = some g →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 φ (fun q => Ok q ∧ C q) (fixed9 φ a.1) e → Fx9 φ (fun q => Ok q ∧ C q) (fixed9 φ a.1) t →
      laterK atS (O9 (K := GE8) φ (fun q => Ok q ∧ C q) (FullAt nU)) ((e.putTl tl').putFork F1) t →
      DigitsRest x tlD D rad seatT arr (pb.ext a τ w₀) g tl tlX Fc c b.L y)
    (Tb : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz k pb
      (relFW Rd own rdW items fork heard x tlD D rad seatT arr) (relTotB α L own rdW Rw ctx))
    (Tq : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1) pq (relTotB' α L own rdW Rw)
      (relTot own rdW Rw))
    (Te : TieRestR Nm Mg links pl (fun s : S => (z, s)) Rz (k + 1 + 1) pe (relTot own rdW Rw)
      (relRow own N rdW)) :
    ThreeAsksR Nm Mg links pl Rz k pb pq pe
      (relFW Rd own rdW items fork heard x tlD D rad seatT arr) (relTotB α L own rdW Rw ctx)
      (relTotB' α L own rdW Rw) (relTot own rdW Rw) (relRow own N rdW) z :=
  have g := link_table_worth C Rw l sub L h φ Ok nU p pw tmOf lenOf d N b₃ pb pq pe o0 o1 o2 o3 ctx
    Rd own rdW items A T h01 hR1 hR2 hR3 u π hπ hkeep ent hOk4 hFu4 o ho run hAt hu ht fork heard x
    tlD D rad seatT arr HD hfk hhd hRest
  ⟨g.1, g.2.1, g.2.2, Tb, Tq, Te⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.threeAsksR_of_worth
