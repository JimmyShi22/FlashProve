-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WorthLeft.lean: THE LAW OF A LINK AS THREE CORE LAWS IN THE TABLE's
LETTERS, WITH THE TWO SENTENCES BESIDE THE FORMS IN FRONT OF THE BATCHING (`link_table_worth`,
WorthAtFront.lean), WITH TWO OF ITS PREMISES PAID AND ONE LETTER A TERM. One theorem, by one call.
  `link_table_worth_left`: `link_table_worth`'s own premises and end, but: the letter ent is the
    term `ent4 π` (FullFour.lean); hFu4 is paid by `hFu4_full`; hRest is paid by `hRest_of`
    (RestStatic.lean). In their place three: okDig (`DigStatic` at the fixed structure and the
    snapshot's ledger; its field coef pays `hFu4_full`'s okCoef), okEnts (an entry that one of the
    four claims' forms names stands at a row whose weights the four read), hLeft (hRest's own text
    with `DigitsLeft` at its end).
Limits. Nothing new is proved: Lean holds here that the payers fit the law's binders. The three
premises are shown of nothing here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RestStatic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open _root_.Run (ckP)

variable {α Cells Tok : Type} {F : Sound.Frame}

/-- **THE LAW OF A LINK, WITH hFu4 AND hRest PAID.** -/
theorem link_table_worth_left (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Desc.Wit Cells Tok MsgT))
    (on0 on1 on2 on3 : S × F.E.Str → Prop) (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : Desc.Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) (FullAt nU) p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes L φ tmOf lenOf on0 on1 on2 Rd own rdW items)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (hOk4 : ∀ q v tlb g, (Ok q ∧ C q) → q.2 = some v → (π q.1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π (ent4 π) q y) ++ tmRest π q y)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard) (x : First.Look.Place)
    (tlD : HTailF2) (D : First.Look.Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {set : Params.Setting}
    {pp : ℕ} (HD : DigOK set x tlD D rad pp) (hfk : ∀ s, fork s = s.fork?)
    (hhd : ∀ s, heard s = s.tl?.bind (·.heard))
    (okDig : ∀ q tlb v, (Ok q ∧ C q) → (π q.1).1 = some tlb → q.2 = some v →
      DigStatic tlD tlb v.F)
    (okEnts : ∀ q tlb g, (Ok q ∧ C q) → (π q.1).1 = some tlb → tlb.heard = some g →
      ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row)
    (hLeft : ∀ a τ b' w₀ y, on0 a → pb.ior.red.out a τ = some b' →
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
      DigitsLeft x tlD D rad seatT arr (pb.ext a τ w₀) g tl c b.L y) :
    pb.GoodIn on0 on1
        (fun a w => (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧
          WorthTwo fork heard x tlD D rad seatT arr a.1 w)
        (fun b w =>
          (totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b.1 (rdW w) ∧ Rw b) ∧
            ctx b w) ∧
      pq.GoodIn on1 on2
        (fun a w => totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own a.1 (rdW w) ∧ Rw a)
        (fun b w => totalQ own b.1 (rdW w) ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => totalQ own a.1 (rdW w) ∧ Rw a)
        (fun e w => rowEqQ own N e.1 (rdW w)) :=
  link_table_worth
    C Rw l sub L h φ Ok nU p pw tmOf lenOf d N b₃ pb pq pe on0 on1 on2 on3 ctx Rd own rdW items A
    T h01 hR1 hR2 hR3 u π hπ hkeep (ent4 π) hOk4
    (hFu4_full π φ (fun q => Ok q ∧ C q) nU u hπ
      (fun q tlb v h h1 hv => (okDig q tlb v h h1 hv).coef) okEnts)
    o ho run hAt hu ht fork heard x tlD D rad seatT arr HD hfk hhd
    fun a τ b' w₀ y ha hout hbd =>
      hRest_of L φ (fun q => Ok q ∧ C q) nU u π hπ x tlD D rad seatT arr a b' y (pb.ext a τ w₀)
        okDig (hLeft a τ b' w₀ y ha hout hbd)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_table_worth_left
