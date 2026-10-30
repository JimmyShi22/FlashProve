-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WorthAtFront.lean: THE TWO ITEMS OF THE SORT "worth" THAT THE BATCHING's
ROW OF THE TABLE OF JOINTS CLOSES BESIDE THE FORMS (of the lookup on the digits: "planes", "keys"),
AT A LINK: THE PREMISE hW OF `link_table_more` (LinkTableMore.lean) PAID AT THESE TWO SENTENCES,
UNDER NAMED PREMISES. Theorems: a joining of `four_at_front_full` (FourAtFront.lean)
and another file's exchange `digits_planesKeys_at_world`
(Johnson/Top/H/Keep/EquationsPlanesKeys.lean).

What is said.
  `DigitsRest`: what the exchange asks beside the run's yes, the heard structure, the four claims'
    worth and what is paid here: thirteen fields, each in the exchange's own text: as one Lean
    structure, so that each has a name and a payer.
  `WorthTwo`: the two sentences (`K3WorthPlanes`, `K3WorthKeys`, Johnson/Top/H/K3Worth.lean) at the
    letters of the lookup on the digits.
  `worth_at_front`: **from the link's duties at `Fu := FullAt nU`, a yes of the batching's
    sub-protocol from a to b', the table's sentence "totalB" at b', every term's coefficient 0 at
    the data y, the seat's two readers by their text (hfk, hhd), and hRest: the two sentences at a
    and the witness w.** hRest: `DigitsRest` at whatever run, ledgers and structures
    `four_at_front_full` finds, UNDER THE THREE TIES THAT IT HANDS ON: the run's state e and the
    full state t go on from what is fixed at a; t goes on from the state behind the run. PAID HERE
    OUT OF THESE TIES: the ledger at e is
    later than the one at a, and has its sizes; the ledger at t is later than the one behind the
    run; what the state a holds as heard is what the run's structure has heard.
  `link_table_worth`: **`link_table` with the two sentences beside the forms in front of the
    batching**: `link_table_more` at Wq := `WorthTwo`, hW by `worth_at_front`: the book-keeping in
    front comes out of the sub-protocol's yes, the promise C out of the relation behind, RunOk of
    each run out of the link's duties.

Limits. AN IMPLICATION. `DigitsRest` IS PAID BY NOBODY HERE: each field has its payer on a page
that is not in this library. WITHOUT THE THREE TIES hRest COULD BE PAID BY NOBODY (the run's
state would be pinned to nothing: alter a shown value under a filled slot of its
ledger). WITH THEM: coef and inside read the numbers of rows of the ledger in front of the run of
self tests: these are pinned only where "goes on" carries the arrays' looks; that same, sameZ and
pieces read none of the structure's fourteen written fields is not held. hFu4 (the entries' half of
the four values) is taken as given, as in Johnson/Desc/First/Batch/Law/K8Four.lean. NOT TRIED FOR
EMPTINESS AT ANY REAL PLACE. From the two sentences back to the filling's letter `Mg.worth` is not
shown here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FourAtFront
import Johnson.Top.H.Keep.EquationsPlanesKeys

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

/-- **What the exchange asks beside the run's yes, the heard structure and the four claims' worth.**
Each field in the exchange's own text. -/
structure DigitsRest {Cells Tok : Type} (x : First.Look.Place) (tlD : HTailF2) (D : First.Look.Sent)
    (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (w : Desc.Wit Cells Tok MsgT) (g : Forest.Heard) (tl tlX : HTailF2) (Fc : Fork)
    (c : List Claim) (L : LinkCtx) (y : Bound Cb.Gl.E) : Prop where
  same : SameDig tlD tl
  shape : tl.f9 = g.shape
  five : 5 ≤ g.shape.kT + g.shape.cK
  points : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n
  small : ∀ q < 2, (tl.zOf q).call.n ≤ 63
  pieces : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p
  apart : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
    p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off
  sameZ : SameZ tl tlX
  coef : CoefOK tlX Fc
  inside : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R
  cellsB : ∀ r < 32, ∀ i < tlD.bzColumns,
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tlD.ix.BZ r i) =
      some (unknownOf L y (Sum.inl (tlD.ix.BZ, r, i)))
  cellsZ : ∀ q < 2, ∀ p ∈ piecesL tlD q, ∀ r < p.Rp, ∀ i < p.Cp,
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
        (.cell tlD.ix.ZZ (p.r0 + r) (p.c0 + i)) =
      some (unknownOf L y (Sum.inl (tlD.ix.ZZ, p.r0 + r, p.c0 + i)))
  masks : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
    y.mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1)

variable {α Cells Tok : Type} {F : Sound.Frame}

/-- **The two sentences.** -/
def WorthTwo (fork : S → Option Fork) (heard : S → Option Forest.Heard) (x : First.Look.Place)
    (tlD : HTailF2) (D : First.Look.Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (s : S)
    (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthPlanes fork heard tlD.f9 5 x.F.next (fun w => digNu x tlD D rad seatT arr w) s w ∧
    K3WorthKeys fork heard tlD.f9 5 x.F.next (fun w => digNu x tlD D rad seatT arr w)
      (fun w => forK Cb.Gl.E (digL5 Cb.Gl.E tlD (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
        (zext (digMu x D rad seatT arr w))) s w

/-- **THE TWO SENTENCES AT THE BATCHING's FRONT.** -/
theorem worth_at_front (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₁ b₂ b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Desc.Wit Cells Tok MsgT))
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → Desc.Wit Cells Tok MsgT → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
    (ctx : S × F.E.Str → Desc.Wit Cells Tok MsgT → Prop)
    (H : JoinAsks φ Ok (FullAt nU) p pw (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) d N b₁ b₂ b₃ pb
      pq pe on0 on1 on2 on3 tabOf ctx)
    (hrun : ∀ r ∈ rlOf L tmOf lenOf,
      RunOk Reading.gl atS (O9 φ Ok (FullAt nU)) (Fx9 φ Ok) r.run.2 r.tm r.len)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → FullAt nU t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard) (x : First.Look.Place)
    (tlD : HTailF2) (D : First.Look.Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {set : Params.Setting}
    {pp : ℕ} (HD : DigOK set x tlD D rad pp) (hfk : ∀ s, fork s = s.fork?)
    (hhd : ∀ s, heard s = s.tl?.bind (·.heard))
    (a : S × F.E.Str) (τ : _) (b' : S × F.E.Str) (ha : on0 a)
    (hout : pb.ior.red.out a τ = some b')
    (hB : totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b'.1 rd) (y : Bound GE8)
    (h0 : ∀ x ∈ termsRuns (fixed9 φ a.1) y (rlOf L tmOf lenOf) 0, x.2 = 0)
    (w : Desc.Wit Cells Tok MsgT)
    (hRest : ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ)
      (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t = some b →
      k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
      b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
      blank u tl = blank u tlX → tl.heard = some g →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 φ Ok (fixed9 φ a.1) e → Fx9 φ Ok (fixed9 φ a.1) t →
      laterK atS (O9 (K := GE8) φ Ok (FullAt nU)) ((e.putTl tl').putFork F1) t →
      DigitsRest x tlD D rad seatT arr w g tl tlX Fc c b.L y) :
    WorthTwo fork heard x tlD D rad seatT arr a.1 w := by
  obtain ⟨t, e', b, Fc, tlX, g, front, e, Fe, tl, tl', funs, F1, c, r1, r2, r3, r4, r5, r6, r7, r8,
      r9, r10, r11, r12, r13, fe, ft, hl, hz⟩ :=
    four_at_front_full L φ Ok nU p pw tmOf lenOf d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx H
      hrun u π hπ hkeep ent hOk4 hFu4 o ho run hAt hu ht own rd a τ b' ha hout hB y h0
  have key : ∀ g₀ F', fork a.1 = some F' → heard a.1 = some g₀ →
      K3OutPlanes tlD.f9 5 x.F.next (digNu x tlD D rad seatT arr w) Reading.gl g₀ F' ∧
        K3OutKeys tlD.f9 5 x.F.next (digNu x tlD D rad seatT arr w)
          (forK Cb.Gl.E (digL5 Cb.Gl.E tlD (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
            (zext (digMu x D rad seatT arr w))) Reading.gl g₀ F' := by
    intro g₀ F' hf hh
    have R := hRest t e' b Fc tlX g front e Fe tl tl' funs F1 c r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
      r12 r13 fe ft hl
    obtain ⟨hOk, hφe, v, be, hv, hbe, gv⟩ := fe
    obtain ⟨a₀, ha₀, rfl⟩ :=
      Option.map_eq_some_iff.1 (show (atS.get? a.1).map pubOf = some v from hv)
    have eF' : F' = a₀.F :=
      Option.some.inj (((hfk a.1).symm.trans hf).symm.trans (K9.get_fork a.1 a₀ ha₀))
    have eFe : be.F = Fe := Option.some.inj ((K9.get_fork e be hbe).symm.trans r8)
    have q1 : (π (fixed9 φ a.1).1).1 = some (blank u tl) := by
      rw [← hφe, hπ, r9]
      rfl
    have eg : g₀ = g := by
      rw [hhd] at hh
      obtain ⟨tla, hta, hga⟩ := Option.bind_eq_some_iff.1 hh
      have q0 : (π (fixed9 φ a.1).1).1 = some (blank u tla) := by
        show (π (φ a.1)).1 = _
        rw [hπ, hta]
        rfl
      have e1 : (blank u tla).heard = (blank u tl).heard :=
        congrArg (·.heard) (Option.some.inj (q0.symm.trans q1))
      exact Option.some.inj (hga.symm.trans ((show tla.heard = tl.heard from e1).trans r12))
    subst eg
    have l0 : OnBytes.PscRun.Later F' Fe := by
      rw [eF', ← eFe]
      exact gv.1
    have hsz : Sized Fe :=
      l0.sized (eF' ▸ (hOk4 _ (pubOf a₀) (blank u tl) g₀ hOk hv q1 r12).1)
    obtain ⟨a₁, ha₁, f1, _⟩ := get_put e be hbe tl' F1
    obtain ⟨b₂, hb₂, g₂⟩ := hl.2.1.2 a₁ ha₁
    obtain rfl : b₂ = b := Option.some.inj (hb₂.symm.trans r2)
    have l1 : OnBytes.PscRun.Later F1 (coefAll tlX g₀ Fc) := by
      rw [← f1, ← r7]
      exact g₂.1
    exact digits_planesKeys_at_world seatT arr HD w g₀ F' tl tl' tlX R.same funs Fe F1 Fc c r13 r12
      R.shape ⟨l0.next, l0.ns, l0.keep⟩ hsz R.five R.points R.small R.pieces R.apart b₂.L y R.sameZ
      R.coef R.inside ⟨l1.next, l1.ns, l1.keep⟩ R.cellsB R.cellsZ R.masks hz
  exact ⟨fun g₀ F' hf hh => (key g₀ F' hf hh).1, fun g₀ F' hf hh => (key g₀ F' hf hh).2⟩

/-- **THE LAW OF A LINK AS THREE CORE LAWS IN THE TABLE's LETTERS, WITH THE TWO SENTENCES BESIDE THE
FORMS IN FRONT OF THE BATCHING.** -/
theorem link_table_worth (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
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
    (hRest : ∀ a τ b' w₀ y, on0 a → pb.ior.red.out a τ = some b' →
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
      DigitsRest x tlD D rad seatT arr (pb.ext a τ w₀) g tl tlX Fc c b.L y) :
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
        (fun e w => rowEqQ own N e.1 (rdW w)) := by
  have RA := runsAsk_of_owes h A
  have H := joinAsks_of_runs RA
  refine link_table_more C Rw l sub L h φ Ok (FullAt nU) p pw tmOf lenOf d N b₃ pb pq pe on0 on1 on2
    on3 ctx Rd own rdW items A T h01 hR1 hR2 hR3
    (fun a w => WorthTwo fork heard x tlD D rad seatT arr a.1 w) ?_
  intro a τ b' w₀ ha hout _ hR y hbd h0
  have hA : k9OnA a.1 = true := by
    obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact yes_onA p _ L.batchB H.hb₁ _ _ _ _ _ k hs
  exact worth_at_front L φ (fun q => Ok q ∧ C q) nU p pw tmOf lenOf d N L.batchB L.behindB b₃ pb pq
    pe _ on1 on2 on3 _ ctx H RA.hrun u π hπ hkeep ent hOk4 hFu4 o ho run hAt hu ht own (rdW w₀)
    fork heard x tlD D rad seatT arr HD hfk hhd a τ b' ⟨⟨ha, hA⟩, hR1 a τ b' ha hout hR.1.2⟩ hout
    hR.1.1 y
    h0 (pb.ext a τ w₀) (hRest a τ b' w₀ y ha hout hbd)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.worth_at_front
#print axioms VerifiableInference.Desc.LinkJoin.link_table_worth
