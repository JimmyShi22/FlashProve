-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RestStatic.lean: THE PREMISE hRest OF THE LAW ON THE TWO SENTENCES AT
THE BATCHING's FRONT (`worth_at_front`, `link_table_worth`, WorthAtFront.lean: it asks
`DigitsRest`'s thirteen fields) SHRINKS TO SIX FIELDS: THE SEVEN THAT READ NO HEARD VALUE FOLLOW
FROM ONE MORE CLAUSE OF THE PROMISE Ok ON WHAT IS FIXED BEFORE THE DRAW. Structures and theorems.
  `DigStatic tlD tl F`: six of the seven, each in `DigitsRest`'s own text: same, small, pieces,
    apart (on the structure), coef, inside (on the structure and the ledger's frame).
    `digStatic_blank`: it reads none of the fourteen written fields. `sameZ_of_blank`: the seventh,
    from "one but for the fourteen" and "have heard the same".
  `rest_static`: **under okDig (`DigStatic` at the fixed structure and the snapshot's ledger), at a
    state e that goes on from q with the structure tl, and a state t that goes on from q whose
    ledger is `coefAll tlX g Fc`: `DigStatic tlD tl Fc`, and `CoefOK tlX Fc`.** The snapshot's frame
    is t's ledger's (`goesOn_looks`), and that is Fc's (`frame_all`).
  `DigitsLeft`: the six fields that stay: shape, five, points (on what was heard); cellsB, cellsZ,
    masks (the exchange's). `digitsRest_of`: **`DigitsRest` out of `DigitsLeft` and okDig**, under
    those of hRest's own hypotheses that it spends. `hRest_of`: **hRest to the letter, from the like
    premise at `DigitsLeft` and okDig.**
  `worth_at_front_left`: **`worth_at_front` with hRest paid so**: its premises are that theorem's,
    but for okDig and the like of hRest at `DigitsLeft` in hRest's place. (It is also Lean's own
    check that `hRest_of` ends in that premise.)
Limits. An implication. okDig's lower bound is owed with the rest of Ok (`hready`, LinkOwes.lean).
Nothing is evaluated. It compiles only over the turn of "goes on" that carries the arrays' looks.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WorthAtFront
import Johnson.Desc.First.Link.Law.FullFour

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

/-! ## 1 The seven fields that read no heard value -/

/-- **Six of them, as one sentence on a structure and a ledger.** Each field in `DigitsRest`'s own
text. -/
structure DigStatic (tlD tl : HTailF2) (F : Fork) : Prop where
  same : SameDig tlD tl
  small : ∀ q < 2, (tl.zOf q).call.n ≤ 63
  pieces : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p
  apart : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
    p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off
  coef : CoefOK tl F
  inside : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (F.trees.getD a.2.tree {}).R

/-- It reads none of the fourteen written fields. -/
theorem digStatic_blank {u tlD tl : HTailF2} {F : Fork} (h : DigStatic tlD (blank u tl) F) :
    DigStatic tlD tl F :=
  ⟨⟨h.same.f9, h.same.ix, h.same.mz, h.same.tau, h.same.z1, h.same.z2⟩, h.small,
    fun q hq p hp => by
      have k := h.pieces q hq p hp
      exact ⟨k.tree, k.c0, k.le, k.pw, k.rp, k.b, k.bn, k.dvd, k.fit⟩,
    h.apart, coefOK_blank h.coef, h.inside⟩

/-- Two structures that are one but for the fourteen written fields, and have heard the same. -/
theorem sameZ_of_blank {u tl tlX : HTailF2} (h : blank u tl = blank u tlX)
    (hh : tlX.heard = tl.heard) : SameZ tl tlX :=
  ⟨(congrArg (·.ix) h).symm, (congrArg (·.z1) h).symm, (congrArg (·.z2) h).symm, hh⟩

section
variable {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (u : HTailF2)
  (π : α → Option HTailF2 × Option (Array HFun))
  (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (tlD : HTailF2)
  (okDig : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F)
include hπ okDig

/-- **THE SIX AT A STATE THAT GOES ON FROM q, THE LEDGER's TWO AT THE LEDGER IN FRONT OF THE LAYING
OF THE WEIGHTS.** -/
theorem rest_static (q : α × Option Pub9) (t e : S) (b : K9.Part) (Fc : Fork) (tlX tl : HTailF2)
    (g : Forest.Heard) (hb : atS.get? t = some b) (hF : b.F = coefAll tlX g Fc)
    (he : e.tl? = some tl) (h11 : blank u tl = blank u tlX) (fe : Fx9 φ Ok q e)
    (ft : Fx9 φ Ok q t) :
    DigStatic tlD tl Fc ∧ CoefOK tlX Fc := by
  obtain ⟨hOk, hφ, v, _, hv, _, _⟩ := fe
  obtain ⟨_, _, v', b', hv', hb', hgo⟩ := ft
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have q1 : (π q.1).1 = some (blank u tl) := by
    rw [← hφ, hπ, he]
    rfl
  have D := okDig q _ v hOk q1 hv
  have fr : Frame v.F Fc :=
    (frame_of_looks (goesOn_looks hgo)).trans (Frame.symm' (hF ▸ frame_all tlX g Fc))
  have D' := digStatic_blank D
  refine ⟨⟨D'.same, D'.small, D'.pieces, D'.apart, coefOK_frame fr D'.coef, fun a ha => ?_⟩,
    coefOK_frame fr (coefOK_blank (h11 ▸ D.coef))⟩
  rw [(fr.2 a.2.tree).1]
  exact D'.inside a ha

end

/-! ## 2 The premise hRest, from the six fields that stay -/

/-- **What stays of `DigitsRest`.** Each field in its own text. -/
structure DigitsLeft {Cells Tok : Type} (x : First.Look.Place) (tlD : HTailF2)
    (D : First.Look.Sent) (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w : Desc.Wit Cells Tok MsgT) (g : Forest.Heard) (tl : HTailF2)
    (c : List Claim) (L : LinkCtx) (y : Bound Cb.Gl.E) : Prop where
  shape : tl.f9 = g.shape
  five : 5 ≤ g.shape.kT + g.shape.cK
  points : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n
  cellsB : ∀ r < 32, ∀ i < tlD.bzColumns,
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w) (.cell tlD.ix.BZ r i) =
      some (unknownOf L y (Sum.inl (tlD.ix.BZ, r, i)))
  cellsZ : ∀ q < 2, ∀ p ∈ piecesL tlD q, ∀ r < p.Rp, ∀ i < p.Cp,
    digVal x D rad (msgsOf D.codes (digList x D rad) seatT arr w)
        (.cell tlD.ix.ZZ (p.r0 + r) (p.c0 + i)) =
      some (unknownOf L y (Sum.inl (tlD.ix.ZZ, p.r0 + r, p.c0 + i)))
  masks : ∀ k ∈ c.take 4, ∀ s ∈ k.form.slots.toList,
    y.mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1)

/-- **`DigitsRest` OUT OF THE SIX THAT STAY AND THE CLAUSE okDig**, under those of hRest's own
hypotheses that it spends. -/
theorem digitsRest_of {α Cells Tok : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (x : First.Look.Place) (tlD : HTailF2)
    (D : First.Look.Sent) (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w : Desc.Wit Cells Tok MsgT)
    (okDig : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F)
    (q : α × Option Pub9) (t e : S) (b : K9.Part) (Fc : Fork) (tlX tl : HTailF2)
    (g : Forest.Heard) (c : List Claim) (y : Bound Cb.Gl.E) (hb : atS.get? t = some b)
    (hX : tlX.heard = some g) (hF : b.F = coefAll tlX g Fc) (he : e.tl? = some tl)
    (h11 : blank u tl = blank u tlX) (h12 : tl.heard = some g) (fe : Fx9 φ Ok q e)
    (ft : Fx9 φ Ok q t) (Lf : DigitsLeft x tlD D rad seatT arr w g tl c b.L y) :
    DigitsRest x tlD D rad seatT arr w g tl tlX Fc c b.L y := by
  obtain ⟨S1, S2⟩ := rest_static φ Ok u π hπ tlD okDig q t e b Fc tlX tl g hb hF he h11 fe ft
  exact ⟨S1.same, Lf.shape, Lf.five, Lf.points, S1.small, S1.pieces, S1.apart,
    sameZ_of_blank h11 (hX.trans h12.symm), S2, S1.inside, Lf.cellsB, Lf.cellsZ, Lf.masks⟩

/-- **hRest TO THE LETTER, FROM THE LIKE PREMISE AT `DigitsLeft` AND THE CLAUSE okDig.** -/
theorem hRest_of {α Cells Tok : Type} {F : Sound.Frame} (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (x : First.Look.Place) (tlD : HTailF2)
    (D : First.Look.Sent) (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (a b' : S × F.E.Str) (y : Bound GE8) (w : Desc.Wit Cells Tok MsgT)
    (okDig : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F)
    (hLeft : ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ)
      (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t = some b →
      k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
      b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
      blank u tl = blank u tlX → tl.heard = some g →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 φ Ok (fixed9 φ a.1) e → Fx9 φ Ok (fixed9 φ a.1) t →
      laterK atS (O9 (K := GE8) φ Ok (FullAt nU)) ((e.putTl tl').putFork F1) t →
      DigitsLeft x tlD D rad seatT arr w g tl c b.L y) :
    ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ)
      (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t = some b →
      k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
      b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
      blank u tl = blank u tlX → tl.heard = some g →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 φ Ok (fixed9 φ a.1) e → Fx9 φ Ok (fixed9 φ a.1) t →
      laterK atS (O9 (K := GE8) φ Ok (FullAt nU)) ((e.putTl tl').putFork F1) t →
      DigitsRest x tlD D rad seatT arr w g tl tlX Fc c b.L y :=
  fun t e' b Fc tlX g front e Fe tl tl' funs F1 c r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 fe ft
      hl =>
    digitsRest_of φ Ok u π hπ x tlD D rad seatT arr w okDig _ t e b Fc tlX tl g c y r2 r6 r7 r9 r11
      r12 fe ft
      (hLeft t e' b Fc tlX g front e Fe tl tl' funs F1 c r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
        fe ft hl)

variable {α Cells Tok : Type} {F : Sound.Frame}

/-- **THE TWO SENTENCES AT THE BATCHING's FRONT, FROM THE SIX FIELDS THAT STAY.** `worth_at_front`
with hRest paid by `hRest_of`: so Lean holds `hRest_of`'s end against that premise. -/
theorem worth_at_front_left (L : Link S Claim) (φ : S → α) (Ok : α × Option Pub9 → Prop)
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
    (okDig : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F)
    (hLeft : ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g : Forest.Heard) (front : ℕ)
      (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork) (c : List Claim),
      K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t = some b →
      k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
      b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
      blank u tl = blank u tlX → tl.heard = some g →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 φ Ok (fixed9 φ a.1) e → Fx9 φ Ok (fixed9 φ a.1) t →
      laterK atS (O9 (K := GE8) φ Ok (FullAt nU)) ((e.putTl tl').putFork F1) t →
      DigitsLeft x tlD D rad seatT arr w g tl c b.L y) :
    WorthTwo fork heard x tlD D rad seatT arr a.1 w :=
  worth_at_front
    L φ Ok nU p pw tmOf lenOf d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx H hrun u π hπ hkeep
    ent hOk4 hFu4 o ho run hAt hu ht own rd fork heard x tlD D rad seatT arr HD hfk hhd a τ b' ha
    hout hB y h0 w (hRest_of L φ Ok nU u π hπ x tlD D rad seatT arr a b' y w okDig hLeft)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.digStatic_blank
#print axioms VerifiableInference.Desc.LinkJoin.rest_static
#print axioms VerifiableInference.Desc.LinkJoin.digitsRest_of
#print axioms VerifiableInference.Desc.LinkJoin.hRest_of
#print axioms VerifiableInference.Desc.LinkJoin.worth_at_front_left
