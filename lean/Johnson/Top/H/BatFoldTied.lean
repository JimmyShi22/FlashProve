-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatFoldTied.lean: at the rounds "BAT", "FOLD epsilon" and the k rounds "FOLD round":
the TARGET of the statement that the typed block puts out on the image of the written stretch is the
reading of the target that the program's fold returns, if the target with which the typed fold
begins is the reading of the program's row's.

Johnson/Top/H/BatFoldPlace.lean has the law of this place: the written stretch has an image, the
typed verifier puts out a statement on it, the rest of the view is still to be taken. It does not
say what is put out. Here the scalar at the head of that statement is tied. Statements and proofs.

Main names (c : a caller of the kind `kBatFoldRide` over the program's extension field; ρ : the
readings of Johnson/Top/H/BatFoldPlace.lean):
  `batX c a z`: what the batching round puts out at the seed z: the statement with which
    arrangement, cut and fold begin.
  `batFoldRide_out`: the block's verifier in closed form, under the premise on fx of
  `Tower.foldRide_total`.
  `Rd.Scal`: the readings are those of the field: rdK is `readE`; a challenge that is read off one
    element has that element's reading as its value; the items of a round's view do not hang on the
    verifier's message.
  `rd2 c`: the program's two scalars of a round as the typed short message: the first n of them, 0
  beyond.
  `Rd.carK_reads`: the image of the k written rounds reads the program's scalars and elements
    (`Reads`, OnBytes/Tie/Pv/Fold/FoldClaim.lean).
  `batFold_tied`: as `batFold_meet`, and: if AT THE SEED z THAT IS READ OFF WHAT THE FIRST OF THE
    ROUNDS STILL TO BE TAKEN DREW `(batX c a z).1.1 = readE row.target`, the target of the statement
    put out is `readE out.target`.
Limits: the target alone: nothing on the point, the coefficient, the
forms or the words in the statement put out. The premise on `batX` (the batching's target is the
reading of the program's combined row's) is not shown.
`StepOK` at the caller's n and fx is a premise: it is shown at n = 2, fx = (1, 1) alone
(`stepOK_firstN`, OnBytes/Tie/Pv/Fold/FoldClaim.lean): so the tie asks of a caller two scalars a
round and the linear coefficient left out. One direction.
-/
import Johnson.Top.H.BatFoldPlace
import OnBytes.Tie.Pv.Fold.FoldClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.BatFoldAt
open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold Iop OnBytes.Flat KObj KObj.RowCar
open VerifiableInference.OnPublicFiles Cb Cb.Pv
open OnBytes.PscRun (sentOf drawnOf)

variable (c : BatFoldCaller GE)

/-- What the batching round puts out at the seed z. -/
noncomputable def batX (a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp) (z : c.s.Z.D) :
    LdBrXo c.s.G c.s.kp c.s.Sb c.s.Z c.St₀ :=
  ldBrNx c.s.G c.s.kp c.s.Sb c.s.Z c.St₀ (ldBrF c.s.G c.s.kp c.s.Sb c.St₀ a) z

/-- The block's verifier in closed form. -/
theorem batFoldRide_out (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1)
    (a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp)
    (y : ((c.E₀.prod c.s.S.ext).prod c.Sh.par.Cw.nat).Str) (z : c.s.Z.D) (sum : GE)
    (e : (Yc c).Ch) (τk : Tr (List.replicate (Yc c).k (sRoundS GE (Yc c).Ch (Yc c).n))) :
    ∃ xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).out a y
        (((), ()), z, ((), sum), e, τk) = some xo ∧
      xo.1.1 = sClaim (Yc c).val (Yc c).n c.fx (Yc c).k
        (sum + (batX c a z).1.1 * (Yc c).val e) τk := by
  refine ⟨((Yc c).newX ((batX c a z).1.1, ((batX c a z).1.2, (batX c a z).1.2))
    ((Yc c).upRhoR (Tr.rho (s := (Yc c).shapeR) (((), sum), e, τk)))
    (sClaim (Yc c).val (Yc c).n c.fx (Yc c).k (sum + (batX c a z).1.1 * (Yc c).val e) τk),
    (batX c a z).2), ?_, rfl⟩
  show ((Tower.foldRide (Yc c) c.fx).out
    ((batX c a z).1.1, ((batX c a z).1.2, (batX c a z).1.2)) _ (((), sum), e, τk)).map
      (fun xo => (xo, (batX c a z).2)) = _
  rw [Tower.foldRide_out (Yc c) c.fx hfx]
  rfl

variable {c} {rB rE rR : Round} (ρ : Rd c rB rE rR)

/-- The readings are those of the field. -/
structure Rd.Scal : Prop where
  rdK : ρ.rdK = readE
  val : ∀ g ch, ρ.rdCh [g] = some ch → (Yc c).val ch = readE g
  okE : ∀ m ch ch', (ρ.viewE m ch).vals = (ρ.viewE m ch').vals
  okR : ∀ m ch ch', (ρ.viewR m ch).vals = (ρ.viewR m ch').vals

variable (c) in
/-- The program's two scalars of a round as the typed short message: the first n of them, 0 beyond.
-/
noncomputable def rd2 : OnBytes.E → OnBytes.E → Fin (Yc c).n → GE := firstN (Yc c).n

variable {ρ}

theorem Rd.Scal.scalOf (h : ρ.Scal) {m : rR.Msg} {ch : rR.Chal} {q : OnBytes.E × OnBytes.E}
    (hq : Holds (ρ.viewR m ch) [q.1, q.2]) : ρ.scalOf m = rd2 c q.1 q.2 := by
  have e : sentOf (ρ.viewR m (Classical.choice rR.neChal)) = [q.1, q.2] := by
    rw [← holds_sent hq]
    unfold sentOf
    rw [h.okR m _ ch]
  unfold Rd.scalOf rd2 firstN
  rw [e, h.rdK]

theorem Rd.Scal.sumOf (h : ρ.Scal) {m : rE.Msg} {ch : rE.Chal} {s : OnBytes.E}
    (hs : Holds (ρ.viewE m ch) [s]) : ρ.sumOf m = readE s := by
  have e : sentOf (ρ.viewE m (Classical.choice rE.neChal)) = [s] := by
    rw [← holds_sent hs]
    unfold sentOf
    rw [h.okE m _ ch]
  unfold Rd.sumOf
  rw [e, h.rdK]
  rfl

/-- The image of the k written rounds reads the program's scalars and elements. -/
theorem Rd.Scal.carK_reads (h : ρ.Scal) : ∀ (k : ℕ) (τ : Tr (List.replicate k rR))
    (qs : List (OnBytes.E × OnBytes.E)) (gs : List OnBytes.E)
    (τ' : Tr (List.replicate k (sRoundS GE (Yc c).Ch (Yc c).n))),
    RoundsHold (ρ.vK k τ) qs gs → (ρ.carK k).tr τ = some τ' →
    Reads (Yc c).val (Yc c).n (rd2 c) k τ' qs gs
  | 0, _, [], [], _, _, _ => trivial
  | 0, _, [], _ :: _, _, hr, _ => hr.elim
  | 0, _, _ :: _, _, _, hr, _ => hr.elim
  | _ + 1, _, [], _, _, hr, _ => hr.elim
  | _ + 1, _, _ :: _, [], _, hr, _ => hr.elim
  | k + 1, (m, x, t), q :: qs, g :: gs, τ', hr, ht => by
    obtain ⟨h1, h2, h3⟩ := hr
    have ht' : (ρ.rdCh (drawnOf (ρ.viewR m x))).bind (fun c' => ((ρ.carK k).tr t).map fun τ'' =>
        ((((), ρ.scalOf m), c', τ'') :
          Tr (List.replicate (k + 1) (sRoundS GE (Yc c).Ch (Yc c).n)))) = some τ' := ht
    obtain ⟨ch, hch, ht''⟩ := Option.bind_eq_some_iff.1 ht'
    obtain ⟨τ'', hτ'', rfl⟩ := Option.map_eq_some_iff.1 ht''
    rw [drawnOf_one h2] at hch
    exact ⟨h.scalOf h1, h.val g ch hch, Rd.Scal.carK_reads h k t qs gs τ'' h3 hτ''⟩

variable (ρ) (L : List (BatFoldCaller GE))

/-- **The target is tied.** As `batFold_meet`; and the target of the statement that the typed
verifier puts out is the reading of the target that the program's fold returns. -/
theorem batFold_tied (hS : ρ.Scal) (hst : StepOK (Yc c).val (Yc c).n c.fx (rd2 c))
    (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1) {g o : Nat} {row : GroupRow}
    {lay : GroupLayout} {F : FoldShape} {out : SingleRows} {x x4 x6 x7 : Ctx}
    (hd : x.ch.dry = false) (ht : ρ.DefAt x.ch.pending)
    (hb : (batVerify g).Yields x (row, lay) x4) (hn : x6.ch = x4.ch)
    (hf : (foldVerify F row (some o)).Yields x6 out x7) (hk : F.layout.k = (Yc c).k)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (hx : ∀ r t z, x.ch.pending = r :: t → ρ.rdZ (drawnOf r) = some z →
      (batX c a.1 z).1.1 = readE row.target)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (rest : List Fmt.RoundView)
    (hp : x.ch.pending = ρ.V τ ++ rest) :
    ∃ τ' a', ρ.carS.tr τ = some τ' ∧ ((kBatFoldRide L).block c).R.red.out a τ' = some a' ∧
      x7.ch.pending = rest ∧ a'.1.1.1 = readE out.target := by
  obtain ⟨vB, xb, b1, -, b3, b4⟩ := batVerify_view g row lay x x4 hd hb
  have d6 : x6.ch.dry = false := by rw [hn]; exact b4.1
  obtain ⟨_, v₀, rs, sum, eps, qs, gs, -, -, -, -, f1, f2, f3, f4, f5, f6, -⟩ :=
    foldVerify_view F row o out x6 x7 d6 hf
  have hpend : x.ch.pending = vB :: v₀ :: (rs ++ x7.ch.pending) := by rw [b1, ← hn, f1]
  have hlen : rs.length = (Yc c).k := by rw [roundsHold_length f4, f5, hk]
  have hmem : ∀ r ∈ v₀ :: rs, (ρ.rdCh (drawnOf r)).isSome := fun r hr => ht.2 r (by
    rw [hpend]
    show r ∈ (v₀ :: (rs ++ x7.ch.pending)).take ((Yc c).k + 1)
    rw [List.take_succ_cons, List.take_left' hlen]
    exact hr)
  rw [hpend] at hp
  obtain ⟨e1, hp⟩ := List.cons.inj hp
  obtain ⟨e2, hp⟩ := List.cons.inj hp
  have hl : rs.length = (ρ.vK (Yc c).k τ.2.2.2.2).length := by
    rw [Rd.vK_length, hlen]
  obtain ⟨e3, e4⟩ := List.append_inj hp hl
  have hvB : vB ∈ x.ch.pending.take 1 := by
    rw [hpend]
    show vB ∈ [vB]
    exact List.mem_singleton.2 rfl
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (ht.1 vB hvB)
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hmem v₀ List.mem_cons_self)
  obtain ⟨τk, hτk⟩ := ρ.carK_some (Yc c).k τ.2.2.2.2 fun rv hrv => by
    rw [← e3] at hrv
    exact hmem rv (List.mem_cons_of_mem _ hrv)
  have gz : ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z := by rw [← e1]; exact hz
  have ge : ρ.rdCh (drawnOf (ρ.viewE τ.2.2.1 τ.2.2.2.1)) = some e := by
    rw [← e2]
    exact he
  have himg : ρ.carS.tr τ = some (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk) := by
    obtain ⟨m1, c1, m2, c2, t⟩ := τ
    show (ρ.rdZ (drawnOf (ρ.viewB m1 c1))).bind (fun z' =>
      ((ρ.rdCh (drawnOf (ρ.viewE m2 c2))).bind fun e' =>
        ((ρ.carK (Yc c).k).tr t).map fun τ' => (((), ρ.sumOf m2), e', τ')).map fun τ' =>
          (((), ()), z', τ')) = _
    rw [gz, ge, hτk]
    rfl
  obtain ⟨xo, hxo, htg⟩ := batFoldRide_out c hfx a.1 a.2 z (ρ.sumOf τ.2.2.1) e τk
  refine ⟨_, (xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
    (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk)), himg, ?_, e4, ?_⟩
  · exact congrArg (Option.map fun xo' => (xo', (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
      (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk))) hxo
  · show xo.1.1 = readE out.target
    have hsum : ρ.sumOf τ.2.2.1 = readE sum := hS.sumOf (ch := τ.2.2.2.1) (by rw [← e2]; exact f2)
    have hval : (Yc c).val e = readE eps := hS.val eps e (by rw [← drawnOf_one f3]; exact he)
    have hrd : Reads (Yc c).val (Yc c).n (rd2 c) (Yc c).k τk qs gs :=
      hS.carK_reads (Yc c).k τ.2.2.2.2 qs gs τk (by rw [← e3]; exact f4) hτk
    rw [htg, hx vB _ z hpend hz, hsum, hval, ← first_claim, sClaim_reads hst _ _ _ _ _ hrd, f6]
    rfl

end VerifiableInference.OnPublicFiles.BatFoldAt

#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batFoldRide_out
#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batFold_tied
