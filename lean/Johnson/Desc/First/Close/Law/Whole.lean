-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Whole.lean: a law of the closing of a link (kind K10): THE WHOLE
STATEMENT THAT THE PROVED BLOCK PUTS OUT, written out from what the closing's text hands on.
Definitions, statements and proofs.

Statement.lean and Proof.lean, beside this file, tie the target alone. The typed statement behind
the proved block `kBatFoldRide` (Johnson/Top/H/BatFold.lean) holds more: the batching's state, the
point at which the rows are folded, the coefficient, and what is carried beside the test. Here each
of them is said.
  `closing_inv2`: what a yes of `closing` says, with what the vectors' laws spend: the fresh mask's
    number; the layout is the verifier's own for the group; its k and h are the plan's; the fold's
    own test of the row's sizes held at the statement handed on; that statement has the codes of the
    statement in front; the claim handed on is `foldOutput` of the batched row at that statement.
  `stAt Y st stS g e`: the state behind a fold Y: the two forms' states, the point g, its first h
    coordinates, the coefficient e, e times the later coordinates.
  `pt_reads`: the point that the typed fold reads off k short rounds is the reading of the
    elements that the written rounds drew.
  `batFoldRide_out_eq`: the proved block's verifier in closed form, whole.
  `law_whole`: if `closing` says yes on the reading of a written stretch, the proved block's
    verifier puts out, on the stretch's image: the reading of the target handed on; `stAt` at the
    state that the batching round puts out at the seed read off "BAT", at the reading of the point
    handed on (gamma) and at the reading of the element that "FOLD epsilon" drew; and, beside it,
    what the batching round carries.
  `slOut_slots`: for any shape of a group and ANY form F on the fold's input code: the form behind
    the fold at `stAt`, as a vector, entry by entry, from the vector `F st`.
  `sum_corner`: a vector that stands on the corner 0 .. 0 alone, folded at g: times the product of
    the 1 - g_t.

Why `slOut_slots` is said at any form. The proved block's verifier does not read the form: the form
stands in the relation of the joint behind it alone. So `law_whole` serves at every form, and
whoever shows of a form F that `F st` is the reading of the batched row has, by `slOut_slots`, the
vector behind the fold.

Limits. Those of Statement.lean but for (a) as far as the point, the coefficient, the state and the
carried part go. THE STATE IS "WHAT THE BATCHING ROUND PUTS OUT": that a form at that state is the
reading of the batched row is shown of no form here. Nothing on the words. The six readings are
letters. One direction; a text that always refuses meets the law. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Proof
import Johnson.Desc.First.Close.Law.InvMore
import Johnson.Desc.First.Close.Law.BatAtClosing
import OnBytes.Slice.BlkLinkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold Iop OnBytes.Flat KObj KObj.RowCar
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv
open OnBytes.PscRun (sentOf drawnOf)

/-- The shape of the fold that closes a link, of the plan's numbers and the group's layout. -/
abbrev shapeAt (P : Plan) (lay : GroupLayout) : FoldShape :=
  ioppFoldShape { code := P.code, maskCode := P.maskCode, k := P.k, h := P.h } lay

/-- **What a yes of the closing says**, with what the vectors' laws spend. -/
theorem closing_inv2 {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ (G : Group) (x : E) (row : GroupRow) (lay : GroupLayout) (m : Nat)
      (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (sum eps : E) (qs : List (E × E)) (gs : List E),
      rs = rB :: rE :: rR ∧ mask = some m ∧ S.groups[g]? = some G ∧
      rB.drawn.elems = [x.triple] ∧
      Bat.combine (begun S g G) g ⟨lay, runRows S G⟩ x = some row ∧
      (begun S g G).layout g = some lay ∧ lay.k = P.k ∧ lay.h = P.h ∧
      Holds rE [sum] ∧ rE.drawn.elems = [eps.triple] ∧ RoundsHold rR qs gs ∧ gs.length = P.k ∧
      foldRowOk S' (shapeAt P lay) row = true ∧ S'.codes = S.codes ∧
      out = foldOutput S' (shapeAt P lay) row m eps gs
        (claimAfter (maddE sum eps row.target) qs gs) := by
  unfold closing at h
  split at h
  · rename_i eB es rB rs' _
    obtain ⟨m, k0, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, kh, h⟩ := ok_bind h
    have kh := need_ok kh
    simp only [Bool.and_eq_true, beq_iff_eq] at kh
    obtain ⟨G, x, a1, a2, a3, a4, -, a6⟩ :=
      bat_inv_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    obtain ⟨rE, rR, sum, eps, qs, gs, S2, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := fold_inv2 h
    subst b8
    refine ⟨G, x, p.1, p.2.1, m, rB, rE, rR, sum, eps, qs, gs, by rw [b1], got_ok k0, a1, a2, a3,
      a6, kh.1, kh.2, b2, b3, b4, ?_, b6, ?_, b9⟩
    · rw [b5]
      rfl
    · rw [b7, a4]
      exact begun_codes S g G
  · exact absurd h (by simp)

/-- The state behind a fold: the two forms' states st and stS, the point g with its first h
coordinates, the coefficient e, and e times the later coordinates of g. -/
def stAt {K P : Type} [Field K] (Y : SumPar K P) (st : Y.St) (stS : Y.StS) (g : Fin Y.k → K)
    (e : K) : ((Y.St × (Fin Y.k → K)) × K) × (((Y.StS × (Fin Y.h → K)) × K) × (Fin Y.k → K)) :=
  (((st, g), e), (((stS, Y.pre g), e * Y.late g), g))

/-- The point that the typed fold reads off k short rounds is the reading of the elements that the
written rounds drew. -/
theorem pt_reads {Ch : Type} [Fintype Ch] [Nonempty Ch] (val : Ch → GE) (n : ℕ)
    (r2 : E → E → Fin n → GE) :
    ∀ (k : ℕ) (τ : Tr (List.replicate k (sRoundS GE Ch n))) (qs : List (E × E)) (gs : List E),
      Reads val n r2 k τ qs gs → sPt n k (sG val n k (sUpRho n k τ.rho)) = readP k gs
  | 0, _, [], [], _ => funext fun i => i.elim0
  | 0, _, [], _ :: _, h => h.elim
  | 0, _, _ :: _, _, h => h.elim
  | _ + 1, _, [], _, h => h.elim
  | _ + 1, _, _ :: _, [], h => h.elim
  | k + 1, τ, q :: qs, g :: gs, h => by
    obtain ⟨-, h2, h3⟩ := h
    have ih := pt_reads val n r2 k τ.2.2 qs gs h3
    show (Fin.cons (α := fun _ => GE) (val τ.2.1)
      (sPt n k (sG val n k (sUpRho n k τ.2.2.rho))) : Fin (k + 1) → GE) = _
    rw [ih, h2]
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i

/-- The proved block's verifier in closed form, whole. -/
theorem batFoldRide_out_eq (c : BatFoldCaller GE)
    (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1)
    (a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp)
    (y : ((c.E₀.prod c.s.S.ext).prod c.Sh.par.Cw.nat).Str) (z : c.s.Z.D) (sum : GE)
    (e : (Yc c).Ch) (τk : Tr (List.replicate (Yc c).k (sRoundS GE (Yc c).Ch (Yc c).n))) :
    (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).out a y (((), ()), z, ((), sum), e, τk) =
      some ((sClaim (Yc c).val (Yc c).n c.fx (Yc c).k
          (sum + (batX c a z).1.1 * (Yc c).val e) τk,
        stAt (Yc c) (batX c a z).1.2 (batX c a z).1.2
          (sPt (Yc c).n (Yc c).k (sG (Yc c).val (Yc c).n (Yc c).k
            (sUpRho (Yc c).n (Yc c).k τk.rho))) ((Yc c).val e)), (batX c a z).2) := by
  show ((Tower.foldRide (Yc c) c.fx).out
    ((batX c a z).1.1, ((batX c a z).1.2, (batX c a z).1.2)) _ (((), sum), e, τk)).map
      (fun xo => (xo, (batX c a z).2)) = _
  rw [Tower.foldRide_out (Yc c) c.fx hfx]
  rfl

/-- **THE WHOLE STATEMENT THAT THE PROVED BLOCK PUTS OUT**, from what the closing hands on. -/
theorem law_whole (L : List (BatFoldCaller GE)) (c : BatFoldCaller GE) (rB rE rR : Round)
    (ρ : Rd c rB rE rR) (hS : ρ.Scal) (hst : StepOK (Yc c).val (Yc c).n c.fx (rd2 c))
    (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1)
    (P : Plan) (S S' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (ht : ρ.DefAt (ρ.V τ))
    (h : closing P S g mask (ρ.V τ) = .ok (out, S'))
    (hO : ∀ G e z, S.groups[g]? = some G → (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z →
      Ordered c a.1 z e ((runRows S G).toList.map fun w => readE w.target))
    (hR : ∀ G, S.groups[g]? = some G → ∀ w ∈ (runRows S G).toList, RowFits (begun S g G) w) :
    ∃ (G : Group) (x eps : E) (row : GroupRow) (lay : GroupLayout) (m : Nat) (claim : E)
      (z : c.s.Z.D) (τ' : Tr ((kBatFoldRide L).block c).R.red.shape)
      (a' : ((kBatFoldRide L).dst c).X × ((kBatFoldRide L).dst c).E.Str),
      S.groups[g]? = some G ∧ mask = some m ∧
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [x.triple] ∧
      (ρ.viewE τ.2.2.1 τ.2.2.2.1).drawn.elems = [eps.triple] ∧
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z ∧
      Bat.combine (begun S g G) g ⟨lay, runRows S G⟩ x = some row ∧
      (begun S g G).layout g = some lay ∧ lay.k = P.k ∧ lay.h = P.h ∧
      out.gamma.length = P.k ∧ foldRowOk S' (shapeAt P lay) row = true ∧ S'.codes = S.codes ∧
      out = foldOutput S' (shapeAt P lay) row m eps out.gamma claim ∧
      ρ.carS.tr τ = some τ' ∧ ((kBatFoldRide L).block c).R.red.out a τ' = some a' ∧
      a'.1 = ((readE out.target, stAt (Yc c) (batX c a.1 z).1.2 (batX c a.1 z).1.2
        (readP (Yc c).k out.gamma) (readE eps)), (batX c a.1 z).2) := by
  obtain ⟨G, x, row, lay, m, vB, v₀, rs, sum, eps, qs, gs, e0, hm, hG, p3, hrow, l0, l1, l2, f2, f3,
    f4, f5, t1, t2, f6⟩ := closing_inv2 h
  have eV : ρ.V τ = ρ.viewB τ.1 τ.2.1 :: ρ.viewE τ.2.2.1 τ.2.2.2.1 ::
      ρ.vK (Yc c).k τ.2.2.2.2 := rfl
  rw [eV] at e0
  obtain ⟨e1, e0⟩ := List.cons.inj e0
  obtain ⟨e2, e3⟩ := List.cons.inj e0
  have hlen : (ρ.vK (Yc c).k τ.2.2.2.2).length = (Yc c).k := Rd.vK_length ρ _ _
  have hmem : ∀ r ∈ ρ.viewE τ.2.2.1 τ.2.2.2.1 :: ρ.vK (Yc c).k τ.2.2.2.2,
      (ρ.rdCh (drawnOf r)).isSome := fun r hr => ht.2 r (by
    rw [eV]
    show r ∈ (ρ.viewE τ.2.2.1 τ.2.2.2.1 :: ρ.vK (Yc c).k τ.2.2.2.2).take ((Yc c).k + 1)
    rw [List.take_succ_cons, List.take_of_length_le (le_of_eq hlen)]
    exact hr)
  obtain ⟨z, gz⟩ := Option.isSome_iff_exists.1 (ht.1 (ρ.viewB τ.1 τ.2.1) (by
    rw [eV]
    show _ ∈ [ρ.viewB τ.1 τ.2.1]
    exact List.mem_singleton.2 rfl))
  obtain ⟨e, ge⟩ := Option.isSome_iff_exists.1 (hmem _ List.mem_cons_self)
  obtain ⟨τk, hτk⟩ := ρ.carK_some (Yc c).k τ.2.2.2.2 fun rv hrv =>
    hmem rv (List.mem_cons_of_mem _ hrv)
  have himg : ρ.carS.tr τ = some (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk) := by
    obtain ⟨m1, c1, m2, c2, t⟩ := τ
    show (ρ.rdZ (drawnOf (ρ.viewB m1 c1))).bind (fun z' =>
      ((ρ.rdCh (drawnOf (ρ.viewE m2 c2))).bind fun e' =>
        ((ρ.carK (Yc c).k).tr t).map fun τ' => (((), ρ.sumOf m2), e', τ')).map fun τ' =>
          (((), ()), z', τ')) = _
    rw [gz, ge, hτk]
    rfl
  obtain ⟨xo, hxo, hxe⟩ : ∃ xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).out a.1 a.2
      (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk) = some xo ∧ xo = _ :=
    ⟨_, batFoldRide_out_eq c hfx a.1 a.2 z (ρ.sumOf τ.2.2.1) e τk, rfl⟩
  have hsum : ρ.sumOf τ.2.2.1 = readE sum := hS.sumOf (ch := τ.2.2.2.1) (by rw [e2]; exact f2)
  have hval : (Yc c).val e = readE eps := hS.val eps e (by
    rw [← drawnOf_one f3, ← e2]
    exact ge)
  have hrd : Reads (Yc c).val (Yc c).n (rd2 c) (Yc c).k τk qs gs :=
    hS.carK_reads (Yc c).k τ.2.2.2.2 qs gs τk (by rw [e3]; exact f4) hτk
  have hx : (batX c a.1 z).1.1 = readE row.target := by
    rw [batX_horner c (hO G x z hG (by rw [e1]; exact p3) gz)]
    have h1 := combine_target rdE (begun S g G) g ⟨lay, runRows S G⟩ x row hrow (hR G hG)
    simp only [rdE_val] at h1
    exact h1.symm
  have hgam : out.gamma = gs := by rw [f6]; rfl
  have htg : readE out.target = sClaim (Yc c).val (Yc c).n c.fx (Yc c).k
      (ρ.sumOf τ.2.2.1 + (batX c a.1 z).1.1 * (Yc c).val e) τk := by
    rw [hx, hsum, hval, ← first_claim, sClaim_reads hst _ _ _ _ _ hrd, f6]
    rfl
  refine ⟨G, x, eps, row, lay, m, _, z, _, (xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
    (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk)), hG, hm, by rw [e1]; exact p3,
    by rw [e2]; exact f3, gz, hrow, l0, l1, l2, by rw [hgam]; exact f5, t1, t2,
    by rw [hgam]; exact f6, himg, ?_, ?_⟩
  · exact congrArg (Option.map fun xo' => (xo', (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
      (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk))) hxo
  · show xo = ((readE out.target, stAt (Yc c) (batX c a.1 z).1.2 (batX c a.1 z).1.2
      (readP (Yc c).k out.gamma) (readE eps)), (batX c a.1 z).2)
    rw [hxe, htg, hgam, ← pt_reads (Yc c).val (Yc c).n (rd2 c) (Yc c).k τk qs gs hrd, hval]

/-! ### the form behind the fold, as a vector -/

/-- **The form behind a fold at any form F on the fold's input code, as a vector**: on a slot of the
folded super-row, the entries of `F st` on that slot of all corners, folded at g, times e; on the
folded carried mask row, those on the mask rows, folded at the first h coordinates of g, times e and
the later coordinates; on the folded fresh mask row, the public weights at g. -/
theorem slOut_slots {K : Type} [Field K] {S : Sig K} {G : Grp S} (Sh : GShape G) {St : Type}
    (F : Slf K St Sh.Cin.J) (st : St) (g : Fin (Sh.par.reform F).k → K) (e : K) :
    (Sh.par.reform F).slOut (stAt (Sh.par.reform F) st st g e) = fun j =>
      match j with
      | .inl x => (∑ b, F st (.inl (b, x)) * Alg.eqk g b) * e
      | .inr (.inl x) => (∑ b, F st (.inr (b, x)) * Alg.eqk ((Sh.par.reform F).pre g) b) *
          (e * (Sh.par.reform F).late g)
      | .inr (.inr x) => Sh.Qw g x :=
  funext fun j => by rcases j with j | j | j <;> rfl

/-- A vector that stands on the corner 0 .. 0 alone, folded at g. -/
theorem sum_corner {K : Type} [Field K] {n : ℕ} (g : Fin n → K) (a : K) :
    ∑ b : Fin n → Bool, (if b = fun _ => false then a else 0) * Alg.eqk g b =
      a * ∏ t, (1 - g t) := by
  rw [Finset.sum_eq_single (fun _ => false)]
  · rw [if_pos rfl]
    simp [Alg.eqk]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closing_inv2
#print axioms VerifiableInference.Desc.First.Close.pt_reads
#print axioms VerifiableInference.Desc.First.Close.batFoldRide_out_eq
#print axioms VerifiableInference.Desc.First.Close.law_whole
#print axioms VerifiableInference.Desc.First.Close.slOut_slots
#print axioms VerifiableInference.Desc.First.Close.sum_corner
