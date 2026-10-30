-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatFoldPlace.lean: the law of a place (`KObj.RowCar.PlaceAt`,
Johnson/Top/H/RowMeet.lean) at the rounds "BAT", "FOLD epsilon" and the k rounds "FOLD round" by
which a group of a request's chain is closed, for the block of the kind `kBatFoldRide`
(Johnson/Top/H/BatFold.lean). Definitions, statements and proofs.

What it is for: as Johnson/Top/H/LocPlace.lean. The typed block and the program have as many rounds,
of the same kinds, in the same order: nothing sent, a seed drawn; the sum sent, a coefficient drawn;
k times: scalars sent, a challenge drawn. No oracle is sent in these rounds.

The three written rounds rB, rE, rR (the last k times) and six readings are letters (`Rd`): viewB,
viewE, viewR read a written prover's and verifier's message as a round of a view; rdK reads an
element of the program's field as an element of the typed field; rdZ and rdCh read the list of the
elements that a round drew as a seed of the batching and as a challenge of the fold.

Main names:
  `Rd c rB rE rR`. `Rd.DefAt p`: rdZ is defined at what the first of the rounds p drew, and rdCh at
    what each of the k + 1 rounds behind it drew.
  `Rd.carK`, `Rd.carS`: the map of the k rounds, by recursion; the map of the place: k + 2 steps.
  `Rd.vK`, `Rd.V`: the reading of a written stretch as rounds of a view.
  `Rd.carK_some`: the k rounds have an image where rdCh is defined at what each drew.
  `Rd.aft d a τ`: what the typed verifier puts out on the image of τ (d where there is none).
  `batFold_meet`: from a run of the program's batching and of its fold on a view: if the rounds
    still to be taken before the batching begin with the reading of τ, then τ has an image, the
    typed verifier puts out a statement on it, and the rounds still to be taken behind the fold are
    the rest.
  `batFold_place`: the same as `PlaceAt`, with `Rd.aft d a τ` as the statement behind.
Limits: THE LAW CARRIES THE TYPED VERIFIER's YES AND THE COUNT OF ROUNDS, AND NO STATEMENT: what the
typed verifier puts out is not compared with what the program's fold returns (`foldOutput`). So
behind this place the typed statement is "whatever came out". That is enough wherever the typed
verifiers that follow never reject. It is not enough at a place whose typed verifier tests its
statement: a chain of places cannot be carried through such a place until it is shown here that
`Rd.aft` is the reading of what the program holds behind the fold, given that a is the reading of
what it held before the batching. The number k of rounds is tied to the program's (hk). Two things
are not: the program sends TWO scalars in a round, and nothing here says that the typed number n of
scalars is 2 (a reading takes the first n, 0 beyond the end); and the program completes the LINEAR
coefficient of a round's polynomial, while the premise on fx (that of
`Tower.foldRide_total`) says that the power that is left out can be completed, not which power it
is. The written rounds, the readings and the caller are letters. One direction. Nothing on an honest
prover.
-/
import OnBytes.Tie.Pv.Fold.FoldView
import Cb.Pv.Switch.BatFoldTotal
import Johnson.Top.H.BatFold
import Johnson.Top.H.RowMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.BatFoldAt
open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold Iop OnBytes.Flat KObj KObj.RowCar
open VerifiableInference.OnPublicFiles Cb Cb.Pv
open OnBytes.PscRun (sentOf drawnOf)

variable {K : Type} [Field K] [Fintype K] (c : BatFoldCaller K) (rB rE rR : Round)

/-- the fold of the caller -/
noncomputable abbrev Yc := c.Sh.fold c.s.Sb c.s.sl c.s.Z

/-- The six readings. -/
structure Rd where
  viewB : rB.Msg → rB.Chal → Fmt.RoundView
  viewE : rE.Msg → rE.Chal → Fmt.RoundView
  viewR : rR.Msg → rR.Chal → Fmt.RoundView
  rdK   : OnBytes.E → K
  rdZ   : List OnBytes.E → Option c.s.Z.D
  rdCh  : List OnBytes.E → Option (Yc c).Ch

variable {c rB rE rR} (ρ : Rd c rB rE rR)

/-- rdZ is defined at what the first of the rounds p drew, rdCh at what each of the k + 1 rounds
behind it drew. -/
def Rd.DefAt (p : List Fmt.RoundView) : Prop :=
  (∀ r ∈ p.take 1, (ρ.rdZ (drawnOf r)).isSome) ∧
    ∀ r ∈ (p.drop 1).take ((Yc c).k + 1), (ρ.rdCh (drawnOf r)).isSome

/-- The sum off a written prover's message. -/
noncomputable def Rd.sumOf (m : rE.Msg) : K :=
  (((sentOf (ρ.viewE m (Classical.choice rE.neChal)))[0]?).map ρ.rdK).getD 0

/-- The n scalars off a written prover's message. -/
noncomputable def Rd.scalOf (m : rR.Msg) : Fin (Yc c).n → K := fun i =>
  (((sentOf (ρ.viewR m (Classical.choice rR.neChal)))[i.1]?).map ρ.rdK).getD 0

/-- The map of the k rounds. -/
noncomputable def Rd.carK : ∀ k : ℕ,
    CarryS (List.replicate k rR) (List.replicate k (sRoundS K (Yc c).Ch (Yc c).n))
  | 0 => .nil
  | k + 1 => .step (fun m => ((), ρ.scalOf m)) (fun m ch => ρ.rdCh (drawnOf (ρ.viewR m ch)))
      fun _ _ => Rd.carK k

/-- The map of the place. -/
noncomputable def Rd.carS :
    CarryS (rB :: rE :: List.replicate (Yc c).k rR)
      (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).shape :=
  .step (fun _ => ((), ())) (fun m ch => ρ.rdZ (drawnOf (ρ.viewB m ch))) fun _ _ =>
    .step (fun m => ((), ρ.sumOf m)) (fun m ch => ρ.rdCh (drawnOf (ρ.viewE m ch))) fun _ _ =>
      ρ.carK (Yc c).k

/-- The reading of the k written rounds. -/
def Rd.vK : ∀ k : ℕ, Tr (List.replicate k rR) → List Fmt.RoundView
  | 0, _ => []
  | k + 1, τ => ρ.viewR τ.1 τ.2.1 :: Rd.vK k τ.2.2

/-- The reading of the written stretch. -/
noncomputable def Rd.V (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) : List Fmt.RoundView :=
  ρ.viewB τ.1 τ.2.1 :: ρ.viewE τ.2.2.1 τ.2.2.2.1 :: ρ.vK (Yc c).k τ.2.2.2.2

theorem Rd.vK_length : ∀ (k : ℕ) (τ : Tr (List.replicate k rR)), (ρ.vK k τ).length = k
  | 0, _ => rfl
  | k + 1, τ => by
    show (ρ.viewR τ.1 τ.2.1 :: ρ.vK k τ.2.2).length = k + 1
    rw [List.length_cons, Rd.vK_length k]

/-- The k rounds have an image where rdCh is defined at what each drew. -/
theorem Rd.carK_some : ∀ (k : ℕ) (τ : Tr (List.replicate k rR)),
    (∀ rv ∈ ρ.vK k τ, (ρ.rdCh (drawnOf rv)).isSome) → ∃ τ', (ρ.carK k).tr τ = some τ'
  | 0, _, _ => ⟨(), rfl⟩
  | k + 1, τ, h => by
    obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.1 (h (ρ.viewR τ.1 τ.2.1) List.mem_cons_self)
    obtain ⟨τ', hτ'⟩ := Rd.carK_some k τ.2.2 fun rv hrv => h rv (List.mem_cons_of_mem _ hrv)
    refine ⟨(((), ρ.scalOf τ.1), ch, τ'), ?_⟩
    obtain ⟨m, x, t⟩ := τ
    show (ρ.rdCh (drawnOf (ρ.viewR m x))).bind (fun c' => ((ρ.carK k).tr t).map fun τ' =>
      (((), ρ.scalOf m), c', τ')) = _
    rw [hch, hτ']
    rfl

theorem drawnOf_one {r : Fmt.RoundView} {x : OnBytes.E} (h : r.drawn.elems = [x.triple]) :
    drawnOf r = [x] := by
  unfold drawnOf
  rw [h]
  rfl

theorem roundsHold_drawn : ∀ {rs : List Fmt.RoundView} {qs : List (OnBytes.E × OnBytes.E)}
    {gs : List OnBytes.E}, RoundsHold rs qs gs → ∀ r ∈ rs, ∃ g, drawnOf r = [g]
  | [], [], [], _, _, hr => absurd hr (List.not_mem_nil)
  | r :: rs, q :: qs, g :: gs, h, r', hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨g, drawnOf_one h.2.1⟩
    · exact roundsHold_drawn h.2.2 r' hr
  | [], [], _ :: _, h, _, _ => h.elim
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _ => h.elim

theorem roundsHold_length : ∀ {rs : List Fmt.RoundView} {qs : List (OnBytes.E × OnBytes.E)}
    {gs : List OnBytes.E}, RoundsHold rs qs gs → rs.length = gs.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by
    rw [List.length_cons, List.length_cons, roundsHold_length h.2.2]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

variable (L : List (BatFoldCaller K))

/-- **The batching and the fold meet the typed block.** -/
theorem batFold_meet
    (hfx : c.fx.2 * (HVar.plain K (Yc c).n).mon c.fx.1 = 1) {g o : Nat} {row : GroupRow}
    {lay : GroupLayout} {F : FoldShape} {out : SingleRows} {x x4 x6 x7 : Ctx}
    (hd : x.ch.dry = false) (ht : ρ.DefAt x.ch.pending)
    (hb : (batVerify g).Yields x (row, lay) x4) (hn : x6.ch = x4.ch)
    (hf : (foldVerify F row (some o)).Yields x6 out x7) (hk : F.layout.k = (Yc c).k)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (rest : List Fmt.RoundView)
    (hp : x.ch.pending = ρ.V τ ++ rest) :
    ∃ τ' a', ρ.carS.tr τ = some τ' ∧ ((kBatFoldRide L).block c).R.red.out a τ' = some a' ∧
      x7.ch.pending = rest := by
  obtain ⟨vB, xb, b1, -, b3, b4⟩ := batVerify_view g row lay x x4 hd hb
  have d6 : x6.ch.dry = false := by rw [hn]; exact b4.1
  obtain ⟨_, v₀, rs, sum, eps, qs, gs, -, -, -, -, f1, -, f3, f4, f5, -, -⟩ :=
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
  obtain ⟨xo, hxo⟩ := Option.isSome_iff_exists.1
    (BatFold.batFoldRide_total c.s c.Sh c.fx c.St₀ c.E₀ hfx a.1 a.2
      (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk))
  refine ⟨_, (xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
    (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk)), himg, ?_, e4⟩
  exact congrArg (Option.map fun xo' => (xo', (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
    (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk))) hxo

/-- What the typed verifier puts out on the image of τ; d where there is none. -/
noncomputable def Rd.aft (d : ((kBatFoldRide L).dst c).X × ((kBatFoldRide L).dst c).E.Str)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) :
    ((kBatFoldRide L).dst c).X × ((kBatFoldRide L).dst c).E.Str :=
  ((ρ.carS.tr τ).bind (((kBatFoldRide L).block c).R.red.out a)).getD d

/-- **The law of the place "BAT, FOLD epsilon, k times FOLD round".** -/
theorem batFold_place
    (hfx : c.fx.2 * (HVar.plain K (Yc c).n).mon c.fx.1 = 1) {g o : Nat} {row : GroupRow}
    {lay : GroupLayout} {F : FoldShape} {out : SingleRows} {x x4 x6 x7 : Ctx}
    (hd : x.ch.dry = false) (ht : ρ.DefAt x.ch.pending)
    (hb : (batVerify g).Yields x (row, lay) x4) (hn : x6.ch = x4.ch)
    (hf : (foldVerify F row (some o)).Yields x6 out x7) (hk : F.layout.k = (Yc c).k)
    (ok : Tr (rB :: rE :: List.replicate (Yc c).k rR) → Prop)
    (d : ((kBatFoldRide L).dst c).X × ((kBatFoldRide L).dst c).E.Str)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) :
    PlaceAt ρ.V ok ((kBatFoldRide L).block c) ρ.carS τ x.ch.pending a x7.ch.pending
      (ρ.aft L d a τ) := by
  intro rest _ hp
  obtain ⟨τ', a', h1, h2, h3⟩ := batFold_meet ρ L hfx hd ht hb hn hf hk a τ rest hp
  refine ⟨τ', h1, ?_, h3⟩
  unfold Rd.aft
  rw [h1]
  show _ = some ((((kBatFoldRide L).block c).R.red.out a τ').getD d)
  rw [h2]
  rfl

end VerifiableInference.OnPublicFiles.BatFoldAt

#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batFold_meet
#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batFold_place
