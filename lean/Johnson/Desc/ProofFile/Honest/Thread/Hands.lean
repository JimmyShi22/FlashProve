-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Hands.lean: the rule for `Owed` at a file, from what a kind's
author supplies. `file_owed` (Honest/Thread/FileOwed.lean) takes `good` as a hypothesis of its own:
`Good` (Honest/Side.lean) at every side, at the list's own parameters L.A, L.B (what `Owed.good`
asks follows from it: the head of that file). Here these two parameters are set to `ThrS` (the
invariant together with `Said`) of the state's own input; `Good.plays` and `Good.acc` there are
obtained from the sub-protocols' hypotheses; of `Good` an author supplies `fits`, `exact` and
`fresh` alone (as one term, at any A and B, at the `pre` that the list's place gives: `preOf`,
Honest/Rule.lean). So `good` is no hypothesis any more; and `TrueLaid` is proved
(Honest/Law/Rule/TrueLaid.lean). Definitions, meant as hypotheses, and two terms; and conditional
lemmas. General in the description, the book, the prover and the lists of parts.

  1  `good_at_pair`, `good_at_familyS`   `Good` at `ThrS`; at `ThrS` of the state's own input
  2  `side_fall`, `side_member`, `side_half`   small lemmas on a list's side
  3  `Lettered.LaidAt`, `goodAt_of_hands`   the parameters are set so; one list
  4  `Prover.ownOf`, `Prover.commonOf`, `own_of_ready`, `common_of_ready`   the input that `ready`
     prepares
  5  `file_owed_hands`   the rule

The families. Each chain's `Thread`s and `Said` are a family in that chain's own input (the first
and the second chain's: what all requests share, the stored tables' pads and encoding randomness,
the instance, the trace; the shared chain's: the first two and the key): so "of the state's own
input" is one term for each chain. The hypotheses are then asked at every input, not at those of Rel
alone: `Good.plays` runs over all states. An author's lemmas are general in the `Thread`: so that
costs nothing. The hypotheses at the chains' starts and ends are asked at the inputs of Rel, at the
input that `ready` prepares; those on `Said` at the states as `ChainProgress.start` lays them (the head of
Honest/Thread/FileOwed.lean).

What it is. A conditional lemma on this folder's own definitions. Its conclusion is a definition of
this folder, a structure of hypotheses: no property, and none of the library's goals. Met trivially:
as the head of Honest/Thread/FileOwed.lean says. `YesS` is among its hypotheses, which `file_owed`
does not ask: `Good.acc` needs it.

Limits.
  * Worked examples: at toy examples alone (Honest/Thread/Four/FourHands.lean: a toy example whose
    first chain has its sealing sub-protocol's rounds alone, no prover's side and no list of parts,
    so that the hypotheses `hand₁`, `let₁`, `on₁` and the first field of `hbud` hold vacuously
    there, whose `Thread`s have no item, no clause of `rides` and no clause of `keeps`, at Said :=
    True; not in the sealed library; its `Good` lacks the parameter `pre`, so it does not fit
    `file_owed_hands` as stated here: of this statement there is no worked example).
  * Among the hypotheses that the prose above does not name: `Block.planOk` and `Block.shaped` at
    every sub-protocol of the chain (the library's executable tests): `good_at_pair`,
    `goodAt_of_hands`; `FileDescription.planOk` (the library's executable test): `file_owed_hands`;
    `sealPlain` (the first chain's last declared round declares no item except roots, and no root):
    `file_owed_hands`; `ProverCoinCounts.word … = none` (every test on the book passes): `file_owed_hands`.
  * `OwesS`, `YesS` and `OnFromS` are asked at every value of the state's field `opened` that `Said`
    allows (`Thr` does not read it): unless `Said` shuts them out, at `none` and at lists of columns
    that no run opens. At a prover with a part that reads the columns and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`), `PlaysS` at a `Said` that lets `none` through before that
    part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits). Of the field
    `OnFromS` has in hand only what `Said` says of it at the border before the sub-protocol.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileOwed
import Johnson.Desc.ProofFile.Honest.Thread.GoodAt
import Johnson.Desc.ProofFile.Honest.Thread.Laid
import Johnson.Desc.ProofFile.Honest.Law.FallFree
import Johnson.Desc.ProofFile.Honest.Law.Rule.TrueLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 `Good` at `ThrS` -/

/-- **`Good` at `ThrS`, from the sub-protocol's hypotheses asked from `ThrS`**: `good_at_thr`
(Honest/Thread/GoodAt.lean) with `ThrS` in the place of `Thr`. `pre`: `Good`'s parameter, free. -/
theorem good_at_pair (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    {b : Nat} {σ : Side S Cl V W X Pb} {ord : List Place}
    {A' B' : Coins Bk → S → Mid W X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {fl : Nat → S → List Fmt.Drawn → Option String}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (g₀ : Good pre T.φ σ Bk ord T.chain T.ft A' B' On bud)
    (hfit : T.fits T.bs.length = true) (hsh : ∀ x ∈ T.bs, x.planOk = true ∧ x.shaped = true)
    (hblk : T.bs[b]? = some σ.block)
    (hf : (T.hs.find? fun g => g.place == σ.block.place) = some σ.half)
    (hlaid : ∀ (k : Coins Bk) (v : Option V), ∃ l,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) v [σ.block] T.hs = .ok l)
    (hP : PlaysS T Said b) (hB : BehindS T Said b) (hX : ExchangeS T Said b)
    (hR : RidesPastS T Said b) (hN : SaidNext T Said b) (hY : AcceptedS T Said fl b)
    (hfl : ∀ s ds, σ.fall s ds = none → fl b s ds = none) :
    Good pre T.φ σ Bk ord T.chain T.ft (ThrS T Said b) (ThrS T Said (b + 1)) On bud where
  fits := g₀.fits
  exact := g₀.exact
  fresh := g₀.fresh
  plays := by
    intro k s m E ds hA hd hst
    obtain ⟨l, hl⟩ := hlaid k (T.φ.sees m.st.input)
    obtain ⟨c, hc, rfl⟩ := steps_one_half hf hl
    obtain ⟨y, cols, hy, hcol, hb⟩ := playsOn_of_paysS T Said hfit (lt_of_member T hblk) hblk hP hB
      hX hR (made_next T hfit hsh b) hN k s m E ds _ hA hd (stop_one_back hf hd hst) hl
    exact ⟨c, y, cols, hc, hy, hcol, hb⟩
  acc := by
    intro k s m E ds hA hd hst hfall c y cols hc hy hcol
    obtain ⟨l, hl⟩ := hlaid k (T.φ.sees m.st.input)
    obtain ⟨c', hc', rfl⟩ := steps_one_half hf hl
    have ec : c' = c := Except.ok.inj (hc'.symm.trans hc)
    subst ec
    exact saysYes_of_acceptedS T Said hblk hY k s m E ds _ y cols hA hd (stop_one_back hf hd hst)
      (hfl s ds hfall) hl hy hcol

/-- **At `ThrS` of the state's own input**: one pair A, B for all inputs. `pre`: `Good`'s parameter,
free. -/
theorem good_at_familyS (T : W → Thread Bk S Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop) {φ : Face V W Pb} {chain ft b : Nat}
    {σ : Side S Cl V W X Pb} {ord : List Place}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hφ : ∀ w, (T w).φ = φ) (hc : ∀ w, (T w).chain = chain) (hf : ∀ w, (T w).ft = ft)
    (g : ∀ w, Good pre (T w).φ σ Bk ord (T w).chain (T w).ft (ThrS (T w) (Sd w) b)
      (ThrS (T w) (Sd w) (b + 1)) On bud) (w₁ : W) :
    Good pre φ σ Bk ord chain ft (fun k s m E => ThrS (T m.st.input) (Sd m.st.input) b k s m E)
      (fun k s m E => ThrS (T m.st.input) (Sd m.st.input) (b + 1) k s m E) On bud := by
  have g' : ∀ w, Good pre φ σ Bk ord chain ft (ThrS (T w) (Sd w) b) (ThrS (T w) (Sd w) (b + 1))
      On bud := fun w => by
    have h := g w
    rw [hφ w, hc w, hf w] at h
    exact h
  exact
    { fits := (g' w₁).fits
      exact := (g' w₁).exact
      fresh := (g' w₁).fresh
      plays := fun k s m E ds hA hd hst => by
        obtain ⟨c, y, cols, h1, h2, h3, h4⟩ := (g' m.st.input).plays k s m E ds hA hd hst
        refine ⟨c, y, cols, h1, h2, h3, fun s' n hs => ?_⟩
        show ThrS (T y.2.st.input) (Sd y.2.st.input) (b + 1) k s' (y.2.took cols) (E.add y.1)
        rw [(play_mid _ _ _ _ _ h2).1]
        exact h4 s' n hs
      acc := fun k s m E ds hA hd hst hfall c y cols h1 h2 h3 =>
        (g' m.st.input).acc k s m E ds hA hd hst hfall c y cols h1 h2 h3 }

/-! ## 2 Small lemmas on a list's side -/

theorem side_fall {L : Lettered Bk S Cl V W X Pb} {bs : List (Block S Cl)} {fs : List (Fall S)}
    {σ : Side S Cl V W X Pb} (h : L.side bs fs = some σ) : σ.fall = fallOf fs L.place := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

theorem side_member {L : Lettered Bk S Cl V W X Pb} {bs : List (Block S Cl)} {fs : List (Fall S)}
    {σ : Side S Cl V W X Pb} (h : L.side bs fs = some σ) : ∃ b : Nat, bs[b]? = some σ.block := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact List.getElem?_of_mem (List.mem_of_find?_eq_some hb)

theorem side_half {L : Lettered Bk S Cl V W X Pb} {bs : List (Block S Cl)} {fs : List (Fall S)}
    {σ : Side S Cl V W X Pb} (h : L.side bs fs = some σ) :
    σ.half = ⟨L.place, L.row.map (·.1)⟩ := by
  have hp := side_place h
  unfold Lettered.side Side.seated at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Side.half
  rw [hp]

/-! ## 3 The parameters are set so; one list -/

/-- **The list's parameters A, B are `ThrS` of the state's own input**, before the sub-protocol at
the list's place and after it. It is a definition, meant as a hypothesis: two equations, which
whoever supplies the lists proves by unfolding. -/
def Lettered.LaidAt (L : Lettered Bk S Cl V W X Pb) (T : W → Thread Bk S Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop) (bs : List (Block S Cl)) : Prop :=
  ∀ b blk, bs[b]? = some blk → blk.place = L.place →
    L.A = (fun k s m E => ThrS (T m.st.input) (Sd m.st.input) b k s m E) ∧
      L.B = fun k s m E => ThrS (T m.st.input) (Sd m.st.input) (b + 1) k s m E

/-- **One list**: `Good` at the list's own parameters, from what its author supplies (`hand`: at the
`pre` that the list's place gives, `preOf`). -/
theorem goodAt_of_hands {φ : Face V W Pb} {bs : List (Block S Cl)} {ord : List Place}
    {chain ft : Nat} {fs : List (Fall S)} {hs : List (Placed V W X)}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (T : W → Thread Bk S Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (L : Lettered Bk S Cl V W X Pb)
    (hT : ∀ w, (T w).φ = φ ∧ (T w).chain = chain ∧ (T w).ft = ft ∧ (T w).bs = bs ∧ (T w).hs = hs)
    (hfit : ∀ w, (T w).fits bs.length = true)
    (hsh : ∀ x ∈ bs, x.planOk = true ∧ x.shaped = true)
    (hhalf : (hs.find? fun g => g.place == L.place) = some ⟨L.place, L.row.map (·.1)⟩)
    (hlaid : ∀ (j : Nat) (blk : Block S Cl), bs[j]? = some blk → ∀ (k : Coins Bk) (v : Option V),
      ∃ l, chainSteps Bk (Bk.rowsOf chain) (k.look chain) v [blk] hs = .ok l)
    (hand : ∀ σ, L.side bs fs = some σ → ∃ A' B',
      Good (preOf chain ft earlier bs L.place) φ σ Bk ord chain ft A' B' L.On L.bud)
    (o : ∀ w, OwesS (T w) (Sd w)) (n : ∀ w b, SaidNext (T w) (Sd w) b)
    (y : ∀ w, YesS (T w) (Sd w) (fallsBy fs bs)) (hL : L.LaidAt T Sd bs) (w₁ : W) :
    L.goodAt earlier φ bs ord chain ft fs := by
  unfold Lettered.goodAt
  intro σ hσ
  obtain ⟨b, hb⟩ := side_member hσ
  obtain ⟨eA, eB⟩ := hL b σ.block hb (side_place hσ)
  rw [eA, eB]
  obtain ⟨A', B', g₀⟩ := hand σ hσ
  refine good_at_familyS T Sd (fun w => (hT w).1) (fun w => (hT w).2.1) (fun w => (hT w).2.2.1)
    (fun w => ?_) w₁
  obtain ⟨e1, e2, e3, e4, e5⟩ := hT w
  have hb' : (T w).bs[b]? = some σ.block := by rw [e4]; exact hb
  have hlt := lt_of_member (T w) hb'
  obtain ⟨hP, hB, hX, hR⟩ := o w b hlt
  refine good_at_pair (T w) (Sd w) (fl := fallsBy fs bs) (A' := A') (B' := B')
    (by rw [e1, e2, e3]; exact g₀) (by rw [e4]; exact hfit w) (by rw [e4]; exact hsh) hb' ?_ ?_
    hP hB hX hR (n w b) (y w b hlt) ?_
  · rw [e5, side_place hσ, side_half hσ]
    exact hhalf
  · intro k v
    rw [e2, e5]
    exact hlaid b σ.block hb k v
  · intro s ds hfall
    unfold fallsBy
    rw [hb]
    show fallOf fs σ.block.place s ds = none
    rw [side_place hσ, ← side_fall hσ]
    exact hfall

end

/-! ## 4 The input that `ready` prepares -/

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- The first and the second chain's input, from the arguments: with the prover's own trace, where
there is one; `tr₀`: any trace, for where there is none. -/
def Prover.ownOf (H : Prover W₀ Rc Xi Ky Tr X₀ X) (tr₀ : Tr) (w₀ : W₀) (rc : Rc) (x : Xi) :
    Local W₀ Rc Xi Tr := ⟨w₀, rc, x, (H.trace w₀ x).getD tr₀⟩

/-- The shared chain's input, from the arguments. -/
def Prover.commonOf (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) :
    Common W₀ Rc Ky := ⟨w₀, rc, H.key x⟩

theorem own_of_ready {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w₀ rc x k = .ok R) (tr₀ : Tr) : R.own = H.ownOf tr₀ w₀ rc x := by
  obtain ⟨-, tr, htr, hown, -, -, -, -⟩ := ready_ok hR
  unfold Prover.ownOf
  rw [hown, htr]
  rfl

theorem common_of_ready {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w₀ rc x k = .ok R) : R.common = H.commonOf w₀ rc x := by
  obtain ⟨-, tr, -, -, hcom, -, -, -⟩ := ready_ok hR
  exact hcom

/-! ## 5 The rule -/

/-- **The rule for `Owed` at a file, from what a kind's author supplies.** A conditional lemma on
this folder's own definitions. Its conclusion is a definition of this folder, a structure of
hypotheses: no property, and none of the library's goals. -/
theorem file_owed_hands {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (hand₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    (let₁ : ∀ L ∈ G.first, L.LaidAt T₁ S₁ F.first.blocksInOrder)
    (let₂ : ∀ L ∈ G.shared, L.LaidAt T₂ S₂ F.shared.blocksInOrder)
    (let₃ : ∀ L ∈ G.second, L.LaidAt T₃ S₃ F.second.blocksInOrder)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    {w₁ : W₀} {rc₁ : Rc} {x₁ : Xi} {k₁ : Coins Bk} {R₁ : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hone : ready F Bk (G.prover H) w₁ rc₁ x₁ k₁ = .ok R₁)
    (hbud : BudDebts F Bk G)
    (sits : ∀ w w', Sits F (G.prover H) (T₁ w) (T₂ w') (T₃ w))
    (o₁ : ∀ w, OwesS (T₁ w) (S₁ w)) (o₂ : ∀ w, OwesS (T₂ w) (S₂ w))
    (o₃ : ∀ w, OwesS (T₃ w) (S₃ w))
    (n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b) (n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b)
    (n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b)
    (y₁ : ∀ w, YesS (T₁ w) (S₁ w) (fallsBy G.falls₁ F.first.blocksInOrder))
    (y₂ : ∀ w, YesS (T₂ w) (S₂ w) (fallsBy G.falls₂ F.shared.blocksInOrder))
    (y₃ : ∀ w, YesS (T₃ w) (S₃ w) (fallsBy G.falls₃ F.second.blocksInOrder))
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ R.own) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ R.common) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ R.own F.first.blocksInOrder.length k m₁ →
        S₂ R.common F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ R.own 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G Rel := by
  obtain ⟨ht, -, -, -, -, -, -, -⟩ := ready_ok hone
  obtain ⟨t1, t2, t3⟩ := tests_twice ht
  have r1 : (G.first.map (·.place)).Nodup := by
    have e' : ((G.first.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := nodup_of_twice t1
    rw [List.map_map] at e'
    exact e'
  have r2 : (G.shared.map (·.place)).Nodup := by
    have e' : ((G.shared.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed Empty (Common W₀ Rc Ky) X₀)).map (·.place)).Nodup := nodup_of_twice t2
    rw [List.map_map] at e'
    exact e'
  have r3 : (G.second.map (·.place)).Nodup := by
    have e' : ((G.second.map fun L => (⟨L.place, L.row.map (·.1)⟩ :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).map (·.place)).Nodup := nodup_of_twice t3
    rw [List.map_map] at e'
    exact e'
  obtain ⟨s1, s2, s3⟩ := planOk_all plan
  have good :
      (∀ L ∈ G.first, L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared, L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃ :=
    ⟨fun L hL => goodAt_of_hands (hs := (G.prover H).first) T₁ S₁ L
        (fun w => (sits w R₁.common).one) (fun w => (sits w R₁.common).fits.1) s1
        (find_row G.first r1 L hL) (fun j blk hj k v => laid_first hone hj k v) (hand₁ L hL) o₁ n₁
        y₁ (let₁ L hL) R₁.own,
      fun L hL => goodAt_of_hands (hs := (G.prover H).shared) T₂ S₂ L
        (fun w => (sits R₁.own w).two) (fun w => (sits R₁.own w).fits.2.1) s2
        (find_row G.shared r2 L hL) (fun j blk hj k v => laid_shared hone hj k v) (hand₂ L hL) o₂
        n₂ y₂ (let₂ L hL) R₁.common,
      fun L hL => goodAt_of_hands (hs := (G.prover H).second) T₃ S₃ L
        (fun w => (sits w R₁.common).three) (fun w => (sits w R₁.common).fits.2.2) s3
        (find_row G.second r3 L hL) (fun j blk hj k v => laid_second hone hj k v) (hand₃ L hL) o₃
        n₃ y₃ (let₃ L hL) R₁.own⟩
  exact file_owed (fun w₀ rc x => T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => T₂ ((G.prover H).commonOf w₀ rc x))
    (fun w₀ rc x => T₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => S₂ ((G.prover H).commonOf w₀ rc x))
    (fun w₀ rc x => S₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) (depthAt F)
    plan book seats hq hroot good input hst hone hbud
    (fun w₀ rc _ _ => ⟨fun ρ p _ => trueTo_one F _ ρ p, fun ρ p _ => trueTo_two F _ ρ p,
      fun ρ p₀ p₁ p _ => trueTo_three F _ ρ p₀ p₁ p⟩)
    (fun _ _ _ _ => sits _ _) (fun _ _ _ _ => o₁ _) (fun _ _ _ _ => o₂ _) (fun _ _ _ _ => o₃ _)
    (fun _ _ _ _ => n₁ _) (fun _ _ _ _ => n₂ _) (fun _ _ _ _ => n₃ _)
    (fun w₀ rc x h k R hR => by
      show Enters₁ F (G.prover H) (T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) w₀ rc x k R
      rw [← own_of_ready hR]
      exact a₁ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show Enters₂ F (G.prover H) (T₂ ((G.prover H).commonOf w₀ rc x)) w₀ rc x k R
      rw [← common_of_ready hR]
      exact a₂ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show DoorBehind F (G.prover H) (T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
        (T₂ ((G.prover H).commonOf w₀ rc x)) (T₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) x k R
      rw [← own_of_ready hR, ← common_of_ready hR]
      exact a₃ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x) 0 k
        { R.start₁ (G.prover H) with opened := some [] }
      rw [← own_of_ready hR]
      exact e₁ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₂ ((G.prover H).commonOf w₀ rc x) 0 k { R.start₂ (G.prover H) with opened := some [] }
      rw [← common_of_ready hR]
      exact e₂ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show ∀ m₁ m₂ o₁ o₂, S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x) F.first.blocksInOrder.length k m₁ →
        S₂ ((G.prover H).commonOf w₀ rc x) F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x) 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) }
      rw [← own_of_ready hR, ← common_of_ready hR]
      exact e₃ w₀ rc x h k R hR)
    (fun _ _ _ _ => on₁ _) (fun _ _ _ _ => on₂ _) (fun _ _ _ _ => on₃ _)

end ProofFile.Honest

#print axioms ProofFile.Honest.good_at_pair
#print axioms ProofFile.Honest.good_at_familyS
#print axioms ProofFile.Honest.side_fall
#print axioms ProofFile.Honest.side_member
#print axioms ProofFile.Honest.side_half
#print axioms ProofFile.Honest.goodAt_of_hands
#print axioms ProofFile.Honest.own_of_ready
#print axioms ProofFile.Honest.common_of_ready
#print axioms ProofFile.Honest.file_owed_hands
#print axioms ProofFile.Honest.Lettered.LaidAt
#print axioms ProofFile.Honest.Prover.ownOf
#print axioms ProofFile.Honest.Prover.commonOf
