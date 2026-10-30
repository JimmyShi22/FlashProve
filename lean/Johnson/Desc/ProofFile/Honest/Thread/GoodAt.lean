-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/GoodAt.lean: `Good` (Honest/Side.lean) at a `Thread`'s own
parameters: A := the invariant before the sub-protocol, B := the invariant after it, which `Good`
asks at the state that has taken the sub-protocol's columns (`Mid.took`). Its fields `plays` and
`acc` there say what the sub-protocol's hypotheses say (Honest/Thread/Pays.lean): here they are
obtained from these hypotheses; `fits`, `exact` and `fresh`, which read neither A nor B, are taken
over from `Good` at any A and B, at the same value of its parameter `pre`, which is free. A
conditional lemma on this folder's own definitions, general in the `Thread`'s parameters: no kind is
named.

  `stop_one_back`   where the list of parts does not stop, the chain's stops return `none` at the
     sub-protocol
  `good_at_thr`   the lemma, at one `Thread`
  `good_at_family`   at the `Thread` of the state's own input: one pair A, B for all inputs

Hypotheses of `good_at_thr` besides those of Honest/Thread/Pays.lean: `g₀`; the executable test
`T.fits`; `Block.planOk` and `Block.shaped` at every sub-protocol of `T.bs`; the sub-protocol is the
side's own, and the prover's side at its place is the side's (`hblk`, `hf`); `hfl`; and `hlaid`: the
book gives the sub-protocol's `Step`s their coins, at all coins: `Good.plays` concludes that, while
those hypotheses assume it. `MadeNext` is not among them: it is proved (`made_next`).

Its place in `Owed.good` (Honest/Owed.lean). That field reads the list's parameters L.A, L.B, each
with the field's clause beside it (`Lettered.withField`): fields of one structure for all inputs;
the rules for a file need the `Thread`s as a family in the input: so "L.A := the invariant" cannot
be written there. "The invariant of the state's own input" can (`good_at_family`): so whoever
supplies the lists of parts sets these two parameters so, and `plays` and `acc` there are obtained
from the sub-protocol's hypotheses: no kind's author proves them a second time, at a list none of
whose parts reads the field. From `goodAt` at these two parameters to what that field asks:
`Lettered.goodAt_withField` (Honest/FieldFree.lean).

Limits.
  * It is none of the library's goals.
  * A := `Thr T b` does not read the state's field `opened`: so `plays` and `acc` there, like the
    hypotheses of Honest/Thread/Pays.lean from which they are obtained, are asked at every value of
    that field, `none` too. At a side with a part that reads the field and errs at `none`, `Plays`
    is met only vacuously (Honest/Thread/ThrField.lean, Limits).
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `stop_one_back`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

theorem stop_one_back {φ : Face V W Pb} {hs : List (Placed V W X)} {σ : Side S Cl V W X Pb}
    {w : W} {loc ds : List Fmt.Drawn}
    (hf : (hs.find? fun g => g.place == σ.block.place) = some σ.half)
    (hd : drawsFit σ.block.rounds ds = true) (hst : σ.stopAt φ w loc ds = none) :
    chainStopAt (φ.sees w) [σ.block] hs loc ds = none := by
  have hlen := drawsFit_length _ _ hd
  show ((hs.find? fun g => g.place == σ.block.place).bind fun g =>
    rowStopAt (φ.sees w) g.parts loc (ds.take σ.block.rounds.length)).or
      (none : Option Why) = none
  rw [hf, ← hlen, List.take_length]
  show (σ.stopAt φ w loc ds).or none = none
  rw [hst]
  rfl

/-- **`Good` at the `Thread`'s own parameters, from the sub-protocol's hypotheses.** `g₀`: `Good` at
any A and B, and at any `pre`: its `fits`, `exact` and `fresh` are taken over. `fl`: the falls by
the sub-protocol's number: at b it returns `none` where the side's own fall returns `none`. A
conditional lemma on this folder's own definitions. It is none of the library's goals. -/
theorem good_at_thr (T : Thread Bk S Cl V W X Pb) {b : Nat} {σ : Side S Cl V W X Pb}
    {ord : List Place} {A' B' : Coins Bk → S → Mid W X → Env → Prop}
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
    (hP : Plays T b) (hB : Behind T b) (hX : Exchange T b) (hR : RidesPast T b)
    (hY : Accepted T fl b) (hfl : ∀ s ds, σ.fall s ds = none → fl b s ds = none) :
    Good pre T.φ σ Bk ord T.chain T.ft (Thr T b) (Thr T (b + 1)) On bud where
  fits := g₀.fits
  exact := g₀.exact
  fresh := g₀.fresh
  plays := by
    intro k s m E ds hA hd hst
    obtain ⟨l, hl⟩ := hlaid k (T.φ.sees m.st.input)
    obtain ⟨c, hc, rfl⟩ := steps_one_half hf hl
    obtain ⟨y, cols, hy, hcol, hb⟩ := playsOn_of_pays T hfit (lt_of_member T hblk) hblk hP hB hX hR
      (made_next T hfit hsh b) k s m E ds _ hA hd (stop_one_back hf hd hst) hl
    exact ⟨c, y, cols, hc, hy, hcol, hb⟩
  acc := by
    intro k s m E ds hA hd hst hfall c y cols hc hy hcol
    obtain ⟨l, hl⟩ := hlaid k (T.φ.sees m.st.input)
    obtain ⟨c', hc', rfl⟩ := steps_one_half hf hl
    have ec : c' = c := Except.ok.inj (hc'.symm.trans hc)
    subst ec
    exact saysYes_of_accepted T hblk hY k s m E ds _ y cols hA hd (stop_one_back hf hd hst)
      (hfl s ds hfall) hl hy hcol

/-- **`Good` at the `Thread` of the state's own input.** `T`: the `Thread`s as a family in the
input. A := at a state, the invariant of that state's own input, before the sub-protocol; B := the
same after it: one pair for all inputs: so it can be written in a list's fields L.A, L.B. `pre`:
`Good`'s parameter, free. `w₁`: any one input (for `fits`, `exact`, `fresh`, which read neither A
nor B). A conditional lemma on this folder's own definitions. It is none of the library's goals. -/
theorem good_at_family (T : W → Thread Bk S Cl V W X Pb) {φ : Face V W Pb} {chain ft b : Nat}
    {σ : Side S Cl V W X Pb} {ord : List Place}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hφ : ∀ w, (T w).φ = φ) (hc : ∀ w, (T w).chain = chain) (hf : ∀ w, (T w).ft = ft)
    (g : ∀ w,
      Good pre (T w).φ σ Bk ord (T w).chain (T w).ft (Thr (T w) b) (Thr (T w) (b + 1)) On bud)
    (w₁ : W) :
    Good pre φ σ Bk ord chain ft (fun k s m E => Thr (T m.st.input) b k s m E)
      (fun k s m E => Thr (T m.st.input) (b + 1) k s m E) On bud := by
  have g' : ∀ w, Good pre φ σ Bk ord chain ft (Thr (T w) b) (Thr (T w) (b + 1)) On bud :=
      fun w => by
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
        show Thr (T y.2.st.input) (b + 1) k s' (y.2.took cols) (E.add y.1)
        rw [(play_mid _ _ _ _ _ h2).1]
        exact h4 s' n hs
      acc := fun k s m E ds hA hd hst hfall c y cols h1 h2 h3 =>
        (g' m.st.input).acc k s m E ds hA hd hst hfall c y cols h1 h2 h3 }

end ProofFile.Honest

#print axioms ProofFile.Honest.stop_one_back
#print axioms ProofFile.Honest.good_at_thr
#print axioms ProofFile.Honest.good_at_family
