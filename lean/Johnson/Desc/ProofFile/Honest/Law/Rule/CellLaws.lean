-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/CellLaws.lean: the two conditions at a part's cell. Take a
cell that is as `PartCell` says (Honest/Law/Rule/Where.lean), at a list of parts that meets `Good`
(Honest/Rule.lean: `Lettered.goodAt`). Then its own row is a lens; the spender's and the owner's
condition (Honest/Law/Rule/Items.lean: `RowOk.exact`, `RowOk.fresh`) hold; and it takes what the
book has for it (`part_laws`). `bud` is a hypothesis here, at the part's position. It is the
eighteenth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `dryFold_input`, `chain_states`   two small lemmas
  2  `CellOk`, `part_laws`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Where

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Two small lemmas -/

theorem dryFold_input : ∀ (hs : List (Option (State W Y → Y))) (ds : List Fmt.Drawn)
    (t : State W Y), (dryFold hs ds t).input = t.input
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | h :: hs, d :: ds, t => by
    show (dryFold hs ds (dryStep h d t)).input = t.input
    rw [dryFold_input hs ds]
    cases h <;> rfl

/-- A chain's `Step`s declare the description's own rounds and oracle messages. -/
theorem chain_states {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss →
    (ss.map fun s => (s.decl, s.oracles)) = bs.flatMap fun b => b.rounds.zip b.oracles
  | [], ss, h => by
    simp only [chainSteps] at h
    cases h
    rfl
  | b :: bs, ss, h => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok h
    have ih := chain_states bs l hl
    rcases hcase with ⟨-, rfl⟩ | ⟨g, c, -, hr, -, -, rfl⟩
    · rw [List.map_append, ih, bare_states b, List.flatMap_cons]
    · rw [List.map_append, ih, row_states g b v c hr ho, List.flatMap_cons]

/-! ## 2 The main lemma -/

/-- Three of the clauses that `RowOk` asks of a cell (`row`, `exact`, `fresh`); that it takes what
the book has for it (`due`); that its chain is `ch` (`chain`). `RowOk` asks more of a cell: `here`,
`within`, `vis`, `owns`, `order`. -/
structure CellOk {F : FileDescription Xi} {Bk : ProverCoinCounts} (ord : List Place) (ch : Nat)
    (C : Cell Bk (Stand F) (List (Shown × Fmt.Drawn))) : Prop where
  row : RowAt Bk C.addr C.chain C.takes C.get C.put
  exact : ∀ ca φ, C.live φ = true → C.On ca φ →
    (unif (Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named))).map
      (fun c => C.speaks c.1 c.2 ca φ) = (unif (Cs C.simTakes)).map (C.tell φ)
  fresh : ∀ (p : Addr) sp ca φ,
    (unif (Cs C.takes)).map (fun c => (cutAll c (Bk.spentBy C.addr p), C.speaks c sp ca φ,
        cutAll c (Bk.knownBy ord C.addr p))) =
      (unif (CsAll ((Bk.spentBy C.addr p).map Ahead.named) × Cs C.takes)).map fun a =>
        (some a.1, C.speaks a.2 sp ca φ, cutAll a.2 (Bk.knownBy ord C.addr p))
  due : C.takes = dueAt (Bk.rowsOf ch) C.addr
  chain : C.chain = ch

/- **The main lemma.** `hv`, `hpb`: `v` and `pb` are what `Face.sees` and `Face.pub` give at the
input of `m₀`. `hσ`: the list's side without a fall (`Lettered.side` at its default `fs := []`),
while `hgood` is `goodAt` at the chain's falls `fs`. `earlier`: the earlier chains' declared rounds:
the cell is built at `preOf` (Honest/Rule.lean) of them at the list's place, as `goodAt` makes the
parameter `pre` of `Good`. The other parameters are glossed in
Honest/Law/Rule/Where.lean and Honest/Law/Rule/RowHere.lean. -/
theorem part_laws {F : FileDescription Xi} {Bk : ProverCoinCounts} (st : List (Nat × Nat × List UInt64))
    (ch ft : Nat) (tree : Nat → List Nat) (φ : Face V W Pb) (pb : Pb)
    (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
    (v : Option V) (rsAll : List (Fmt.DeclaredRound × List Oracle)) (ord : List Place)
    (bs : List (Block S Cl)) (fs : List (Fall S)) (L : Lettered Bk S Cl V W Y Pb)
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound))
    (σ : Side S Cl V W Y Pb) (hgood : L.goodAt earlier φ bs ord ch ft fs) (hσ : L.side bs = some σ)
    (hv : v = φ.sees m₀.st.input) (hpb : pb = φ.pub m₀.st.input)
    (hbud : ∀ u ∈ σ.members, ∀ (dsu : List Fmt.Drawn)
      (kp ku kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn)
      (rp rq : List (Fmt.DeclaredRound × List Oracle)),
      SegAt keys ⟨σ.block.place, u.number⟩ kp ku kq → ku.length = u.rounds.length →
      dsAll = dp ++ dsu ++ dq → rsAll = rp ++ u.rounds ++ rq → dp.length = kp.length →
      rp.length = kp.length → dsu.length = u.rounds.length →
      L.bud u.number dsu (asksFrom tree (u.rounds.map (·.2.length)) (rp.map (·.2.length)).sum))
    (C : Cell Bk (Stand F) (List (Shown × Fmt.Drawn)))
    (hP : PartCell (F := F) st ch ft tree φ pb keys dsAll m₀ v rsAll
      (preOf ch ft earlier bs L.place) σ L.On C) :
    CellOk ord ch C := by
  obtain ⟨u, dsu, kp, kq, dp, dq, rp, rq, hf, hu, rfl, hk, hd, hr, l1, l2, l3, l4, l5, f1, f2, hdry,
    hstop, hfit⟩ := hP
  have hkl : ((u.rounds.zip u.part.moves).map fun z =>
      ((⟨σ.block.place, u.number⟩ : Addr), some z.2.hand)).length = u.rounds.length := by
    rw [List.length_map, List.length_zip, l4, Nat.min_self]
  have hb := hbud u hu dsu kp _ kq dp dq rp rq
    ⟨hk, f1, fun q hq => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hq
        rfl, f2, fun e => by
        have := congrArg List.length e
        rw [hkl, l4] at this
        exact l5 this⟩ hkl hd hr l1 l2 l3
  have hin : (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st.input = m₀.st.input := by
    rw [hdry]
    exact dryFold_input _ _ _
  have hstop' : u.part.stopAt (φ.sees (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st.input)
      (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).loc dsu ≠ some .hid := by
    rw [hin, ← hv, hdry]
    show u.part.stopAt v (m₀.loc ++ dp) dsu ≠ some .hid
    rw [hstop]
    exact fun e => by cases e
  have hpb' : pb = φ.pub (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st.input := by
    rw [hin]
    exact hpb
  unfold Lettered.side Side.seated at hσ
  cases hfind : bs.find? fun b => b.place == L.place with
  | none =>
    rw [hfind] at hσ
    cases hσ
  | some b =>
    rw [hfind] at hσ
    have eσ : (⟨b, L.row, fallOf [] L.place⟩ : Side S Cl V W Y Pb) = σ := Option.some.inj hσ
    subst eσ
    have hG := hgood ⟨b, L.row, fallOf fs L.place⟩ (by
      unfold Lettered.side Side.seated
      rw [hfind]
      rfl)
    exact
      { row := cellAt_row _ u ch hf
        exact := fun ca Z _ hOn => cell_exact φ ⟨b, L.row, fallOf fs L.place⟩ u pb ch ft _ _ st dsu
            _
          _ _ hf.sp hf.ca hG hu hpb' hfit hb hstop' ca Z hOn
        fresh := fun p sp ca Z => cell_fresh φ ⟨b, L.row, fallOf fs L.place⟩ u pb ch ft _ _ st dsu _
          _ _ hf.sp hf.ca hG hu hfit hb hstop' p sp ca Z
        due := hf.due
        chain := rfl }

end ProofFile.Honest

#print axioms ProofFile.Honest.dryFold_input
#print axioms ProofFile.Honest.chain_states
#print axioms ProofFile.Honest.part_laws
#print axioms ProofFile.Honest.CellOk
