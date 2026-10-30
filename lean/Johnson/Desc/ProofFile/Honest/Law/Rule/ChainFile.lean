-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ChainFile.lean: one chain of a file: `chain_model`
(Honest/Law/Rule/ChainModel.lean) with its hypotheses on look-ups and on reads proved
(Honest/Law/Rule/Members.lean: `look_ok`; Honest/Law/Rule/FaithFile.lean: `faithAll_of`;
Honest/Law/Rule/FaithOwnFile.lean: `faithOwn_of`), from the chain's start (`ChainProgress.start`) to its end.

  1  `chainSteps_length`   as many `Step`s as the sub-protocols have rounds
  2  `chain_file`   the main lemma

Limits.
  * What the field `opened` holds at the chain's start (`htie`: `TieAt`,
    Honest/Law/Rule/OpenedStep.lean) is a hypothesis of `chain_file`. So is `hsrc`: each tree that
    the chain's look-up returns is one of the chain's own, or `2 ≤ ch` (at a file: the second chain,
    whose number is 2).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Members
import Johnson.Desc.ProofFile.Honest.Law.Rule.FaithFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.FaithOwnFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

theorem chainSteps_length {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss → ss.length = (bs.map (·.rounds.length)).sum
  | [], ss, h => by
    simp only [chainSteps] at h
    cases h
    rfl
  | b :: bs, ss, h => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok h
    have ih := chainSteps_length bs l hl
    have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
      rw [List.length_zip, ho, Nat.min_self]
    rw [List.map_cons, List.sum_cons, ← ih]
    rcases hcase with ⟨-, rfl⟩ | ⟨g, c, -, hr, -, -, rfl⟩
    · have e := congrArg List.length (bare_states (W := W) (Y := Y) b)
      rw [List.length_map, hzl] at e
      rw [List.length_append, e]
    · have e := congrArg List.length (row_states g b v c hr ho)
      rw [List.length_map, hzl] at e
      rw [List.length_append, e]

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **One chain of a file, from its start to its end.** `Z`: the `Stand` before the chain. `mid`,
`ver`: the state of the prover's run and the verifier's state there (what `mid` holds in the field
`opened` is dropped: `ChainProgress.start`). `m₀`: the state and the challenges there, as the honest side's
`dryAt` is given them. `trip`: the three chains' rounds, as a function of this chain's. `earlier`:
the earlier chains' declared rounds, as `preOf` (Honest/Rule.lean) takes them. `front`: the columns
that `ChainProgress.start` is handed. `htie`, `hsrc`: see the Limits; `model` (Honest/Law/Rule/Model.lean)
and `file_inv` (Honest/Law/Rule/FileInv.lean) pay both. -/
theorem chain_file {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {front : List OpenedColumn} (x : Xi)
    (ρ : Draws) (R : RealAt Bk) (k : Coins Bk) (ch ft : Nat)
    (φ : Face V W Pb) (pb : Pb) (bs : List (Block S Cl)) (Ls : List (Lettered Bk S Cl V W Y Pb))
    (dsAll : List Fmt.Drawn) (m₀ : Mid W Y) (L : Lay) (hLc : L.chain = ch) (hLf : L.firstTree = ft)
    (Ve : VerAt F S Cl x (storedShown L.stored (storedAsks F ρ)) ch ft) (Z : Stand F)
    (trip : List Played → List Played × List Played × List Played) (hZ0 : Z.laid.of ch = [])
    (hZ : ∀ l, Z.laid.add ch (pairsBy (treeAsks F ρ ch) l 0) =
      laidOf F ρ (trip l).1 (trip l).2.1 (trip l).2.2)
    (htr : ∀ l o pT, L.tree l o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 (trip l).1 (trip l).2.1 (trip l).2.2
        (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2)
    (hsrc : ∀ l o pT, L.tree l o = some pT → ch = (srcOf ch o).1 ∨ 2 ≤ ch)
    (hR : R ch = realIn φ bs Ls ch ft earlier (dryAt (chainKeys bs
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y))) dsAll m₀))
    (hseat : ∀ L ∈ Ls, ∃ σ, L.side bs = some σ ∧ σ.fits = true)
    (hLs : (Ls.map (·.place)).Nodup) (hbs : (bs.map (·.place)).Nodup)
    (hsh : ∀ b ∈ bs, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots)
    (hcuts : ∀ a cs, Bk.cuts.lookup a = some cs → ∀ n ∈ cs, n ≠ 0) (ss : List (Step W Y))
    (hss : chainSteps Bk (Bk.rowsOf ch) (k.look ch) (φ.sees m₀.st.input) bs
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) = .ok ss)
    (mid : Option (Mid W Y)) (ver : Option S)
    (hmid : ∀ m, mid = some m → m.st = m₀.st ∧ m.loc = m₀.loc ∧
      m.seen = (Z.laid.front ch (storedShown L.stored (storedAsks F ρ))).seen)
    (hvm : ver.isSome = true → mid.isSome = true) (hget : Ve.get Z = ver) (a z' : ChainProgress S Cl W Y)
    (ha : ChainProgress.start L bs mid ver front = .ok a) (hw : walk L ss dsAll a = .ok z')
    (htie : TieAt earlier ch ft []
      (if ver.isSome then mid.map ({ · with opened := some front }) else none)
      (Z.laid.front ch (storedShown L.stored (storedAsks F ρ))))
    (hmem : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) dsAll,
      q ∈ allBare F ρ) :
    Kit.real ((chainActs F Bk ch (treeAsks F ρ ch)
        (tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb)
        (fun a => (Ls.flatMap fun L => L.row.map (·.2)).any (·.addr.place == a)) Ve.J bs 0
        dsAll).map (Act.stage x (storedShown L.stored (storedAsks F ρ)) R)) k Z =
      Ve.set { Z with laid := laidOf F ρ (trip z'.laid).1 (trip z'.laid).2.1 (trip z'.laid).2.2 }
        z'.ver := by
  have hlen := chainSteps_length bs ss hss
  have hdl := walk_length ss dsAll a z' hw
  have hC := chained_of_start ha hw hlen
  have hver : (if mid.isSome then ver else none) = ver := by
    cases hv : ver with
    | none => cases mid <;> rfl
    | some s =>
      rw [hvm (by rw [hv]; rfl)]
      rfl
  have h := chain_model (earlier := earlier) (bsAll := bs) x
    (storedShown L.stored (storedAsks F ρ)) R k ch ft (treeAsks F ρ ch)
    (tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb)
    (fun a => (Ls.flatMap fun L => L.row.map (·.2)).any (·.addr.place == a)) φ pb
    (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y))
    (chainKeys bs (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y))) dsAll m₀ Ve L hLc
    hLf (φ.sees m₀.st.input) Z.laid hZ0 bs ss dsAll
    ⟨if ver.isSome then mid.map ({ · with opened := some front }) else none,
      if mid.isSome then ver else none, [], [], []⟩ z'.core Z [] [] [] hss hC
    (Laid.add_nil _ _).symm (hget.trans hver.symm)
    (by cases mid <;> cases ver <;> rfl)
    (by
      intro m hm
      have hm' : ∃ m₁, mid = some m₁ ∧ m = { m₁ with opened := some front } := by
        cases hv : ver with
        | none =>
          rw [hv] at hm
          cases hm
        | some s =>
          rw [hv] at hm
          cases hq : mid with
          | none =>
            rw [hq] at hm
            cases hm
          | some m₁ =>
            rw [hq] at hm
            have hm2 : some ({ m₁ with opened := some front } : Mid W Y) = some m := hm
            exact ⟨m₁, rfl, (Option.some.inj hm2).symm⟩
      obtain ⟨m₁, hm₁, rfl⟩ := hm'
      obtain ⟨e1, e2, e3⟩ := hmid m₁ hm₁
      refine ⟨?_, e3, e1, ?_⟩
      · show φ.sees m₀.st.input = φ.sees m₁.st.input
        rw [e1]
      · show m₁.loc = m₀.loc ++ []
        rw [e2]
        exact (List.append_nil _).symm)
    (by exact htie) rfl rfl rfl (fun q hq => by cases hq) rfl (fun q hq => by cases hq) hbs hsh
    (fun b _ cs => hcuts b.place cs)
    (look_ok R ch φ pb bs Ls _ dsAll m₀ hR hseat hLs hbs)
    (faithAll_of F ρ ch ft L Z.laid trip hZ htr bs dsAll (hdl.trans hlen) hmem)
    (faithOwn_of F ρ ch ft L Z.laid trip hZ htr hsrc bs dsAll (hdl.trans hlen) hmem)
  have h' : Kit.real ((chainActs F Bk ch (treeAsks F ρ ch)
      (tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb)
      (fun a => (Ls.flatMap fun L => L.row.map (·.2)).any (·.addr.place == a)) Ve.J bs 0
      dsAll).map (Act.stage x (storedShown L.stored (storedAsks F ρ)) R)) k Z =
      Ve.set { Z with laid := Z.laid.add ch (pairsBy (treeAsks F ρ ch) z'.laid 0) } z'.ver := h
  rw [h', hZ]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.chainSteps_length
#print axioms ProofFile.Honest.chain_file
