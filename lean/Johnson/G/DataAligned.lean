-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DataAligned.lean: where the made plans fit the format's words, the rounds' data that are
made of the three public files are none at all, or are aligned, round by round, with the rounds of
the planner's own records, the first chain without its last round; and each round's kind is that of
its name.

THE THEOREMS HERE ARE TOOLS: they hold at all public files, and name no description of the protocol
and no value of the release. No line under Owed/ [not in this library] is to be laid on them.

Why. The library's laws on a priced round (`held_round`, OnBytes/Slice/HeldRound.lean; `held_list`,
OnBytes/Flat/HeldAll.lean) speak of a written round and a round of the planner's record that bear
one entry, place by place (`Aligned`). Here that is shown of the data of the key file's and of the
proof file's rounds, from two things: the data bear the entries of the plans from which they are
declared (Johnson/G/DataEntries.lean), and these plans are the plans of the priced records
(`KeyPlansPriced`, `ProofPlansPriced`, Johnson/G/PlansPriced.lean). The laws also read a round's
kind (`Fmt.dsOf e k`), of which the planner's record has nothing: the kind of a round's data is the
kind of the name in its entry.

Definitions, statements and proofs.
  `AlignedCut ds P`: the written rounds' entries are those of the plan's rounds of the chain without
    the last, one by one. (The first chain's last round, in which the chain is sealed, is no round
    of the data's first list.)
  `key_aligned`, `proof_aligned`: if `dataKAt m` (`dataPAt m`) returns D and the three equations
    between plans hold, then D is the data of three empty lists, or
      AlignedCut (D.ds₁.map toRD) P₁, Aligned (D.ds₂.map toRD) P₂, Aligned (D.ds₃.map toRD) P₃.
  `key_aligned_of_fit`, `proof_aligned_of_fit`: the same from: `madeOf` returns m; the planner's
    record has the three plans; the public test `Desc.keyFit` (`Desc.proofFit`) says yes.
  `round_kind`, `writtenOf_kinds`, `of_kinds`, `dataAt_kinds`: on the road from declared rounds to
    the data every round has the kind of its entry's name (`Fmt.kindOf`).
  `dataKAt_kinds`, `dataPAt_kinds`: so has every round of what `dataKAt m`, `dataPAt m` return.

What of OnBytes/Model/ is used. The statements bear `m.p.chains.made`: `m.p` is a
`Model.Verify.Planned` (OnBytes/Model/Verify.lean), `.chains` a `Model.Verify.Chains`
(OnBytes/Model/VerifyChains.lean), and `dataKAt`, `dataPAt`, `madeOf` (Johnson/G/RoundsOfPlan.lean)
are made of them. All of it is a function of the public files alone. No further file under
OnBytes/Model/ is reached than Johnson/G/PlansPriced.lean lists in its head.

Limits. Which of the two cases holds at given public files is not shown. Nothing on a round's items,
trees or openings. Nothing on the entry file. Nothing on any price or count. Nothing on soundness.


-/
import Johnson.G.PlansPriced
import OnBytes.Flat.HeldAll
import OnBytes.Flat.RoundsT
import OnBytes.Maker.ReadData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan
open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Flat.Held VerifiableInference
open OnBytes.Params (Rounds Planned)

/-! ### Aligned, chain by chain -/

/-- The written rounds' entries are those of the plan's rounds of the chain without the last. -/
def AlignedCut (ds : List Run.PQ.RD) (P : Planned) : Prop :=
  ds.map (·.entry) = (chainRounds P).dropLast.map (·.entry)

/-- From the entries of a list of rounds' data. -/
theorem aligned_of_entries {ds : List RDT} {g : Fmt.Plan} {P : Planned}
    (h : ds.map (·.entry) = g.rounds) (hg : g = P.plan) : Aligned (ds.map toRD) P := by
  unfold Aligned
  rw [List.map_map, chainRounds_entries, ← hg]
  exact h

/-- The same without the last round. -/
theorem alignedCut_of_entries {ds : List RDT} {g : Fmt.Plan} {P : Planned}
    (h : ds.map (·.entry) = g.rounds.dropLast) (hg : g = P.plan) :
    AlignedCut (ds.map toRD) P := by
  unfold AlignedCut
  rw [List.map_map, List.map_dropLast, chainRounds_entries, ← hg]
  exact h

/-- **The data of the key file's rounds are aligned with the priced rounds.** -/
theorem key_aligned {m : Made} {D : WholeD} {K₁ K₂ K₃ : Planned} (hD : dataKAt m = .ok D)
    (hp : KeyPlansPriced m K₁ K₂ K₃) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (AlignedCut (D.ds₁.map toRD) K₁ ∧ Aligned (D.ds₂.map toRD) K₂ ∧
        Aligned (D.ds₃.map toRD) K₃) := by
  rcases dataKAt_entries hD with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨alignedCut_of_entries h1 hp.1, aligned_of_entries h2 hp.2.1,
      aligned_of_entries h3 hp.2.2⟩

/-- **The data of the proof file's rounds are aligned with the priced rounds.** -/
theorem proof_aligned {m : Made} {D : WholeD} {F₁ F₂ F₃ : Planned} (hD : dataPAt m = .ok D)
    (hp : ProofPlansPriced m F₁ F₂ F₃) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (AlignedCut (D.ds₁.map toRD) F₁ ∧ Aligned (D.ds₂.map toRD) F₂ ∧
        Aligned (D.ds₃.map toRD) F₃) := by
  rcases dataPAt_entries hD with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨alignedCut_of_entries h1 hp.1, aligned_of_entries h2 hp.2.1,
      aligned_of_entries h3 hp.2.2⟩

/-- The key file's, from the public test on the made plans. -/
theorem key_aligned_of_fit {pol lay KL : ByteArray} {m : Made} {D : WholeD} {K₁ K₂ K₃ : Planned}
    (h : madeOf pol lay KL = .ok m) (hm : m.p.chains.made.key = [K₁, K₂, K₃])
    (hf : Desc.keyFit m.p.chains.made = true) (hD : dataKAt m = .ok D) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (AlignedCut (D.ds₁.map toRD) K₁ ∧ Aligned (D.ds₂.map toRD) K₂ ∧
        Aligned (D.ds₃.map toRD) K₃) :=
  key_aligned hD (keyPlansPriced_of_fit h hm hf)

/-- The proof file's, from the public test on the made plans. -/
theorem proof_aligned_of_fit {pol lay KL : ByteArray} {m : Made} {D : WholeD}
    {F₁ F₂ F₃ : Planned} (h : madeOf pol lay KL = .ok m)
    (hm : m.p.chains.made.proof = [F₁, F₂, F₃]) (hf : Desc.proofFit m.p.chains.made = true)
    (hD : dataPAt m = .ok D) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (AlignedCut (D.ds₁.map toRD) F₁ ∧ Aligned (D.ds₂.map toRD) F₂ ∧
        Aligned (D.ds₃.map toRD) F₃) :=
  proof_aligned hD (proofPlansPriced_of_fit h hm hf)

/-! ### The kinds -/

/-- A declared round as the readers take it has the kind of its entry's name. -/
theorem round_kind {earlier : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound}
    {x : Fmt.Round} (h : r.round earlier = some x) : Fmt.kindOf x.entry.name = some x.kind := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hk

/-- What holds of each value of a function that may refuse holds of all that `mapM` returns. -/
theorem mapM_all {ε α β : Type} (f : α → Except ε β) (p : β → Prop)
    (hf : ∀ a b, f a = .ok b → p b) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → ∀ b ∈ r, p b
  | [], r, h, b, hb => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    cases hb
  | x :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hf x _ h1
    · exact mapM_all f p hf l r' h2 b hb

/-- Every written round that `writtenOf` returns has the kind of its entry's name. -/
theorem writtenOf_kinds {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) :
    ∀ x ∈ R.1 ++ (R.2.1 ++ R.2.2), Fmt.kindOf x.1.entry.name = some x.1.kind := by
  unfold writtenOf at h
  dsimp only at h
  obtain ⟨r1, h1, h⟩ := bind_ok h
  obtain ⟨r2, h2, h⟩ := bind_ok h
  obtain ⟨r3, h3, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  have key : ∀ (chain : String) (e : List (List ByteArray × ByteArray)) (a : Fmt.DeclaredRound)
      (b : Fmt.Round × List Fmt.Stored),
      (match a.round e with
        | some x => (pure (x, a.stored) : Except String (Fmt.Round × List Fmt.Stored))
        | none => throw <| refusal s!"{file}, {chain} chain" <| s!"the round \"{a.entry.name}\" " ++
            (if (Fmt.kindOf a.entry.name).isNone then "has a name that the format does not know"
             else "takes over a tree that the earlier chain does not send")) = .ok b →
        Fmt.kindOf b.1.entry.name = some b.1.kind := by
    intro chain e a b hab
    split at hab
    · rename_i x hx
      obtain rfl := Except.ok.inj hab
      exact round_kind hx
    · exact absurd hab (throw_ne _ _)
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact mapM_all _ _ (key "first" []) _ _ h1 x hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact mapM_all _ _ (key "shared" []) _ _ h2 x hx
    · exact mapM_all _ _ (key "second" _) _ _ h3 x hx

/-- One chain's data keep entry and kind together. -/
theorem rdsFromL_kinds (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (R : Rounds) (h : ∀ x ∈ R, Fmt.kindOf x.1.entry.name = some x.1.kind) :
    ∀ d ∈ Three.rdsFromL all t₁ t₂ here base first R, Fmt.kindOf d.entry.name = some d.kind :=
  all_of_map (fun d : Three.RDL => (d.entry, d.kind))
    (fun r : Fmt.Round × List Fmt.Stored => (r.1.entry, r.1.kind))
    (fun y => Fmt.kindOf y.1.name = some y.2)
    (rdsFromL_map all t₁ t₂ here base first _ _ (fun _ _ => rfl) R) h

/-- The data of a whole file, from three lists of rounds. -/
theorem of_kinds (a : ℕ) (R₁ R₂ R₃ : Rounds)
    (h : ∀ x ∈ R₁ ++ (R₂ ++ R₃), Fmt.kindOf x.1.entry.name = some x.1.kind) :
    ∀ d ∈ (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁ ++
      ((WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂ ++ (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃),
      Fmt.kindOf d.entry.name = some d.kind := by
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact rdsFromL_kinds _ _ _ _ _ _ R₁ (fun x hx => h x (List.mem_append_left _ hx)) d'
      (List.mem_of_mem_dropLast hd')
  · rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact rdsFromL_kinds _ _ _ _ _ _ R₂
        (fun x hx => h x (List.mem_append_right _ (List.mem_append_left _ hx))) d' hd'
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact rdsFromL_kinds _ _ _ _ _ _ R₃
        (fun x hx => h x (List.mem_append_right _ (List.mem_append_right _ hx))) d' hd'

/-- The data at three lists of written rounds, whichever way the makers' tests say. -/
theorem dataAt_kinds (a : ℕ) (R : Rounds × Rounds × Rounds)
    (h : ∀ x ∈ R.1 ++ (R.2.1 ++ R.2.2), Fmt.kindOf x.1.entry.name = some x.1.kind) :
    ∀ d ∈ (WholeD.of a (dataAt a (some R))).ds₁ ++
      ((WholeD.of a (dataAt a (some R))).ds₂ ++ (WholeD.of a (dataAt a (some R))).ds₃),
      Fmt.kindOf d.entry.name = some d.kind := by
  unfold dataAt
  split
  · exact of_kinds a R.1 R.2.1 R.2.2 h
  · exact of_kinds a [] [] [] (fun x hx => by cases hx)

/-- **Every round of the key file's data has the kind of its entry's name.** -/
theorem dataKAt_kinds {m : Made} {D : WholeD} (h : dataKAt m = .ok D) :
    ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), Fmt.kindOf d.entry.name = some d.kind := by
  unfold dataKAt at h
  obtain ⟨a, _, h⟩ := bind_ok h
  obtain ⟨Dc, _, h⟩ := bind_ok h
  obtain ⟨R, hR, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  exact dataAt_kinds a R (writtenOf_kinds hR)

/-- **Every round of the proof file's data has the kind of its entry's name.** -/
theorem dataPAt_kinds {m : Made} {D : WholeD} (h : dataPAt m = .ok D) :
    ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), Fmt.kindOf d.entry.name = some d.kind := by
  unfold dataPAt at h
  obtain ⟨a, _, h⟩ := bind_ok h
  obtain ⟨Dc, _, h⟩ := bind_ok h
  obtain ⟨R, hR, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  exact dataAt_kinds a R (writtenOf_kinds hR)

end Johnson.G.OfPlan

#print axioms Johnson.G.OfPlan.aligned_of_entries
#print axioms Johnson.G.OfPlan.alignedCut_of_entries
#print axioms Johnson.G.OfPlan.key_aligned
#print axioms Johnson.G.OfPlan.proof_aligned
#print axioms Johnson.G.OfPlan.key_aligned_of_fit
#print axioms Johnson.G.OfPlan.proof_aligned_of_fit
#print axioms Johnson.G.OfPlan.round_kind
#print axioms Johnson.G.OfPlan.mapM_all
#print axioms Johnson.G.OfPlan.writtenOf_kinds
#print axioms Johnson.G.OfPlan.rdsFromL_kinds
#print axioms Johnson.G.OfPlan.of_kinds
#print axioms Johnson.G.OfPlan.dataAt_kinds
#print axioms Johnson.G.OfPlan.dataKAt_kinds
#print axioms Johnson.G.OfPlan.dataPAt_kinds
