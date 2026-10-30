-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ForestMap.lean: the library's checks of openings, carried from one interface to another.

The library's evaluable verifier (Run/ThinDefs.lean) gathers the openings of a chain's own trees
into forests and walks each forest up to its roots. A leaf's input has a body and a salt. The body's
type depends on the interface L. Let φ map bodies of one interface to those of another. Gathering,
flattening and reading off the paths commute with φ; walking does if the oracle functions agree
along φ. The file also splits the walk over two lists of forests.

Main definitions: `mapC`, `mapF`.
Main theorems: `forestsP_map`, `flatP_map`, `readsP_map`, `wellP_map`, `runForestsP_map`,
`runForestsP_append`.
It claims nothing on what a chain proves.
-/
import Run.ThinDefs

namespace OnBytes.Tie

open Iop Rom Compile Compile.Batch Run.Twin Run.Thin

section Map
variable {I X I' X' : Type} {L : BatchProtocol I X} {L' : BatchProtocol I' X'} {lam K : ℕ} (φ : Body L → Body L')

/-- A check with φ applied to the body of its leaf's input. -/
def mapC (c : Check lam L) : Check lam L' :=
  ⟨⟨φ c.inp.body, c.inp.salt⟩, c.j, c.path, c.root, c.depth⟩

/-- A forest with φ applied to every check. -/
def mapF (F : Forest lam L) : Forest lam L' :=
  ⟨F.depth, F.treeRoot, F.cs.map fun e => (e.1, mapC φ e.2)⟩

/-- Making the checks of one component of one round commutes with φ. -/
theorem compP_map (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ∀ js : List ℕ,
    compP (fun _ => L') r posAt depth (fun p a => φ (emb p a)) rt isRead f js =
      (compP (fun _ => L) r posAt depth emb rt isRead f js).map (List.map (mapC φ))
  | [] => rfl
  | j :: js => by
    have ih := compP_map r posAt depth emb rt isRead f js
    rw [compP, compP]
    cases posAt j with
    | none => exact ih
    | some p =>
      dsimp only
      cases isRead p with
      | false => exact ih
      | true =>
        rw [if_pos rfl, if_pos rfl, ih]
        cases f p with
        | none => rfl
        | some op =>
          cases compP (fun _ => L) r posAt depth emb rt isRead f js with
          | none => rfl
          | some cs => rfl

/-- The same where the component may have no root. -/
theorem optP_map (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    optP (fun _ => L') r posAt depth (fun p a => φ (emb p a)) rt isRead f =
      (optP (fun _ => L) r posAt depth emb rt isRead f).map (List.map (mapC φ)) := by
  cases rt with
  | none => rfl
  | some c => exact compP_map φ r posAt depth emb c isRead f _

/-- Cutting a forest into single checks, or not, commutes with φ. -/
theorem splitP_map (pr : Bool) (F : Forest lam L) :
    splitP (fun _ => L') pr (mapF φ F) = (splitP (fun _ => L) pr F).map (mapF φ) := by
  cases pr with
  | true => rfl
  | false =>
    show (F.cs.map fun e => (e.1, mapC φ e.2)).map _ = (F.cs.map _).map (mapF φ)
    rw [List.map_map, List.map_map]
    rfl

/-- Gathering the forests of a chain's own trees commutes with φ. -/
theorem forestsP_map : ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
    (emb : (p : OPos (up S)) → OSym (up S) p → Body L) (rts : RootsOfChain lam (up S))
    (isRead : OPos (up S) → Bool) (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
    forestsP (fun _ => L') S A W (fun p a => φ (emb p a)) rts isRead f =
      (forestsP (fun _ => L) S A W emb rts isRead f).map (List.map (mapF φ))
  | [], _, _, _, _, _, _ => rfl
  | r :: S, (_, A), (w, W), emb, (rt, rts), isRead, f => by
    have ih := forestsP_map S A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p))
      (fun p => f (.inr p))
    have e0 := optP_map (L' := L') φ r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
      (fun p => isRead (.inl p)) (fun p => f (.inl p))
    have eJ := optP_map (L' := L') φ r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
      (fun p => isRead (.inl p)) (fun p => f (.inl p))
    rw [forestsP, forestsP]
    erw [e0, eJ, ih]
    cases optP (fun _ => L) r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
    | none => rfl
    | some a =>
      cases optP (fun _ => L) r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
      | none => rfl
      | some b =>
        cases forestsP (fun _ => L) S A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p))
            (fun p => f (.inr p)) with
        | none => rfl
        | some c =>
          show some _ = some _
          rw [List.map_append, List.map_append, ← splitP_map, ← splitP_map]
          simp only [mapF, List.map_map]
          rfl

/-- Flattening a list of forests into its checks commutes with φ. -/
theorem flatP_map : ∀ Fs : List (Forest lam L),
    flatP (fun _ => L') (Fs.map (mapF φ)) = (flatP (fun _ => L) Fs).map (mapC φ)
  | [] => rfl
  | F :: Fs => by
    have ih := flatP_map Fs
    unfold flatP at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    show (F.cs.map fun e => (e.1, mapC φ e.2)).map Prod.snd = (F.cs.map Prod.snd).map (mapC φ)
    rw [List.map_map, List.map_map]
    rfl

/-- φ does not change the numbers of a forest's opened leaves. -/
theorem idxP_map (F : Forest lam L) : idxP (fun _ => L') (mapF φ F) = idxP (fun _ => L) F := by
  show (F.cs.map fun e => (e.1, mapC φ e.2)).map _ = F.cs.map _
  rw [List.map_map]
  rfl

/-- φ does not change the number of digests that a forest's walk takes. -/
theorem needP_map (F : Forest lam L) : needP (fun _ => L') (mapF φ F) = needP (fun _ => L) F := by
  unfold needP
  rw [idxP_map]
  rfl

/-- φ does not change the digests that a forest's walk takes, read off the checks' paths. -/
theorem readsOneP_map (F : Forest lam L) :
    readsOneP (fun _ => L') (mapF φ F) = readsOneP (fun _ => L) F := by
  show Octopus.reads F.depth ((F.cs.map fun e => (e.1, mapC φ e.2)).map _) = _
  rw [List.map_map]
  rfl

/-- The same for a list of forests. -/
theorem readsP_map : ∀ Fs : List (Forest lam L),
    readsP (fun _ => L') (Fs.map (mapF φ)) = readsP (fun _ => L) Fs
  | [] => rfl
  | F :: Fs => by
    have ih := readsP_map Fs
    unfold readsP at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, readsOneP_map]

/-- φ does not change whether a check has a path of its tree's depth and a leaf's number below
2 ^ depth. -/
theorem wellP_map (c : Check lam L) : wellP (fun _ => L') (mapC φ c) = wellP (fun _ => L) c := rfl

/-- φ does not change the walk of one forest, at oracle functions that agree on its leaves and on
all vertices. -/
theorem runForestP_map (g : Fam (spec lam K L)) (g' : Fam (spec lam K L')) (F : Forest lam L)
    (s : List (Dig lam))
    (hleaf : ∀ e ∈ F.cs, (g' OracleName.leaf (mapC φ e.2).inp : Dig lam) = g OracleName.leaf e.2.inp)
    (hnode : ∀ q : Bits × Bits, (g' OracleName.node q : Dig lam) = g OracleName.node q) :
    runForestP (fun _ => L') g' (mapF φ F) s = runForestP (fun _ => L) g F s := by
  have hn : nodeP (fun _ => L') g' = nodeP (fun _ => L) g := by
    funext a b
    exact hnode _
  have hl : ((mapF φ F).cs.map fun e => (g' OracleName.leaf e.2.inp : Dig lam)) =
      F.cs.map fun e => (g OracleName.leaf e.2.inp : Dig lam) := by
    show (F.cs.map fun e => (e.1, mapC φ e.2)).map _ = _
    rw [List.map_map]
    exact List.map_congr_left hleaf
  unfold runForestP
  rw [idxP_map, hn]
  erw [hl]
  rfl

/-- φ does not change the walks of a list of forests, at oracle functions that agree on their leaves
and on all vertices. -/
theorem runForestsP_map (g : Fam (spec lam K L)) (g' : Fam (spec lam K L'))
    (hnode : ∀ q : Bits × Bits, (g' OracleName.node q : Dig lam) = g OracleName.node q) :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
    (∀ c ∈ flatP (fun _ => L) Fs, (g' OracleName.leaf (mapC φ c).inp : Dig lam) = g OracleName.leaf c.inp) →
    runForestsP (fun _ => L') g' (Fs.map (mapF φ)) s = runForestsP (fun _ => L) g Fs s
  | [], _, _ => rfl
  | F :: Fs, s, h => by
    have h1 : ∀ e ∈ F.cs, (g' OracleName.leaf (mapC φ e.2).inp : Dig lam) = g OracleName.leaf e.2.inp :=
      fun e he => h e.2 (List.mem_flatMap.2 ⟨F, List.mem_cons_self, List.mem_map_of_mem he⟩)
    have h2 : ∀ c ∈ flatP (fun _ => L) Fs,
        (g' OracleName.leaf (mapC φ c).inp : Dig lam) = g OracleName.leaf c.inp := by
      intro c hc
      obtain ⟨F', hF', hc'⟩ := List.mem_flatMap.1 hc
      exact h c (List.mem_flatMap.2 ⟨F', List.mem_cons_of_mem _ hF', hc'⟩)
    rw [List.map_cons, runForestsP, runForestsP, needP_map, runForestP_map φ g g' F _ h1 hnode,
      runForestsP_map g g' hnode Fs _ h2]

end Map

section Append
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ())))

/-- A forest's walk takes as many digests as are read off its checks' paths. -/
theorem length_readsOneP (F : Forest lam (Lf ())) : (readsOneP Lf F).length = needP Lf F := by
  unfold readsOneP needP idxP
  rw [Octopus.length_reads]
  simp only [List.map_map]
  rfl

/-- The walk of a forest and further ones, on the first one's digests and further ones, says yes
exactly if both walks do. -/
theorem runForestsP_cons (F : Forest lam (Lf ())) (Fs : List (Forest lam (Lf ())))
    (s : List (Dig lam)) :
    runForestsP Lf g (F :: Fs) (readsOneP Lf F ++ s) =
      (runForestP Lf g F (readsOneP Lf F) && runForestsP Lf g Fs s) := by
  rw [runForestsP, List.take_left' (length_readsOneP Lf F),
    List.drop_left' (length_readsOneP Lf F)]

/-- The walk of two lists of forests, on the first list's digests and further ones, says yes exactly
if both walks do. -/
theorem runForestsP_append : ∀ (Fs Fs' : List (Forest lam (Lf ()))) (s' : List (Dig lam)),
    runForestsP Lf g (Fs ++ Fs') (readsP Lf Fs ++ s') =
      (runForestsP Lf g Fs (readsP Lf Fs) && runForestsP Lf g Fs' s')
  | [], _, _ => rfl
  | F :: Fs, Fs', s' => by
    have ih := runForestsP_append Fs Fs' s'
    have e : readsP Lf (F :: Fs) = readsOneP Lf F ++ readsP Lf Fs := rfl
    rw [e, List.cons_append, List.append_assoc, runForestsP_cons, ih, runForestsP_cons,
      Bool.and_assoc]

end Append

end OnBytes.Tie

#print axioms OnBytes.Tie.forestsP_map
#print axioms OnBytes.Tie.flatP_map
#print axioms OnBytes.Tie.readsP_map
#print axioms OnBytes.Tie.runForestsP_map
#print axioms OnBytes.Tie.runForestsP_append
