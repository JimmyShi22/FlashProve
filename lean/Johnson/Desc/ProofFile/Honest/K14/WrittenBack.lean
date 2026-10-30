-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/WrittenBack.lean: WHERE THE LIBRARY's writtenOf
(Johnson/G/RoundsOfPlan.lean) LAYS A FILE's THREE LISTS OF DECLARED ROUNDS AS WRITTEN ROUNDS, THE
DECLARED ROUNDS COME BACK FROM THE WRITTEN ONES BY THE LIBRARY's backR
(Johnson/HB/LLHARD/KB8/Written.lean): SO writtenOf IS INJECTIVE WHERE IT RETURNS. General in the
file's name and in the lists. Statements, each with its proof; no definition.

  src_back_nil, src_back_two   a tree's source, laid and turned back, is the source: at no earlier
                  chain (a tree that is taken over refuses there); at two earlier chains whose
                  roots and runs are the library's stand-ins
  opens_back, declared_round_back   the like of a round's list of opened trees, and of a round
  writtenOf_back  **MAIN**: writtenOf file D = .ok R gives D = R's three lists under backR
  writtenOf_inj   **so two files' declared rounds that are laid as the same written rounds are
                  one**
  declared_back   at the library's written values: declProofFull is dryProofFull under backR: from
                  the library's written_proof. (The two written values are laid along one and the
                  same three lists of runs, and their distinct rounds are tied by the library's
                  recs_back, Johnson/AtFull/ProofPlan/WPFacts.lean: so it holds little as a check of
                  one against the other.)

Limits. Bookkeeping on lists: nothing on what a round decides. Nothing is evaluated in this file;
beneath declared_back stand written_proof's own evaluations by Lean's kernel. backSrc is right for
the stand-ins alone (tagRoot n has n + 1 bytes; tagRun c is the one byte c): at other roots and runs
nothing is said. Nothing on what is or is not hidden; no property.
-/
import Johnson.AtFull.ProofRows.WrittenProof
import Johnson.G.DataEntries
import Johnson.Desc.First.Driver.PlacesLaw
import OnBytes.Maker.SrcFitsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open Johnson.G.OfPlan (Decl3 writtenOf bind_ok throw_ne mapM_map refusal rootsOf)
open Johnson.KB8 (backR backSrc)
open OnBytes.Params (Rounds)
open OnBytes.Three (tagRoot tagRun)
open OnBytes.Maker (tagRoot_size)

/-- At no earlier chain a source that can be laid is an own tree's, and comes back. -/
theorem src_back_nil {o : Fmt.TreeSource} {s : Fmt.Src} (h : o.src [] = some s) : backSrc s = o := by
  cases o with
  | own n =>
    obtain rfl : Fmt.Src.own n = s := Option.some.inj h
    rfl
  | taken c p => simp [Fmt.TreeSource.src] at h

/-- At two earlier chains with the stand-ins for roots and runs a source that can be laid comes
back. -/
theorem src_back_two (a b : Nat) {o : Fmt.TreeSource} {s : Fmt.Src}
    (h : o.src [((List.range a).map tagRoot, tagRun 1), ((List.range b).map tagRoot, tagRun 2)] =
      some s) : backSrc s = o := by
  cases o with
  | own n =>
    obtain rfl : Fmt.Src.own n = s := Option.some.inj h
    rfl
  | taken c p =>
    unfold Fmt.TreeSource.src at h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    match c, he with
    | 0, he =>
      obtain rfl := Option.some.inj he
      rw [List.getElem?_map] at hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain rfl : p = q := by
        have := List.getElem?_eq_some_iff.1 hq
        obtain ⟨hlt, e⟩ := this
        simpa using e
      show Fmt.TreeSource.taken _ ((tagRoot p).size - 1) = _
      rw [tagRoot_size]
      rfl
    | 1, he =>
      obtain rfl := Option.some.inj he
      rw [List.getElem?_map] at hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain rfl : p = q := by
        have := List.getElem?_eq_some_iff.1 hq
        obtain ⟨hlt, e⟩ := this
        simpa using e
      show Fmt.TreeSource.taken _ ((tagRoot p).size - 1) = _
      rw [tagRoot_size]
      rfl

/-- A round's list of opened trees, laid and turned back. -/
theorem opens_back (e : List (List ByteArray × ByteArray))
    (hs : ∀ (o : Fmt.TreeSource) (s : Fmt.Src), o.src e = some s → backSrc s = o) :
    ∀ (l : List (Fmt.Shape × Fmt.TreeSource)) (os : List (Fmt.Shape × Fmt.Src)),
      (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) = some os →
      (os.map fun o => (o.1, backSrc o.2)) = l
  | [], os, h => by
    obtain rfl : [] = os := Option.some.inj h
    rfl
  | o :: l, os, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := VerifiableInference.Desc.First.mapM_cons_some _ o l os h
    obtain ⟨s, hsrc, rfl⟩ := Option.map_eq_some_iff.1 hb
    rw [List.map_cons, opens_back e hs l bs hbs]
    show (o.1, backSrc s) :: l = o :: l
    rw [hs o.2 s hsrc]

/-- A declared round, laid and turned back. -/
theorem declared_round_back (e : List (List ByteArray × ByteArray))
    (hs : ∀ (o : Fmt.TreeSource) (s : Fmt.Src), o.src e = some s → backSrc s = o)
    {r : Fmt.DeclaredRound} {x : Fmt.Round} (h : r.round e = some x) : backR (x, r.stored) = r := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, hos, rfl⟩ := Option.map_eq_some_iff.1 h
  show (⟨r.entry, r.stored, os.map fun o => (o.1, backSrc o.2)⟩ : Fmt.DeclaredRound) = r
  rw [opens_back e hs r.opens os hos]

/-- **MAIN: THE DECLARED ROUNDS COME BACK FROM THE WRITTEN ONES.** -/
theorem writtenOf_back {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) :
    D = (R.1.map backR, R.2.1.map backR, R.2.2.map backR) := by
  unfold writtenOf at h
  dsimp only at h
  obtain ⟨r1, h1, h⟩ := bind_ok h
  obtain ⟨r2, h2, h⟩ := bind_ok h
  obtain ⟨r3, h3, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  have key : ∀ (chain : String) (e : List (List ByteArray × ByteArray)),
      (∀ (o : Fmt.TreeSource) (s : Fmt.Src), o.src e = some s → backSrc s = o) →
      ∀ (a : Fmt.DeclaredRound) (b : Fmt.Round × List Fmt.Stored),
      (match a.round e with
        | some x => (pure (x, a.stored) : Except String (Fmt.Round × List Fmt.Stored))
        | none => throw <| refusal s!"{file}, {chain} chain" <| s!"the round \"{a.entry.name}\" " ++
            (if (Fmt.kindOf a.entry.name).isNone then "has a name that the format does not know"
             else "takes over a tree that the earlier chain does not send")) = .ok b →
        backR b = id a := by
    intro chain e hs a b hab
    split at hab
    · rename_i x hx
      obtain rfl := Except.ok.inj hab
      exact declared_round_back e hs hx
    · exact absurd hab (throw_ne _ _)
  have e1 := mapM_map _ backR id (key "first" [] fun _ _ => src_back_nil) _ _ h1
  have e2 := mapM_map _ backR id (key "shared" [] fun _ _ => src_back_nil) _ _ h2
  have e3 := mapM_map _ backR id (key "second" _ fun _ _ => src_back_two _ _) _ _ h3
  rw [List.map_id] at e1 e2 e3
  exact Prod.ext e1.symm (Prod.ext e2.symm e3.symm)

/-- **So two files' declared rounds that are laid as the same written rounds are one.** -/
theorem writtenOf_inj {file file' : String} {D D' : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) (h' : writtenOf file' D' = .ok R) : D = D' :=
  (writtenOf_back h).trans (writtenOf_back h').symm

/-- At the library's written values: from written_proof. -/
theorem declared_back : Johnson.AtFull.ProofRows.declProofFull =
    (Johnson.G.dryProofFull.1.map backR, Johnson.G.dryProofFull.2.1.map backR,
      Johnson.G.dryProofFull.2.2.map backR) :=
  writtenOf_back Johnson.AtFull.ProofRows.written_proof

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.src_back_nil
#print axioms ProofFile.Honest.K14.src_back_two
#print axioms ProofFile.Honest.K14.opens_back
#print axioms ProofFile.Honest.K14.declared_round_back
#print axioms ProofFile.Honest.K14.writtenOf_back
#print axioms ProofFile.Honest.K14.writtenOf_inj
#print axioms ProofFile.Honest.K14.declared_back
