-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsKinds.lean: the run of the verifier program on an accepted proof file, cut
at every link of the first chain, with the routine that has run there.

Main names:
  accepted_at: accepted ⟹ for the link Y at place j: the record of the whole first chain's run
    (FileRan); the chain over the links before Y, from the file's own start; Y's step; the chain
    over the links behind it, to the file's own end (OnBytes/Tie/Pv/Keeps/KeepsChain.lean).
  OfAPlan X cov m: the routine m is that of the layers' plan of a group g of X, with X.G[g]? = some
    hp; or of an attention plan A of X, with A ∈ X.A; or of the head's plan of X.
  listLinksH_all: listLinksH takes every link's routine from one of the plans that it is given.
  linksOf_kinds, zipped_kinds: every link of the program's own list (Verify.linksOf, and the built
    links with these routines) has such a routine.
  layers_of_link, attention_of_link, head_of_link: what a success of each of the three says:
    Layer.runForkHidG2, Attention.run, Head.runForkHidH2 have succeeded from the same states and
    context and have left the same.
  accepted_own: for the program's own links no hypothesis of the kind "keeps" is left: accepted ⟹ at
    every place j: accepted_at's four, and OfAPlan of the link's routine.

Limits: one direction: from the verdict. Nothing is said on what a routine does. Which place has
which kind of link is not said (the order in which listLinksH lays them).
-/
import OnBytes.Tie.Pv.Keeps.KeepsChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5

open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- Accepted ⟹ the step of the link at place j, in its place in the file's own run. -/
theorem accepted_at (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (j : Nat) (Y : LinkH) (hj : Z.toList[j]? = some Y) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkJ outJ cJ r1 cm chk o C' F' k1 k2,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE (Z.toList.take j) 0 check0 {} ca (checkJ, outJ) cJ ∧
      LinkStep Z c.first wsLay cE j Y checkJ outJ cJ r1 cm chk o C' F' k1 k2 ∧
      LinksChain Z c.first wsLay cE (Z.toList.drop (j + 1)) (j + 1) r1.1 r1.2 cm rN cb := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, R⟩ := accepted_file Z hk h
  obtain ⟨checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1, k2, A1, S, _, _, B⟩ :=
    LinksChain.split R.links j Y hj
  rw [Nat.zero_add] at S B
  exact ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1,
    k2, R, A1, S, B⟩

/-- A success of "f applied to m's value". -/
theorem runs_map {m : Type → Type} [Monad m] [LawfulMonad m] [HasRuns m] {α β : Type} {f : α → β}
    {x : m α} {s : HasRuns.St m} {b : β} {s' : HasRuns.St m} (h : Runs (f <$> x) s b s') :
    ∃ a, Runs x s a s' ∧ b = f a := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure h2
  exact ⟨a, e2 ▸ h1, e1⟩

/-! ## Which routines the links have -/

/-- listLinksH takes every link's routine from one of the plans that it is given: what holds of
all their routines holds of every link's. -/
theorem listLinksH_all (Q : LinkM (Option WsForkOut) → Prop) {NGr : Nat} {p4 : Bool}
    {G A : Array SubPlanH} {H : SubPlanH} {ls : Array LinkH} (hG : ∀ s ∈ G, Q s.run)
    (hA : ∀ a ∈ A, Q a.run) (hH : Q H.run) (h : listLinksH NGr p4 G A H = .ok ls) :
    ∀ l ∈ ls, Q l.run := by
  have push : ∀ {xs : Array LinkH} {y : LinkH}, (∀ l ∈ xs, Q l.run) → Q y.run →
      ∀ l ∈ xs.push y, Q l.run := by
    intro xs y h1 h2 l hl
    rcases Array.mem_push.1 hl with h3 | rfl
    · exact h1 l h3
    · exact h2
  unfold listLinksH at h
  by_cases hc : (G.size != NGr || (p4 && A.size != NGr)) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨r, hr, h⟩ := bind_ok h
    cases h
    refine push ?_ hH
    refine forIn_inv (fun xs : Array LinkH => ∀ l ∈ xs, Q l.run) _ _ _ _
      (fun _ hx => absurd hx (Array.not_mem_empty _)) ?_ hr
    rintro ⟨s0, g⟩ hx b s hb hs
    have hs0 : Q s0.run := hG s0 (Array.mem_toList_iff.1 (mem_zipIdx_fst _ _ _ hx))
    dsimp only at hs
    split at hs
    · split at hs
      · rename_i a ha
        cases hs
        exact push (push hb hs0) (hA a (Array.mem_of_getElem? ha))
      · cases hs
        exact push hb hs0
    · cases hs
      exact push hb hs0

/-- The routine is that of a layers' plan, of an attention plan or of the head's plan of X. -/
def OfAPlan (X : Verify.Public) (cov : Head.Covered) (m : LinkM (Option WsForkOut)) : Prop :=
  (∃ g hp, X.G[g]? = some hp ∧ m = (Verify.layersPlanOf X cov.tokv g hp).run) ∨
  (∃ A, A ∈ X.A ∧ m = (Verify.attentionPlanOf A).run) ∨ m = (Verify.headPlanOf X cov).run

theorem linksOf_kinds {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) : ∀ l ∈ ls, OfAPlan X cov l.run := by
  unfold Verify.linksOf at h
  refine listLinksH_all (OfAPlan X cov) ?_ ?_ (Or.inr (Or.inr rfl)) h
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hs
    rw [Array.getElem_mapIdx]
    rw [Array.size_mapIdx] at hi
    exact Or.inl ⟨i, X.G[i], Array.getElem?_eq_getElem hi, rfl⟩
  · intro a ha
    obtain ⟨A, hA, rfl⟩ := Array.mem_map.1 ha
    exact Or.inr (Or.inl ⟨A, hA, rfl⟩)

theorem zipped_kinds {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (h : Verify.linksOf X cov = .ok ls) (built : Array LinkH) :
    ∀ Z ∈ built.zipWith (fun b l => { b with run := l.run }) ls, OfAPlan X cov Z.run := by
  intro Z hZ
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hZ
  have hi' : i < ls.size := by
    rw [Array.size_zipWith] at hi
    omega
  rw [Array.getElem_zipWith]
  exact linksOf_kinds h (ls[i]'hi') (Array.getElem_mem hi')

/-! ## What a success of each kind of routine says -/

/-- An attention link has run Attention.run. -/
theorem attention_of_link {A : Attention.Plan} {L C' : LinkCtx} {F F' : Fork} {c1 c2 : Ctx}
    {o : Option WsForkOut} (h : (Verify.attentionPlanOf A).run L F c1 = .ok (((o, C'), F'), c2)) :
    Attention.run A L F c1 = .ok ((((), C'), F'), c2) ∧ o = none := by
  have h : Runs (Verify.attentionPlanOf A).run (L, F, c1) o (C', F', c2) := h
  unfold Verify.attentionPlanOf at h
  obtain ⟨u, s1, h1, h2⟩ := HasRuns.runs_bind (m := LinkM) h
  obtain ⟨e0, e⟩ := HasRuns.runs_pure h2
  subst e
  exact ⟨h1, e0⟩

/-- A layers' link has run Layer.runForkHidG2. -/
theorem layers_of_link {X : Verify.Public} {tokv : Array Nat} {g : Nat} {hp : Layer.HPlan2}
    {L C' : LinkCtx} {F F' : Fork} {c1 c2 : Ctx} {o : Option WsForkOut}
    (h : (Verify.layersPlanOf X tokv g hp).run L F c1 = .ok (((o, C'), F'), c2)) :
    ∃ wo, Layer.runForkHidG2 { X.layers with tokv := tokv } hp g L F c1 =
      .ok (((wo, C'), F'), c2) ∧ o = some wo := by
  have h : Runs (Verify.layersPlanOf X tokv g hp).run (L, F, c1) o (C', F', c2) := h
  unfold Verify.layersPlanOf at h
  exact runs_map (m := LinkM) h

/-- The head's link has run Head.runForkHidH2. -/
theorem head_of_link {X : Verify.Public} {cov : Head.Covered} {L C' : LinkCtx} {F F' : Fork}
    {c1 c2 : Ctx} {o : Option WsForkOut}
    (h : (Verify.headPlanOf X cov).run L F c1 = .ok (((o, C'), F'), c2)) :
    ∃ wo, Head.runForkHidH2 X.hS X.HLy (Verify.borderOf X.y) X.H X.owner cov X.layers.wsLay L F
      c1 = .ok (((wo, C'), F'), c2) ∧ o = some wo := by
  have h : Runs (Verify.headPlanOf X cov).run (L, F, c1) o (C', F', c2) := h
  unfold Verify.headPlanOf at h
  exact runs_map (m := LinkM) h

/-! ## The program's own links -/

/-- Accepted, for the program's own links ⟹ at every place: the step in its place, and the kind of
its routine. No hypothesis of the kind "keeps". -/
theorem accepted_own {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (hl : Verify.linksOf X cov = .ok ls) (built : Array LinkH) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply
      (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay) file =
        .accepted)
    (j : Nat) (Y : LinkH)
    (hj : (built.zipWith (fun b l => { b with run := l.run }) ls).toList[j]? = some Y) :
    OfAPlan X cov Y.run ∧
    ∃ r fin cE check0 ca rN cb cc lin cd checkJ outJ cJ r1 cm chk o C' F' k1 k2,
      FileRan (built.zipWith (fun b l => { b with run := l.run }) ls) c table copy request words
        reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay cE
        ((built.zipWith (fun b l => { b with run := l.run }) ls).toList.take j) 0 check0 {} ca
        (checkJ, outJ) cJ ∧
      LinkStep (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay cE j Y checkJ
        outJ cJ r1 cm chk o C' F' k1 k2 ∧
      LinksChain (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay cE
        ((built.zipWith (fun b l => { b with run := l.run }) ls).toList.drop (j + 1)) (j + 1) r1.1
        r1.2 cm rN cb :=
  ⟨zipped_kinds hl built Y (Array.mem_toList_iff.1 (List.mem_of_getElem? hj)),
    accepted_at _ (zipped_keep (linksOf_keep hl) built) h j Y hj⟩

#print axioms accepted_at
#print axioms listLinksH_all
#print axioms linksOf_kinds
#print axioms zipped_kinds
#print axioms attention_of_link
#print axioms layers_of_link
#print axioms head_of_link
#print axioms accepted_own

end OnBytes.L5
