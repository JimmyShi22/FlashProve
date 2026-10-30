-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesSeated.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE TERM OFF THE PLAN (`anOfBuilt`) AND THE MAKERS WHOSE SUB-PROTOCOLS ARE LAID INTO THE LINKS IN
FRONT OF THE BATCHING. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksSeated.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (13): shOfBuilt → anOfBuilt · shOfBuilt_at → anOfBuilt_at · frameAt_letters →
frameAt_lettersN · zeroAt_letters → zeroAt_lettersN · tailHead_keeps → tailHead_keepsN · frames_keep
→ frames_keepN · k4C_steps → k4C_stepsN · k8W_steps → k8W_stepsN · k1Later_steps → k1Later_stepsN ·
readsLay_steps → readsLay_stepsN · readsHead_steps → readsHead_stepsN · readsAtt_steps →
readsAtt_stepsN · quietAt_keeps → quietAt_keepsN.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (3): theOwn_steps · theWhole_steps · theStated_steps.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesFrame
import Johnson.Desc.K8.Honest.Names.ArrNamesK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The term off the plan**: the names of link m's planned arrays. -/
def anOfBuilt (built : Array Stages.LinkH) (m : ℕ) : List String :=
  ((built[m]?).map fun X => X.Fp.trees.toList.map treeName).getD []

theorem anOfBuilt_at {built : Array Stages.LinkH} {m : ℕ} {X : Stages.LinkH}
    (h : built[m]? = some X) : anOfBuilt built m = X.Fp.trees.toList.map treeName := by
  unfold anOfBuilt
  rw [h]
  rfl

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- The letters of link l are made of built[l]. -/
theorem frameAt_lettersN {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ} {x : Par}
    (h : frameAt built W l = some x) :
    match x with
    | .att P _ => P.l = l ∧ anOfBuilt built l = P.X.Fp.trees.toList.map treeName
    | .lay P => P.l = l ∧ anOfBuilt built l = P.X.Fp.trees.toList.map treeName := by
  unfold frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, anOfBuilt_at hX⟩
    · split at h
      · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, anOfBuilt_at hX⟩
      · exact nomatch h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
theorem zeroAt_lettersN {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (h : zeroAt built W = some P) : anOfBuilt built 0 = P.X.Fp.trees.toList.map treeName := by
  unfold zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · exact nomatch h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact anOfBuilt_at hX

/-- The end of the head's link is the frame's one clearing. -/
theorem tailHead_keepsN (shOf : ℕ → List String) {X : Johnson.Desc.First.Walk.LinkPub} {lay : WsLay}
    {lin : Params.LinShape} {s t : S} (h : First.Close.tailHead X lay lin s = .ok t) :
    KeepsArrNames shOf s t :=
  cleared_keepsN shOf (X := X) (counts := First.Close.countsHead) (left := First.Close.leftHead)
    (row := fun masks w claims os => First.Pend.pendingRowO lay masks w claims lin os) h

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **EVERY ROW OF THE FRAME, LINK BY LINK.** -/
theorem frames_keepN {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    (∀ s t, f.lay s = .ok t → KeepsArrNames (anOfBuilt built) s t) ∧
      (∀ s t, f.opened s = .ok t → KeepsArrNames (anOfBuilt built) s t) ∧
      ∀ s t, f.clear s = .ok t → KeepsArrNames (anOfBuilt built) s t := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fun _ _ k => laid_keepsN _ k, fun s t k => by cases k; exact keeps_reflN _ s,
        fun _ _ k => tailHead_keepsN _ k⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        exact ⟨fun _ _ k => laid_keepsN _ k,
          fun _ _ k => openLayZero_makesN _ k (zeroAt_lettersN hP),
          fun _ _ k => cleared_keepsN _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩
    · split at e
      · cases e
      · rename_i P nLin hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_lettersN hP
        exact ⟨fun _ _ k => laid_keepsN _ k, fun _ _ k => openAtt_makesN _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keepsN _ (X := P.X) (counts := countsAtt nLin)
            (left := fun _ => none) (row := rowOf W first) k⟩
      · rename_i P hP
        cases e
        obtain ⟨e1, e2⟩ := frameAt_lettersN hP
        exact ⟨fun _ _ k => laid_keepsN _ k, fun _ _ k => openLay_makesN _ k (by rw [e1]; exact e2),
          fun _ _ k => cleared_keepsN _ (X := P.X) (counts := countsLay P.tl₀.NM) (left := leftLay)
            (row := rowOf W first) k⟩

section
variable (shOf : ℕ → List String)

theorem k4C_stepsN (p : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p).Steps (KeepsArrNames shOf) :=
  fun s rs gs s' h => k4_stepsN shOf p s rs gs s' h

theorem k8W_stepsN (p : First.K8.ParW) : (First.K8.whole p).Steps (KeepsArrNames shOf) :=
  fun s rs gs s' h => k8_stepsN (Cl := Claim) shOf p.toPar s rs gs s' h

theorem k1Later_stepsN {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps (KeepsArrNames shOf) :=
  k1_stepsN shOf _ link moment arrays

theorem readsLay_stepsN (P : K8.ReadsQuiet.PG) :
    (K8.ReadsQuiet.layers P).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact keeps_sameN shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsHead_stepsN (P : K8.ReadsQuiet.PH) :
    (K8.ReadsQuiet.head P).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact keeps_sameN shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsAtt_stepsN {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : b.Steps (KeepsArrNames shOf) := by
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq (A := A) e
  exact keeps_sameN shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])

/-- The steps without a round behind a lookup. -/
theorem quietAt_keepsN {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : KeepsArrNames shOf s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsArrNames shOf s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, hF, k⟩ := K9L.ok_bind k
    obtain ⟨G, hG, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    have hF' := named_some hF
    have hG' := named_some hG
    unfold First.Look.slotsTaken at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      refine keeps_of_casesN shOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF', ?_, rfl, ?_⟩
      · rw [← link_putFork s]
        exact e2
      · rw [fork_putFork s F hF'] at e1
        rw [← Option.some.inj e1]
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsArrNames shOf s t := by
    intro k
    unfold K3.quietHead at k
    split at k
    · rename_i a ha
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain rfl := Except.ok.inj k
      exact keeps_sameN shOf (by simp [S.fork?, ha]) (by simp [S.link?, ha])
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → KeepsArrNames shOf s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact keeps_reflN shOf s
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lk _ h)
    | cases hf

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.anOfBuilt_at
#print axioms VerifiableInference.Desc.LinkJoin.frameAt_lettersN
#print axioms VerifiableInference.Desc.LinkJoin.zeroAt_lettersN
#print axioms VerifiableInference.Desc.LinkJoin.tailHead_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.frames_keepN
#print axioms VerifiableInference.Desc.LinkJoin.k4C_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.k8W_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_keepsN
