-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/FlArrNames.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
PLAIN ENGINE's STEPS LEAVE THE LEDGER's ARRAYS' NAMES. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/FlLooks.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
ITS FORM, AS ITS SOURCE's: ONE NEW CLASS (`StaysN x`: wherever the function x returns, the ledger
that it leaves has the names of the one that it was handed) · 35 INSTANCES OF THE CLASS `StaysN` (3
of them unnamed) · ONE LOCAL MACRO, "staysN" (the library's "stays" is global; this one is laid anew
in each file that spends it).
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (49): SameLooks → SameArrNames · SameLooks.refl → SameArrNames.refl ·
SameLooks.trans → SameArrNames.trans · sameLooks_frame → sameArrNames_frame · push_looks →
push_arrNames · lin_looks → lin_arrNames · hideRun_looks → hideRun_arrNames · Stays → StaysN ·
Stays.of_same → StaysN.of_same · stays_pure → stays_pureN · Stays.bind → StaysN.bind · stays_bind →
stays_bindN · stays_map → stays_mapN · stays_ite → stays_iteN · stays_none → stays_noneN ·
stays_foldlM → stays_foldlMN · stays_mapM_list → stays_mapM_listN · stays_mapM_array →
stays_mapM_arrayN · stays_must → stays_mustN · stays_need → stays_needN · stays_ask → stays_askN ·
stays_onTape → stays_onTapeN · Stays.change → StaysN.change · stays_takeSlots → stays_takeSlotsN ·
stays_hideRun → stays_hideRunN · stays_lin → stays_linN · stays_read → stays_readN · stays_readSum →
stays_readSumN · stays_answer → stays_answerN · stays_point → stays_pointN · stays_batch →
stays_batchN · stays_empty → stays_emptyN · stays_shown → stays_shownN · stays_publicPart →
stays_publicPartN · stays_claimsIn → stays_claimsInN · stays_pscBeginAt → stays_pscBeginAtN ·
stays_pscBegin → stays_pscBeginN · stays_pscRound → stays_pscRoundN · stays_roundIn → stays_roundInN
· stays_pscEnds → stays_pscEndsN · stays_pscRow → stays_pscRowN · stays_levelRounds →
stays_levelRoundsN · stays_levelIn → stays_levelInN · stays_tscLoop → stays_tscLoopN ·
stays_tscRounds → stays_tscRoundsN · stays_tscIn → stays_tscInN · stays_wsForkRounds →
stays_wsForkRoundsN · stays_wsForkMerge → stays_wsForkMergeN · stays_flatForkEnd →
stays_flatForkEndN.
CALLED WHERE THEY LIE (1): pushEnts_frame.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND, ONE: in `sameArrNames_frame` the two lines behind `congr 1` fall: that tactic closes
the goal by itself here.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.K8.Honest.Names.TreeName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)

variable {α β γ : Type}

/-- G has the names of F. -/
def SameArrNames (F G : Fork) : Prop := G.trees.map treeName = F.trees.map treeName

theorem SameArrNames.refl (F : Fork) : SameArrNames F F := rfl

theorem SameArrNames.trans {F G H : Fork} (a : SameArrNames F G) (b : SameArrNames G H) :
    SameArrNames F H :=
  Eq.trans b a

theorem sameArrNames_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) :
    SameArrNames F G := by
  have e : ∀ tr : Array HTree, tr.map treeName = (treesFrame tr).map ofFrameN := by
    intro tr
    unfold treesFrame
    rw [Array.map_map]
    congr 1
  unfold SameArrNames
  rw [e, e, h]

/-- Adding w times a form to the one equation. -/
theorem push_arrNames {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) :
    SameArrNames F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h1
      exact sameArrNames_frame (pushEnts_frame w _ _ _ h1)
    · simp at h

/-- The adding of a claim. -/
theorem lin_arrNames {F G : Fork} {f : Aff} (h : F.lin f = some G) : SameArrNames F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have htr : F1.trees = F.trees := by rw [hF1]
    have e := push_arrNames h2
    unfold SameArrNames at e ⊢
    rw [e, htr]

/-- A run of hidings. -/
theorem hideRun_arrNames {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameArrNames F G := by
  unfold SameArrNames
  rw [(hideRun_core h).trees]

/-- Wherever x returns, the ledger that it leaves has the names of the one that it was handed. -/
class StaysN (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameArrNames F G

/-- A function that leaves the ledger as it is. -/
theorem StaysN.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    StaysN x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameArrNames.refl F⟩

instance stays_pureN (a : α) : StaysN (pure a : Fl α) :=
  StaysN.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem StaysN.bind {x : Fl α} {f : α → Fl β} (hx : StaysN x) (hf : ∀ a, StaysN (f a)) :
    StaysN (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance stays_bindN (x : Fl α) (f : α → Fl β) [StaysN x] [∀ a, StaysN (f a)] : StaysN (x >>= f) :=
  StaysN.bind inferInstance inferInstance

instance stays_mapN (g : α → β) (x : Fl α) [StaysN x] : StaysN (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance stays_iteN (p : Prop) [Decidable p] (x y : Fl α) [StaysN x] [StaysN y] :
    StaysN (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance stays_noneN : StaysN (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysN" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysN.bind ?_ ?_
    | intro _
    | split)

theorem stays_foldlMN {f : β → γ → Fl β} (hf : ∀ s a, StaysN (f s a)) :
    ∀ (l : List γ) (s : β), StaysN (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact StaysN.bind (hf s a) fun s' => stays_foldlMN hf l s'

theorem stays_mapM_listN {f : α → Fl β} (hf : ∀ a, StaysN (f a)) : ∀ l : List α, StaysN (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysN.bind (hf a) fun _ => StaysN.bind (stays_mapM_listN hf l) fun _ => inferInstance

theorem stays_mapM_arrayN {f : α → Fl β} (hf : ∀ a, StaysN (f a)) (l : Array α) :
    StaysN (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := stays_mapM_listN hf l.toList
  infer_instance

instance stays_mustN (b : Bool) : StaysN (Fl.must b) :=
  StaysN.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance stays_needN (x : Option α) : StaysN (Fl.need x) :=
  StaysN.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance stays_askN (f : Fork → Option α) : StaysN (Fl.ask f) :=
  StaysN.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance stays_onTapeN (g : Tape → Option (α × Tape)) : StaysN (Fl.onTape g) :=
  StaysN.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the names. -/
theorem StaysN.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameArrNames F G) :
    StaysN (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance stays_takeSlotsN (n : Nat) : StaysN (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameArrNames.refl F⟩

instance stays_hideRunN (j : Nat) (v : Array E) (c : E) :
    StaysN (Fl.change fun F => F.hideRun j v c) :=
  StaysN.change fun _ _ h => hideRun_arrNames h

instance stays_linN (a : Aff) : StaysN (Fl.change fun F => F.lin a) :=
  StaysN.change fun _ _ h => lin_arrNames h

instance stays_readN (n : Nat) : StaysN (Fl.read n) := by unfold Fl.read; infer_instance
instance stays_readSumN : StaysN Fl.readSum := by unfold Fl.readSum; infer_instance
instance stays_answerN (r : RoundName) : StaysN (Fl.answer r) := by unfold Fl.answer; infer_instance
instance stays_pointN (r : RoundName) (n : Nat) : StaysN (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance stays_batchN (n : Nat) : StaysN (Fl.batch n) := by unfold Fl.batch; infer_instance
instance stays_emptyN (r : RoundName) : StaysN (Fl.empty r) := by unfold Fl.empty; infer_instance
instance stays_shownN (j : Nat) : StaysN (Fl.shown j) := by unfold Fl.shown; infer_instance
instance stays_publicPartN (a : Aff) : StaysN (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

instance stays_claimsInN (n : Nat) : StaysN (Fl.claimsIn n) := by unfold Fl.claimsIn; staysN
instance stays_pscBeginAtN (x : E) : StaysN (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; staysN
instance stays_pscBeginN (C : Aff) : StaysN (Fl.pscBegin C) := by unfold Fl.pscBegin; staysN

instance stays_pscRoundN (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    StaysN (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; staysN

instance stays_roundInN (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    StaysN (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; staysN

instance stays_pscEndsN (p : Psc) (d n : Nat) : StaysN (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; staysN

instance stays_pscRowN (p : Psc) (S0 : E) (kept : Aff) : StaysN (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; staysN

theorem stays_levelRoundsN (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E)
    (p : Psc),
    StaysN (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine StaysN.bind inferInstance fun _ => ?_
    refine StaysN.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_levelRoundsN mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    StaysN (Fl.levelRounds mu rho order r p) := stays_levelRoundsN mu rho order r p

instance stays_levelInN (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysN (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; staysN

theorem stays_tscLoopN : ∀ (zs : List E) (r : Array E) (p : Psc), StaysN (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine StaysN.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_tscLoopN zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : StaysN (Fl.tscLoop zs r p) := stays_tscLoopN zs r p

instance stays_tscRoundsN (P : Array E) (lt : Nat) : StaysN (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; staysN

instance stays_tscInN (P : Array E) (lt n d : Nat) : StaysN (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; staysN

theorem stays_wsForkRoundsN : ∀ (n : Nat) (rm : Array E) (p : Psc), StaysN (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine StaysN.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact stays_wsForkRoundsN n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : StaysN (Fl.wsForkRounds n rm p) :=
  stays_wsForkRoundsN n rm p

instance stays_wsForkMergeN (lk : Nat) (sv : Array Nat) : StaysN (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; staysN

instance stays_flatForkEndN (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    StaysN (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; staysN

end VerifiableInference.Desc.LinkJoin.FlL

#print axioms VerifiableInference.Desc.LinkJoin.FlL.SameArrNames.refl
#print axioms VerifiableInference.Desc.LinkJoin.FlL.SameArrNames.trans
#print axioms VerifiableInference.Desc.LinkJoin.FlL.sameArrNames_frame
#print axioms VerifiableInference.Desc.LinkJoin.FlL.push_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.FlL.lin_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.FlL.hideRun_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysN.of_same
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysN.bind
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_foldlMN
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_mapM_listN
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_mapM_arrayN
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysN.change
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_levelRoundsN
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_tscLoopN
#print axioms VerifiableInference.Desc.LinkJoin.FlL.stays_wsForkRoundsN
