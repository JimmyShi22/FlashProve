-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FlSizes.lean: K4's HEARING TURNS NO ARRAY's LENGTH: wherever it returns,
the ledger that it leaves has the four sizes (`SameSizes`, SizesBack.lean) of the one that it was
handed. So the ledger's sizes can be pulled back over K4's accept. A class, its instances, and
theorems.
MADE BY PROGRAM out of OnBytes/Desc/First/FlGrows.lean and OnBytes/Desc/First/K4/HearGrows.lean.
There the class `Grows x` says "wherever x returns, its ledger is a later one"; it is closed under
pure, bind, map, if and the folds, and speaks of "later" at six places alone. Here the sister class
`KeepsLen x` has the same instances, text for text, and three other stones at the steps that turn
the ledger: `sizes_next` (slots are taken); `hideRun_sizes` (SizesBack.lean: a run of values is put
under slots); `lin_sizes` (a claim is added: from `lin_slots`, OnBytes/Tie/Pv/Psc/PscLater.lean).
  `hearFl_sizes`: **`hearFl P hp g fo F t = some (o, G, u)` gives `SameSizes F G`: no premise but
    the return.** `k4_sizesS`: **the decision of K4's sub-protocol at the carried state keeps
    `SizesS`** (SizesStretch.lean): `kept_atS` (Johnson/Road/K4/KeptAtS.lean) holds the hearing's
    own equation.
Limits. On the ledger's four sizes alone. Nothing on soundness.

-/
import OnBytes.Desc.First.K4.HearGrows
import Johnson.Road.K4.KeptAtS
import Johnson.Desc.First.Link.Law.SizesStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.GrowLen
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open VerifiableInference.Desc.LinkJoin (SameSizes hideRun_sizes)

variable {α β γ : Type}

/-- Adding a claim keeps the four sizes. -/
theorem lin_sizes {F G : Fork} {f : Aff} (h : F.lin f = some G) : SameSizes F G :=
  have S := OnBytes.PscRun.lin_slots h
  ⟨S.ns, by rw [S.vp], by rw [S.mf], by rw [S.gotF]⟩

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the four sizes of the one that it was
handed. -/
class KeepsLen (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameSizes F G

/-- A function that leaves the ledger as it is. -/
theorem KeepsLen.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    KeepsLen x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameSizes.refl F⟩

instance keepsLen_pure (a : α) : KeepsLen (pure a : Fl α) :=
  KeepsLen.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem KeepsLen.bind {x : Fl α} {f : α → Fl β} (hx : KeepsLen x) (hf : ∀ a, KeepsLen (f a)) :
    KeepsLen (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance keepsLen_bind (x : Fl α) (f : α → Fl β) [KeepsLen x] [∀ a, KeepsLen (f a)] :
    KeepsLen (x >>= f) :=
  KeepsLen.bind inferInstance inferInstance

instance keepsLen_map (g : α → β) (x : Fl α) [KeepsLen x] : KeepsLen (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance keepsLen_ite (p : Prop) [Decidable p] (x y : Fl α) [KeepsLen x] [KeepsLen y] :
    KeepsLen (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance keepsLen_none : KeepsLen (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "keepsLen" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine KeepsLen.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem keepsLen_foldlM {f : β → γ → Fl β} (hf : ∀ s a, KeepsLen (f s a)) :
    ∀ (l : List γ) (s : β), KeepsLen (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact KeepsLen.bind (hf s a) fun s' => keepsLen_foldlM hf l s'

theorem keepsLen_mapM_list {f : α → Fl β} (hf : ∀ a, KeepsLen (f a)) : ∀ l :
    List α, KeepsLen (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact KeepsLen.bind (hf a) fun _ =>
      KeepsLen.bind (keepsLen_mapM_list hf l) fun _ => inferInstance

theorem keepsLen_mapM_array {f : α → Fl β} (hf : ∀ a, KeepsLen (f a)) (l : Array α) :
    KeepsLen (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := keepsLen_mapM_list hf l.toList
  infer_instance

/-! ### The steps -/

instance keepsLen_must (b : Bool) : KeepsLen (Fl.must b) :=
  KeepsLen.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance keepsLen_need (x : Option α) : KeepsLen (Fl.need x) :=
  KeepsLen.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance keepsLen_ask (f : Fork → Option α) : KeepsLen (Fl.ask f) :=
  KeepsLen.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance keepsLen_onTape (g : Tape → Option (α × Tape)) : KeepsLen (Fl.onTape g) :=
  KeepsLen.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that keeps the four sizes. -/
theorem KeepsLen.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameSizes F G) :
    KeepsLen (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

/-- Taking slots keeps the four sizes. -/
theorem sizes_next (F : Fork) (n : Nat) : SameSizes F { F with next := F.next + n } :=
  ⟨rfl, rfl, rfl, rfl⟩

instance keepsLen_takeSlots (n : Nat) : KeepsLen (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact sizes_next F n⟩

instance keepsLen_hideRun (j : Nat) (v : Array E) (c : E) :
    KeepsLen (Fl.change fun F => F.hideRun j v c) :=
  KeepsLen.change fun _ _ h => hideRun_sizes h

instance keepsLen_lin (a : Aff) : KeepsLen (Fl.change fun F => F.lin a) :=
  KeepsLen.change fun _ _ h => lin_sizes h

instance keepsLen_read (n : Nat) : KeepsLen (Fl.read n) := by unfold Fl.read; infer_instance
instance keepsLen_readSum : KeepsLen Fl.readSum := by unfold Fl.readSum; infer_instance
instance keepsLen_answer (r : RoundName) : KeepsLen (Fl.answer r) := by
  unfold Fl.answer; infer_instance
instance keepsLen_point (r : RoundName) (n : Nat) : KeepsLen (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance keepsLen_batch (n : Nat) : KeepsLen (Fl.batch n) := by unfold Fl.batch; infer_instance
instance keepsLen_empty (r : RoundName) : KeepsLen (Fl.empty r) := by
  unfold Fl.empty; infer_instance
instance keepsLen_shown (j : Nat) : KeepsLen (Fl.shown j) := by unfold Fl.shown; infer_instance
instance keepsLen_publicPart (a : Aff) : KeepsLen (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance keepsLen_claimsIn (n : Nat) : KeepsLen (Fl.claimsIn n) := by unfold Fl.claimsIn; keepsLen
instance keepsLen_pscBeginAt (x : E) : KeepsLen (Fl.pscBeginAt x) := by
  unfold Fl.pscBeginAt; keepsLen
instance keepsLen_pscBegin (C : Aff) : KeepsLen (Fl.pscBegin C) := by unfold Fl.pscBegin; keepsLen

instance keepsLen_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    KeepsLen (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; keepsLen

instance keepsLen_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    KeepsLen (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; keepsLen

instance keepsLen_pscEnds (p : Psc) (d n : Nat) : KeepsLen (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; keepsLen

instance keepsLen_pscRow (p : Psc) (S0 : E) (kept : Aff) : KeepsLen (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; keepsLen

theorem keepsLen_levelRounds (mu : Nat) (rho : Array E) :
    ∀ (order : List Nat) (r : Array E) (p : Psc),
    KeepsLen (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine KeepsLen.bind inferInstance fun _ => ?_
    refine KeepsLen.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact keepsLen_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    KeepsLen (Fl.levelRounds mu rho order r p) := keepsLen_levelRounds mu rho order r p

instance keepsLen_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    KeepsLen (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; keepsLen

theorem keepsLen_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), KeepsLen (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine KeepsLen.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact keepsLen_tscLoop zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : KeepsLen (Fl.tscLoop zs r p) :=
  keepsLen_tscLoop zs r p

instance keepsLen_tscRounds (P : Array E) (lt : Nat) : KeepsLen (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; keepsLen

instance keepsLen_tscIn (P : Array E) (lt n d : Nat) : KeepsLen (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; keepsLen

/-! ### The merge of the claims on the weights -/

theorem keepsLen_wsForkRounds :
    ∀ (n : Nat) (rm : Array E) (p : Psc), KeepsLen (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine KeepsLen.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact keepsLen_wsForkRounds n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : KeepsLen (Fl.wsForkRounds n rm p) :=
  keepsLen_wsForkRounds n rm p

instance keepsLen_wsForkMerge (lk : Nat) (sv : Array Nat) : KeepsLen (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; keepsLen

instance keepsLen_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    KeepsLen (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; keepsLen

end OnBytes.Desc.First.GrowLen

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.GrowLen
open VerifiableInference.Desc.LinkJoin (SameSizes)

variable {α : Type}

/-! ### The engine's fields -/

instance (x : Option α) : KeepsLen (engFl.get x) := inferInstanceAs (KeepsLen (Fl.need x))
instance (b : Bool) : KeepsLen (engFl.must b) := inferInstanceAs (KeepsLen (Fl.must b))
instance (n : String) (b : Bool) : KeepsLen (engFl.mustAs n b) :=
  inferInstanceAs (KeepsLen (Fl.must b))
instance (n : String) (b : Bool) : KeepsLen (engFl.check n b) :=
  inferInstanceAs (KeepsLen (Fl.must b))
instance : KeepsLen engFl.fork := inferInstanceAs (KeepsLen (Fl.ask some))
instance (j : Nat) : KeepsLen (engFl.shown j) := inferInstanceAs (KeepsLen (Fl.shown j))
instance (a : Aff) : KeepsLen (engFl.lin a) :=
  inferInstanceAs (KeepsLen (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : KeepsLen (engFl.point r n) :=
  inferInstanceAs (KeepsLen (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : KeepsLen (engFl.claimsIn n) := inferInstanceAs (KeepsLen (Fl.claimsIn n))
instance (n : Nat) : KeepsLen (engFl.batch n) := inferInstanceAs (KeepsLen (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    KeepsLen (engFl.levelIn mu rho C order) :=
      inferInstanceAs (KeepsLen (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : KeepsLen (engFl.tscIn P lt n d) :=
  inferInstanceAs (KeepsLen (Fl.tscIn P lt n d))

instance (C : Aff) : KeepsLen (engFl.pscBegin C) := inferInstanceAs (KeepsLen (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : KeepsLen (engFl.roundIn f p z d) :=
  inferInstanceAs (KeepsLen (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : KeepsLen (engFl.pscEnds p d n) :=
  inferInstanceAs (KeepsLen (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : KeepsLen (engFl.pscRow p s k) :=
  inferInstanceAs (KeepsLen (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    KeepsLen (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (KeepsLen (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : KeepsLen (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : KeepsLen (shownRun engFl first n) := by
  unfold shownRun
  exact keepsLen_mapM_array (fun _ => inferInstance) _

instance (st : Stack) : KeepsLen (plainRounds engFl st) := by
  unfold plainRounds
  refine KeepsLen.bind (keepsLen_foldlM (fun s z => ?_) _ _) fun x => ?_
  · keepsLen
  · keepsLen

instance (g : Forest.Heard) (laid : Array Nat) : KeepsLen (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : KeepsLen (hearNorms engFl P g fo) := by
  unfold hearNorms; keepsLen

instance (P : Pub) (H : Heard) : KeepsLen (hearTerms engFl P H) := by
  unfold hearTerms; keepsLen

instance (v : Env) (H : Heard) (om : Array E) : KeepsLen (joinStart engFl v H om) := by
  unfold joinStart; keepsLen

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    KeepsLen (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; keepsLen

instance (P : Pub) (H : Heard) (K : HeardStack) : KeepsLen (hearGated engFl P H K) := by
  unfold hearGated; keepsLen

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) :
    KeepsLen (hear engFl P hp g fo) := by
  unfold hear; keepsLen

/-- **WHEREVER HEAR RETURNS, ITS LEDGER HAS THE FOUR SIZES OF THE ONE THAT IT WAS HANDED.** -/
theorem hearFl_sizes {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : SameSizes F G := by
  have i : KeepsLen (hear engFl P hp g fo) := inferInstance
  exact i.same h

end OnBytes.Desc.First.K4

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Desc.First.K4 (Par blockAtS hearFl_sizes)
open OnBytes.Road.K4 (kept_atS)

/-- **K4's DECISION KEEPS THE LEDGER's SIZES.** -/
theorem k4_sizesS (p : Par) : Decides SizesS (blockAtS p) := by
  intro s rs gs s' h G' hG'
  obtain ⟨a, fo, o, G, ha, -, hG, -, -, -, -, -, -, -, -, t, u, hh⟩ := kept_atS h
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  exact ⟨a.F, by simp [S.fork?, ha], hearFl_sizes hh⟩

end VerifiableInference.Desc.LinkJoin

#print axioms OnBytes.Desc.First.GrowLen.lin_sizes
#print axioms OnBytes.Desc.First.GrowLen.KeepsLen.of_same
#print axioms OnBytes.Desc.First.GrowLen.KeepsLen.bind
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_foldlM
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_mapM_list
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_mapM_array
#print axioms OnBytes.Desc.First.GrowLen.KeepsLen.change
#print axioms OnBytes.Desc.First.GrowLen.sizes_next
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_levelRounds
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_tscLoop
#print axioms OnBytes.Desc.First.GrowLen.keepsLen_wsForkRounds
#print axioms OnBytes.Desc.First.K4.hearFl_sizes
#print axioms VerifiableInference.Desc.LinkJoin.k4_sizesS
