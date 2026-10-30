-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Ledger.lean: THE LAYERS' OWN ROUNDS (K4): WHAT THE HEARING DOES TO THE
LEDGER's SHAPE (Johnson/Desc/First/Shape/Parts.lean): ONE UPDATE, EXACT. General laws: nothing is
evaluated.

  Side F G        G is F but for the next slot and the three arrays on the slots.
  Sides x         wherever the flat function x returns, the ledger behind is so. An instance for
                  each step of OnBytes/K/Kc/Flat.lean that the hearing calls, for each field of the
                  plain engine, and for each part of the hearing, walked by the tactic "sides" (the
                  pattern of OnBytes/Desc/First/FlGrows.lean).
  hearFl_side     FROM A RETURN ALONE: the hearing turns nothing else of the ledger.
  marksU, tvFirstOf, hearLedU   THE UPDATE on the ledger's shape: the next slot k4Takes further;
                  every slot between filled, but for the two sumchecks that are left open.
  **hear_ledSh**   a return of the hearing with room in front and behind, "nothing below has turned"
                  and HearLeft (Johnson/Desc/First/K4/Returns/Whole.lean: all of it is what
                  hear_returns says of its return): the ledger's shape behind is the update of the
                  shape in front.

Limits. From a return and what hear_returns says of it. The tactic "sides" is a macro of this file,
not a local one, and the instances of Sides are global: every importer inherits both. Sides is a
class of propositions: no term's value hangs on which instance is found. Nothing on values. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.P1 (bind_some some_triple)

variable {α β γ : Type}

/-- G is F but for the next slot and the three arrays on the slots. -/
def Side (F G : Fork) : Prop :=
  G = { F with next := G.next, vp := G.vp, mf := G.mf, gotF := G.gotF }

theorem Side.refl (F : Fork) : Side F F := rfl

theorem Side.trans {F G H : Fork} (a : Side F G) (b : Side G H) : Side F H := by
  unfold Side at a b ⊢
  rw [b, a]

/-- Wherever x returns, the ledger behind is the one in front but for these four fields. -/
class Sides (x : Fl α) : Prop where
  side : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) → Side F G

theorem Sides.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    Sides x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact Side.refl F⟩

instance sides_pure (a : α) : Sides (pure a : Fl α) :=
  Sides.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

theorem Sides.bind {x : Fl α} {f : α → Fl β} (hx : Sides x) (hf : ∀ a, Sides (f a)) :
    Sides (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.side h1).trans ((hf a).side h2)⟩

instance sides_bind (x : Fl α) (f : α → Fl β) [Sides x] [∀ a, Sides (f a)] : Sides (x >>= f) :=
  Sides.bind inferInstance inferInstance

instance sides_map (g : α → β) (x : Fl α) [Sides x] : Sides (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance sides_ite (p : Prop) [Decidable p] (x y : Fl α) [Sides x] [Sides y] :
    Sides (if p then x else y) := by
  split <;> infer_instance

instance sides_none : Sides (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each "if" and each pattern. -/
macro "sides" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Sides.bind ?_ ?_
    | intro _
    | split)

theorem sides_foldlM {f : β → γ → Fl β} (hf : ∀ s a, Sides (f s a)) :
    ∀ (l : List γ) (s : β), Sides (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact Sides.bind (hf s a) fun s' => sides_foldlM hf l s'

theorem sides_mapM_list {f : α → Fl β} (hf : ∀ a, Sides (f a)) : ∀ l : List α, Sides (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact Sides.bind (hf a) fun _ => Sides.bind (sides_mapM_list hf l) fun _ => inferInstance

theorem sides_mapM_array {f : α → Fl β} (hf : ∀ a, Sides (f a)) (l : Array α) :
    Sides (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := sides_mapM_list hf l.toList
  infer_instance

instance sides_must (b : Bool) : Sides (Fl.must b) :=
  Sides.of_same fun _ _ _ _ _ e => (OnBytes.Desc.First.P1.must_some.mp e).2.1

instance sides_need (x : Option α) : Sides (Fl.need x) :=
  Sides.of_same fun _ _ _ _ _ e => (OnBytes.Desc.First.P1.need_some.mp e).2.1

instance sides_ask (f : Fork → Option α) : Sides (Fl.ask f) :=
  Sides.of_same fun _ _ _ _ _ e => (OnBytes.Desc.First.P1.ask_some.mp e).2.1

instance sides_onTape (g : Tape → Option (α × Tape)) : Sides (Fl.onTape g) :=
  Sides.of_same fun _ _ _ _ _ e => (OnBytes.Desc.First.P1.onTape_some.mp e).2

instance sides_takeSlots (n : Nat) : Sides (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (OnBytes.Desc.First.P1.takeSlots_some.mp e).2.1
    rfl⟩

theorem hide_side {F G : Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) : Side F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

theorem hideSteps_side (f : E) : ∀ (l : List E) (x y : Nat × Fork),
    l.foldlM (Fork.hideStep f) x = some y → Side x.2 y.2
  | [], x, y, h => by
    obtain rfl : x = y := by simpa using h
    exact Side.refl _
  | e :: l, (j, G), y, h => by
    rw [List.foldlM_cons] at h
    cases hs : Fork.hideStep f (j, G) e with
    | none =>
      rw [hs] at h
      cases h
    | some z =>
      rw [hs] at h
      have h1 : (G.hide j e f).map (fun H => (j + 1, H)) = some z := hs
      cases hh : G.hide j e f with
      | none =>
        rw [hh] at h1
        cases h1
      | some H =>
        rw [hh] at h1
        obtain rfl := Option.some.inj h1
        exact (hide_side hh).trans (hideSteps_side f l _ y h)

theorem hideRun_side {F G : Fork} {j : Nat} {v : Array E} {f : E}
    (h : F.hideRun j v f = some G) : Side F G := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hs : v.toList.foldlM (Fork.hideStep f) (j, F) with
  | none =>
    rw [hs] at h
    cases h
  | some x =>
    rw [hs] at h
    obtain rfl := Option.some.inj h
    exact hideSteps_side f _ _ _ hs

instance sides_hideRun (j : Nat) (v : Array E) (c : E) :
    Sides (Fl.change fun F => F.hideRun j v c) :=
  ⟨fun e => hideRun_side (OnBytes.Desc.First.P1.change_some.mp e).1⟩

instance sides_read (n : Nat) : Sides (Fl.read n) := by unfold Fl.read; infer_instance
instance sides_readSum : Sides Fl.readSum := by unfold Fl.readSum; infer_instance
instance sides_answer (r : RoundName) : Sides (Fl.answer r) := by unfold Fl.answer; infer_instance
instance sides_point (r : RoundName) (n : Nat) : Sides (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance sides_batch (n : Nat) : Sides (Fl.batch n) := by unfold Fl.batch; infer_instance
instance sides_empty (r : RoundName) : Sides (Fl.empty r) := by unfold Fl.empty; infer_instance
instance sides_shown (j : Nat) : Sides (Fl.shown j) := by unfold Fl.shown; infer_instance
instance sides_publicPart (a : Aff) : Sides (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance
instance sides_claimsIn (n : Nat) : Sides (Fl.claimsIn n) := by unfold Fl.claimsIn; sides
instance sides_pscBeginAt (x : E) : Sides (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; sides
instance sides_pscBegin (C : Aff) : Sides (Fl.pscBegin C) := by unfold Fl.pscBegin; sides
instance sides_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    Sides (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; sides
instance sides_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    Sides (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; sides
instance sides_pscEnds (p : Psc) (d n : Nat) : Sides (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; sides
instance sides_pscRow (p : Psc) (S0 : E) (kept : Aff) : Sides (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; sides

theorem sides_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E)
    (p : Psc), Sides (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine Sides.bind inferInstance fun _ => ?_
    refine Sides.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact sides_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    Sides (Fl.levelRounds mu rho order r p) := sides_levelRounds mu rho order r p

instance sides_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Sides (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; sides

theorem sides_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), Sides (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine Sides.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact sides_tscLoop zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : Sides (Fl.tscLoop zs r p) := sides_tscLoop zs r p

instance sides_tscRounds (P : Array E) (lt : Nat) : Sides (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; sides
instance sides_tscIn (P : Array E) (lt n d : Nat) : Sides (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; sides

theorem sides_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc), Sides (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Sides.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact sides_wsForkRounds n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : Sides (Fl.wsForkRounds n rm p) :=
  sides_wsForkRounds n rm p

instance sides_wsForkMerge (lk : Nat) (sv : Array Nat) : Sides (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; sides
instance sides_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Sides (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; sides

/-! ### The engine's fields, and the parts of the hearing -/

instance (x : Option α) : Sides (engFl.get x) := inferInstanceAs (Sides (Fl.need x))
instance (b : Bool) : Sides (engFl.must b) := inferInstanceAs (Sides (Fl.must b))
instance (n : String) (b : Bool) : Sides (engFl.mustAs n b) := inferInstanceAs (Sides (Fl.must b))
instance (n : String) (b : Bool) : Sides (engFl.check n b) := inferInstanceAs (Sides (Fl.must b))
instance (j : Nat) : Sides (engFl.shown j) := inferInstanceAs (Sides (Fl.shown j))
instance (r : RoundName) (n : Nat) : Sides (engFl.point r n) :=
  inferInstanceAs (Sides (if r == .batSigma then (fun _ _ => none) else Fl.point r n))
instance (n : Nat) : Sides (engFl.claimsIn n) := inferInstanceAs (Sides (Fl.claimsIn n))
instance (n : Nat) : Sides (engFl.batch n) := inferInstanceAs (Sides (Fl.batch n))
instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Sides (engFl.levelIn mu rho C order) := inferInstanceAs (Sides (Fl.levelIn mu rho C order))
instance (P : Array E) (lt n d : Nat) : Sides (engFl.tscIn P lt n d) :=
  inferInstanceAs (Sides (Fl.tscIn P lt n d))
instance (C : Aff) : Sides (engFl.pscBegin C) := inferInstanceAs (Sides (Fl.pscBegin C))
instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : Sides (engFl.roundIn f p z d) :=
  inferInstanceAs (Sides (Fl.roundIn f p z d))
instance (p : Psc) (d n : Nat) : Sides (engFl.pscEnds p d n) :=
  inferInstanceAs (Sides (Fl.pscEnds p d n))
instance (p : Psc) (s : E) (k : Aff) : Sides (engFl.pscRow p s k) :=
  inferInstanceAs (Sides (Fl.pscRow p s k))
instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : Sides (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (Sides (flatForkEnd lay cl sv))

instance (p : Psc) (S0 : E) : Sides (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance
instance (first n : Nat) : Sides (shownRun engFl first n) := by
  unfold shownRun
  exact sides_mapM_array (fun _ => inferInstance) _
instance (st : Stack) : Sides (plainRounds engFl st) := by
  unfold plainRounds
  refine Sides.bind (sides_foldlM (fun s z => ?_) _ _) fun x => ?_
  · sides
  · sides
instance (g : Forest.Heard) (laid : Array Nat) : Sides (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance
instance (P : Pub) (g : Nat) (fo : Forest.Heard) : Sides (hearNorms engFl P g fo) := by
  unfold hearNorms; sides
instance (P : Pub) (H : Heard) : Sides (hearTerms engFl P H) := by
  unfold hearTerms; sides
instance (v : Env) (H : Heard) (om : Array E) : Sides (joinStart engFl v H om) := by
  unfold joinStart; sides
instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    Sides (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; sides
instance (P : Pub) (H : Heard) (K : HeardStack) : Sides (hearGated engFl P H K) := by
  unfold hearGated; sides
instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : Sides (hear engFl P hp g fo) := by
  unfold hear; sides

/-- **Wherever the hearing returns, it has turned nothing of the ledger but the next slot and the
three arrays on the slots.** -/
theorem hearFl_side {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : Side F G := by
  have i : Sides (hear engFl P hp g fo) := inferInstance
  exact i.side h

/-! ## The update on the ledger's shape -/

open VerifiableInference.Desc.First.Shape (LedSh ledSh)

/-- The marks behind: those in front, with the slots from first up to last filled, but for the
windows from a1 up to a2 and from b1 up to b2. -/
def marksU (got : List Bool) (first last a1 a2 b1 b2 : Nat) : List Bool :=
  got.zipIdx.map fun x =>
    x.1 || (decide (first ≤ x.2) && decide (x.2 < last) &&
      !(decide (a1 ≤ x.2) && decide (x.2 < a2)) && !(decide (b1 ≤ x.2) && decide (x.2 < b2)))

/-- The first slot of the row products' token sumcheck, from the hearing's first slot. -/
def tvFirstOf (P : Pub) (first : Nat) : Nat :=
  first + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) + ledNP P.y.h.xl * P.y.NI + 1

/-- **THE UPDATE on the ledger's shape**: the next slot k4Takes further; every slot between filled,
but for the two sumchecks that are left open. -/
def hearLedU (P : Pub) (hp : HPlan2) (g : Nat) (L : LedSh) : LedSh :=
  LedSh.mk L.ns L.shown L.factors
    (marksU L.got L.next (L.next + k4Takes P hp g) (tvFirstOf P L.next)
      (tvFirstOf P L.next + (1 + (2 * P.y.h.lt + 2)))
      (L.next + k4Takes P hp g - slotsMerge P.wsLay.lk)
      (L.next + k4Takes P hp g - slotsMerge P.wsLay.lk + (1 + (2 * P.wsLay.lk + 1))))
    L.owed L.planClaims L.trees (L.next + k4Takes P hp g) L.coefs L.claims L.drawn L.handed L.shut

/-- **The ledger's shape behind the hearing is the update of the shape in front.** -/
theorem hear_ledSh {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} {k iU3 : Nat} {tab : List TableAt} (h : hearFl P hp g fo F t = some (o, G, u))
    (hF : Room F (k4Takes P hp g + k)) (hG : Room G k) (hB : Below F G)
    (hn : G.next = F.next + k4Takes P hp g) (hL : HearLeft P hp g fo iU3 tab F G o) :
    ledSh G = hearLedU P hp g (ledSh F) := by
  have hs := hearFl_side h
  have sF := hF.sized
  have sG := hG.sized
  have e1 : G.vp.size = F.vp.size := by rw [sG.1, sF.1, hB.ns]
  have e2 : G.mf.size = F.mf.size := by rw [sG.2.1, sF.2.1, hB.ns]
  have e3 : G.gotF.size = F.gotF.size := by rw [sG.2.2, sF.2.2, hB.ns]
  have w1 := hL.tvFirst
  have w2 := hL.tvEnd
  have w3 := hL.woFirst
  have w4 := hL.sFv
  have eg : G.gotF.toList = marksU F.gotF.toList F.next (F.next + k4Takes P hp g)
      (tvFirstOf P F.next) (tvFirstOf P F.next + (1 + (2 * P.y.h.lt + 2)))
      (F.next + k4Takes P hp g - slotsMerge P.wsLay.lk)
      (F.next + k4Takes P hp g - slotsMerge P.wsLay.lk + (1 + (2 * P.wsLay.lk + 1))) := by
    unfold marksU
    have t1 : tvFirstOf P F.next = o.H.tV.p.first := by unfold tvFirstOf; omega
    have t2 : F.next + k4Takes P hp g - slotsMerge P.wsLay.lk = o.wo.p.first := by omega
    rw [t1, t2, ← w2, ← w4, ← hn]
    refine List.ext_getElem (by simp [e3]) fun i i1 i2 => ?_
    have iG : i < G.gotF.size := by simpa using i1
    have iF : i < F.gotF.size := by rw [← e3]; exact iG
    have fG : Filled G i ↔ G.gotF[i] = true := by simp [Filled, Array.getD, iG]
    have fF : Filled F i ↔ F.gotF[i] = true := by simp [Filled, Array.getD, iF]
    simp only [List.getElem_map, List.getElem_zipIdx, Array.getElem_toList, Nat.zero_add]
    by_cases c1 : i < F.next
    · have k := hB.same i c1
      rw [fG, fF] at k
      have hb : decide (F.next ≤ i) = false := by simpa using c1
      rw [hb]
      simp only [Bool.false_and, Bool.or_false]
      exact Bool.eq_iff_iff.2 k
    · have nF : F.gotF[i] = false := by
        have := hF.free i (by omega)
        rw [fF] at this
        simpa using this
      rw [nF, Bool.false_or]
      by_cases c2 : i < G.next
      · have k := hL.marks i (by omega) c2
        rw [fG] at k
        apply Bool.eq_iff_iff.2
        rw [k]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        constructor
        · intro hh
          exact ⟨⟨⟨by omega, c2⟩, by have := hh.1; omega⟩, by have := hh.2; omega⟩
        · intro hh
          exact ⟨fun hc => by have := hh.1.2; omega, fun hc => by have := hh.2; omega⟩
      · have nG : G.gotF[i] = false := by
          have := hG.free i (by omega)
          rw [fG] at this
          simpa using this
        rw [nG]
        have hb : decide (i < G.next) = false := by simpa using c2
        rw [hb]
        simp
  unfold hearLedU
  rw [hs]
  show LedSh.mk F.ns G.vp.size G.mf.size G.gotF.toList _ _ _ G.next _ _ _ _ _ = _
  rw [e1, e2, eg, hn]
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.Side.refl
#print axioms OnBytes.Desc.First.K4.Rt.Side.trans
#print axioms OnBytes.Desc.First.K4.Rt.Sides.of_same
#print axioms OnBytes.Desc.First.K4.Rt.Sides.bind
#print axioms OnBytes.Desc.First.K4.Rt.sides_foldlM
#print axioms OnBytes.Desc.First.K4.Rt.sides_mapM_list
#print axioms OnBytes.Desc.First.K4.Rt.sides_mapM_array
#print axioms OnBytes.Desc.First.K4.Rt.hide_side
#print axioms OnBytes.Desc.First.K4.Rt.hideSteps_side
#print axioms OnBytes.Desc.First.K4.Rt.hideRun_side
#print axioms OnBytes.Desc.First.K4.Rt.sides_levelRounds
#print axioms OnBytes.Desc.First.K4.Rt.sides_tscLoop
#print axioms OnBytes.Desc.First.K4.Rt.sides_wsForkRounds
#print axioms OnBytes.Desc.First.K4.Rt.hearFl_side
#print axioms OnBytes.Desc.First.K4.Rt.hear_ledSh
#print axioms OnBytes.Desc.First.K4.Rt.Side
#print axioms OnBytes.Desc.First.K4.Rt.Sides
#print axioms OnBytes.Desc.First.K4.Rt.sides_pure
#print axioms OnBytes.Desc.First.K4.Rt.sides_bind
#print axioms OnBytes.Desc.First.K4.Rt.sides_map
#print axioms OnBytes.Desc.First.K4.Rt.sides_ite
#print axioms OnBytes.Desc.First.K4.Rt.sides_none
#print axioms OnBytes.Desc.First.K4.Rt.sides_must
#print axioms OnBytes.Desc.First.K4.Rt.sides_need
#print axioms OnBytes.Desc.First.K4.Rt.sides_ask
#print axioms OnBytes.Desc.First.K4.Rt.sides_onTape
#print axioms OnBytes.Desc.First.K4.Rt.sides_takeSlots
#print axioms OnBytes.Desc.First.K4.Rt.sides_hideRun
#print axioms OnBytes.Desc.First.K4.Rt.sides_read
#print axioms OnBytes.Desc.First.K4.Rt.sides_readSum
#print axioms OnBytes.Desc.First.K4.Rt.sides_answer
#print axioms OnBytes.Desc.First.K4.Rt.sides_point
#print axioms OnBytes.Desc.First.K4.Rt.sides_batch
#print axioms OnBytes.Desc.First.K4.Rt.sides_empty
#print axioms OnBytes.Desc.First.K4.Rt.sides_shown
#print axioms OnBytes.Desc.First.K4.Rt.sides_publicPart
#print axioms OnBytes.Desc.First.K4.Rt.sides_claimsIn
#print axioms OnBytes.Desc.First.K4.Rt.sides_pscBeginAt
#print axioms OnBytes.Desc.First.K4.Rt.sides_pscBegin
#print axioms OnBytes.Desc.First.K4.Rt.sides_pscRound
#print axioms OnBytes.Desc.First.K4.Rt.sides_roundIn
#print axioms OnBytes.Desc.First.K4.Rt.sides_pscEnds
#print axioms OnBytes.Desc.First.K4.Rt.sides_pscRow
#print axioms OnBytes.Desc.First.K4.Rt.sides_levelIn
#print axioms OnBytes.Desc.First.K4.Rt.sides_tscRounds
#print axioms OnBytes.Desc.First.K4.Rt.sides_tscIn
#print axioms OnBytes.Desc.First.K4.Rt.sides_wsForkMerge
#print axioms OnBytes.Desc.First.K4.Rt.sides_flatForkEnd
#print axioms OnBytes.Desc.First.K4.Rt.marksU
#print axioms OnBytes.Desc.First.K4.Rt.tvFirstOf
#print axioms OnBytes.Desc.First.K4.Rt.hearLedU
#print axioms OnBytes.Desc.First.K4.Rt.instSidesArrayEBatchFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesTscTscInFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesGetFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesUnitMustFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesArrayEShownRunFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdArrayEPscLevelRounds
#print axioms OnBytes.Desc.First.K4.Rt.instSidesStackPlainRoundsFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesWsForkOutWsForkEndFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesOwnHearFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesPscPscBeginFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdEPscRoundInFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesEShownFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdNatPscPscEndsFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesHeardStackHearStackFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesLevelLevelInFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdLevelHearGatedFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesHeardHearNormsFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesAffJoinStartFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesUnitCheckFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdArrayEPscWsForkRounds
#print axioms OnBytes.Desc.First.K4.Rt.instSidesUnitMustAsFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesArrayEPointFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdAffPscSumcheckClaimFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesNatClaimsInFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesHeardHearTermsFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdAffPscPscRowFlEngFl
#print axioms OnBytes.Desc.First.K4.Rt.instSidesProdArrayEPscTscLoop
#print axioms OnBytes.Desc.First.K4.Rt.instSidesUnitPaddingFitsFlEngFl
