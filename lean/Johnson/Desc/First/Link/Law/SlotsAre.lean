-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsAre.lean: THE PROPERTY, ITS MAKER, ITS FIVE CLOSURE RULES.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
The walk is adapted from LooksAre.lean (beside this file): that file's theorems on the arrays'
looks, carried over by program to the two numbers, name by name (…looks… ↦ …slots…; else a letter S
behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Core hideRun_core paid_core)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side coefBody_inv)
open VerifiableInference.Desc.K9 (drawn drawnClean)
open VerifiableInference.Desc.K9L
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-- A ledger's two numbers: how many slots it has; how many coefficients its list LS has. -/
def sl (F : Fork) : ℕ × ℕ := (F.ns, F.LS.size)

/-- **They are v.** -/
def SlotsAre (v : ℕ × ℕ) (F : Fork) : Prop := sl F = v

theorem slotsAre_iff (n : ℕ) (F : Fork) : SlotsAre (n, n) F ↔ F.ns = n ∧ F.LS.size = F.ns := by
  unfold SlotsAre sl
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, b.trans a.symm⟩
  · rintro ⟨a, b⟩
    exact ⟨a, b.trans a⟩

theorem sl_core {F G : Fork} (h : Core F G) : sl G = sl F := by
  unfold sl
  rw [h.ns, h.LS]

/-- A ledger that parts from another in its arrays alone. -/
theorem sl_trees (F : Fork) (tr : Array HTree) : sl { F with trees := tr } = sl F := rfl

section
variable {sh : ℕ × ℕ}

theorem slots_map {F G : Fork} (h : sl G = sl F) (hF : SlotsAre sh F) : SlotsAre sh G := by
  unfold SlotsAre at hF ⊢
  rw [h]
  exact hF

end

/-- The ledger that is laid with ns slots has the two numbers ns. -/
theorem slots_laid (F : Fork) (ns : ℕ) :
    SlotsAre (ns, ns) (emptySlots (weightsAtZero F) ns) := by
  unfold SlotsAre sl emptySlots
  simp

/-- **The five closure rules.** -/
theorem slots_rests (sh : ℕ × ℕ) : ForkRests (SlotsAre sh) where
  later _ _ hc _ := slots_map (sl_core hc)
  hide _ _ _ _ _ h := slots_map (sl_core (hideRun_core h))
  paid F i := slots_map (sl_core (paid_core F i))
  eq _ _ _ _ _ _ _ he := slots_map (by unfold sl; rw [(eq_side he).ns, (eq_side he).LS])
  coef tl g F h := coefBody_inv (SlotsAre sh) (fun r t' r' f hr => slots_map rfl hr) tl g F h

/-- The filling of the weights that are not yet there. -/
theorem slots_fill {sh : ℕ × ℕ} (F : Fork) (T : Tail2) (h : SlotsAre sh F) :
    SlotsAre sh (t2FillL F T) := slots_map rfl h

/-- **The batching's draw.** -/
theorem slots_draw {sh : ℕ × ℕ} (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ)
    (L : LinkCtx) (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o)
    (hF : SlotsAre sh F) : SlotsAre sh o.F := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact slots_map (F := t2FillL F L.list) rfl (slots_fill F L.list hF)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.slots_rests
#print axioms VerifiableInference.Desc.LinkJoin.slots_draw
