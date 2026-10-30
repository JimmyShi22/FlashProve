-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyTen.lean: THE KEY FILE's FIRST CHAIN AT THE KEY FILE's DESCRIPTION (Johnson/Desc/Key/Desc.lean; written over an earlier working state of these files): THE BLOCKS WITHOUT A ROUND: WHAT EACH ONE's YES DOES TO THE STATE, AS THE FACTS THAT KeyKeeps.emptyRow_keeps ASKS: KeyQuiet.Rides · the book-keeping's step.
OVER KeyShape.lean (the ties to the plan, one reader, in the promise): c_…: the steps of core₁; sh_…: of shape₁; start_shape: border 0's Bool at the first state. SEVEN OF THE TEN: a lookup's «laid» · «behind the batching» · «cleared», at both lookups · THE SEAL (it declares the sealing round, in which nothing is drawn: its decide hands the state on just where the chain's own clauses hold). (The caller ×2 · rng.0.rows: in KeyCaller.lean · KeyThree.lean; their «yes» facts in KeyYes.lean.)
  seal_ok                         the chains' end's one text (Johnson/Desc/ChainEnd.lean: chainEnd): its yes hands the state on unturned, whatever the clauses
  lay_ok | after_ok | clear_ok    the three texts' yes: the state is handed on unturned · unturned · with the lookup's ledger, what was heard and the homes struck (clr)
  ReadsD G                        A PREMISE ON THE READING (a letter still): of the chain's state it reads the statement's part (d) alone
  rides_same | rides_clr          **PROVED**: KeyQuiet.Rides at every open set
  sh_2_3 · sh_8_9 · sh_6_7 · sh_12_13 · sh_7_8 · sh_13_14 · sh_18_19   **PROVED**: the book-keeping's step across the six, AT TWO LOOKUPS (the number is a premise where these are spent: n₁ one = 2: by evaluation at both sizes' public files)
Nothing on soundness.
-/
import Johnson.RunOne.KeyReaders1
import Johnson.Desc.Means.Order
import Johnson.Desc.Key.KeyQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)

/-- What «cleared» leaves. -/
def clr (s : FirstState) : FirstState := { s with base := { s.base with fork := none, heard := none, home := #[] } }

section
variable (one : OneTime) (set : Setting) (i : Nat) (x : Lookup)

theorem lay_ok (s s' : FirstState) (h : (lookupLink one set i x).lay s = .ok s') : s' = s := by
  have h' : (need "a lookup's link: a ledger is open" s.base.fork.isNone >>= fun _ => (pure s : Except String FirstState)) = .ok s' := h
  cases hb : s.base.fork.isNone with
  | false => rw [hb] at h'; cases h'
  | true => rw [hb] at h'; exact (Except.ok.inj h').symm

theorem after_ok (s s' : FirstState) (h : afterIn (lookupLink one set i x).hear (lookupLink one set i x).orderAfter s = .ok s') : s' = s :=
  (Except.ok.inj h).symm

theorem clear_ok (s s' : FirstState) (h : (lookupLink one set i x).clear s = .ok s') : s' = clr s :=
  (Except.ok.inj h).symm

end

theorem seal_ok (asks : FirstState → ChainEnd.Clauses) (s s' : FirstState) (h : ((ChainEnd.refuse (asks s)).map fun _ => s) = .ok s') : s' = s := by
  cases hr : ChainEnd.refuse (asks s) with
  | error e => rw [hr] at h; cases h
  | ok u => rw [hr] at h; exact (Except.ok.inj h).symm

section
variable {Cells M Smp Rec : Type} (G : Reading (Xi × FirstState) Cells M Smp Rec) (one : OneTime)

/-- **A premise on the reading**: of the chain's state it reads the statement's part alone. -/
def ReadsD : Prop := ∀ (p : Xi) (s s' : FirstState), s'.d = s.d → SamePins G (p, s) (p, s')

theorem rides_same (O : List KItem) (p : Xi) (s : FirstState) : Rides G (readers₁ one) O p s s :=
  { marked := rfl, pins := ⟨fun _ _ => rfl, rfl⟩
    stmt := fun _ => ⟨⟨rfl, fun _ _ => rfl⟩, fun _ x' h => ⟨x', h, rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun _ G' h => ⟨G', h, rfl⟩⟩ }

theorem rides_clr (hG : ReadsD G) (O : List KItem) (p : Xi) (s : FirstState) : Rides G (readers₁ one) O p s (clr s) :=
  { marked := rfl, pins := hG p s (clr s) rfl
    stmt := fun _ => ⟨⟨rfl, fun _ _ => rfl⟩, fun _ x' h => ⟨x', h, rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun _ G' h => ⟨G', h, rfl⟩⟩ }

end

/-! ## The book-keeping's step, at two lookups -/

section
variable (one : OneTime) (s : FirstState)

theorem c_2_3 : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 3 s = core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 2 s := rfl
theorem c_8_9 : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 9 s = core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 8 s := rfl
theorem c_6_7 : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 7 s = core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 6 s := rfl
theorem c_12_13 : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 13 s = core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 12 s := rfl
theorem c_18_19 : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 19 s = core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 18 s := rfl

theorem c_7_8 (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 7 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 8 (clr s) = true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) && _) = true := h
  have h1 : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) = true := (Bool.and_eq_true_iff.1 h').1
  show ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) && true) = true
  rw [h1]; rfl

theorem c_13_14 (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 13 s = true) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 (clr s) = true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 2 s && ((readers₁ one).pile s).isNone) && _) = true := h
  have h1 : (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 && doneB (plan₁ one) (readers₁ one) 2 2 s && ((readers₁ one).pile s).isNone) = true := (Bool.and_eq_true_iff.1 h').1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h1
  show (sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 && true && true && doneB (plan₁ one) (readers₁ one) 2 2 s && (groupB (readers₁ one) s false 0 && ((readers₁ one).pile s).isNone && !sentB (plan₁ one) (readers₁ one) s 2)) = true
  rw [a, b, c, d, e, f]; rfl


/-! ## The same with the ties to the plan (KeyShape.lean; KeyReaders1.ties₁): none of the seven turns a field that a tie reads, and no tie parts between the two borders -/

theorem sh_2_3 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 2 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 3 s = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 2 3 s s (fun h' => (show ties₁ one 3 s = ties₁ one 2 s from rfl).trans h') (fun h' => (c_2_3 one s).trans h') h

theorem sh_8_9 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 8 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 9 s = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 8 9 s s (fun h' => (show ties₁ one 9 s = ties₁ one 8 s from rfl).trans h') (fun h' => (c_8_9 one s).trans h') h

theorem sh_6_7 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 6 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 7 s = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 6 7 s s (fun h' => (show ties₁ one 7 s = ties₁ one 6 s from rfl).trans h') (fun h' => (c_6_7 one s).trans h') h

theorem sh_12_13 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 12 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 13 s = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 12 13 s s (fun h' => (show ties₁ one 13 s = ties₁ one 12 s from rfl).trans h') (fun h' => (c_12_13 one s).trans h') h

theorem sh_18_19 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 18 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 19 s = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 18 19 s s (fun h' => (show ties₁ one 19 s = ties₁ one 18 s from rfl).trans h') (fun h' => (c_18_19 one s).trans h') h

theorem sh_7_8 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 7 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 8 (clr s) = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 7 8 s (clr s) (fun h' => (show ties₁ one 8 (clr s) = ties₁ one 7 s from rfl).trans h') (c_7_8 one s) h

theorem sh_13_14 (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 13 s = true) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 (clr s) = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 13 14 s (clr s) (fun h' => (show ties₁ one 14 (clr s) = ties₁ one 13 s from rfl).trans h') (c_13_14 one s) h

/-- **At the first chain's first state the book-keeping's Bool at border 0 says yes**, where the plan has just two lookups and the lookups' own message has the number 1: the start lays the plan's codes; no message, no group. -/
theorem start_shape (h2 : (lookupsOf one).length = 2) (hm : one.ranges.messageId = 1) : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0 (chainStart one.codes {}) = true := by
  refine (shape₁_iff (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0 _).2 ⟨?_, rfl⟩
  show (((lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (one.codes = one.codes) && true && true) && true && true) = true
  rw [h2, hm]
  simp

end

/-- The first chain's first state's statement is in order: InOrder.start. -/
theorem start_order (codes : OnBytes.Codes) : OnBytes.Means.InOrder (chainStart (β := LookupRecord) codes {}).d.st := OnBytes.Means.InOrder.start codes

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.lay_ok
#print axioms Johnson.RunOne.KeyRows1.seal_ok
#print axioms Johnson.RunOne.KeyRows1.rides_clr
#print axioms Johnson.RunOne.KeyRows1.sh_7_8
#print axioms Johnson.RunOne.KeyRows1.sh_13_14
#print axioms Johnson.RunOne.KeyRows1.start_shape
