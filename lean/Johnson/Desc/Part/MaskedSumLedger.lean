-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumLedger.lean: THE PART «THE MASKED SUMCHECK»: WHAT LIES UNDER ITS SLOTS IN THE LEDGER's WORLD.
The laws of the ledger (OnBytes/Model/HideLaws.lean: Fork.worldOf; OnBytes/Tie/Pv/Psc/PscFork.lean: Sized; PscLater.lean:
Later; PscForm.lean: hideRun_slot, value_public, value_later_public) are MOVED onto Part/MaskedSum4.lean's «hear» and «row».
THE WORLD is the function H.worldOf ρ mask entry: slot j is worth (what was shown under j) less (its factor) times mask j.
mask (the mask row) and entry (the virtual rows' entries) are letters in front of every statement. H: any ledger later than the
one that the write hands back, that one among them.
  ledger_own  : AT EVERY CALL, with ends or without: behind «row»'s write, under the sumcheck's own slots lie the mask's entries: slot (h.first + i) is worth
                mask (F.next + i), i below ownSlots; F: the ledger IN FRONT of the hearing.
  ledger_ends : behind «hear», under the end values' slots: what was shown less beta times the mask's entry.
  ledger_shown, ledger_shownEnds : what the ledger shows under these slots, and «shownEnds», is what the hearing read.
  ledger_ownLaid, row_of_laid, laid_of_row : the same for a caller that writes by «rowLaid» (Part/MaskedSumMore.lean).
  ledger_place, ledger_D1 : plain_row's condition (D1), in that world, is a sentence on the mask row alone.
  ledger_D2, ledger_D2all : the right side of its condition (D2), in that world: the masked part of the start form.
  hear_later, row_later, hear_keeps, row_keeps : both lead to later ledgers (the last two ask nothing of the sizes).
ASSUMED OF THE LEDGER IN FRONT: Sized, and that «hear» | «row» returns there.
WHICH «Later»: OnBytes.PscRun.Later (OnBytes/Tie/Pv/Psc/PscLater.lean), written with its full name throughout; NOT Fo.Later
(OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean, which lacks the field on sizes), and not a relation of that short name on statements. The
proofs of ledger_own and ledger_ends spend its clause «keep» alone: ledger_own_keep and ledger_ends_keep take that clause bare, so
that a holder of Fo.Later spends them by its own field keep.
FOR WHOEVER SPENDS ledger_own IN A LAW WITH BAD SETS: F (its next slot) and mask must stand IN FRONT of the bad sets and of eps:
the coefficients «fun i => mask (F.next + i)» hang on the mask and on the ledger in front of the hearing, on nothing of the rounds.
THE STANDING CAVEAT: ledger_own IS TRUE OF EVERY FUNCTION mask: it is the ledger's bookkeeping read back (0 shown, factor −1), NO
FACT ABOUT A COMMITMENT. A law gets teeth only where «the row's form is worth 0 in this world» comes from the chain's one equation on
the committed row (algebra: Fork.settle_total, settle_whole) WITH THE SAME LETTER mask.
REACH: of the part's text (Part/MaskedSum4.lean) alone; `verify-on-bytes`'s routines have the twins pscRow_slot, pscEnds_slot.
STANDS ON: hear_spec, readAll_spec, varRounds_spec of Part/MaskedSumShape.lean (core Lean).
WHAT IS NOT SAID. That mask is the committed mask row. That ledger_D1's right side holds (which entries of the message are which
mask entries). Anything on kept terms. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumTie
import Johnson.Desc.Part.MaskedSumMore
import OnBytes.Tie.Pv.Psc.PscForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-! ## How many slots -/

theorem powersFrom_len (x : E) : ∀ (n : Nat) (a : E), (powersFrom x n a).length = n
  | 0, _ => rfl
  | n + 1, a => by
    show (powersFrom x n (mulE a x)).length + 1 = n + 1
    rw [powersFrom_len x n]

theorem foldl_own : ∀ (vs : List Var) (a : Nat),
    vs.foldl (fun n v => n + (v.d - 1)) a = a + (vs.map fun v => v.d - 1).sum
  | [], a => by simp
  | v :: vs, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_own vs]
    omega

theorem ownSlots_one_add (vs : List Var) : ownSlots vs = 1 + (vs.map fun v => v.d - 1).sum := foldl_own vs 1

/-- The hiding polynomial has as many coefficients as the sumcheck has slots of its own. -/
theorem hidingAt_zip_len : ∀ (vs : List Var) (r : List E), vs ≠ [] → vs.length = r.length → (∀ v ∈ vs, 1 ≤ v.d) →
    (hidingAt (vs.zip r)).1.length = 1 + (vs.map fun v => v.d - 1).sum
  | [], _, h, _, _ => absurd rfl h
  | [v], [x], _, _, hd => by
    have h1 : 1 ≤ v.d := hd v (by simp)
    show (powersFrom x v.d oneE).length = 1 + ((v.d - 1) + 0)
    rw [powersFrom_len]
    omega
  | v :: w :: vs, x :: y :: r, _, hl, hd => by
    have ih := hidingAt_zip_len (w :: vs) (y :: r) (by simp)
      (by simp only [List.length_cons] at hl ⊢; omega) (fun u hu => hd u (List.mem_cons_of_mem _ hu))
    show (powersFrom x (v.d - 1) (mulE (hidingAt ((w :: vs).zip (y :: r))).2 x) ++
      (hidingAt ((w :: vs).zip (y :: r))).1).length = 1 + ((v.d - 1) + ((w :: vs).map fun v => v.d - 1).sum)
    rw [List.length_append, powersFrom_len, ih]
    omega
  | [_], [], _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | [_], _ :: _ :: _, _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _ :: _, [], _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _ :: _, [_], _, hl, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

theorem one_le_all {lead : Nat} {vs : List Var} {e : Ends} (hs : shapeOk ⟨lead, vs, some e⟩ = true) :
    ∀ v ∈ Call.all ⟨lead, vs, some e⟩, 1 ≤ v.d := by
  intro v hv
  have hv' : v ∈ vs ++ [Var.point zeroE (e.dY + 1)] := hv
  rcases List.mem_append.1 hv' with h1 | h1
  · unfold shapeOk at hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    have h2 := (hs.1 v h1).1
    omega
  · have e1 : v = Var.point zeroE (e.dY + 1) := by simpa using h1
    subst e1
    show 1 ≤ e.dY + 1
    omega

/-- What the hearing hands back: the first slot, the end values' first slot, the number of the hiding polynomial's coefficients. -/
theorem heard_len {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C ⟨lead, vs, some e⟩ F rs = some (h, G)) :
    h.first = F.next ∧ h.sEnd = F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) ∧
      (hidingAt (h.vars.zip h.r)).1.length = ownSlots (Call.all ⟨lead, vs, some e⟩) := by
  obtain ⟨hs, T, R, _, hR, he, _⟩ := hear_spec hh
  obtain ⟨_, _, _, _, _, _, _, a4, _⟩ := readAll_spec hR
  have hlen : R.rounds.length = (Call.all ⟨lead, vs, some e⟩).length := (VarsRead.length a4).2
  have hne : Call.all ⟨lead, vs, some e⟩ ≠ [] := by
    show vs ++ [Var.point zeroE (e.dY + 1)] ≠ []
    simp
  subst he
  refine ⟨rfl, rfl, ?_⟩
  show (hidingAt ((Call.all ⟨lead, vs, some e⟩).zip (R.rounds.map (·.2)))).1.length = _
  rw [hidingAt_zip_len _ _ hne (by rw [List.length_map, hlen]) (one_le_all hs), ownSlots_one_add]

/-- A call without ends: as many rounds are read as there are variables. -/
theorem readAll_none_len {lead : Nat} {vs : List Var} {rs : List Fmt.RoundView} {R : Read}
    (h : readAll ⟨lead, vs, none⟩ rs = some R) : R.rounds.length = vs.length := by
  unfold readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · rename_i x mu eps l h1 h2 h3
      have e := Option.some.inj h
      subst e
      obtain ⟨used, _, a2⟩ := varRounds_spec _ _ _ _ h2
      exact (VarsRead.length a2).2
    · rename_i h3
      cases h3
    · cases h

/-- The same at every call, with ends or without. -/
theorem heard_lenK {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) :
    h.first = F.next ∧ h.sEnd = F.next + ownSlots k.all ∧
      (hidingAt (h.vars.zip h.r)).1.length = ownSlots k.all := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | some e => exact heard_len hh
  | none =>
    obtain ⟨hs, T, R, _, hR, he, _⟩ := hear_spec hh
    have hlen : R.rounds.length = vs.length := readAll_none_len hR
    unfold shapeOk at hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
    have hne : vs ≠ [] := by
      intro h0
      rw [h0] at hs
      simp at hs
    have hge : ∀ v ∈ vs, 1 ≤ v.d := by
      intro v hv
      have h2 := (hs.1 v hv).1
      omega
    subst he
    refine ⟨rfl, rfl, ?_⟩
    show (hidingAt (vs.zip (R.rounds.map (·.2)))).1.length = ownSlots vs
    rw [hidingAt_zip_len _ _ hne (by rw [List.length_map, hlen]) hge, ownSlots_one_add]

/-- The count at two variables, by evaluation. -/
theorem hiding_count_two :
    (hidingAt ([Var.plain 3, Var.plain 2].zip [oneE, oneE])).1.length = ownSlots [Var.plain 3, Var.plain 2] := rfl

/-! ## The writes -/

/-- What «row» writes. -/
theorem row_write {h : Heard} {S0 : E} {kept f : Aff} {F G : Fork} (hr : row h S0 kept F = some (f, G)) :
    F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) = some G := by
  unfold row at hr
  cases ho : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) with
  | none => simp [ho] at hr
  | some G' =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
    rw [hr.2]

/-- «row»'s write is «rowLaid» (Part/MaskedSumMore.lean). -/
theorem laid_of_row {h : Heard} {S0 : E} {kept f : Aff} {F G : Fork} (hr : row h S0 kept F = some (f, G)) :
    rowLaid h F = some G := row_write hr

/-- A caller that writes by «rowLaid» and takes «rowForm» has «row»'s return. -/
theorem row_of_laid {h : Heard} {F G : Fork} (S0 : E) (kept : Aff) (hw : rowLaid h F = some G) :
    row h S0 kept F = some (rowForm h S0 kept, G) := by
  have hw' : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) =
      some G := hw
  unfold row
  simp only [hw', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- Without a premise on the sizes. -/
theorem row_keeps {h : Heard} {S0 : E} {kept f : Aff} {F G : Fork} (hr : row h S0 kept F = some (f, G)) :
    OnBytes.PscRun.Later F G := OnBytes.PscRun.hideRun_keeps (row_write hr)

theorem hear_keeps {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) : OnBytes.PscRun.Later F G := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := hear_spec hh
  have l1 : OnBytes.PscRun.Later F ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) :=
    ⟨Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _), rfl, id, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  exact l1.trans (OnBytes.PscRun.hideRun_keeps hG)

theorem row_later {h : Heard} {S0 : E} {kept f : Aff} {F G : Fork} (hF : OnBytes.PscRun.Sized F)
    (hr : row h S0 kept F = some (f, G)) : OnBytes.PscRun.Later F G :=
  OnBytes.PscRun.hideRun_later hF (row_write hr)

theorem hear_later {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hF : OnBytes.PscRun.Sized F)
    (hh : hear C k F rs = some (h, G)) : OnBytes.PscRun.Later F G := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := hear_spec hh
  have l1 : OnBytes.PscRun.Later F ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) :=
    ⟨Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _), rfl, id, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  exact l1.trans (OnBytes.PscRun.hideRun_later hF hG)

section World
variable {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)

/-- Behind «row»'s write: the mask's entries themselves. -/
theorem row_slot {h : Heard} {S0 : E} {kept f : Aff} {F G H : Fork} (hF : OnBytes.PscRun.Sized F)
    (hr : row h S0 kept F = some (f, G)) (hl : OnBytes.PscRun.Later G H) (i : Nat)
    (hi : i < (hidingAt (h.vars.zip h.r)).1.length) :
    (H.worldOf ρ mask entry).slot (h.first + i) = mask (h.first + i) := by
  rw [OnBytes.PscRun.hideRun_slot ρ hF (row_write hr) hl mask entry i (by simpa using hi)]
  have e : (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE).getD i zeroE = zeroE := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [e, ρ.zero, ρ.sub, ρ.zero, ρ.one]
  ring

/-- hideRun_slot (OnBytes/Tie/Pv/Psc/PscForm.lean), the clause «keep» bare in the place of Later. -/
theorem hideRun_slot_keep {F G H : Fork} {first : Nat} {v : Array E} {factor : E} (hF : OnBytes.PscRun.Sized F)
    (h : F.hideRun first v factor = some G)
    (hk : ∀ j, OnBytes.PscRun.Filled G j → OnBytes.PscRun.Filled H j ∧ H.vp.getD j zeroE = G.vp.getD j zeroE ∧
      H.mf.getD j zeroE = G.mf.getD j zeroE) (i : Nat) (hi : i < v.size) :
    (H.worldOf ρ mask entry).slot (first + i) = ρ.val (v.getD i zeroE) - ρ.val factor * mask (first + i) := by
  obtain ⟨-, -, h3, -⟩ := OnBytes.PscRun.hideRun_ok F G first v factor hF h
  obtain ⟨-, -, f1, f2, f3⟩ := h3 i hi
  obtain ⟨-, k2, k3⟩ := hk _ f1
  show ρ.val (H.vp.getD (first + i) zeroE) - ρ.val (H.mf.getD (first + i) zeroE) * mask (first + i) = _
  rw [k2, k3, f2, f3]

/-- (L1) with the clause «keep» bare. -/
theorem ledger_own_keep {C : Aff} {k : Call} {F G F' G' H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {S0 : E} {kept f : Aff} (hh : hear C k F rs = some (h, G)) (hF' : OnBytes.PscRun.Sized F')
    (hr : row h S0 kept F' = some (f, G'))
    (hk : ∀ j, OnBytes.PscRun.Filled G' j → OnBytes.PscRun.Filled H j ∧ H.vp.getD j zeroE = G'.vp.getD j zeroE ∧
      H.mf.getD j zeroE = G'.mf.getD j zeroE) :
    ∀ i, i < ownSlots k.all → (H.worldOf ρ mask entry).slot (h.first + i) = mask (F.next + i) := by
  obtain ⟨e1, _, e3⟩ := heard_lenK hh
  intro i hi
  have hi' : i < (hidingAt (h.vars.zip h.r)).1.length := by rw [e3]; exact hi
  rw [hideRun_slot_keep ρ mask entry hF' (row_write hr) hk i (by simpa using hi')]
  have e : (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE).getD i zeroE = zeroE := by
    simp [Array.getD_eq_getD_getElem?, hi']
  rw [e, ρ.zero, ρ.sub, ρ.zero, ρ.one, e1]
  ring

/-- **(L1) Under the sumcheck's own slots lie the mask's entries.** F.next and mask must stand in front of eps at the caller. -/
theorem ledger_own {C : Aff} {k : Call} {F G F' G' H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {S0 : E} {kept f : Aff} (hh : hear C k F rs = some (h, G)) (hF' : OnBytes.PscRun.Sized F')
    (hr : row h S0 kept F' = some (f, G')) (hl : OnBytes.PscRun.Later G' H) :
    ∀ i, i < ownSlots k.all →
      (H.worldOf ρ mask entry).slot (h.first + i) = mask (F.next + i) := by
  obtain ⟨e1, _, e3⟩ := heard_lenK hh
  intro i hi
  rw [row_slot ρ mask entry hF' hr hl i (by rw [e3]; exact hi), e1]

/-- (L1) for a caller that writes by «rowLaid». -/
theorem ledger_ownLaid {C : Aff} {k : Call} {F G F' G' H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hF' : OnBytes.PscRun.Sized F') (hw : rowLaid h F' = some G')
    (hl : OnBytes.PscRun.Later G' H) :
    ∀ i, i < ownSlots k.all → (H.worldOf ρ mask entry).slot (h.first + i) = mask (F.next + i) :=
  ledger_own ρ mask entry hh hF' (row_of_laid zeroE {} hw) hl

/-- **(L2) Under the end values' slots: what was shown less beta times the mask's entry.** -/
theorem ledger_ends {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {R : Read} (hF : OnBytes.PscRun.Sized F) (hh : hear C ⟨lead, vs, some e⟩ F rs = some (h, G))
    (hR : readAll ⟨lead, vs, some e⟩ rs = some R) (hl : OnBytes.PscRun.Later G H) :
    ∀ j, j < e.n → (H.worldOf ρ mask entry).slot (h.sEnd + j) =
      ρ.val (R.values.getD j zeroE) -
        ρ.val (h.r.getLastD zeroE) * mask (F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + j) := by
  obtain ⟨_, _, R', _, hR', he, hG⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  rw [hRR] at he hG
  obtain ⟨_, _, _, _, _, _, _, _, a5⟩ := readAll_spec hR
  intro j hj
  have hs2 : j < R.values.toArray.size := by
    simp [a5.2.1, hj]
  have hF2 : OnBytes.PscRun.Sized
      ({ F with next := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + R.values.length } : Fork) := hF
  have key := OnBytes.PscRun.hideRun_slot ρ hF2 hG hl mask entry j hs2
  have e1 : R.values.toArray.getD j zeroE = R.values.getD j zeroE := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e1] at key
  subst he
  exact key

/-- (L2) with the clause «keep» bare. -/
theorem ledger_ends_keep {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {R : Read} (hF : OnBytes.PscRun.Sized F) (hh : hear C ⟨lead, vs, some e⟩ F rs = some (h, G))
    (hR : readAll ⟨lead, vs, some e⟩ rs = some R)
    (hk : ∀ j, OnBytes.PscRun.Filled G j → OnBytes.PscRun.Filled H j ∧ H.vp.getD j zeroE = G.vp.getD j zeroE ∧
      H.mf.getD j zeroE = G.mf.getD j zeroE) :
    ∀ j, j < e.n → (H.worldOf ρ mask entry).slot (h.sEnd + j) =
      ρ.val (R.values.getD j zeroE) -
        ρ.val (h.r.getLastD zeroE) * mask (F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + j) := by
  obtain ⟨_, _, R', _, hR', he, hG⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  rw [hRR] at he hG
  obtain ⟨_, _, _, _, _, _, _, _, a5⟩ := readAll_spec hR
  intro j hj
  have hs2 : j < R.values.toArray.size := by
    simp [a5.2.1, hj]
  have hF2 : OnBytes.PscRun.Sized
      ({ F with next := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + R.values.length } : Fork) := hF
  have key := hideRun_slot_keep ρ mask entry hF2 hG hk j hs2
  have e1 : R.values.toArray.getD j zeroE = R.values.getD j zeroE := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e1] at key
  subst he
  exact key

/-- A loop of steps that all return. -/
theorem mapM_some {α β : Type} (f : α → Option β) (g : α → β) : ∀ l : List α, (∀ a ∈ l, f a = some (g a)) →
    l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    have ih := mapM_some f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp [List.mapM_cons, h a (by simp), ih]

theorem range_getD (l : List E) : ((List.range l.length).map fun j => l.getD j zeroE) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h2]

/-- **(L2a) What the ledger shows under the end values' slots is what the hearing read.** -/
theorem ledger_shown {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {R : Read} (hF : OnBytes.PscRun.Sized F) (hh : hear C ⟨lead, vs, some e⟩ F rs = some (h, G))
    (hR : readAll ⟨lead, vs, some e⟩ rs = some R) (hl : OnBytes.PscRun.Later G H) :
    ∀ j, j < e.n → H.shown (h.sEnd + j) = some (R.values.getD j zeroE) := by
  obtain ⟨_, _, R', _, hR', he, hG⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  rw [hRR] at he hG
  obtain ⟨_, _, _, _, _, _, _, _, a5⟩ := readAll_spec hR
  intro j hj
  have hs2 : j < R.values.toArray.size := by
    simp [a5.2.1, hj]
  have hF2 : OnBytes.PscRun.Sized
      ({ F with next := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + R.values.length } : Fork) := hF
  obtain ⟨b1, _, b3, _⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hF2 hG
  obtain ⟨c1, _, c3, c4, _⟩ := b3 j hs2
  have e1 : R.values.toArray.getD j zeroE = R.values.getD j zeroE := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e1] at c4
  have hs := (OnBytes.PscRun.shown_iff G _ _).2 ⟨by rw [b1.ns]; exact c1, c3, c4.symm⟩
  subst he
  exact OnBytes.PscRun.shown_later hl hs

/-- **(L2') «shownEnds» gives what the hearing read**: for a caller that makes its end term from what the ledger shows. -/
theorem ledger_shownEnds {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {R : Read} (hF : OnBytes.PscRun.Sized F) (hh : hear C ⟨lead, vs, some e⟩ F rs = some (h, G))
    (hR : readAll ⟨lead, vs, some e⟩ rs = some R) (hl : OnBytes.PscRun.Later G H) :
    shownEnds h e.n H = some R.values := by
  obtain ⟨_, _, _, _, _, _, _, _, a5⟩ := readAll_spec hR
  have hn : R.values.length = e.n := a5.2.1
  unfold shownEnds
  rw [mapM_some _ (fun j => R.values.getD j zeroE) _
    (fun j hj => ledger_shown hF hh hR hl j (List.mem_range.1 hj)), ← hn, range_getD]

/-- **(L4) The right side of (D2) in the ledger's world: the masked part of the start form.** -/
theorem ledger_D2 {C : Aff} {k : Call} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hC : C.ents = #[]) (hl : OnBytes.PscRun.Later F H) :
    ρ.val h.target - h.start.value ρ (H.worldOf ρ mask entry) =
      (C.slots.toList.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum := by
  obtain ⟨_, T, _, hT, _, he, _⟩ := hear_spec hh
  have e1 : h.target = T := by rw [he]
  have e2 : h.start = C := by rw [he]
  rw [e1, e2, OnBytes.PscRun.value_later_public ρ hl C T hT mask entry,
    OnBytes.PscRun.value_public ρ F C T hT hC mask entry]
  ring

theorem value_split (W : World K) (a : Aff) :
    a.value ρ W = (a.ents.toList.map (Ent.value ρ W)).sum + ({ a with ents := #[] } : Aff).value ρ W := by
  simp [Aff.value, add_assoc]

/-- (L4) for every start form: the entries of virtual rows come as one term more. -/
theorem ledger_D2all {C : Aff} {k : Call} {F G H : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hl : OnBytes.PscRun.Later F H) :
    ρ.val h.target - h.start.value ρ (H.worldOf ρ mask entry) =
      (C.slots.toList.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum -
        (C.ents.toList.map (Ent.value ρ (H.worldOf ρ mask entry))).sum := by
  obtain ⟨_, T, _, hT, _, he, _⟩ := hear_spec hh
  have e1 : h.target = T := by rw [he]
  have e2 : h.start = C := by rw [he]
  have hT' : F.publicPart ({ C with ents := #[] } : Aff) = some T := hT
  have e3 := OnBytes.PscRun.value_later_public ρ hl _ T hT' mask entry
  have e4 : ({ C with ents := #[] } : Aff).value ρ (F.worldOf ρ mask entry) = ρ.val T -
      (C.slots.toList.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum :=
    OnBytes.PscRun.value_public ρ F _ T hT' rfl mask entry
  rw [e1, e2, value_split ρ _ C, e3, e4]
  ring

/-! ## (D1) -/

omit [Field K] in
/-- Which mask stands where hangs on the masks from s on alone, as many as the hiding polynomial has coefficients. -/
theorem place_congr (a b : ℕ → K) : ∀ (l : List (Cb.HVar K)) (s : ℕ),
    (∀ j, s ≤ j → j < s + (1 + (l.map (·.n)).sum) → a j = b j) →
    ∀ i : Cb.HIdx l, OnBytes.Road.Hd.place a l s i = OnBytes.Road.Hd.place b l s i
  | [], s, h, _ => h s (Nat.le_refl _) (by omega)
  | [v], s, h, Sum.inl t => h (s + 1 + t) (by omega) (by
      have := t.2
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
  | [_], s, h, Sum.inr _ => h s (Nat.le_refl _) (by omega)
  | v :: _ :: _, s, h, Sum.inl t => h (s + t) (by omega) (by
      have := t.2
      simp only [List.map_cons, List.sum_cons]
      omega)
  | v :: v' :: l, s, h, Sum.inr i => place_congr a b (v' :: l) (s + v.n) (fun j h1 h2 => h j (by omega) (by
      simp only [List.map_cons, List.sum_cons] at h2 ⊢
      omega)) i

omit [Field K] in
theorem pVars_n : ∀ (l : List (PFmt K)) (d : PDats l), (pVars l d).map (·.n) = l.map PFmt.n
  | [], _ => rfl
  | f :: l, d => congrArg (f.n :: ·) (pVars_n l d.2)

end World

theorem own_varsOf : ∀ (degs : List Nat) (DY : Nat),
    ((degs.map (fun d => Var.plain (d + 1)) ++ [Var.point zeroE (DY + 1)]).map fun v => v.d - 1) = degs ++ [DY]
  | [], _ => rfl
  | d :: degs, DY => congrArg (d :: ·) (own_varsOf degs DY)

/-- **(L3) The two places are one**: which mask stands for which coefficient, read in the ledger's world from the record's first
slot on, is the same read in the mask row from the ledger's next slot in front of the hearing on. -/
theorem ledger_place {K : Type} [Field K] [Fintype K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    (T : PlainSc K) (st : T.St) {lead : Nat} {e : Ends} {C : Aff}
    {F G F' G' H : Fork} {rs : List Fmt.RoundView} {h : Heard} {S0 : E} {kept f : Aff}
    (hh : hear C ⟨lead, (List.ofFn T.deg).map (fun d => Var.plain (d + 1)), some e⟩ F rs = some (h, G))
    (hY : e.dY = T.DY) (hF' : OnBytes.PscRun.Sized F') (hr : row h S0 kept F' = some (f, G'))
    (hl : OnBytes.PscRun.Later G' H) :
    OnBytes.Road.Hd.place (H.worldOf ρ mask entry).slot (T.our.par.vars st) h.first =
      OnBytes.Road.Hd.place mask (T.our.par.vars st) F.next := by
  have hown := ledger_own ρ mask entry hh hF' hr hl
  obtain ⟨e1, _, _⟩ := heard_len hh
  have hsum : 1 + ((T.our.par.vars st).map (·.n)).sum =
      ownSlots (Call.all ⟨lead, (List.ofFn T.deg).map (fun d => Var.plain (d + 1)), some e⟩) := by
    rw [ownSlots_one_add]
    show 1 + _ = 1 + (((List.ofFn T.deg).map (fun d => Var.plain (d + 1)) ++
      [Var.point zeroE (e.dY + 1)]).map fun v => v.d - 1).sum
    rw [own_varsOf, (pVars_n _ _).trans (plain_degs T), hY]
  rw [e1]
  funext i
  refine place_congr _ _ _ _ (fun j h1 h2 => ?_) i
  obtain ⟨t, rfl⟩ : ∃ t, j = F.next + t := ⟨j - F.next, by omega⟩
  have h3 := hown t (by rw [← hsum]; omega)
  rw [e1] at h3
  exact h3

/-- **(D1), as plain_row (OnBytes/Tie/Pv/Att/RowTie.lean) words it, in the ledger's world, is a sentence on the mask row alone.** -/
theorem ledger_D1 {K : Type} [Field K] [Fintype K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    (T : PlainSc K) (st : T.St) (m : T.J → K) {lead : Nat} {e : Ends} {C : Aff}
    {F G F' G' H : Fork} {rs : List Fmt.RoundView} {h : Heard} {S0 : E} {kept f : Aff}
    (hh : hear C ⟨lead, (List.ofFn T.deg).map (fun d => Var.plain (d + 1)), some e⟩ F rs = some (h, G))
    (hY : e.dY = T.DY) (hF' : OnBytes.PscRun.Sized F') (hr : row h S0 kept F' = some (f, G'))
    (hl : OnBytes.PscRun.Later G' H) :
    (T.our.par.W st m = OnBytes.Road.Hd.place (H.worldOf ρ mask entry).slot (T.our.par.vars st) h.first) ↔
      (T.our.par.W st m = OnBytes.Road.Hd.place mask (T.our.par.vars st) F.next) := by
  rw [ledger_place ρ mask entry T st hh hY hF' hr hl]

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_own
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_ends
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_own_keep
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_ends_keep
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_shownEnds
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_ownLaid
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_place
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_D1
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_D2
#print axioms VerifiableInference.Desc.Part.MaskedSum.ledger_D2all
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_keeps
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_keeps
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_later
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_later
