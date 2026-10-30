-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/BridgeEntries.lean: the kind "lookup" (K3): the hearing on a view's rounds
against the general text on a tape, at the plan's own entries. Theorems.

Main theorems:
  `esMsg_eq`: the entries as the binds lay them (Johnson/Top/H/K3Via/Bridge.lean) are `entriesV f`
    (Johnson/Desc/First/Look/Via/Rounds.lean), the list that `entriesFit` holds the plan's entries
    against.
  `tapeT_work`, `staticT_work`: neither the strict maker nor the entry-alone tests read an entry's
    work bits.
  `hearV_general`: where hearV says yes, at entries es that pass entriesFit and the entry-alone
    tests, the general text off the strict tape says yes on the same rounds at es: the same ledger,
    and toHeardG of what hearV heard. As machine words; no premise on words.
  `hearV_hearG`: the same as hearG's yes at a place whose planner's entries are such.

Limits. Nothing of K3.lean's own messages h: from messagesG at faceOf h to messages h is a tie of
two flat texts (Johnson/Top/H/K3Via/BridgeProof.lean). Nothing the other way round: that the general
text's yes gives hearV's yes is not stated. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (entry entries callOf openCall)
open VerifiableInference.Desc.First.Tape (tapeT roundT flRun)

/-! ## The entries -/

theorem constFlat {α : Type} (L : List Fmt.Entry) : ∀ (l l' : List α), l.length = l'.length →
    l.flatMap (fun _ => L) = l'.flatMap (fun _ => L)
  | [], [], _ => rfl
  | _ :: l, _ :: l', h => by
    rw [List.flatMap_cons, List.flatMap_cons, constFlat L l l' (Nat.succ.inj h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem entries_noVar (dY n : Nat) : entries (noVar dY n) = sumE 0 dY n := entries_callOf [] dY n

theorem tieE_eq (w : Nat) :
    tieE w = entries (noVar 3 3) ++ (List.range (w - 2)).flatMap
      (fun _ => entries (noVar 3 2)) := by
  unfold tieE
  rw [entries_noVar, entries_noVar, List.append_nil]
  have e : (fun (_ : Nat) => sumE 0 3 2 ++ []) = fun _ => sumE 0 3 2 := by
    funext _
    rw [List.append_nil]
  rw [e]

theorem partsE_eq : ∀ (n : Nat), partsE n = (List.range n).flatMap (fun _ => entries (noVar 2 2))
  | 0 => rfl
  | n + 1 => by
    have k : (List.range (n + 1)).flatMap (fun _ => entries (noVar 2 2)) =
        (0 :: List.range n).flatMap (fun _ => entries (noVar 2 2)) := constFlat _ _ _ (by simp)
    rw [k, List.flatMap_cons, ← partsE_eq n, entries_noVar]
    show sumE 0 2 2 ++ (partsE n ++ []) = _
    rw [List.append_nil]

theorem levelE_eq (m : Nat) : levelE m ++ [] = First.ProdV.levelEntries m := by
  unfold levelE First.ProdV.levelEntries
  have e : entries { lead := 0, vs := List.replicate m (MaskedSum.Var.point zeroE 3),
                     ends := some First.ProdV.levelEnds } =
      sumE m 2 2 := by
    show ([entry "PSC epsilon" (0 + 1) 1 0] ++
        ((List.replicate m (MaskedSum.Var.point zeroE 3)).map fun v =>
          entry "PSC round" (v.d - 1) 1 0)) ++
      [entry "PSC Y" 2 1 1, entry "PSC values" 2 0 0] = _
    rw [List.map_replicate]
    rfl
  rw [e, List.append_nil, List.append_nil]
  rfl

theorem runE_eq (m0 n : Nat) : runE m0 n = First.ProdV.runEntries m0 n := by
  unfold runE First.ProdV.runEntries
  have e : (fun i => levelE (m0 + i) ++ []) = fun i => First.ProdV.levelEntries (m0 + i) := by
    funext i
    exact levelE_eq _
  rw [e]

theorem keysE_eq : ∀ (l : List Nat) (k : Nat), keysE (l.zipIdx k) =
    l.flatMap (fun v => First.ProdV.runEntries 0 v)
  | [], _ => rfl
  | v :: l, k => by
    show runE 0 v ++ (keysE (l.zipIdx (k + 1)) ++ []) = _
    rw [List.flatMap_cons, keysE_eq l (k + 1), runE_eq, List.append_nil]

theorem openE_eq (f : Face) : openE (leafDs f) =
    entries { lead := 0, vs := leafVars f #[], ends := none } := by
  rw [leafVars_eq, ← leafDs_eq f #[], ← entries_openCall]
  rfl

theorem bitsE_eq (m : Nat) : sumE m 2 1 = entries (bitsCall (List.replicate m zeroE)) := by
  have e := entries_callOf (List.replicate m zeroE) 2 1
  rw [List.length_replicate] at e
  exact e.symm

/-- **The entries as the binds lay them are entriesV f.** -/
theorem esMsg_eq (f : Face) : esMsg f = entriesV f := by
  unfold esMsg entriesV
  rw [tieE_eq, partsE_eq, keysE_eq, runE_eq, openE_eq, bitsE_eq]
  simp only [List.nil_append, List.append_nil, List.append_assoc]
  rfl

/-! ## The work bits -/

theorem roundT_work (r : Fmt.RoundView) (e : Fmt.Entry) :
    roundT {} r { e with work := 0 } = roundT {} r e := rfl

theorem staticT_work (e : Fmt.Entry) : staticT { e with work := 0 } = staticT e := rfl

theorem tapeT_work : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    tapeT {} rs (es.map fun e => { e with work := 0 }) = tapeT {} rs es
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, e :: es => by
    show tapeT {} (r :: rs) ({ e with work := 0 } :: es.map fun e => { e with work := 0 }) = _
    simp only [tapeT, roundT_work, tapeT_work rs es]

theorem static_work (es : List Fmt.Entry) :
    (es.map fun e => { e with work := 0 }).all staticT = es.all staticT := by
  rw [List.all_map]
  rfl

/-! ## The premise on the entries follows wherever the strict tape is made -/

theorem static_of_round {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound} (h : roundT {} r e = some x) :
    staticT e = true := by
  unfold First.Tape.roundT at h
  cases hs : First.Tape.elemsOf r.vals with
  | none => simp [hs] at h
  | some sent =>
    simp only [hs] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨-, -, a1⟩, -, a2⟩, a3⟩, a5⟩, ⟨⟨-, a6⟩, a7⟩, a8⟩, -⟩ := hc
      have a3' : (e.rows == 0) = true ∧ (e.name != Model.RoundName.batSigma.name) = true := by
        rcases a3 with a3 | a3
        · exact a3
        · cases a3
      have a5' : (Params.kindOf e.name == some (First.Tape.kindAsked e.name)) = true := a5
      unfold staticT
      rw [a1, a2, a3'.1, a3'.2, a5', a6, a7, a8]
      rfl
    · cases h

/-- **Wherever the strict maker makes a tape at es, every entry of es passes the entry-alone
tests.** So the bridge's premise is met at every list of entries at which K3.lean's own hearing has
said yes on some rounds. -/
theorem static_of_tape : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape), tapeT {} rs es =
    some t →
    es.all staticT = true
  | [], [], _, _ => rfl
  | r :: rs, e :: es, t, h => by
    obtain ⟨x, t', k1, k2, -⟩ := tapeT_cons_some h
    show (staticT e && es.all staticT) = true
    rw [static_of_round k1, static_of_tape rs es t' k2]
    rfl
  | [], _ :: _, t, h => by
    have e : (none : Option Tape) = some t := h
    cases e
  | _ :: _, [], t, h => by
    have e : (none : Option Tape) = some t := h
    cases e

/-! ## The bridge -/

/-- **Where hearV says yes, the general text off the strict tape says yes at the plan's entries: the
same ledger, the same values.** -/
theorem hearV_general {f : Face} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hfit : entriesFit f es = true) (hst : es.all staticT = true) (h : hearV f F rs = some (g, G)) :
    flRun {} (messagesG f) es F rs = some (toHeardG g, G) := by
  have he : (es.map fun e => { e with work := 0 }) = esMsg f := by
    rw [esMsg_eq]
    exact eq_of_beq hfit
  have hst' : (esMsg f).all staticT = true := by
    rw [← he, static_work]
    exact hst
  obtain ⟨t, k1, k2⟩ := flRun_some (hearV_flRun hst' h)
  rw [← he, tapeT_work] at k1
  exact flRun_mk k1 k2

/-- The same, as hearG's yes at a place. -/
theorem hearV_hearG {p : PG} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hes : p.entries = some es)
    (hfit : entriesFit p.face es = true) (hst : es.all staticT = true)
      (h : hearV p.face F rs = some (g, G)) :
    hearG p F rs = some (toHeardG g, G) := by
  have hok : p.face.ok = true := by
    cases hk : p.face.ok with
    | true => rfl
    | false =>
      unfold hearV at h
      rw [hk] at h
      have h' : (none : Option (HeardV × Fork)) = some (g, G) := h
      cases h'
  unfold hearG
  rw [hok, hes]
  exact hearV_general hfit hst h

end VerifiableInference.Desc.K3

#print axioms VerifiableInference.Desc.K3.static_of_tape
#print axioms VerifiableInference.Desc.K3.esMsg_eq
#print axioms VerifiableInference.Desc.K3.hearV_general
#print axioms VerifiableInference.Desc.K3.hearV_hearG
